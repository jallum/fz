//! What a fixture child may spend before the harness stops it.
//!
//! A limit on a child's wall-clock time measures the machine: a child waiting
//! for a core is charged as if it were working. The limit here is on the CPU
//! the child and its descendants spend (user plus system), read while they
//! run. A hung child spends no CPU, so a wall-clock ceiling beside the CPU
//! limit still stops it.

use std::time::Duration;

/// How many times the CPU limit the wall-clock ceiling allows.
const CEILING_FACTOR: u32 = 10;

/// How often a running child's CPU is read.
pub(super) const SAMPLE_INTERVAL: Duration = Duration::from_millis(200);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ChildLimit {
    cpu: Duration,
    wall_ceiling: Duration,
}

impl ChildLimit {
    pub(super) fn new(cpu: Duration, wall_ceiling: Duration) -> Self {
        Self { cpu, wall_ceiling }
    }

    /// A CPU limit with the standard wall-clock ceiling.
    pub(super) fn of_cpu(cpu: Duration) -> Self {
        Self::new(cpu, cpu * CEILING_FACTOR)
    }

    pub(super) fn wall_ceiling(&self) -> Duration {
        self.wall_ceiling
    }

    /// What a window that has spent `charge` has exceeded, if anything.
    pub(super) fn exceeded(&self, charge: Charge) -> Option<Exceeded> {
        if charge.cpu >= self.cpu {
            Some(Exceeded::Cpu {
                limit: self.cpu,
                charge,
            })
        } else if charge.wall >= self.wall_ceiling {
            Some(Exceeded::WallCeiling {
                ceiling: self.wall_ceiling,
                charge,
            })
        } else {
            None
        }
    }
}

/// What a child has spent inside one window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Charge {
    pub(super) cpu: Duration,
    pub(super) wall: Duration,
}

/// A limit that was passed, worded with both numbers so a failure says whether
/// the child worked too long or merely lived too long.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Exceeded {
    Cpu { limit: Duration, charge: Charge },
    WallCeiling { ceiling: Duration, charge: Charge },
}

impl std::fmt::Display for Exceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cpu { limit, charge } => {
                write!(f, "{limit:?} of CPU (wall {})", seconds(charge.wall))
            }
            Self::WallCeiling { ceiling, charge } => {
                write!(f, "the {ceiling:?} wall ceiling (CPU {})", seconds(charge.cpu))
            }
        }
    }
}

fn seconds(duration: Duration) -> String {
    format!("{:.1}s", duration.as_secs_f64())
}

/// The CPU one window has charged: a baseline taken when the window opened,
/// and the highest group total seen since. A group's total can fall when a
/// member exits before its parent collects its time, so the charge follows the
/// peak.
#[derive(Debug)]
pub(super) struct Window {
    started: std::time::Instant,
    baseline: Duration,
    peak: Duration,
}

impl Window {
    pub(super) fn open(started: std::time::Instant, group_cpu: Duration) -> Self {
        Self {
            started,
            baseline: group_cpu,
            peak: group_cpu,
        }
    }

    pub(super) fn started(&self) -> std::time::Instant {
        self.started
    }

    pub(super) fn charge(&mut self, group_cpu: Duration) -> Charge {
        self.peak = self.peak.max(group_cpu);
        Charge {
            cpu: self.peak - self.baseline,
            wall: self.started.elapsed(),
        }
    }
}

/// The CPU time spent so far by the process group led by `leader`: every live
/// member, plus the time of members their parents have already collected.
pub(super) fn group_cpu_time(leader: libc::pid_t) -> Result<Duration, String> {
    platform::group_cpu_time(leader)
}

/// The user, system and collected-children ticks of the process described
/// by a `/proc/<pid>/stat` line, when it belongs to group `leader`. The
/// command name is parenthesised and may hold spaces, so fields are
/// counted from the closing parenthesis.
#[cfg(any(target_os = "linux", test))]
pub(super) fn member_ticks(stat: &str, leader: libc::pid_t) -> Option<u64> {
    let after_name = &stat[stat.rfind(')')? + 1..];
    let fields: Vec<&str> = after_name.split_whitespace().collect();
    // fields[0] is the state (field 3 of proc(5)).
    let group: libc::pid_t = fields.get(2)?.parse().ok()?;
    if group != leader {
        return None;
    }
    let ticks = |proc_field: usize| fields.get(proc_field - 3)?.parse::<u64>().ok();
    Some(ticks(14)? + ticks(15)? + ticks(16)? + ticks(17)?)
}

#[cfg(target_os = "linux")]
mod platform {
    use std::fs;
    use std::time::Duration;

    pub(super) fn group_cpu_time(leader: libc::pid_t) -> Result<Duration, String> {
        let ticks_per_second = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
        if ticks_per_second <= 0 {
            return Err("sysconf(_SC_CLK_TCK) is unavailable".to_string());
        }
        let entries = fs::read_dir("/proc").map_err(|error| format!("read /proc: {error}"))?;
        let mut ticks = 0_u64;
        for entry in entries.flatten() {
            let is_pid = entry.file_name().to_string_lossy().bytes().all(|b| b.is_ascii_digit());
            if !is_pid {
                continue;
            }
            // A process that exits between listing and reading is gone, not an error.
            let Ok(stat) = fs::read_to_string(entry.path().join("stat")) else {
                continue;
            };
            if let Some(member_ticks) = super::member_ticks(&stat, leader) {
                ticks += member_ticks;
            }
        }
        Ok(Duration::from_secs_f64(ticks as f64 / ticks_per_second as f64))
    }
}

#[cfg(target_os = "macos")]
mod platform {
    use std::mem::MaybeUninit;
    use std::time::Duration;

    /// The ratio between mach absolute-time units and nanoseconds. The `libc`
    /// binding is deprecated in favour of a crate this harness does not use.
    #[repr(C)]
    struct MachTimebase {
        numer: u32,
        denom: u32,
    }

    unsafe extern "C" {
        fn mach_timebase_info(info: *mut MachTimebase) -> libc::c_int;
    }

    pub(super) fn group_cpu_time(leader: libc::pid_t) -> Result<Duration, String> {
        let members = group_members(leader)?;
        let mut mach_units = 0_u128;
        for pid in members {
            mach_units += member_mach_units(pid);
        }
        Ok(mach_units_to_duration(mach_units))
    }

    /// The live members of the group. The call reports how many it listed in
    /// its own units, so the list is read up to its first unused slot.
    fn group_members(leader: libc::pid_t) -> Result<Vec<libc::pid_t>, String> {
        const CAPACITY: usize = 4096;
        let mut pids: Vec<libc::pid_t> = vec![0; CAPACITY];
        let listed = unsafe {
            libc::proc_listpgrppids(
                leader,
                pids.as_mut_ptr().cast(),
                (CAPACITY * size_of::<libc::pid_t>()) as libc::c_int,
            )
        };
        if listed < 0 {
            return Err(format!(
                "proc_listpgrppids {leader}: {}",
                std::io::Error::last_os_error()
            ));
        }
        pids.retain(|pid| *pid > 0);
        if pids.len() == CAPACITY {
            return Err(format!("process group {leader} fills the {CAPACITY}-pid listing"));
        }
        Ok(pids)
    }

    /// The user, system and collected-children time of one process in mach
    /// absolute-time units. A process that has exited since it was listed has
    /// nothing to read.
    fn member_mach_units(pid: libc::pid_t) -> u128 {
        let mut usage = MaybeUninit::<libc::rusage_info_v2>::zeroed();
        let rc = unsafe { libc::proc_pid_rusage(pid, libc::RUSAGE_INFO_V2, usage.as_mut_ptr().cast()) };
        if rc != 0 {
            return 0;
        }
        let usage = unsafe { usage.assume_init() };
        [
            usage.ri_user_time,
            usage.ri_system_time,
            usage.ri_child_user_time,
            usage.ri_child_system_time,
        ]
        .into_iter()
        .map(u128::from)
        .sum()
    }

    fn mach_units_to_duration(units: u128) -> Duration {
        let mut timebase = MachTimebase { numer: 0, denom: 0 };
        let rc = unsafe { mach_timebase_info(&mut timebase) };
        assert_eq!(rc, 0, "mach_timebase_info");
        let nanos = units * u128::from(timebase.numer) / u128::from(timebase.denom);
        Duration::from_nanos(u64::try_from(nanos).expect("CPU nanoseconds fit in u64"))
    }
}
