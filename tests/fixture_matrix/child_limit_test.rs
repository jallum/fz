//! The limit on a fixture child measures what the child spends, not what the
//! machine takes from it: a child kept off the CPU is not charged for waiting,
//! a child that burns CPU is, and a child that spends none is still bounded by
//! the wall-clock ceiling.

use super::*;

const CPU_LIMIT: Duration = Duration::from_secs(1);
const HANG_CEILING: Duration = Duration::from_secs(3);
// Far above anything these probes take, so machine load cannot trip it.
const ROOMY_CEILING: Duration = Duration::from_secs(60);

fn run_probe(script: &str, label: &str, cpu: Duration, ceiling: Duration) -> Result<Output, String> {
    run_command(Command::new("sh").args(["-c", script]), label, cpu, ceiling)
}

fn run_command(command: &mut Command, label: &str, cpu: Duration, ceiling: Duration) -> Result<Output, String> {
    let limit = ChildLimit::new(cpu, ceiling);
    guarded_fixture_command(
        command,
        label,
        ExecutionBoundary::Spawn,
        limit,
        limit,
        ReadyWriterAction::Inherit,
    )
    .map(|finished| finished.output)
}

pub(super) fn a_child_kept_off_the_cpu_is_not_charged_for_waiting() {
    let dir = FixtureWorkingDir::new().expect("scratch dir for the pid pipe");
    let fifo = dir.path.join("pid");
    let fifo_c = std::ffi::CString::new(fifo.to_str().expect("utf-8 path")).expect("no NUL in path");
    assert_eq!(unsafe { libc::mkfifo(fifo_c.as_ptr(), 0o600) }, 0, "mkfifo");

    // The child announces its pid on the pipe and stops itself. The controller
    // learns the pid from the pipe, waits for the stop to be reported, lets the
    // child stay off the CPU for longer than its CPU limit, then resumes it.
    let starvation = CPU_LIMIT + CPU_LIMIT / 2;
    let controller_fifo = fifo.clone();
    let controller = std::thread::spawn(move || {
        let mut pid_text = String::new();
        File::open(controller_fifo)
            .and_then(|mut f| f.read_to_string(&mut pid_text))
            .expect("read the child's pid");
        let pid: libc::pid_t = pid_text.trim().parse().expect("a pid");
        wait_until_stopped(pid);
        // The starvation itself is a span of wall time; nothing observable
        // marks its passing.
        std::thread::sleep(starvation);
        assert_eq!(unsafe { libc::kill(pid, libc::SIGCONT) }, 0, "resume the child");
    });

    let started = Instant::now();
    let output = run_command(
        Command::new("sh")
            .env("PID_FIFO", &fifo)
            .args(["-c", "echo $$ > \"$PID_FIFO\"; kill -STOP $$"]),
        "starved child",
        CPU_LIMIT,
        ROOMY_CEILING,
    )
    .expect("a child that spent no CPU is within its CPU limit however long it waited");
    controller.join().expect("controller thread");
    assert!(output.status.success());
    assert!(
        started.elapsed() > CPU_LIMIT,
        "the child must have been kept off the CPU for longer than its limit"
    );
}

fn wait_until_stopped(pid: libc::pid_t) {
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    let rc = unsafe {
        libc::waitid(
            libc::P_PID,
            pid as libc::id_t,
            &mut info,
            libc::WSTOPPED | libc::WNOWAIT,
        )
    };
    assert_eq!(rc, 0, "waitid for the stop: {}", Error::last_os_error());
}

pub(super) fn a_child_that_burns_cpu_past_the_limit_is_charged_for_it() {
    let error = run_probe("while :; do :; done", "burner", CPU_LIMIT, ROOMY_CEILING)
        .expect_err("a child that spends more CPU than its limit exceeds it");
    assert!(
        error.starts_with("burner exceeded 1s of CPU (wall "),
        "the failure names the CPU limit and the wall time: {error}"
    );
}

pub(super) fn a_descendant_that_burns_cpu_is_charged_to_the_child() {
    let error = run_probe(
        "(while :; do :; done) & wait",
        "parent of a burner",
        CPU_LIMIT,
        ROOMY_CEILING,
    )
    .expect_err("the CPU of a descendant counts against the child that started it");
    assert!(
        error.starts_with("parent of a burner exceeded 1s of CPU (wall "),
        "{error}"
    );
}

pub(super) fn a_child_that_hangs_hits_the_wall_ceiling() {
    let error = run_probe("sleep 600", "hung child", CPU_LIMIT, HANG_CEILING)
        .expect_err("a child that spends no CPU and never exits is stopped by the wall ceiling");
    assert!(
        error.starts_with("hung child exceeded the 3s wall ceiling (CPU 0."),
        "the failure names the ceiling and the CPU spent: {error}"
    );
}

pub(super) fn a_failure_names_both_the_cpu_and_the_wall_time() {
    let charge = child_limit::Charge {
        cpu: Duration::from_millis(20_400),
        wall: Duration::from_millis(31_200),
    };
    let limit = ChildLimit::of_cpu(Duration::from_secs(20));
    assert_eq!(
        limit.exceeded(charge).expect("over the CPU limit").to_string(),
        "20s of CPU (wall 31.2s)"
    );

    let hung = child_limit::Charge {
        cpu: Duration::from_millis(300),
        wall: Duration::from_secs(200),
    };
    assert_eq!(
        limit.exceeded(hung).expect("over the ceiling").to_string(),
        "the 200s wall ceiling (CPU 0.3s)"
    );

    let waiting = child_limit::Charge {
        cpu: Duration::from_secs(5),
        wall: Duration::from_secs(150),
    };
    assert_eq!(limit.exceeded(waiting), None, "waiting under the ceiling is free");
}

pub(super) fn a_cpu_limits_wall_ceiling_does_not_shrink_with_the_budget() {
    let small = ChildLimit::of_cpu(Duration::from_secs(1));
    assert_eq!(
        small.wall_ceiling(),
        ChildLimit::of_cpu(DEFAULT_FIXTURE_CPU_LIMIT).wall_ceiling(),
        "the wall ceiling backstops a hang whatever the budget is"
    );

    // A child that is running but kept off the CPU for far longer than its
    // budget has spent almost no CPU; waiting is not a verdict.
    let starved = child_limit::Charge {
        cpu: Duration::from_millis(100),
        wall: Duration::from_secs(11),
    };
    assert_eq!(
        small.exceeded(starved),
        None,
        "a starved child that is still running is not over a limit"
    );
}

/// Linux reads a group's CPU from `/proc/<pid>/stat`; the line is parsed the
/// same way on every platform so its reading is exercised everywhere.
pub(super) fn a_proc_stat_line_is_charged_to_its_group_by_the_fields_after_the_command_name() {
    // pid (comm) state ppid pgrp session tty tpgid flags minflt cminflt majflt
    // cmajflt utime stime cutime cstime ...; the command name holds spaces and ')'.
    let stat = "4242 (odd) name) S 1 4200 4200 0 -1 4194560 100 0 0 0 7 5 3 1 20 0 1 0";
    assert_eq!(child_limit::member_ticks(stat, 4200), Some(7 + 5 + 3 + 1));
    assert_eq!(
        child_limit::member_ticks(stat, 4201),
        None,
        "another group's process is not charged"
    );
}
