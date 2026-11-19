# usage: trace.py BIN BPSYM SKIP MAXSTEPS [STOPMODE]
# Runs BIN, breaks on BPSYM (nth hit = SKIP+1), then single-steps recording pcs until
# BPSYM address is hit again (STOPMODE=loop) or MAXSTEPS reached; prints annotated trace.
import sys,subprocess,re,bisect
sys.path.insert(0,subprocess.check_output(["lldb","-P"]).decode().strip())
import lldb
binp,sym,skip,maxsteps=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4])
mode="loop"; args=sys.argv[5:]
# static tables
nm=subprocess.check_output(["nm","-n",binp]).decode().splitlines()
syms=[]
for l in nm:
    p=l.split(None,2)
    if len(p)==3 and p[1] in "tT": syms.append((int(p[0],16),p[2]))
addrs=[a for a,_ in syms]
dis={}
out=subprocess.check_output(["objdump","-d","--no-show-raw-insn",binp]).decode().splitlines()
for l in out:
    m=re.match(r"\s*([0-9a-f]+):\s+(.*)",l)
    if m: dis[int(m.group(1),16)]=m.group(2).strip()
def symof(a):
    i=bisect.bisect_right(addrs,a)-1
    if i<0: return "?"
    n=syms[i][1]
    return "%s+%#x"%(n,a-syms[i][0])
dbg=lldb.SBDebugger.Create(); dbg.SetAsync(False)
t=dbg.CreateTarget(binp)
bp=t.BreakpointCreateBySBAddress(t.GetModuleAtIndex(0).ResolveFileAddress(int(sym,16))) if sym.startswith("0x") else t.BreakpointCreateByName(sym)
err=lldb.SBError()
proc=t.LaunchSimple(args,None,".")
hits=0
for i in range(skip+1):
    if proc.GetState()!=lldb.eStateStopped: print("exited early",i); sys.exit(1)
    if i<skip: proc.Continue()
th=proc.GetSelectedThread()
start=th.GetFrameAtIndex(0).GetPC()
o=subprocess.check_output(["otool","-l",binp]).decode()
mm=re.search(r"sectname __text\n\s+segname __TEXT\n\s+addr (0x[0-9a-f]+)\n\s+size (0x[0-9a-f]+)",o)
tend=int(mm.group(1),16)+int(mm.group(2),16)
ext={}
pcs=[start]
lo=start; hi=min([x for x in addrs if x>start-th.GetFrameAtIndex(0).GetModule().FindSection("__TEXT").GetLoadAddress(t)+th.GetFrameAtIndex(0).GetModule().FindSection("__TEXT").GetFileAddress()] or [0])
for s in range(maxsteps):
    th.StepInstruction(False)
    if proc.GetState()!=lldb.eStateStopped: break
    pc=th.GetFrameAtIndex(0).GetPC()
    pcs.append(pc)
    if pc>=tend and pc not in ext:
        f=th.GetFrameAtIndex(0); ext[pc]=(f.GetSymbol().GetName() or "?")+"+EXT"
# One steady-state iteration: between the last two visits to the least-visited
# instruction of the loop function in the second half of the recording.
import collections
half=pcs[len(pcs)//2:]
own=[p for p in half if symof(p).startswith(symof(start).split("+")[0]+"+")]
cnt=collections.Counter(own)
least=min(c for c in cnt.values() if c>=2)
anchor=[p for p in own if cnt[p]==least][0]
idx=[i for i,p in enumerate(pcs) if p==anchor]
pcs=pcs[idx[-2]:idx[-1]]
slide=0
for pc in pcs:
    print("%x  %-48s %s"%(pc,dis.get(pc,"??"),ext[pc] if pc in ext else symof(pc)))
print("TOTAL",len(pcs),file=sys.stderr)
proc.Kill()
