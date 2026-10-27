# Paper G — cross-machine reproduction of paperg_brocard on the arm64 machine (2026-10-25)

**Result: reproduced.** On the arm64 machine the build, gate and tamper checks all pass. Every .lean file in both Paper G repos is byte-identical to the x86-64 machine's. The leancheck battery gives exactly the same summary numbers as the x86-64 machine's run.

## Setup
- Copied the x86-64 machine:~/paperg_brocard to the arm64 machine:~/lean/paperg_brocard without .lake. the arm64 machine cannot ssh to the x86-64 machine itself (`Host key verification failed`), so the tar stream was piped through the orchestrator host: `ssh <x86-64 host> 'tar czf - --exclude=.lake paperg_brocard' | ssh <arm64 host> 'tar xzf - -C ~/lean/'`.
- `.lake/packages -> ~/lean/clifford/.lake/packages`. lean-toolchain `leanprover/lean4:v4.33.1` matches clifford, and lake-manifest.json is identical to clifford's.
- git HEAD is the same on both machines and both worktrees are clean (0 lines from `git status --porcelain`):
  - paperg_brocard `e23b8c3a3bd9446b1b90f917820e67bc87d35133`
  - paperg_nagel `16b07eb67c9ec732cec35b2c030946ce3faf5990`

## Build / gate / tamper (the arm64 machine, ~/lean/paperg_brocard)
| step | line | rc |
|---|---|---|
| `~/lean/jl build` (system/BSD tools) | `✔ [8711/8712] Built Brocard (2.9s)` / `Build completed successfully (8712 jobs).` (37 s wall; unused-tactic linter warnings only) | ok |
| `~/lean/jl gate` | `PASS (67 declarations, standard axioms only)` | 0 |
| `~/lean/jl -g tamper` | `ALL TAMPERING TESTS REJECTED` (7/7: sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2) | 0 |

## .lean hash comparison (sha256: the x86-64 machine `sha256sum`, the arm64 machine `shasum -a 256`)
- paperg_brocard: 6 files on the x86-64 machine and 6 on the arm64 machine. **IDENTICAL**
- paperg_nagel: 4 files on the x86-64 machine and 4 on the arm64 machine. **IDENTICAL**

```
ae99086feccb3ee068ac1a208d5500b08a0fe42bb4fbf560a3fc605eb37fe1c4  ./Brocard/Basic.lean
76dbd72a906fe7da7a8dbdb32cd79c82a706f9612fd22119632b127cd7f37c2a  ./Brocard/Extensions.lean
f85d6ad0c7218d91929a59c72f03f5f4098c838430ff0ac26e639fb36dc1e42f  ./Brocard/ExtLemmas.lean
175852a1f7616d8780bb48f882c3de57ae1409aba43eebf967661bea5757f648  ./Brocard.lean
bd3f5bad07c560d1a0f2761b372d4a852cddaf4fd732c262575ba3958d630e29  ./Brocard/Lemmas.lean
b57048dcad1ac875579cd4371b57ab5789dc773e8007c7c4cb6533c1ff10a9b1  ./Brocard/Main.lean
ea4380692d8cfbbead1a4c5f28ca2b556a89e73df1078d4a7d3ba909a576e641  ./NagelLine/Basic.lean
a5fcb3bba5f58a5f4f4034417245068861f90e241171ae3ff6e3169f54a91d95  ./NagelLine/Extensions.lean
f2369819eb85d4e3979d40f87a435462453050b33d72e2e9bff7fba55cd7089a  ./NagelLine.lean
51a82eaf0660b68298f5fbe12d71c61548e9784180a8992a4a8517d64517c2fd  ./NagelLine/Main.lean
```

## Battery (the arm64 machine, `WORKERS=4 bash ~/leancheck/run_john.sh paperg_brocard`)
Run from 21:35:09 to 22:41:32 UTC (66 min), `END paperg_brocard rc=0`.
Report: `the arm64 machine:~/leancheck/reports/paperg_brocard_20261025_213509.md` (log `.log`, nohup log `paperg_brocard_batt.log`)

```
{"thm": 68, "mut": 152, "killed": 152, "surv": 0, "tout": 0, "contra": 0, "sat": 7, "unres": 61, "nohyp": 0, "invalid": 0}
jobs 111 | UNUSED 0 | NEEDED 111 | SKIP 0 | timeout 0 | bad-control decls 0
```

The x86-64 machine's run (`the x86-64 machine:~/leancheck/reports/paperg_brocard_20261025_164034.md`) has exactly the same two lines.

Other layers:
- Contradiction probe: 0 contradictory, 28 probed ok.
- Linter: 0 warnings in 4 library files.
- Bridge inventory: 2 notions, both NO-BRIDGE.
- Satisfiability: 7/68 certified, 61 unresolved, recorded as unresolved and not counted as success. Most of the unresolved ones are coordinate lemmas.

**Error in the verdict table:** the .md verdict table says gate "no PASS/FAIL line found" and tamper "0/0 … not all rejected". This is a parsing error in the verdict script. Section "Layers 1-2" of the same report contains the verbatim `PASS (67 declarations, standard axioms only)` and `ALL TAMPERING TESTS REJECTED` lines. the arm64 machine's earlier paperg_nagel report (20261025_154123) shows the same false table entries, so the error was already there before this run and has nothing to do with these repos. It should be fixed in `~/leancheck/verdict.py` on the arm64 machine.
