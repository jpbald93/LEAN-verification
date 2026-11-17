# Paper I — clean-tree rebuild receipts (2026-11-10)

**What this is and is not.** None of the four repositories has a remote, so **no `git clone` was performed**. Each receipt is a rebuild from a pristine `git archive <commit>` export (tracked files only, no `.git`, no `.lake`, no untracked or git-ignored files from the working copy) into `~/receipts/<repo>` on the repo's own host, with an empty `.lake/` except for a `.lake/packages` symlink to the source repo's existing dependency checkout. The project's own build cache (`.lake/build`) was not copied: every project module was compiled from source in the export (the build logs show `Built <Module>` for each). **The dependencies were *not* rebuilt from scratch**: the linked packages directory already holds compiled Mathlib/Batteries/Aesop/… artefacts, which `lake` replayed (~8705 of the jobs per build). The Mathlib checkout behind each link was verified clean (`git status --porcelain` empty) at rev `0df444a360eaa60ab8c11dca51a86af692955474`, the same rev pinned in each `lake-manifest.json`.

All four exports built, passed `gate.sh`, and had every tamper test rejected. Nothing in any export was edited.

Every number below comes from a command run on 2026-11-10 (~20:52–20:57 UTC). Raw logs are in `raw/` (`<repo>.log` summary, `.build.log`, `.gate.log`, `.tamper.log`, `.lean.sha`, `.src.lean.sha`); the driver script is `scripts/receipt.sh`.

**On the digest check against the working tree.** Each source working tree has exactly one `.lean` file the export doesn't: `scratch/L15_compare.lean`. It is untracked and git-ignored via `.git/info/exclude` (`scratch/`), so `git status --porcelain` is empty even though the file exists. It is a working-copy leftover that `git archive` correctly leaves out. It is not part of the library and isn't imported (the gate's `SOURCES` only covers `<Lib>/*.lean` + `<Lib>.lean`). Every `.lean` file the export *does* contain matches its working-tree counterpart byte for byte (the `diff` output shows only that one added line), and the tree digest of the source's **tracked** `.lean` files (`git ls-files '*.lean'`) equals the export tree digest for all four repos. So I count this mismatch as explained, and all four stand as receipts.

## paperi_quad

- host: jack (gmktec x86_64  date: 2026-11-10T20:52:40Z)
- source: `~/final_quad`, HEAD `0c372061edd32cc7935cf1521d404dfbc3993ac5`, `git status --porcelain` lines: 0
- commit: `0c372061edd32cc7935cf1521d404dfbc3993ac5`
- export path: `~/receipts/paperi_quad` (`git archive 0c372061edd32cc7935cf1521d404dfbc3993ac5 | tar -x`); `find -name .lake` in the fresh export: none
- packages target: `/home/jackagent/paperi_quad/.lake/packages`
- `git status` in export: not a git repository (`fatal: not a git repository`), as expected for an archive export
- `lake build`: exit 0, wall 39s; last line: `Build completed successfully (8718 jobs).`
- `gate.sh`: exit 0, wall 8s; PASS line: `PASS (133 declarations, standard axioms only)`
- `tests/tamper.sh`: exit 0, wall 96s; final line: `ALL TAMPERING TESTS REJECTED`; `ok … rejected` lines: 11
- lean-toolchain: `leanprover/lean4:v4.33.1`; Mathlib rev (lake-manifest.json): `0df444a360eaa60ab8c11dca51a86af692955474`
- Note: this commit *tracks* 9 files under `scratch/` (B, C, C2, E, N, P, PC, T, VA `.lean`), so they show up in the export. They are committed content, not working-copy leftovers. They are not part of the `Quadrilaterals` lib target and were not built.
- `.lean` tree digest (export, `LC_ALL=C sort`): `8a67f0c8e1894d090bf3140add6c9c01f2b34b943e76c2145af6c24e4f3281a4` (= tracked `.lean` files in source; source WT incl. untracked `scratch/L15_compare.lean`: `d60540e33d58ae7d11aee16f7eaaef569bc7114a150f3c8f1e0d488859f4ac1d`)

Per-file `.lean` sha256 (export):
```
994465397d276ad2e15a5d1d243b4bbeb6c07b999537d03c562ecf1466ff19b5  ./Quadrilaterals.lean
8776fcc1e870a1e6d401f4b29115c2abdcd284f733609cefd82606dbf9e75d3b  ./Quadrilaterals/Algebra.lean
3c2a8dd65ce6eb3384fac01269182b1ba43e5880792aa08e3e2a35acf12d7fff  ./Quadrilaterals/Basic.lean
e9b402bd43dbb129b61fe39c9780f9512d842295b0b7be5d239e046a287a992c  ./Quadrilaterals/Bridge.lean
df1466608b238b0eb7bf00067268fc447a2b26733b6528a299e5a1af20e0a80e  ./Quadrilaterals/Bridges.lean
6b32f1e93139a4f0b89697029d0967be5b2748548f2f07cc32faedaf69b220e1  ./Quadrilaterals/Coord.lean
2d6f93eba01a389ce8e41a8b7beacb405a487fa0b16f00aa2cec915a5024c8bb  ./Quadrilaterals/Cyclic.lean
aecf1e2175401c68ae6358674d61021cef5f7a96f0d9314892aa26ecbf9a2023  ./Quadrilaterals/Frame.lean
bf8225d1a42b4d7d1e96f8748e5627fdf27b985ce2c6d9788486a9107cce897d  ./Quadrilaterals/Fuss.lean
7442d6b0f477c43cf5ca7ab1c284bb7c40e91100998dd12e371b009f4bf94345  ./Quadrilaterals/FussAlg.lean
3a7fa40d0c76251a5537a5144dab3e6b5cc9ed21fa69063d6e002608d73e33f9  ./Quadrilaterals/L14.lean
2635f19170bceb3669de95fae190396d43ae2ba1c589e99bd65b7c1801ec4050  ./Quadrilaterals/Main.lean
a1b7dc5703d63c0b701dfb16909299e9f5052cd3f4ac56cd1eac7836336f7b6c  ./scratch/B.lean
6fdf95362df8b978aee6c5a7a6f0f92272085ba232d37f46b5e6b685fe2bb9aa  ./scratch/C.lean
f5945a9ae03a71674145d2879eec161ca10096a802f70d01599841231e130eee  ./scratch/C2.lean
9c31805b41bba5ea2214f5f7ac544a07e07595dc4e22ace44c6a61333eba417d  ./scratch/E.lean
102f4c014a3e91558c31dda14c8b3afc5cb5c0b9c33e1303d79d0e205b85ac0c  ./scratch/N.lean
19c167a5080ab001900b21b6de49ea26f6cd6f5ca4ac6639fa44c04a8976affd  ./scratch/P.lean
fd05ba0c8e539175ffb5cfe86d98a53244e71d1612c0e625c7620dacf63389d6  ./scratch/PC.lean
b1bf39176c93f598fbb3386c9a31f8c2ff6f60d50ce8397c6a57c9d80e28fb76  ./scratch/T.lean
7a47c6b1e658b850664c1e32e2fa001f6d481903a63c0e5c0357a7516a2421ac  ./scratch/VA.lean
```
Config/gate digests:
```
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
e23e42856489dd279d0bcfab5a02ca35a70cc9cd994ef7a86ad8866d09377a36  lakefile.toml
ab486de198559df0c65f6e73b1bbf3851f4410612b9344436ec734242ed22f8d  lake-manifest.json
e9cac5e65eb47b53ec6299fa367823d9376bc3819a8d8a3efa8e3bf498a8ea1a  gate.sh
662136a0ae012c46a36074a7cf02b4e0456a06e1a92a0ceebe0799ca7ba484b2  tests/tamper.sh
```
## paperi_circles

- host: jack (gmktec x86_64  date: 2026-11-10T20:55:03Z)
- source: `~/final_circles`, HEAD `6c714e57d5cf41a43838d2a0e380fdc028e9b15b`, `git status --porcelain` lines: 0
- commit: `6c714e57d5cf41a43838d2a0e380fdc028e9b15b`
- export path: `~/receipts/paperi_circles` (`git archive 6c714e57d5cf41a43838d2a0e380fdc028e9b15b | tar -x`); `find -name .lake` in the fresh export: none
- packages target: `/home/jackagent/paperi_circles/.lake/packages`
- `git status` in export: not a git repository (`fatal: not a git repository`), as expected for an archive export
- `lake build`: exit 0, wall 24s; last line: `Build completed successfully (8714 jobs).`
- `gate.sh`: exit 0, wall 8s; PASS line: `PASS (121 declarations, standard axioms only)`
- `tests/tamper.sh`: exit 0, wall 48s; final line: `ALL TAMPERING TESTS REJECTED`; `ok … rejected` lines: 9
- lean-toolchain: `leanprover/lean4:v4.33.1`; Mathlib rev (lake-manifest.json): `0df444a360eaa60ab8c11dca51a86af692955474`
- `.lean` tree digest (export, `LC_ALL=C sort`): `db7c08cac4acaed6c92671b435413c73261032f0a2a3ef07d22af1191d8a759f` (= tracked `.lean` files in source; source WT incl. untracked `scratch/L15_compare.lean`: `1072903e0b1e8f78c57e57cfe9593e5a492abf9aedf2179e3361870b819ffeb4`)

Per-file `.lean` sha256 (export):
```
e2f0579a99d05368c197525419cdbc67c1cfcbb378f45b81f6bd85d965aa8386  ./CircleSystems.lean
3e21b055d4b6640b582279c0477130a994b6eb4cacefe24b57979a4bc5d030b4  ./CircleSystems/Bridge.lean
661db8cb5a3a4c96f6598647b1e70afa890f773c1fd0f153aebd0f1321e940c6  ./CircleSystems/Coaxal.lean
2a690b88e4b06bcabc0740cabcc6e174c9efb4c6a69a7b457e32047953af3b1c  ./CircleSystems/Coord.lean
11942585e088535d61b7dfeb0c4985b1aabf9613fce07c931526eae6232a6e18  ./CircleSystems/Johnson.lean
bef435c55146c508932ea68fd0e200614e9b879026e510b4753d1c37e47eafb5  ./CircleSystems/L14.lean
634d749617a2eb4b542ef22466b1375cfece730e37b5bbdc20320db75b4d0286  ./CircleSystems/PowerOfPoint.lean
4e02ce0848b0058b09ae10ff0cd8870a1e0b7b9ccd7073581b15dfff4ae27b42  ./CircleSystems/SimsonSteiner.lean
```
Config/gate digests:
```
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
a2d2d73ac3373d35efd6cd34bffd6ca6feab81aacf2c944dda1b01b3095577a3  lakefile.toml
ab486de198559df0c65f6e73b1bbf3851f4410612b9344436ec734242ed22f8d  lake-manifest.json
6965e496f488a48bb069d3291cc204c7b970e8eb8d59a17730322924f324ac67  gate.sh
a8ec15f5a19f00c4dd0ca2ac3026e1982fd44f0749b08ab30f702d6e0a791aab  tests/tamper.sh
```
## paperi_arbelos

- host: john (Joshs-Mac-Mini.local arm64  date: 2026-11-10T20:52:43Z)
- source: `~/lean/final_arbelos`, HEAD `0dddc6e05fc14ad3d25325aecfc1ca225837ae6b`, `git status --porcelain` lines: 0
- commit: `0dddc6e05fc14ad3d25325aecfc1ca225837ae6b`
- export path: `~/receipts/paperi_arbelos` (`git archive 0dddc6e05fc14ad3d25325aecfc1ca225837ae6b | tar -x`); `find -name .lake` in the fresh export: none
- packages target: `/Users/john/lean/paperi_arbelos/.lake/packages`
- `git status` in export: not a git repository (`fatal: not a git repository`), as expected for an archive export
- `lake build`: exit 0, wall 30s; last line: `Build completed successfully (8716 jobs).`
- `gate.sh`: exit 0, wall 9s; PASS line: `PASS (138 declarations, standard axioms only)`
- `tests/tamper.sh`: exit 0, wall 50s; final line: `ALL TAMPERING TESTS REJECTED`; `ok … rejected` lines: 7
- lean-toolchain: `leanprover/lean4:v4.33.1`; Mathlib rev (lake-manifest.json): `0df444a360eaa60ab8c11dca51a86af692955474`
- `.lean` tree digest (export, `LC_ALL=C sort`): `2b43ae51b309604c290213bfaba4d459551116d7ea079a1ab4fd9b6233506264` (= tracked `.lean` files in source; source WT incl. untracked `scratch/L15_compare.lean`: `a00010627ebfd73b6be1bcc85932ae2c1f2ba25938172c26b0ae2d3372c2ba6e`)

Per-file `.lean` sha256 (export):
```
ab06299ecc106134cab75c187f4ec79bf203569e4d2cff5d7f839da0aa14332b  ./Arbelos.lean
15513196a5d978ab5fb93e1740a57710065d523289deee46a0fd31b21b58c76f  ./Arbelos/Area.lean
e118f6eed44e821d1b7ef52d7782adc536ebd1117afdfdb6e2b205eb712f3c21  ./Arbelos/Bankoff.lean
d6dcc9d46596e62be30fb466a8c5d0b2ca56b9433b35afadf981fd4b3b1de3a3  ./Arbelos/Basic.lean
ebfc04c342e6afac3663fd6e8f3756cb454c8593f69af5c36574132177b3ee58  ./Arbelos/Bridge.lean
0392e4a21196616c063e7e0fc73a8dc4790253ba9576022952a13fdc7a598b74  ./Arbelos/Inversion.lean
d9712ccf27fe9c2211c905a78de266ce4ef422018cde263ea77a7ff57a6cea46  ./Arbelos/L14.lean
b64662926ed4fa87e8d44cdea3c757e257161f33a36b7014ed277885149a3383  ./Arbelos/Pappus.lean
3e1eadd433d43308c4ed75921c5275ea89c12c575ad180a9011aaeda9c4ec661  ./Arbelos/Steiner.lean
bb995d95c1122731ff2662f0ce67ee75a48e8cc96bbd28ef19f2411bf4ae73d9  ./Arbelos/Twin.lean
```
Config/gate digests:
```
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
b21ee844e5623d5e08fbbdd5df81f3a6a840f24d4366b8df0a269b84c7cceffc  lakefile.toml
ab486de198559df0c65f6e73b1bbf3851f4410612b9344436ec734242ed22f8d  lake-manifest.json
4a610bb1373e943b7bea166b50b66ae00914e210a798bcf7eb7964c8d201d372  gate.sh
0d930b6d66055b096ae7cc33c21a02179124037db00845c90411c2ef038c2092  tests/tamper.sh
```
## paperi_inversion

- host: john (Joshs-Mac-Mini.local arm64  date: 2026-11-10T20:54:12Z)
- source: `~/lean/final_inversion`, HEAD `c71abb76b265d660ae2d73b629beac2c338c8b27`, `git status --porcelain` lines: 0
- commit: `c71abb76b265d660ae2d73b629beac2c338c8b27`
- export path: `~/receipts/paperi_inversion` (`git archive c71abb76b265d660ae2d73b629beac2c338c8b27 | tar -x`); `find -name .lake` in the fresh export: none
- packages target: `/Users/john/lean/paperi_arbelos/.lake/packages`
- `git status` in export: not a git repository (`fatal: not a git repository`), as expected for an archive export
- `lake build`: exit 0, wall 25s; last line: `Build completed successfully (8713 jobs).`
- `gate.sh`: exit 0, wall 9s; PASS line: `PASS (84 declarations, standard axioms only)`
- `tests/tamper.sh`: exit 0, wall 55s; final line: `ALL TAMPERING TESTS REJECTED`; `ok … rejected` lines: 9
- lean-toolchain: `leanprover/lean4:v4.33.1`; Mathlib rev (lake-manifest.json): `0df444a360eaa60ab8c11dca51a86af692955474`
- `.lean` tree digest (export, `LC_ALL=C sort`): `ade9a958ceeea8f4951f6db68360f96c2297ab6097a584e5af471e0f282f2243` (= tracked `.lean` files in source; source WT incl. untracked `scratch/L15_compare.lean`: `f1264afeea82fa656da4fad041ab8355e5f3227875a31167737b1cefebf5feea`)

Per-file `.lean` sha256 (export):
```
c6041d5d8c16aea2c44594d8b76bde420a9f39f5ebf00d7461ed69d7ad2baa64  ./Inversion.lean
a82367f1a9fec802afc5b058d4600024fbf4f0498594c4e04157126514852129  ./Inversion/Basic.lean
dd8a16f9abda65d23e856273fd6f23f06552b6589f0603defa1468f55d35202e  ./Inversion/Bridge.lean
0108b3aef0d8d7f69db35ab25c5cbb3e8a46a740ff6a242c2c1269f66edeef03  ./Inversion/Descartes.lean
2791291999404a506e3a6f929bf44acc42fd099e48059db5adce7d4e9b8bdbc2  ./Inversion/L14.lean
b1afd92778f7aa5cfa276df3ce71c0cf1ad1d461f2d065772657cc3a44925af1  ./Inversion/Peaucellier.lean
8d5a503cc34fafe48ad7e9da6092fb7e85123bfeabc77db4a88af5a549510ada  ./Inversion/PtolemyInversion.lean
```
Config/gate digests:
```
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
7132be6ac84de2c0225b0677831fd6e9f08b2891468f9290b23c95020c58cc2b  lakefile.toml
ab486de198559df0c65f6e73b1bbf3851f4410612b9344436ec734242ed22f8d  lake-manifest.json
6f426e9ce13b3ce545f0d2a8acd05ce1bb8dd60e1b232e20012e6bb2c245df7e  gate.sh
436d5a91deede002612b4dde83fbc9dc18fba0e760c3d5c66c587464c153a728  tests/tamper.sh
```
## Process notes

- jack: each `lake build`, `gate.sh` and `tamper.sh` ran under `flock ~/pi.lock`, with quad and then circles in sequence. When the quad build started, another job's `lake build` (a tamper run in `/tmp/quadrilaterals_tamper_*`) was already running on jack. The lock serialised against it.
- john: arbelos and then inversion ran strictly one after the other from a single sequential driver. `ps aux | grep -c "[l]ean"` reported 5 before each build. That pattern also matches non-Lean processes (macOS `CleanupPreparePathService` and the driver's own shell, whose command line contains `~/lean/…`). After the runs it reported 3 (same false positives), and `pgrep` found 0 real `lean`/`lake` toolchain processes. So the raw count is noisy; it is not evidence of concurrent builds.
- Build warnings (not errors) appear in quad (`Quadrilaterals/Frame.lean`: unused simp argument) and arbelos (`Arbelos/Area.lean`, `Steiner.lean`: deprecated `Set.mem_setOf_eq`). They don't affect the gate.
- Wall times are small because Mathlib was replayed from the linked packages, not compiled (see top).

## Summary

| repo | commit | gate PASS line | tamper | .lean tree digest |
|---|---|---|---|---|
| paperi_quad | `0c372061edd32cc7935cf1521d404dfbc3993ac5` | `PASS (133 declarations, standard axioms only)` | ALL TAMPERING TESTS REJECTED (11 ok…rejected) | `8a67f0c8e1894d090bf3140add6c9c01f2b34b943e76c2145af6c24e4f3281a4` |
| paperi_circles | `6c714e57d5cf41a43838d2a0e380fdc028e9b15b` | `PASS (121 declarations, standard axioms only)` | ALL TAMPERING TESTS REJECTED (9 ok…rejected) | `db7c08cac4acaed6c92671b435413c73261032f0a2a3ef07d22af1191d8a759f` |
| paperi_arbelos | `0dddc6e05fc14ad3d25325aecfc1ca225837ae6b` | `PASS (138 declarations, standard axioms only)` | ALL TAMPERING TESTS REJECTED (7 ok…rejected) | `2b43ae51b309604c290213bfaba4d459551116d7ea079a1ab4fd9b6233506264` |
| paperi_inversion | `c71abb76b265d660ae2d73b629beac2c338c8b27` | `PASS (84 declarations, standard axioms only)` | ALL TAMPERING TESTS REJECTED (9 ok…rejected) | `ade9a958ceeea8f4951f6db68360f96c2297ab6097a584e5af471e0f282f2243` |
