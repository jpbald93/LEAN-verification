# INTEGRATE report: Paper Baranyai (Layers 14 + 15)

Date: 2026-10-22. All work was done inline on jack; no subagents were used. A local commit was made and **not pushed**.

## Repo: baranyai → `jack:~/pubBaranyai_baranyai`

- **Start point.**
  - The copy was made from `~/l14Baranyai_baranyai`.
  - `git fetch origin && git merge --ff-only origin/main` printed "Already up to date".
  - GitHub HEAD = `051ae8c` (the published commit; `git ls-remote` shows nothing later). No later commits were lost.
- **Copy contents.**
  - `.lake/packages` is a symlink to `~/barbier/.lake/packages`, and it was kept.
  - The copy had no untracked `scratch/` and no stray logs.
  - The tracked `scratch/` files (Ax, Referee, Satisfiable, ax.out) are part of the published repo and are cited by the README, so they were kept.

### New files
| file | lines | sha256 |
|---|---|---|
| `Baranyai/L14.lean` | 409 | `ade44d32b8b7bceb3b4911aee8fdcb53afd92769203986701dbe059100c9d760` (unchanged from L14) |
| `Baranyai/L15Classical.lean` | 358 | `945498040bfe28079bdad9a0b14becbd0aa814b228936f9fe05b3fec88f44019` |

### L15Classical.lean contents (namespace `Baranyai.Classical`)
- **Header:** the required Layer-15 docstring.
- **Writer's definitions:** the 4 definitions are verbatim, including their docstrings: `IsPerfectMatchingK`, `IsPartitionOfKSubsets`, `pointDegree`, `IsAlmostRegular`.
- **Writer's statements:** the 7 proved `classical_*` theorems are verbatim, including their docstrings and AMBIGUOUS comments. Only `:= by sorry` was replaced, by `apply cov_X <;> assumption`. A Python check confirmed that each is a byte-for-byte substring of the writer's `Classical.lean` (sha256 `c4f5f448…`).
- **`classical_Baranyai3_main`:** the general van Lint–Wilson form is unproved. It is kept as `def classical_Baranyai3_main : Prop := ∀ <writer's binders>, <writer's conclusion>`. The binders and conclusion text are unchanged; only the theorem-to-Prop wrapper was added.
- **8 `cov_*` theorems:**
  - `cov_Baranyai1_a`, `cov_Baranyai1_b`
  - `cov_Baranyai2_a`, `cov_Baranyai2_b`
  - `cov_Baranyai3_a`, `cov_Baranyai3_b`
  - `cov_Baranyai3_a_implication` (NEW PROOF)
  - `cov_Baranyai3_main_part` (the partial instance)
- **7 NEW PROOF bridges:** `classesOf`, `mem_classesOf`, `classesOf_spec`, `classes_exist`, `toFinpartition`, `pointDegree_eq_one`, `ratio_eq_one`.
- **Construction obligations:** none. L15 found none.
- **Counterexample (`¬ classical_…`) theorems:** none, because no writer statement is false.
- **Removed from the scratch file:** the 15 trailing `#print axioms` lines and the scratch header. The scratch file had no `set_option`, `macro` or `notation`.
- **Root file:** `import Baranyai.L15Classical` was appended at the end of `Baranyai.lean`, after the L14 line.

### REQUIRED
- Count: published **32** → L14 **49** → final **76**.
- The 27 added names are all `Baranyai.Classical.*`: the 4 writer definitions, 7 bridges, 8 cov, 7 classical theorems and the `classical_Baranyai3_main` Prop.
- This keeps the README's claim "every public theorem and definition" true.

### Gate / tamper / grep
- `lake build`: rc 0. The only warnings are unused-variable lints on the binders of the verbatim `classical_Baranyai3_main` Prop.
- Gate: `PASS (76 declarations, standard axioms only)`.
  - 74 declarations use `[propext, Classical.choice, Quot.sound]` and 2 use `[propext, Quot.sound]`.
  - The 27 Classical declarations: 25 use the full set, and 2 (`cov_Baranyai1_b`, `classical_Baranyai1_b`) use `[propext, Quot.sound]`.
- Tamper: `ALL TAMPERING TESTS REJECTED` (rc 0).
- Forbidden grep on `L15Classical.lean` (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`): **0 matches**.
  - On `L14.lean` the grep hits only l.395 "`Fin 5` admits no partition…". That is the English word "admits" inside a docstring, so it counts as 0 outside comments.
  - The gate's own stricter token check also passed.

### Hash table (published `051ae8c` → final)
| file | published | final | |
|---|---|---|---|
| Baranyai/Basic.lean | fc63a71e…2d31d | fc63a71e…2d31d | unchanged |
| Baranyai/Partition.lean | 551d9d83…ed367 | 551d9d83…ed367 | unchanged |
| Baranyai/Transport.lean | 9c59609d…fea76 | 9c59609d…fea76 | unchanged |
| tests/tamper.sh | a6a61abe…9025c | a6a61abe…9025c | unchanged |
| .gitignore | 2bc299c9…4247b | 2bc299c9…4247b | unchanged (already has `.gatecheck_*`) |
| Baranyai.lean (root) | 825eb491…0cd | df5ba48c…720 | +2 import lines |
| gate.sh | 01ea39a8…af7 | 91c480b1…1e8 | REQUIRED line + mktemp line |
| README.md | 376a025c…a85 | b00ab05f…bbf | count 32→76 (3 places) + new section |

### Addendum items
- **(a)** The repo was already at GitHub HEAD (fast-forward was a no-op).
- **(b)** `gate.sh` used GNU-only `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)`. That single line was replaced with `chk=".gatecheck_$$.lean"` (the desargues form). `.gatecheck_*` was already in `.gitignore`. The gate was re-run after the change: it passed, and no leftover `.gatecheck_*` file remained.
- **(c)** No repository docstring or README claim was found to be wrong or overclaiming.
  - L14 found no false statement. It only confirmed that the Finpartition form needs `0 < n`, which `baranyai_partition` already assumes.
  - L15 found 0 mis-statements.
  - The only text changes are the declaration count (32→76) and the new "Layers 14 and 15" section.
  - The README has no machine paths.
- **(d)** One local commit:
  - **SHA:** `1ab21623da9572cb10a8630a086c010b9e554269`
  - **Author/committer:** Josh Bald <jpbald93@gmail.com>
  - **Trailer:** `Co-Authored-By: Claude Opus 5.5`
  - **Pushed:** no

```
1ab2162 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
051ae8c Referee round: converse corollary dvd_card_of_factorisation; scratch/Referee.lean (n=3,k=2 impossibility, step witness, removable hypotheses)
9289dfa Baranyai's theorem: Lean 4 formalisation, gate, tamper tests and satisfiability certificates
```
Diff vs published: 5 files (Baranyai.lean +2, L14.lean +409, L15Classical.lean +358, README.md +21/−3, gate.sh 2 lines changed).

`git status --short` before commit:
```
 M Baranyai.lean
 M README.md
 M gate.sh
?? Baranyai/L14.lean
?? Baranyai/L15Classical.lean
```
`git status --short` after commit: *(empty — clean)*

### Dropped
- Nothing was dropped.
- `classical_Baranyai3_main` (general form) was never proved. L15 left it open, and the paper says it is not formalised. It is included as a verbatim `Prop` and is not assumed anywhere.

### Logs
- `jack:~/pubBaranyai_gate.log`
- `jack:~/pubBaranyai_tamper.log`
