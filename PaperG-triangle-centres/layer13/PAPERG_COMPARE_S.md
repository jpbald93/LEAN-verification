# Paper G — L13 COMPARER (statement level), blind_19 .. blind_36 vs repo `Brocard`

Machine: the x86-64 machine (x86_64 Linux), 2026-10-26. Lean v4.33.1, Mathlib from `~/barbier/.lake/packages`.
Repo copy: `~/l13_brocard` (tar copy of `~/paperg_brocard` without .lake/.git); `lake build` → *Build completed successfully (8714 jobs)*.
Blind file: `~/PaperGBlind.lean`, sha256 `f271e87d16551867…29d2` (prefix matches). A verbatim copy is at `scratch/PaperGBlind_verbatim.lean.txt` (same hash).

## Method
- `scratch/L13_compare.lean` (`import Brocard`) contains the blind file's preamble and **all** `Blind…` definitions, copied verbatim (namespace `PaperGBlind`, lines 18–71 and 173–242 of the blind file). The blind theorems `blind_1..18` and their `sorry`s are **left out**: they are not assigned here, and leaving them out keeps the file sorry-free. One mechanical change: the verbatim definition block is wrapped in `section BlindDefs … end`.
- For each K: `def blindK_stmt : Prop := ∀ <blind binders>, <blind conclusion>` (copied verbatim), then
  - `rb_K : (type_of% @Brocard.<Real>.{u,v}) → blindK_stmt`
  - `br_K : blindK_stmt → <real type restated verbatim>`
  - and, as a check that the restatement is faithful, `br_K_typed : (∀ V P [inst], blindK_stmt) → (type_of% @Brocard.<Real>.{u,v})`, proved by delegating to `br_K`. This shows the restated type is definitionally the real declaration's type.
- The proof bodies use only the premise, the agreement lemmas below, `simp only`/`rw`/`linarith`, `fin_cases`, and two general Mathlib lemmas. **No repository theorem is used** (checked with grep: the only references to `Brocard.*` names in the scratch file are inside `type_of%` and comments; `Affine.Triangle.*` names appear only in `unfold`/`simp` of definitions plus the Mathlib lemma `Affine.Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12`).

## Results

| pair | real decl | R→B | B→R | difference | note |
|---|---|---|---|---|---|
| blind_19 | symmedian_angles | ✅ rb_19 | ✅ br_19 | none | Only difference: the blind version names the midpoints with `let`. |
| blind_20 | symmedianPoint_mem_interior | ✅ | ✅ | none | Conjuncts in a different order. |
| blind_21 | symmedianPoint_eq_centroid_pedal | ✅ | ✅ | none | `BlindPedalCentroid` = the same centroid of `orthogonalProjection`s (rfl). |
| blind_22 | eq_symmedianPoint_of_eq_centroid_pedal | ✅ | ✅ | none | The blind version takes an explicit `hV : finrank = 2`; the real one takes `[Fact (finrank = 2)]`. Converted with `⟨hV⟩` / `.out`. |
| blind_23 | brocardPoint₁_angles | ✅ | ✅ | none | |
| blind_24 | brocardPoint₂_angles | ✅ | ✅ | none | |
| blind_25 | cot_brocardAngle_eq_sum_cot ∧ cot_brocardAngle_eq_div_area | ✅ | ✅ | none | The blind version is the chain cot ω = Σcot = S/(4Δ); the real one has two equalities, each from cot ω. They convert by `Eq.trans`/`symm`. `BlindSide*` unfold to the same `dist`s. |
| blind_26 | brocardAngle_pos_le | ✅ | ✅ | none | |
| blind_27 | brocardPoints_isogonal | ✅ | ✅ | none | |
| blind_28 | dist_circumcenter_brocardPoint | ✅ | ✅ | none | |
| blind_29 | brocardCircle | ✅ | ✅ | none | The blind version has four equalities with `(1/2)*dist O K`; the real one is `∀ X ∈ {O,K,Ω,Ω'}` with `dist O K / 2`. `linarith` and a set-membership case split cover it. The blind writer's `-- AMBIGUOUS` centre (midpoint of OK) matches the real statement. |
| blind_30 | brocardCircle_right_angles | ✅ | ✅ | none | The blind statement is the inner-product half. B→R recovers the angle half via Mathlib `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`. The pairing table also lists `brocardCircle (inner-product part)`, but `brocardCircle` has no inner-product part; the right target is `brocardCircle_right_angles`, which is the one used. |
| blind_31 | brocardCircle_right_angles | ✅ | ✅ | none | The blind statement is the angle half. B→R recovers the inner products with the same Mathlib lemma. |
| blind_32 | brocardCircle_degenerate | ✅ | ✅ | none | The blind version uses `t.Equilateral`; the real one uses `dist A B = dist B C ∧ dist B C = dist C A` (agreement lemma `agree_equilateral`, from a Mathlib lemma). |
| blind_33 | brocard_eq_circumcenter_of_equilateral | ✅ | ✅ | none | The blind version has the chain Ω=Ω'=K=O; the real one has Ω=O, Ω'=O, K=O. They convert by `trans`. The hypothesis is `Equilateral` vs two `dist` equalities (`agree_equilateral`). |
| blind_34 | lemoineCircle | ✅ | ✅ | none | The blind version is `∀ i j` equal; the real one is `∀ i`, equal to point 0. `BlindLemoinePoint` (written with `•`/`+ᵥ`) = `lemoinePoints` (written with `lineMap`), proved by `simp [lineMap_apply]`; the point order is the same. |
| blind_35 | cospherical_lemoinePoints | ✅ | ✅ | none | |
| blind_36 | drozFarny | ✅ | ✅ | none | The blind version uses `X Y : Fin 3 → P` with `∀ k, X k ∈ mk' H (ℝ∙d₁)`; the real one uses six separate points. B→R instantiates `![X₁,X₂,X₃]`. Also explicit `hV` vs `[Fact]`. |

**All 18 pairs are proved equivalent in both directions. There are no REAL, ARTEFACT or SAFE differences.**

Notes on the blind `-- AMBIGUOUS` comments in this range:
- The pedal-feet reading (projections onto the side lines) matches the repo.
- The Brocard-circle centre (midpoint of OK) matches the repo.

## Agreement / bridge lemmas used (all proved in the scratch file by unfolding)
- `agree_symmedian : BlindSymmedianPoint t = t.symmedianPoint` (unfold, `congr 1`)
- `agree_brocard₁ : BlindFirstBrocard t = t.brocardPoint₁` (unfold, `congr 1`)
- `agree_brocard₂ : BlindSecondBrocard t = t.brocardPoint₂` (unfold, `congr 1`)
- `agree_area : BlindArea t = t.area` (`rfl`)
- `agree_lemoine : BlindLemoinePoint t = t.lemoinePoints` (`funext`, `fin_cases`, `simp [AffineMap.lineMap_apply, BlindSide*]`)
- `agree_pedalCentroid : BlindPedalCentroid t X = centroid ![orthogonalProjection …]` (`rfl`)
- `agree_equilateral : t.Equilateral ↔ (dist 01 = dist 12 ∧ dist 12 = dist 20)` (Mathlib `Affine.Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12` + `dist_comm`)

General Mathlib lemmas used: `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`, `EuclideanGeometry.angle` (unfold), `dist_comm`, `AffineMap.lineMap_apply`.
No repository bridge lemmas were needed. No repository theorems were used.
Not needed in this range: Nagel, Spieker, anticomplementary, ninePointCircle.

## Compile
- `cd ~/l13_brocard && flock ~/l15jack.lock lake env lean scratch/L13_compare.lean` → **exit 0** (no errors; only linter warnings)
- `… lake env lean scratch/L13_axioms.lean` (a copy of the compare file plus `#print axioms` lines) → **exit 0**

## Forbidden-token grep
`grep -nE "sorry|admit|native_decide|axiom" scratch/L13_compare.lean` → **empty** (exit 1).
`scratch/L13_axioms.lean` → empty apart from the `#print axioms` lines themselves.

## #print axioms
All 54 theorems give `[propext, Classical.choice, Quot.sound]`: `rb_19..rb_36`, `br_19..br_36` and `br_19_typed..br_36_typed`. None depends on `sorryAx` or any other axiom.

## Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`)
- before: `bd4e777b12dd04fdf9adf8d2d4c3b1aa4a37b1262bdd0ec050ffbff27865a6d3`
- after:  `bd4e777b12dd04fdf9adf8d2d4c3b1aa4a37b1262bdd0ec050ffbff27865a6d3` (unchanged)

## Files (the x86-64 machine)
- `~/l13_brocard/scratch/L13_compare.lean` (sha256 `ad06898da1510866cd6cc4912694990257be2a8dcdf367612568e7f793cc4884`)
- `~/l13_brocard/scratch/L13_axioms.lean` (sha256 `4bae3d90267e01a334fd6d45607a230d5b5906d0e3656f5926e9da6751a97f2a`)
- `~/l13_brocard/scratch/PaperGBlind_verbatim.lean.txt` (sha256 `f271e87d…29d2`)
- compile logs: `~/l13_cmp.out`, `~/l13_ax.out`; build log: `~/l13_brocard_build.log`
- Report: the requested path `~/reformal/~/l13_brocard/PAPERG_COMPARE_S.md` looked garbled, so the report was written to both `~/l13_brocard/PAPERG_COMPARE_S.md` and `~/reformal/PAPERG_COMPARE_S.md` on the x86-64 machine. `<paper folder>/` does not exist on the x86-64 machine, so that copy was placed on the orchestrating machine, where the directory exists.
