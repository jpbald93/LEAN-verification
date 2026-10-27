# Paper G — Layer 13 comparer (statement-level equivalence), pairs blind_1 … blind_18

Machine: the arm64 machine (arm64 macOS). Repo copy: `~/lean/l13_nagel` (tar copy of `~/lean/paperg_nagel`, without .lake/.git; packages symlinked to `~/lean/clifford/.lake/packages`). `~/lean/jl build` finished: "Build completed successfully (8712 jobs)". Lean toolchain v4.33.1.
Blind file: `~/lean/reformalG/PaperGBlind.lean`, sha256 `f271e87d1655186750a2119bfeb94f627f47bea26b2c944f21bd139e9af529d2` (prefix matches f271e87d16551867). An unedited copy is at `scratch/PaperGBlind.lean.orig`, same hash.
The `Blind…` definitions (common + Nagel-line section) and blind_1..18 are copied verbatim into namespace `PaperGBlind` as `blindK_stmt : Prop`, with `V P` made explicit. The real side is `type_of% (@NagelLine.<decl> V P _ _ _ _)`. Multi-declaration pairs (5, 15) use `realK_stmt := A ∧ B ∧ C` of the three `type_of%`s.

## Result table

| pair | real decl | R→B | B→R | difference | note |
|---|---|---|---|---|---|
| blind_1 | gergonnePoint_mem_cevian | ✅ rb_1 | ✅ br_1 | none | uses gergonnePoint_agree (`1/x` vs `x⁻¹`, `D` vs `∑`) |
| blind_2 | gergonne_cevians_concurrent | ✅ rb_2 | ✅ br_2 | none | the two types are definitionally equal (`fun h => h`) |
| blind_3 | nagelPoint_mem_cevian | ✅ rb_3 | ✅ br_3 | none | nagelPoint_agree |
| blind_4 | nagel_cevians_concurrent | ✅ rb_4 | ✅ br_4 | none | definitionally equal |
| blind_5 | sbtw_touchpoint_singleton_zero ∧ _one ∧ _two | ✅ rb_5 | ✅ br_5 | none | blind uses arbitrary distinct (i,j,k). It covers the 6 orderings via `Sbtw.symm`; real covers the 3 cyclic ones |
| blind_6 | nagelPoint_vsub_centroid | ✅ rb_6 | ✅ br_6 | none | `N−G = −2(I−G)` vs `2(G−I)`: rewrite with `neg_vsub_eq_vsub_rev`. The AMBIGUOUS reconstruction matches the real statement |
| blind_7 | collinear_incenter_centroid_nagelPoint | ✅ rb_7 | ✅ br_7 | none | |
| blind_8 | medial_incenter_eq_midpoint | ✅ rb_8 | ✅ br_8 | none | |
| blind_9 | collinear_spiekerCenter_incenter_nagelPoint | ✅ rb_9 | ✅ br_9 | none | Spieker centre: both sides define it as `t.medial.incenter`, so the two are equal by `rfl`. The AMBIGUOUS alternative reading does not arise |
| blind_10 | midpoint_orthocenter_deLongchampsPoint | ✅ rb_10 | ✅ br_10 | none | equation is reversed (`Eq.symm`) |
| blind_11 | collinear_deLongchampsPoint_circumcenter_orthocenter | ✅ rb_11 | ✅ br_11 | none | |
| blind_12 | collinear_centroid_circumcenter_deLongchampsPoint | ✅ rb_12 | ✅ br_12 | none | |
| blind_13 | anticomplementary_orthocenter | ✅ rb_13 | ✅ br_13 | none | BlindAnticomplementary = anticomplementary by **`rfl`**. Both are `t.map (homothety G (-2)) _`, so no extra work was needed. Equation reversed |
| blind_14 | medial_nagelPoint | ✅ rb_14 | ✅ br_14 | none | the AMBIGUOUS reconstruction ("medial Nagel point = I") matches the real statement |
| blind_15 | midpoint_touchpoint_zero ∧ _one ∧ _two | ✅ rb_15 | ✅ br_15 | none | the same conjunction, pure repackaging |
| blind_16 | nagelPoint_eq_anticomplementary_incenter | ✅ rb_16 | ✅ br_16 | none | |
| blind_17 | spiekerCenter_power_exsphere | ✅ rb_17 | ✅ br_17 | none | `Sphere.power` unfolded with `exsphere_radius` |
| blind_18 | spiekerCenter_power_exsphere_eq | ❌ (only the first conjunct: rb_18a) | ✅ br_18 | **REAL (minor), blind stronger** | see below |

**Pair 18 detail.**
- blind_18 is the conjunction (power = ¼(s² + (s−a)(s−b)(s−c)/s)) ∧ (¼(s² + (s−a)(s−b)(s−c)/s) = (s² + r²)/4), where `r = t.inradius` (Mathlib).
- The real `spiekerCenter_power_exsphere_eq` states only the first form. The identity r² = (s−a)(s−b)(s−c)/s appears only in its docstring. No theorem in the repo states the `(s²+r²)/4` form, and `inradius` occurs nowhere in the library (grep).
- B→R is pure repackaging (first conjunct plus `ring`). R→B needs the inradius identity `t.inradius² = (s−a)(s−b)(s−c)/s`, which is genuine geometry (Heron's formula plus the incentre weights). So the clean R→B direction is omitted.
- The paper's prose ("The common value is … = (s²+r²)/4, with r the inradius") claims more than the Lean statement does. So this is a REAL prose/Lean gap. It is mild: the omitted part is a standard identity, and the docstring states it.
- For information only, `inradius_sq_doc` proves that identity from the repository's Basic.lean bridge lemmas. `rb_18_with_inradius_identity` then derives blind_18 from the real statement plus that identity. These two are **not** counted as a clean rb_18, since this goes beyond repackaging. They do show that the gap is exactly the inradius identity and nothing else.

**Pairing table check:** all 18 pairings look correct.

## Agreement / bridge lemmas used
In the rb_/br_ proofs, definition agreements are proved in the scratch file by `rfl`, `simp`/`congr`/`fin_cases`, or `ring`:
- `sideA_agree`, `sideB_agree`, `sideC_agree` (rfl); `semiperimeter_agree` (ring: `1/2*(…)` vs `(…)/2`); `centroid_agree` (rfl)
- `nagelPoint_agree` (BlindNagelPoint = Triangle.nagelPoint: `![…]` vs `fun i ↦ … side t i`, by funext + fin_cases)
- `gergonnePoint_agree` (BlindGergonnePoint = Triangle.gergonnePoint)
- `spiekerCentre_agree`, `deLongchampsPoint_agree`, `anticomplementary_agree` (all `rfl`)
- `power_exsphere_agree` (`Sphere.power` = `dist² − exradius²`, by Mathlib `Sphere.power` and `Simplex.exsphere_radius`)
- Mathlib lemmas in the proof bodies: `neg_vsub_eq_vsub_rev`, `smul_neg`, `neg_smul`, `Sbtw.symm`, `Fin.sum_univ_three`.
- Repository definitions unfolded: `NagelLine.sideA/B/C`, `semiperimeter`, `side`, `Triangle.nagelPoint`, `Triangle.gergonnePoint`, `Triangle.spiekerCenter`, `Triangle.deLongchampsPoint`, `Triangle.anticomplementary`.
- **No repository theorem is used in any rb_/br_ proof.**

In the documentation-only lemmas (`inradius_sq_doc`, `rb_18_with_inradius_identity`; not counted):
- repository Basic.lean bridge lemmas `dblArea`, `dblArea_pos`, `semiperimeter_pos`, `height0_sq`, `heron_factor`, `height_eq`, `side`
- Mathlib `Simplex.inradius`, `exsphere_radius`, `exradius_eq_abs_inv_sum`, `excenterWeightsUnnorm_empty_apply`.

## Checks
- Compile `cd ~/lean/l13_nagel && ~/lean/jl lake env lean scratch/L13_compare.lean`: **exit 0** (no errors or warnings).
- Compile `scratch/L13_axioms.lean` (the same content plus `#print axioms` lines): **exit 0**.
- Forbidden-token grep `sorry|admit|native_decide|axiom`:
  - `scratch/L13_compare.lean`: **empty**
  - `scratch/L13_axioms.lean`: only the `#print axioms` lines.
- `#print axioms`: all 38 checked declarations depend on **[propext, Classical.choice, Quot.sound]** only.
  - rb_1..rb_17, br_1..br_17, rb_18a, br_18, plus inradius_sq_doc and rb_18_with_inradius_identity.
- Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`):
  - before: `9e74f30c9307af64cec052f24d211e8fdb9297d92196146cdb289acd24500fb1`
  - after: `9e74f30c9307af64cec052f24d211e8fdb9297d92196146cdb289acd24500fb1` (unchanged)

## Files (the arm64 machine)
- `~/lean/l13_nagel/scratch/L13_compare.lean` (sha256 044ec33ad047f6892c8e4309e95d8dc5d73bcd7da850faa6e4726e58ac828be7)
- `~/lean/l13_nagel/scratch/L13_axioms.lean` (sha256 d11224c9547ef968e81b49b34a164dad65c86f7e98c25b5af0efd13a83877aec)
- `~/lean/l13_nagel/scratch/PaperGBlind.lean.orig` (verbatim blind copy)
- Report: `~/lean/l13_nagel/PAPERG_COMPARE_N.md` on the arm64 machine; copy at `<paper folder>/PAPERG_COMPARE_N.md` on the x86-64 machine.
  - The requested path `~/reformal/~/lean/l13_nagel/…` looked garbled, so I used `~/lean/l13_nagel/`.
- Local mirror of the scratch file on the x86-64 machine: `<work dir>`.
