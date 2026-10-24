# Paper F — Layer 13 comparer B (blind_12 … blind_23)

Blind file: `jack:~/reformal/PaperFBlind.lean`, sha256 `7f96c9e2fac5b630a5aa17d4a3333b6b8707c8cc254113a2d23aa5d9d982f33a` (prefix matches). I read it and did not edit it. The Blind model definitions (lines 7–67) and the Part B definitions (lines 238–276) are copied verbatim into namespace `PaperFB`. Every `blindK_stmt` is the blind theorem's binders, hypotheses and conclusion, copied verbatim and closed under `∀`/`→`.
Repo: `john:~/lean/quadrangle_l13` (namespace `QuadMiquel`).

## Result table

| pair | R→B | B→R | difference | note |
|---|---|---|---|---|
| blind_12 / `ponDen_eq_zero_iff` | ✔ `rb_12` | ✔ `br_12` | none | rewrite with `ponDen_agree` (rfl), `ortho_agree`, `qgen_agree` |
| blind_13 / `orthocentric_npc_eq ∧ orthocentric_ninePointCircle_eq` | ✔ `rb_13` | ✔ `br_13` | none | The blind side states the circles as `Set ℂ` (sphere centred at npc, through the midpoint of ab); the real side states them as Mathlib `Sphere` equalities. B→R also needs radius equality from carrier equality, which `sphere_radius_eq` gives (a pure metric fact, proved in scratch). Orientation of the equalities is flipped (`=` symm). |
| blind_14 / `orthocentric_example` | ✔ `rb_14` | ✔ `br_14` | none | `(3/2 : ℂ) * I` and `3 / 2 * I` elaborate to the same term |
| blind_15 / `ninepoint_concur` | ✔ `rb_15` | ✔ `br_15` | none | via `nineCircle_agree` (bridge `mem_ninePointCircle_iff`) |
| blind_15 / `poncelet_on_ninepoint` (also listed) | ✔ `rb_15'` | ✔ `br_15'` | none | pure unfolding of `BlindNineCircle` into `dist` equalities |
| blind_16 / `ninepoint_unique` | ✔ `rb_16` | ✔ `br_16` | none | via `nineCircle_agree` |
| blind_17 / `poncelet_on_pedal_d` | ✔ `rb_17` | ✔ `br_17` | none | sides ab, bc, ca, same order as the real theorem; `BlindFoot z (BlindLineThrough p q)` is `foot z (lineThrough p q)` by rfl |
| blind_18 / `poncelet_on_pedal_c` | ✔ `rb_18` | ✔ `br_18` | none | sides ab, bd, da, same order as the real theorem |
| blind_19 / `poncelet_on_pedal_b` | ✔ `rb_19` | ✔ `br_19` | none | sides ac, cd, da, same order as the real theorem |
| blind_20 / `poncelet_on_pedal_a` | ✔ `rb_20` | ✔ `br_20` | none | sides bc, cd, db, same order as the real theorem; no reorder needed |
| blind_21 / `poncelet_on_diagonal_circle` | ✔ `rb_21` | ✔ `br_21` | none | `BlindDiagPt = diagPt` by rfl; the non-parallel hypotheses are identical |
| blind_22 / `poncelet_S4` | ✔ `rb_22` | ✔ `br_22` | none | same six permutations in the same order; each equality is flipped (`P abcd = P σ` vs `P σ = P abcd`) |
| blind_23 / `ortho_swap_iff` | ✔ `rb_23` | ✔ `br_23` | none | `ortho_agree` + `qgen_agree` |

**Summary:** all 12 pairs are equivalent in both directions. I found no REAL, ARTEFACT or SAFE difference, and none of the blind_12–23 statements carry an `-- AMBIGUOUS` comment. The pairing table looks correct.

## Agreement / bridge lemmas (all in `scratch/L13_compare.lean`)

| lemma | statement | how proved |
|---|---|---|
| `cr_agree` | `BlindCr a b = cr a b` | `rfl` |
| `meet_agree` | `BlindMeet L M = meet (toLine L) (toLine M)`, with `toLine L = ⟨L.p, L.d⟩` | `rfl` (not needed for Part B) |
| `foot_agree`, `footLT_agree` | `BlindFoot z L = foot z (toLine L)`, and the same for `BlindLineThrough p q` vs `lineThrough p q` | `rfl` |
| `lineThrough_agree` | `toLine (BlindLineThrough p q) = lineThrough p q` | `rfl` |
| `qgen_agree` | `BlindQGen ↔ QGen` (4-fold `∧` vs a structure with the same four fields) | anonymous constructor |
| `ponDen_agree`, `poncelet_agree` | `BlindPonDen = ponDen`, `BlindPoncelet = poncelet` | `rfl` (`let`s vs `pD`/`pN` unfold to the same term) |
| `diagPt_agree` | `BlindDiagPt = diagPt` | `rfl` |
| `mid_agree` | `BlindMid a b = (a+b)/2` | `rfl` |
| **`circ_agree`** | `BlindCirc a b c = circ a b c` | **Not definitional.** The blind formula is `a − i·N / (2·cr(u,v))`; the repo's is `a + N / (conj u·v − u·conj v)`. They are equal for all inputs because `conj u·v − u·conj v = 2i·cr(u,v)` and `1/i = −i`; in the degenerate case both sides are `a`. Proof: `Complex.ext`, `field_simp`, `ring`, `I_sq`. This is an unconditional identity between two closed formulas with no geometric content, so I classify it as a harmless presentation difference, not a statement difference. |
| `ortho_agree` | `BlindOrtho = ortho` | unfold + `circ_agree` |
| `ninePt_agree` | `BlindNinePt a b c = npc a b c` | `(1/2)·(…)` vs `(…)/2`: unfold, `circ_agree`, `ring` (trivial algebra) |
| `nineCircle_agree` | for non-collinear a, b, c: `z ∈ BlindNineCircle a b c ↔ z ∈ (tri h).ninePointCircle` | **repo bridge** `QuadMiquel.mem_ninePointCircle_iff` (which rests on `npc_eq_ninePointCircle_center` and `ninePointCircle_radius_eq`) |
| `sphere_radius_eq` | spheres in ℂ with the same centre and the same carrier have equal nonnegative radii | Mathlib metric lemmas only |

Other repository facts used: the bridge lemmas `npc_eq_ninePointCircle_center` and `ninePointCircle_radius_eq` (in `br_13`), and `QGen.ncol_abc/abd/acd/bcd` (from `ncol_of_cr`: cr ≠ 0 ⇒ ¬Collinear). The `ncol` lemmas are needed just to form the real statements' `tri h.ncol_…` terms. I used no repository theorem as a truth-level proof: every proof body uses the premise H.

Blind M (the Miquel point built by reflection) belongs to Part A and is not used by blind_12–23, so the M vs `miquelPt` question does not arise here.

## Build / checks (john, inside the repo, via `~/lean/jl lake env lean …`)

- `scratch/L13_compare.lean`: **exit 0**. The only output is one linter warning (`unnecessarySeqFocus`).
- `scratch/L13_compare_axioms.lean` (the same content plus `#print axioms`): **exit 0**.
- Forbidden-token grep `sorry|admit|native_decide|axiom`:
  - `L13_compare.lean`: no matches (grep rc=1).
  - `L13_compare_axioms.lean`: no matches apart from the `#print axioms` lines themselves (rc=1).
- `#print axioms`: every one of `rb_12 br_12 rb_13 br_13 rb_14 br_14 rb_15 br_15 rb_15' br_15' rb_16 br_16 rb_17 br_17 rb_18 br_18 rb_19 br_19 rb_20 br_20 rb_21 br_21 rb_22 br_22 rb_23 br_23 circ_agree nineCircle_agree` depends on axioms `[propext, Classical.choice, Quot.sound]` and nothing else.
- Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`):
  - before: `6431797ed093b76d73cc804f333981b1ce294704863ca998c95edc1523c17b27`
  - after: `6431797ed093b76d73cc804f333981b1ce294704863ca998c95edc1523c17b27` (unchanged)

## Scratch files

- `john:~/lean/quadrangle_l13/scratch/L13_compare.lean`, sha256 `5e5343aa28f29e8056ed3a13790c81f0783a277401ffb5f0bd2fc58755f46fb5`
- `john:~/lean/quadrangle_l13/scratch/L13_compare_axioms.lean`, sha256 `e84a2609ceabb0b48d4454d173a45f5e9e66702cf77e899657ed809c3401f75c`
