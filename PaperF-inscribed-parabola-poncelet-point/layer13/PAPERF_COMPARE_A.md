# Paper F — Layer 13 comparer, part A (blind_1 … blind_11)

Blind file: `~/reformal/PaperFBlind.lean` (jack), sha256 `7f96c9e2fac5b630a5aa17d4a3333b6b8707c8cc254113a2d23aa5d9d982f33a`, which matches the expected prefix `7f96c9e2fac5b630`. The file was not edited.
Repo: `~/quadparabola_l13` (namespace `QuadMiquel`, Lean v4.33.1).

## Result table

| pair | R→B | B→R | difference | note |
|---|---|---|---|---|
| blind_1 / `reflPt_mem_orthoLine` | ✅ `rb_1` | ✅ `br_1` | none | |
| blind_2 / `reflections_collinear` | ✅ `rb_2` | ✅ `br_2` | none | |
| blind_3 / `reflections_collinear_orthos` | ✅ `rb_3` | ✅ `br_3` | none | The real theorem quantifies over `L ∈ {L1..L4}` and lists `H3, H1, H2`. The blind one quantifies over `r ∈ {R1..R4}` and `H ∈ {H1,H2,H3}`. The difference is only packaging. |
| blind_4 / `miquel_cr_ne` (and `miquel_not_mem_orthoLine`) | ✅ `rb_4`, `rb_4'` | ✅ `br_4`, `br_4'` | none | The set-membership form goes through the bridge lemma `mem_orthoLine`. |
| blind_5 / `parabola_tangent` | ✅ `rb_5` | ✅ `br_5` | none | The real theorem uses `∀ L, L = L1 ∨ …`; the blind one is a four-way conjunction. |
| blind_6 / `tanPt_all` | ✅ `rb_6` | ✅ `br_6` | none | Blind `contact` matches real `perpMeet` by unfolding. |
| blind_7 / `vertex_onParabola ∧ dist_vertex ∧ vertex_closest` | ✅ `rb_7` | ✅ `br_7` | none | Real `infDist/2` and blind `(1/2)*infDist` are related by `one_div_mul_eq_div`. Real `(M+foot)/2` and blind `(1/2)(M+foot)` are related by `ring`. |
| blind_8 / `vertex_mem_axis ∧ axis_perp` | ✅ `rb_8` | ⚠️ only under `GenPos` (`br_8_genpos`) | **SAFE: the Lean is more general** | The real theorems have **no `GenPos` hypothesis**; the blind one assumes `GenPos`. A full B→R is impossible: off general position, the blind M (a reflection construction) need not equal `miquelPt`, and the blind statement gives nothing there. The converse restricted to `GenPos` is proved. |
| blind_9 / `newton_perp_orthoLine` | ✅ `rb_9` | ✅ `br_9` | none | The blind file marks this `-- AMBIGUOUS` (truncated prose). The blind reading, `⟨x-y, N3-N1⟩ = 0` as the second conjunct, is exactly what the Lean says, so the ambiguity causes no difference. |
| blind_10 / `newton_perp_cr` | ✅ `rb_10` | ✅ `br_10` | none | |
| blind_11 / `lambert` | ✅ `rb_11` | ✅ `br_11` | none | The real sphere is `sphere (circ a b c) (dist a (circ a b c))`, which matches `BlindOnCircumcircle` after `circ_agree`. |

**No REAL differences and no ARTEFACT differences.** One SAFE item: blind_8, where the Lean drops `GenPos`. The pairing table looks correct to me.

### Notable point about the Miquel point (requested check)
The blind writer defines `Q.M` as the reflection of `A12` in the line through the circumcentres of `T3` and `T4`. The repository's `miquelPt` is the explicit spiral-similarity formula. These are **not definitionally equal**. Proving them equal (`M_agree`) needs a real geometric fact. I used the **Bridge.lean** lemma `QuadMiquel.miquelPt_spec` (paper's M1: under `GenPos`, `miquelPt` is the reflection of `A12` in `line[O4, O3]`, and `O4 ≠ O3`). I combined it with Mathlib's `EuclideanGeometry.reflection_apply'` and the bridge lemma `foot_eq_orthogonalProjection`.

So the two definitions of M agree, but **only under `GenPos`**, and only because of a repository lemma, not by unfolding. Every pair carries `GenPos`, so this changes no verdict except blind_8 (above). If `miquelPt_spec` were not admissible as a "bridge lemma", every pair would need this one fact and should be read as conditional on M1.

## Agreement lemmas (in `scratch/L13_compare.lean`, namespace `PFBlindA`)
- Translation maps: `toL : BlindLine → Line := ⟨L.p, L.d⟩`, `toB` in the other direction, and `ofL L1 L2 L3 L4 : BlindQuadrilateral`.
- Proved by `rfl` / `Iff.rfl`: `cr_agree`, `carrier_agree`, `meet_agree`, `foot_agree`, `refl_agree` (BlindRefl = reflPt), `onParabola_agree`, `tangent_agree`, `A12_agree`, `N_agree` (BlindMid = `(a+b)/2`).
- `circ_agree` (BlindCirc = circ). This is **not pure unfolding** but a short unconditional algebraic identity: `conj u·v − u·conj v = 2i·cr(u,v)` and `1/i = −i`. Proved with `Complex.ext`, `field_simp`, `ring`. It holds even when degenerate, because both sides reduce to `a` when cr = 0. Not a difference.
- `ortho_agree`, `H1_agree`…`H4_agree` follow from `circ_agree`.
- `genpos_agree` / `qgenpos_agree` (BlindGenPos ↔ GenPos) use the Bridge.lean lemma `conc_iff`.
- `blindRefl_eq_reflection` uses the Bridge.lean lemma `foot_eq_orthogonalProjection` plus Mathlib's `reflection_apply'` and `eq_reflection_of_eq_subspace`.
- `M_agree` (blind M = miquelPt, under GenPos) uses the **Bridge.lean lemma `miquelPt_spec`**. See the section above.
- `W_agree` (W = dirW), `R_agree`, `tanPt_agree`, `axis_agree`, `directrix_agree`, `V_agree` all follow from `M_agree`, plus unfolding and `ring`.
- `orthoLine_agree` (blind `line[H4, H4+W]` = `orthoLine`) uses the **Parabola.lean bridge lemma `orthoLine_eq`**.
- `onCirc_agree` uses `circ_agree` and `Metric.mem_sphere`.
- Bridge lemma used in `rb_4'`/`br_4'`: `QuadMiquel.mem_orthoLine` (Parabola.lean).
- No repository theorem was used to prove any blind conclusion. Each premise is the real (or blind) statement taken as a hypothesis.

## Checks
- `lake env lean scratch/L13_compare.lean` gives **exit 0**. There were only unused-variable linter warnings (the `h` binder in the `_stmt` defs).
- `lake env lean scratch/L13_axioms.lean` gives **exit 0**.
- The blind definitions block (blind lines 3–153) is a verbatim copy: `diff` with `scratch/L13_compare.lean` lines 4–154 is empty. The `blindK_stmt` bodies copy the blind binders and statements verbatim.
- Forbidden-token grep `sorry|admit|native_decide|axiom`:
  - `L13_compare.lean`: no matches.
  - `L13_axioms.lean`: no matches apart from the `#print axioms` lines.
- `#print axioms` on all of `rb_1, br_1, rb_2, br_2, rb_3, br_3, rb_4, br_4, rb_4', br_4', rb_5, br_5, rb_6, br_6, rb_7, br_7, rb_8, br_8_genpos, rb_9, br_9, rb_10, br_10, rb_11, br_11`, and also on `M_agree, circ_agree, genpos_agree, orthoLine_agree`: each gives `[propext, Classical.choice, Quot.sound]`.
- Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`):
  - before: `5d4aee5f0cc570fd13b2162523931d92db7d4881b12c578dfafe534ecb90de90`
  - after: `5d4aee5f0cc570fd13b2162523931d92db7d4881b12c578dfafe534ecb90de90` (unchanged)

## Scratch files (jack)
- `~/quadparabola_l13/scratch/L13_compare.lean` (sha256 `4fb1e146…aa7b`)
- `~/quadparabola_l13/scratch/L13_axioms.lean` (the same content plus `#print axioms`)
- `~/quadparabola_l13/scratch/L13_compare.log` (compile output)
