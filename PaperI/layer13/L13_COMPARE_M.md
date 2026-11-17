# L13 comparison, Paper I: arbelos + inversion (machine john)

Comparer files. Two files, because `Arbelos` and `Inversion` are separate lake projects and neither can import the other:

| file on john | local copy | md5 |
|---|---|---|
| `~/lean/l13_arbelos/scratch/L13_compare.lean` (namespace `L13CmpArb`, 877 lines) | `L13_compare_arbelos.lean` | `8552f0109ae2c69a44e08720635bd84a` |
| `~/lean/l13_inversion/scratch/L13_compare.lean` (namespace `L13CmpInv`, 372 lines) | `L13_compare_inversion.lean` | `277da257616fd7a25c27b4f6596b197e` |

How the files are built:
- Blind definitions are copied verbatim.
- Each `blindK_stmt` is the blind theorem written as a closed `Prop`.
- Real statements appear only as `type_of% @Lib.decl`.

Rule check: no library theorem is used in any proof body. I grepped every `Arbelos.`/`Inversion.` name that appears outside `type_of%`. All of them are library **definitions** that get unfolded: `bigS leftS rightS perpC ptC arbelosRegion pappusCircle powC invSphere IsSteinerChain HasDisjointDiscs invPt descartesForm descartesFormZ`.

There are two places where I re-proved a small library fact from Mathlib, by copying its proof rather than calling it:
- `cmp_isTangent_vline_iff`
- `cmp_volume_realAxis`

## Table

✓ = proved in the compiled file. ½ = proved only on a restricted range (the restriction is in the note).

| pair (label, real decl ↔ blind) | R→B | B→R | difference (REAL/ARTEFACT) | note |
|---|---|---|---|---|
| thm:twin `twin_left` ↔ blind_14 | ✓ | ✓ | none | Blind's `0 < s.2` follows from line tangency plus `hside`. Mathlib's `IsTangent (vline)` becomes `\|re − 2a\| = r`. |
| thm:twin `twin_right` ↔ blind_15 | ✓ | ✓ | none | as above |
| thm:twin `twin_left_exists ∧ twin_right_exists` ↔ blind_16 | ✓ | ✓ | none | `BlindArchimedesTwins` unfolded. Blind requires positive radii, which follow from tangency plus side. |
| thm:area `arbelos_area` ↔ blind_17 | ✓ | ✓ | none (null set) | Blind region uses `0 ≤ im` and library uses `0 < im`. They differ by a subset of the real axis, which has measure 0 (Mathlib `addHaar_submodule`). `midpoint ℝ C D = (C + D)/2`. |
| thm:pappus `pappus_chain` ↔ blind_22 (and blind_26) | ✓ | ✓ | none | Both sides are unconditional field identities (`blind26_holds`, by unfolding and `ring`). So the equivalence is trivial and does not test the interpretation much. The real statement has no `0<a, 0<b`; blind_22 has them, blind_26 has none. |
| thm:pappus `pappus_tangent_big ∧ _left ∧ _succ` ↔ blind_19 ∧ 20 ∧ 21 | ✓ | ✓ | none | Blind tangency = Mathlib tangency plus radii > 0. Radius positivity comes from `positivity` on the unfolded family. |
| thm:pappus `pappus_unique` ↔ blind_24 | ✓ | ✓ | none | Transfer `Sphere ℂ` ↔ `ℂ × ℝ` (injective both ways). |
| thm:bankoff `incircle_eq` ↔ blind_30 | ✓ | ✓ | none | B→R needs `0 < s.radius`, because the real statement allows radius 0. I proved it in the comparer file (`incircle_rad_pos`): a point-circle cannot lie on all three arbelos circles. This is about 10 lines of `nlinarith`, more than pure repackaging. |
| thm:bankoff `bankoff` ↔ — | — | — | **REAL (blind omission)** | Blind.lean has no statement about Bankoff's circle through C, T₁, T₂ (radius ab/(a+b)). blind_30 only covers the incircle. Unattempted: there is nothing to compare. |
| thm:bankoff `bankoff_exists` ↔ — | — | — | **REAL (blind omission)** | Same: no blind existence statement for Bankoff's circle. |
| thm:steiner `steiner_porism` ↔ blind_31 | ✓ | ½ | **ARTEFACT** (real stronger at n = 0) | B→R is proved for `0 < n` (`steiner_B_to_pos`). At `n = 0` the library chain is indexed by `ZMod 0 = ℤ` (a bi-infinite chain), while blind requires `0 < n`. That case is not reachable from blind. The difference comes from the ZMod encoding, not the prose. |
| thm:steiner `steiner_porism_simple` ↔ blind_32 | ✓ | ✓ | none | Blind's `hn : 3 ≤ n` matches the `3 ≤ n` inside `IsSimpleSteinerChain`. Real takes no `0 < s₀.radius`; I derived it from strict nesting (`s0_pos`). |
| thm:steiner `steiner_porism_disjoint` ↔ blind_33 | ✓ | ✓ | none | Blind's disjoint open interiors = `HasDisjointDiscs` (open balls). Same ℕ-periodic ↔ ZMod transfer. |
| thm:steiner `steiner_porism_strong` ↔ blind_32 ∧ 33 | ✓ | ✗ | **ARTEFACT** (real stronger) | The strong form transfers injectivity and disjointness for every n, including n < 3 and n = 0. Blind covers only n ≥ 3. The missing cases would need the porism construction itself. It is a library strengthening beyond the prose. |
| thm:steiner `steiner_concentric_strong` ↔ blind_34 | ✓ | ✗ | **ARTEFACT** (real stronger) | Same reason, plus the degenerate radii below. |
| thm:steiner `steiner_concentric` ↔ blind_34 | ✓ | ½ | **ARTEFACT** (real stronger) | B→R is proved for `0 < S₁.radius ∧ 0 < n` (`conc_B_to_pos`); nesting is derived from the chain. Real also covers `S₁.radius = 0` and `n = 0`, and blind's `hpos`, `0 < n` exclude those. This traces to the blind `AMBIGUOUS` radius-convention comment. Blind correctly drops positivity of s₀ (s₀ is plain-distance tangent), matching the prose. |
| thm:steiner `exists_inversion_concentric` ↔ blind_35 | ✓ | ✓ | none | Blind allows any radius > 0; the centre condition scales away (`invC_scale`) to the library's radius 1. `BlindPower` = `powC`. |
| thm:steiner `image_inversion_sphere` ↔ — | — | — | unattempted (no counterpart) | No blind statement is about the image set of a circle under inversion. blind_36/37 state tangency preservation; those match `invSphere_isExtTangent`/`_isIntTangent`, which are not in my pair list. |
| thm:ptolemyinv `ptolemy_inequality` ↔ blind_57 | ✓ | ✓ | none | Blind carries an unused `R ≠ 0`; instantiated with R = 1. |
| thm:ptolemyinv `collinear_iff_dist_boundary` ↔ blind_58 | ✓ | ✓ | none | identical up to variable names |
| thm:ptolemyinv `ptolemy_concyclic` ↔ blind_60 | ✓ | ✓ | none | Blind carries an unused `R ≠ 0`. |
| thm:peaucellier `peaucellier_add ∧ _inner ∧ _collinear` ↔ blind_62 ∧ 63 ∧ 61 | ✓ | ✓ | none | Real collinearity is the cross product `P.re·Q.im − P.im·Q.re = 0`; blind uses Mathlib `Collinear ℝ {0,P,Q}`. Bridged by `collinear_zero_iff_cross` (Mathlib only). |
| thm:peaucellier `peaucellier ∧ _classic ∧ _line ∧ _classic_line` ↔ blind_64…69 | ✓ | ✓ | none | `BlindInversion 0 R = invPt R`; `-R²/2 = -(R²/2)`. |
| thm:descartes `descartes` ↔ blind_70 | ✓ | ✓ | none | `Fin 4` families ↔ 4 named circles, `i<j` ↔ six hypotheses. |
| thm:soddy `soddy` ↔ blind_71 | ✓ | ✓ | none | `Fin 5`, ten hypotheses |
| thm:apollonian `descartes_solve` ↔ blind_72 | ✓ | ✓ | none | `BlindDescartesCurvatures ![…] ↔ descartesForm … = 0` |
| thm:apollonian `descartes_vieta` ↔ blind_73 ∧ 74 | ✓ | ✓ | none | |
| thm:apollonian `descartes_reflect` ↔ blind_75 | ✓ | ✓ | none | |
| thm:apollonian `apollonian_integral` ↔ blind_76 (∧ 77) | ✗ | ✓ | **ARTEFACT** (blind stronger) | B→R is proved: blind_76 with the move list `[3]`. For R→B, real gives one reflection in coordinate 4 over ℤ, while blind claims closure under any sequence of moves in any coordinate (Descartes property and integrality). Deriving that needs the form's permutation symmetry plus induction on the list. My attempt (`work/B.lean`, `move_step`) did not compile in time, so it is **not** in the gated file. The paper's iterated claim matches the library's `isDescartes_foldr`, not `apollonian_integral`, so this is a pairing artefact. |

Summary:
- 21 of 29 rows have both directions proved (a row can group several declarations).
- 2 rows are restricted B→R (n > 0, positive radii).
- 3 rows are one-directional with a documented difference: two strong Steiner forms, and `apollonian_integral` R→B.
- 3 rows have no blind counterpart.

None of the documented differences shows the blind writer misreading the prose. The REAL items are omissions: Bankoff's circle is missing from Blind.lean.

## Unattempted / incomplete (explicit)

- `bankoff`, `bankoff_exists`: no blind statement exists. Blind omission.
- `image_inversion_sphere`: no blind statement with this content.
- `steiner_porism_strong`, `steiner_concentric_strong`: B→R. Real is strictly more general; it would need genuine mathematics.
- `steiner_porism` B→R at n = 0, and `steiner_concentric` B→R at n = 0 or S₁.radius = 0: unreachable from blind's hypotheses.
- `apollonian_integral`: R→B not in the gated file (attempt failed to compile; see above). blind_77 is not separately compared.
- Out of scope (blind statements with no listed real pair): blind_18, 23, 25, 27–29, 36–39, 56, 59, 78.

## Gate

Compile:
- `cd ~/lean/l13_arbelos && lake env lean scratch/L13_compare.lean` → **exit 0, 0 errors**. Warnings are lint only (unused `NeZero` section variable). The compile took about 4.7 s wall-clock against the built `.olean`s.
- `cd ~/lean/l13_inversion && lake env lean scratch/L13_compare.lean` → **exit 0, 0 errors**.

Grep: `grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|\baxiom "` on both files returns **nothing** (exit 1). An earlier hit on the word "sorry" in my own docstring was reworded.

Library-theorem audit: I ran a `run_cmd` over every constant in `L13CmpArb` (153) and `L13CmpInv` (58), walking `getUsedConstants`. Result: **no library theorem is used in any proof value**. The only library constants used are definitions: `IsSteinerChain`, `IsSimpleSteinerChain`, `IsDisjointSteinerChain`, `HasDisjointDiscs` in arbelos; none in inversion. The other definitions were unfolded during elaboration. This ran in a temporary copy, which was deleted.

Axioms: `#print axioms` on every `*_R_to_B` / `*_B_to_R` / `*_pos` theorem and `blind26_holds` gives only `[propext, Classical.choice, Quot.sound]`. I ran this in a temporary audit copy, which was then deleted.

git status --porcelain:
- `l13_inversion`: empty.
- `l13_arbelos`: shows `M Arbelos/Bankoff.lean` and `M Arbelos/Steiner.lean`. **This was there before I started.** It was the first thing I saw. The sources are dated Oct 30 16:55 and carry the uncommitted `bankoff_exists` and simple/disjoint Steiner additions, which some of my pairs depend on. I did not edit any library file. `scratch/` is git-excluded (`.git/info/exclude`) in both repos.
- `l13_inversion/scratch/t1.lean` also exists and is not mine.
- Temporary audit files were removed. `scratch/` on john now holds only `L13_compare.lean`, `L15_compare.lean` and `t1.lean` (inversion).
