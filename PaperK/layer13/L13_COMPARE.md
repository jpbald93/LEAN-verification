# Paper K — Layer 13 statement comparison

Repository: `jack:~/paperK`, commit `464a59df987e149e1e545cbd5299196ecce354ed`.
Comparison: `jack:~/paperK/scratch/BlindCompare_K.lean`; local copy: `BlindCompare_K.lean`.
Blind input SHA-256: `27e56aa2054376d397fcb68a912f4fcf5526e89a2bc701a44bc73986d4738818`.
The blind definitions are embedded unchanged, with repository imports added. No blind proofs were imported.

## Reading the results

`YES` means a compiled implication certificate named `L13Compare.sNN_RB` or `sNN_BR`.
`STOP` means no such implication is claimed: the missing step is not mere unfolding, encoding transport, specialization, or explicit arithmetic. It does **not** mean the implication has been disproved in Lean. These are statement-level comparisons; proving two already-true theorems independently would not establish the requested agreement.
`UNPAIRED` respects the collector's instructions; no replacement declaration was silently substituted.
Real declarations appear only as types obtained with `type_of%`, never as proof steps. Conjunction types are explicitly named `R02`, `R19`, `R30`, `R35`, and `R43`.

| pair | R→B | B→R | difference (REAL / AMBIGUITY-ARTEFACT / —) | one-line note |
|---|---|---|---|---|
| s01_null_iff | YES | YES | — | Definitionally identical null-cone relation. |
| s02_gram | YES | YES | — | Existential witness identified with the specified `G` by coordinate-unit-vector specialization; symmetry checked entrywise. |
| s03_signature | UNPAIRED | UNPAIRED | — | Explicitly excluded: no signature declaration. |
| s04_tangency | YES | YES | — | Same null hypotheses and polynomial identity. |
| s05_tangency_defect | UNPAIRED | UNPAIRED | — | Explicitly excluded: no standalone defect declaration. |
| s06_tangency_not_identity | UNPAIRED | UNPAIRED | — | Explicitly excluded: no counterpart. |
| s07_tangency_chart | UNPAIRED | UNPAIRED | AMBIGUITY-ARTEFACT | Listed counterpart is a homogeneous zero-locus iff, not the chart's exact-value identity; no re-pairing. |
| s08_tangent_iff | YES | YES | — | Divide the homogeneous equation by the nonzero v-slots; reverse equality orientation. |
| s09_cofactor_null | YES | YES | — | Identical signed-minor convention and matrix equation. |
| s10_cofactor_orth | YES | YES | — | Identical explicit Gram matrix, cofactor and bilinear form. |
| s11_thm1 | YES | YES | — | All three conclusion conjuncts match after `ℝ × ℝ` ↔ `Fin 2 → ℝ` transport. |
| s12_thm1_cofactor | STOP | YES | REAL | Blind asserts span membership and affine weights; real concludes only collinearity. |
| s13_null_iff_N | YES | YES | — | `LV` ↔ `Cyc` field repackaging. |
| s14_tangency_N | YES | YES | — | Same identity after `LV` ↔ `Cyc` repackaging. |
| s15_tangent_iff_N | YES | YES | — | Common nonzero denominator moved through the finite sum. |
| s16_thm1_N | YES | STOP | AMBIGUITY-ARTEFACT | **Lean more general / stronger, safe:** real also supplies affine weights, deliberately dropped by blind reading. |
| s17_thm2 | YES | YES | — | Determinant columns, signs, denominator, radius and common power agree. |
| s18_thm2_indep | YES | YES | — | Same determinant formulas and pairwise power equality. |
| s19_thm2_link | YES (conjunction) | STOP | AMBIGUITY-ARTEFACT | **Lean component conjunction stronger, safe:** `row_relation` and `cof0`–`cof4` imply the corrected link, but include singular D=0 cases absent from blind. |
| s20_thm2_naive_wrong | UNPAIRED | UNPAIRED | — | Explicitly excluded numeric/existential witness. |
| s21_thm3 | YES | YES | — | Same normalization, nullness, orthogonality, sign and constant. |
| s22_thm3_family | YES | YES (Type 0) | AMBIGUITY-ARTEFACT | Same at blind universe; **Lean more general, safe:** repository theorem permits arbitrary universes. |
| s23_thm3_coord | YES | YES | — | `lag` ↔ `pw`; `2*(P4/P3)` ↔ `2*P4/P3`. |
| s24_thm3_N | YES | YES | — | Explicit chart ↔ fields v=1,w=(r²−Σc²)/2; constants agree by denominator arithmetic. |
| s25_equal_circles | STOP | STOP | AMBIGUITY-ARTEFACT | Blind unique-equidistant-point encoding omits explicit Cramer coordinates; identifying these requires a geometric/algebraic bridge. |
| s26_thm4 | YES | STOP | AMBIGUITY-ARTEFACT | **Lean more general, safe:** real has no null-P hypothesis; fourth circle can be specialized to the first. |
| s27_thm4_no_null | YES | YES | — | Actual real declaration has no null-P hypothesis; repeated first circle supplies the extra fourth circle. |
| s28_thm5_apollonius | YES | YES | — | Chart orthogonality ↔ `Tangent`; explicit index permutation blind→real `[0,3,1,2]`. |
| s29_thm5_distinct | YES | YES | — | Identical inequality. |
| s30_thm5_null_space | YES | YES | — | Three real declarations ↔ span, linear independence and dimension; general Mathlib finite-span dimension lemma only. |
| s31_thm5_not_null | UNPAIRED | UNPAIRED | — | Explicitly excluded: no standalone declaration. |
| s32_thm5_centre | YES | YES | — | Same orthogonal family up to index order; pair/vector zero transport. |
| s33_tetra_centre | YES | STOP | AMBIGUITY-ARTEFACT | **Lean more general, safe:** real does not require P null. |
| s34_tetra_equidistant | YES | YES | — | Pairwise distances ↔ four equations to a common d; conclusions match. |
| s35_tetra_apollonius | YES | PARTIAL: tangency only | AMBIGUITY-ARTEFACT | Blind equals `tetra_tangent_B`; listed conjunction additionally asserts positive metric radii. |
| s36_tetra_scaled | STOP | STOP | AMBIGUITY-ARTEFACT | Real scales centres and radii; blind scales radii only and additionally requires P null. |
| s37_tetra_affind | YES | YES | — | Identical ordered vertices and affine independence. |
| s38_tetra_apart | UNPAIRED | UNPAIRED | — | Pairwise squared vertex distance 8 is not origin-distance/contact-radius statements. |
| s39_simplex | YES | YES | — | Equal squared norms agree; choose the first given cycle for the redundant extra cycle. |
| s40_simplex_circumradius | STOP | STOP | AMBIGUITY-ARTEFACT | Actual Mathlib circumradius versus squared vertex norm / explicit power constant; not a definitional bridge. |
| s41_dist_const | YES | STOP | AMBIGUITY-ARTEFACT | **Lean more general / stronger, safe:** arbitrary common radius and explicit value versus unit-radius pairwise equality. |
| s42_thm6 | YES | STOP | AMBIGUITY-ARTEFACT | **Lean stronger, safe:** failure in n=2 implies failure for some n, but not conversely by specialization. |
| s43_thm6_explicit | YES | YES | — | Four real components plus definitionally computable v-slot/centre fields match the blind conjunction. |

## Differences and stopping points

* **s12 — REAL:** The same hypotheses are present, including the nonzero cofactor v-slot. The real `prop31_cofactor` concludes only `Collinear`; it does not state either blind conjunct. Blind→Real repackages affine weights into collinearity. Real→Blind would need cofactor orthogonality (a development theorem, forbidden as a proof step), then span membership and affine weights. Collinearity alone also does not generally imply membership in the affine line through two specified coincident endpoints. Thus the blind conclusion is stronger in the requested statement-level sense. The documented ambiguity for this row concerns retaining the nonzero v-slot, not these extra conclusions.
* **s16 — AMBIGUITY-ARTEFACT:** `L13_STATEMENTS.md`, s16, explicitly says the affine-weight conjunct was dropped. The real statement is stronger and safely implies the blind. Recovering weights from the spanning hypothesis would reconstruct the affine-combination theorem, not merely transport the collinearity conclusion.
* **s19 — AMBIGUITY-ARTEFACT / partial pairing:** The collector and blind notes explicitly say the prose link is not one formalized statement. The certificate assumes the entire listed conjunction, never calls its component theorems. It rewrites cofactors into determinant expressions and uses the assumed row relation. The converse would have to recover unconditional statements at D=0 and omitted cofactor information; it is not claimed.
* **s22 — AMBIGUITY-ARTEFACT:** `s22` binds `ι : Type`, not `Type u`. Both certificates use the repository theorem at Type 0. No converse for arbitrary universes is certified.
* **s25 — AMBIGUITY-ARTEFACT:** The documented blind encoding is a unique equidistant point, whereas the real declarations give explicit `ccx`/`ccy` coordinates and an iff for arbitrary equal-power points. The real package specifies additional coordinate information and applies to arbitrary points, not only the supplied orthogonal P. A full comparison also needs determinant-nonzero ↔ non-collinearity. Those bridges were not proved by reconstructing the development. No direction is certified; this is not a claim that one statement is false.
* **s26/s33 — AMBIGUITY-ARTEFACT:** The blind notes explicitly interpret “cycle” as null. The corresponding real declarations allow arbitrary P. These are safe weakenings of the real theorem, not errors in the real theorem. In particular, **s27 does match** the actual `equilateral_PX`: the table's conditional warning about a real null hypothesis does not apply.
* **s35 — AMBIGUITY-ARTEFACT:** The blind row explicitly chooses only orthogonality. The real `tetra_tangent_B` component is equivalent and has certificates both ways. Adding `tetra_radii_metric` produces a stronger conjunction, with positivity of the unoriented inscribed/enclosing radii absent from the blind statement. The full converse was stopped, not replaced by an independent proof of positivity.
* **s36 — AMBIGUITY-ARTEFACT:** The blind notes explicitly flag whether centres scale, and choose fixed centres. `tetraFamR` instead uses `(±s,±s,±s)` with radius s. At the same objects and parameter these are different families; neither full statement is a direct specialization of the other. Additionally, only blind requires null P. No rescaling of P or substitution of another theorem was used to conceal this mismatch.
* **s40 — AMBIGUITY-ARTEFACT:** The blind uses an actual Euclidean `Affine.Simplex.circumradius`. The real theorem equates `Σ(cᵢk)²` with its coordinate power constant. Establishing the origin as the geometric circumcentre and relating that to the Mathlib radius is genuine geometry, not unfolding. Neither direction, nor a strength ordering for these differently encoded conclusions, is certified.
* **s41 — AMBIGUITY-ARTEFACT:** Real has arbitrary common radius and an explicit distance value. Blind selects radius 1 and forgets the value; pairwise equality alone does not supply that value. This is safe “Lean more general,” with the forward specialization certified.
* **s42 — AMBIGUITY-ARTEFACT:** The notes deliberately read the negation over all n. Real locates a counterexample specifically in dimension 2. Forward certificate uses only specialization under negation. Reverse would require supplying/localizing a counterexample, which would be truth-level work.
* **s07 — rejected pairing:** The supplied `B_eq_zero_iff_tangent` is an iff about a zero set for arbitrary null homogeneous vectors, while blind states an exact bilinear value on chart vectors. A direct independent polynomial proof of the blind identity would not make these the same statement. The chart restriction is documented in the blind notes. No alternate real declaration was substituted.

Ambiguity source actually read: `/tmp/afmrun/paperK/l13/L13_STATEMENTS.md`, especially rows s07, s16, s19, s25–s27, s33, s35–s36, s40–s42. Its original “not compiled” provenance is superseded for elaboration purposes by the supplied blind file and this comparison's successful run; it is used only as the ambiguity record.

## Unattempted / intentionally unfinished

* **No proof attempts, expressly excluded:** s03, s05, s06, s20, s31. Their Prop definitions remain in the embedded blind source, but no comparison certificates or proofs of these claims were added.
* **Rejected before implication proofs:** s07 and s38, because the supplied counterpart does not state the blind claim. This follows the pairing table's UNPAIRED rule.
* **Inspected and stopped before certificates:** s25, s36, s40, for the mathematical/encoding differences described above.
* **Only safe direction completed:** s12 (B→R); s16, s19, s26, s33, s41, s42 (R→B). s35 additionally has the reverse for its tangency component only. s22 has both directions at Type 0 only.
* s13–s15, omitted from the requested priority enumeration but paired by the collector, were checked after the four priority blocks. No paired row was silently dropped. All compilations were remote on jack, with the prescribed lock; no whole-repository build was run.

## Validation

Final remote invocation (every earlier Lean invocation used the same locked command):

```sh
ssh -o BatchMode=yes jackagent@100.72.132.55 "cd ~/paperK && flock ~/pi.lock bash -c 'PATH=\$HOME/.elan/bin:\$PATH lake env lean scratch/BlindCompare_K.lean'"
```

Result: **`LEAN_RC=0`**. The output consists of the blind `#check` lines and non-fatal style warnings at comparison-file lines 688, 705, 723 and 933; no Lean errors. The warnings concern unnecessary tactic sequencing / `simpa`, not incomplete proofs.

Forbidden scan actually run on jack:

```sh
grep -nE 'sorry|admit|native_decide|axiom' ~/paperK/scratch/BlindCompare_K.lean
```

Output: empty; **`GREP_RC=1`** (no matches). Separate `grep -nE 'opaque'` also returned empty, **`OPAQUE_GREP_RC=1`**.

`git -C ~/paperK status --porcelain`: **empty**, both initially and finally. Final output showed adjacent `STATUS_BEGIN` / `STATUS_END` markers with no intervening lines. `git check-ignore scratch/BlindCompare_K.lean` returned `scratch/BlindCompare_K.lean`, confirming the exclusion remains effective. Final HEAD remained `464a59df987e149e1e545cbd5299196ecce354ed`.

Comparison SHA-256 from jack:

```text
87a224931a10fca9476d0c3082336c351817a79a4d17e5d6f7afd27472d96027  scratch/BlindCompare_K.lean
```

### Library-file hashes before / after

The brief's prefix `24e80351` is already **Bridge.lean's** actual hash; it is not a sixth distinct file in `PaperK/`. The directory contains five Lean files. To make six tracked library files explicit, the root import file `PaperK.lean` was also hashed before comparison edits and after completion. The duplicate source `src/paperK_3d.lean` was independently checked as well. No claimed sixth hash was invented.

| file | before SHA-256 | after SHA-256 |
|---|---|---|
| `PaperK.lean` | `d1d23e3b95b399894aeb32a72832b059b871c95f5341d662fd5f34a2a3d61729` | `d1d23e3b95b399894aeb32a72832b059b871c95f5341d662fd5f34a2a3d61729` |
| `PaperK/Bridge.lean` | `24e803518794cc2a97087f1af7dcdadd9c6567e937e847ebc422b2a2b90f27b8` | `24e803518794cc2a97087f1af7dcdadd9c6567e937e847ebc422b2a2b90f27b8` |
| `PaperK/LieCore.lean` | `6a19ca206116e5f78c7ef3596fc46dc36851324c48b708cccf1951a375f97581` | `6a19ca206116e5f78c7ef3596fc46dc36851324c48b708cccf1951a375f97581` |
| `PaperK/ThreeD.lean` | `3b326b04f20c6e32e4d155c3c3fd8b00dd7c16d993902a0cc73b8f493b9d1cb1` | `3b326b04f20c6e32e4d155c3c3fd8b00dd7c16d993902a0cc73b8f493b9d1cb1` |
| `PaperK/TwoD.lean` | `a77e2e53dd80ef77e3a6b95938ddf2ce91790b5e03e8a9c72320f3c20dca8c7e` | `a77e2e53dd80ef77e3a6b95938ddf2ce91790b5e03e8a9c72320f3c20dca8c7e` |
| `PaperK/GeneralN.lean` | `9e28c5a3f15c5e87526715b20c39013b8dee82a29b8aa54754c763b9883eca4a` | `9e28c5a3f15c5e87526715b20c39013b8dee82a29b8aa54754c763b9883eca4a` |
| `src/paperK_3d.lean` (extra check) | `3b326b04f20c6e32e4d155c3c3fd8b00dd7c16d993902a0cc73b8f493b9d1cb1` | `3b326b04f20c6e32e4d155c3c3fd8b00dd7c16d993902a0cc73b8f493b9d1cb1` |

All read before/after hashes are unchanged. The collector table's numerical summary was not used as evidence: this report follows its individual rows and records each disposition explicitly.
