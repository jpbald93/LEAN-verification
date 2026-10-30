# L13 COMPARE — Paper H, EulerIneq (blind_1 … blind_27)

Machine: x86-64 machine, work copy `~/l14h_euler` (HEAD 545a974). Blind file: `~/PaperHBlind.lean`, sha256 `e257c271479a928f78fd921fe07747d30285031439fe2241e8125a20a8f08cbc` (matches the local copy `layer13/Blind.lean`).
Scratch: `~/l14h_euler/scratch/L13_compare.lean` (sha256 `8094841f4668858a…`); local generator copy: `<work-dir>`. `scratch/` is listed in `.git/info/exclude`.

Method. I copied the Blind preamble (lines 3–82: the `Blind*` definitions, oriented section included) verbatim; `diff` against the blind file shows no differences. Each `blindK_stmt` is `∀ {V P} [instances], ∀ <blind binders>, <blind conclusion>`, with the conclusion copied by script from the blind file. Each `rb_K : type_of% @EulerIneq.<decl> → blindK_stmt` and `br_K` (the reverse) is proved only from the premise plus the agreement lemmas, `ring` and `linarith`. No repository main theorem is used in any proof body.

## Results

| pair | R→B | B→R | difference | note |
|---|---|---|---|---|
| 1 euler | ✓ | ✓ | none | identical |
| 2 euler_inequality | ✓ | ✓ | none | identical |
| 3 euler_inequality_eq_iff | ✓ | ✓ | none | `BlindEquilateral` unfolds definitionally to the repository's conjunction |
| 4 euler_excenter (i=0) | ✓ (`h t 0`) | ✓ only to the i=0 instance | SAFE-Lean-more-general | the Lean statement quantifies over `i : Fin 3`, and each blind statement is one specialisation. All three together imply the full statement: `br_456 : blind4 ∧ blind5 ∧ blind6 → euler_excenter` (proved with `fin_cases`). Pairing is correct. |
| 5 euler_excenter (i=1) | ✓ | ✓ only to the i=1 instance | SAFE-Lean-more-general | same as 4 (`br_456`) |
| 6 euler_excenter (i=2) | ✓ | ✓ only to the i=2 instance | SAFE-Lean-more-general | same as 4 (`br_456`). The blind comment says the theorem body was redacted, but the reconstruction matches Lean exactly, so this is not an artefact. |
| 7 dist_circumcenter_centroid_sq | ✓ | ✓ | none | centroid is `rfl`; `1/9*x` vs `x/9` closed by `ring` |
| 8 dist_circumcenter_orthocenter_sq | ✓ | ✓ | none | identical |
| 9 dist_incenter_centroid_sq | ✓ | ✓ | none | semiperimeter and centroid are `rfl`; `ring` |
| 10 fundamental_quartic | ✓ | ✓ | none | semiperimeter agreement |
| 11 gerretsen (lower bound) | ✓ (`.1`) | ✓ only to this conjunct | SAFE-Lean-more-general | Lean's statement is the conjunction. Both blind statements together give it back: `br_11_12 : blind11 ∧ blind12 → gerretsen`. |
| 12 gerretsen (upper bound) | ✓ (`.2`) | ✓ only to this conjunct | SAFE-Lean-more-general | same as 11 |
| 13 gerretsen_cross_check | ✓ | ✓ | none | identical |
| 14 kooi | ✓ | ✓ | none | semiperimeter agreement |
| 15 kooi_le_gerretsen | ✓ | ✓ | none | identical |
| 16 weitzenboeck | ✓ | ✓ | none | area agreement |
| 17 weitzenboeck_eq_iff | ✓ | ✓ | none | area and equilateral agreement |
| 18 hadwiger_finsler | ✓ | ✓ | none | area agreement |
| 19 hadwiger_finsler_eq_iff | ✓ | ✓ | none | area and equilateral agreement |
| 20 isoperimetric | ✓ | ✓ | none | area agreement (`√3` is the same as `Real.sqrt 3`) |
| 21 isoperimetric_eq_iff | ✓ | ✓ | none | Lean writes "equilateral" as `a=b ∧ b=c`, the blind writer as `c=a ∧ a=b`; bridged by `agree_equilateral'` (a trivial rewrite) |
| 22 leibniz_relation | ✓ | ✓ | none | centroid agreement; `ring` |
| 23 leibniz_min | ✓ | ✓ | none | `1/3*x` vs `x/3`; `linarith` |
| 24 leibniz_min_eq_iff | ✓ | ✓ | none | centroid agreement plus the `1/3` rewriting |
| 25 pedoe | ✓ | ✓ | none | area agreement in both triangles; the triangles may live in different spaces on both sides |
| 26 pedoe_eq_iff | ✓ | ✓ | none | area agreement; the similarity clause `∃ k > 0, …` is identical |
| 27 ptolemy_inequality | ✓ | ✓ | none | identical |

Summary:
- **No REAL differences and no ARTEFACTs.** 21 of the 27 pairs are exact equivalences.
- **Pairs 4–6 and 11–12 are SAFE-Lean-more-general.** Lean bundles the excentre index (`∀ i`) and Gerretsen's two bounds (`∧`) into one statement, while the blind writer split them. Each blind statement is weaker on its own, and the blind statements are jointly equivalent to the Lean statement (`br_456`, `br_11_12`).
- **The pairing looks right throughout.**

## Agreement lemmas used (all proved by `rfl` or `Iff.rfl` plus a trivial rewrite)
- `agree_area : BlindArea t = EulerIneq.area t` (`rfl`)
- `agree_semiperimeter : BlindSemiperimeter t = EulerIneq.semiperimeter t` (`rfl`)
- `agree_centroid : Finset.univ.centroid ℝ t.points = t.centroid` (`rfl`; Mathlib's `Simplex.centroid` is an abbrev)
- `agree_equilateral : BlindEquilateral t ↔ (c = a ∧ a = b)` (`Iff.rfl`)
- `agree_equilateral' : BlindEquilateral t ↔ (a = b ∧ b = c)` (short rewrite)

I did not need L14.lean or any bridge lemmas. None of the Blind oriented/apex/Napoleon/side-line-distance definitions appear in blind_1..27.

## Checks
- Compile: `cd ~/l14h_euler && flock ~/ph.lock lake env lean scratch/L13_compare.lean` gives **exit code 0**, with no errors or warnings beyond the `#print axioms` output.
- Forbidden-token grep: `grep -nE "sorry|admit|native_decide|axiom" scratch/L13_compare.lean | grep -v "#print axioms"` returns **empty**.
- `#print axioms` on all 54 rb_/br_ theorems (rb_1…rb_27; br_1, br_2, br_3, br_4, br_5, br_6, br_456, br_7…br_10, br_11_12, br_13…br_27): every one reports `[propext, Classical.choice, Quot.sound]` (54 of 54).
- Library hash, `find . -name "*.lean" -not -path "./.lake/*" -not -path "./scratch/*" | LC_ALL=C sort | xargs sha256sum | sha256sum`:
  - before: `ab2c9f67c825f6ff38555c42e72c955f7a2e7717679338b47089642af8618376`
  - after: `ab2c9f67c825f6ff38555c42e72c955f7a2e7717679338b47089642af8618376` (unchanged; `git status --short` is empty)

DONE
