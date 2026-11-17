# External review — Paper I v4

**Verdict: MAJOR revision.** The 25 numbered theorems in the frozen paper are substantially faithful to the four pinned Lean libraries, including the repaired Bankoff centre, the explicit non-degeneracy assumptions, and the distinction between repeating and disjoint Steiner chains. The final battery table, automatic satisfiability figures, unused-hypothesis inventory, library sizes, and clean-export digests are reproducible. However, the new completion subsection contains false mathematical statements, notably a claimed nonexistence in the collinear-feet example for which an explicit completion exists, and omits a necessary nonzero-curvature hypothesis. The verification narrative also overstates what the survivors, bridge files, blind comparisons, and supplementary certificates establish. These are substantive claim/evidence discrepancies, not stylistic objections. Most can be fixed by accurately narrowing the prose; the existing numbered results do not need to be discarded.

## Scope and evidence

- Reviewed **this directory's frozen** `paperi.tex`, SHA-256 `129a04e53df9f9a77d0623cd821008508454be670e1f32a72469ef67efa7fb14`, and text extracted from `paperi.pdf`, SHA-256 `8a9e910d0c84d18d96c313745b5f4ce1daaeff8cf51bef9570fd291c6a48a61f`. Native PDF/image input was unavailable; `pdftotext -layout` succeeded. This is a mathematical/content review, not a visual-layout certification.
- All paper line numbers below refer to that frozen TeX source. Section numbers are the rendered PDF's: completion is §6.1, verification §7, availability §10.
- Read the actual sources over SSH, without modifying them. Verified clean working trees at `0c372061edd32cc7935cf1521d404dfbc3993ac5` (quad), `6c714e57d5cf41a43838d2a0e380fdc028e9b15b` (circles), `0dddc6e05fc14ad3d25325aecfc1ca225837ae6b` (arbelos), and `c71abb76b265d660ae2d73b629beac2c338c8b27` (inversion). All four dependency checkouts report Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- Read `gate.sh`, `tests/tamper.sh`, the remote final battery reports, the raw clean-export build/gate/tamper logs, both scouts, and the supplied Layer 10/13/14/15 reports and relevant certificates. Supplementary Paper J source hashes match the collector's recorded remote files.
- Re-ran the supplied name/anchor checker on the **frozen** TeX with fresh SSH input: PASS, 159 distinct `\decl` spellings and 83 anchors. This is not a semantic-equivalence check; see finding 18.
- Did not rerun the hour-long batteries or modify/rebuild the remote repositories. Read their raw receipts and independently recounted source declarations/files and recomputed tracked-source digests. Used `lake env lean --stdin` for read-only elaboration checks and an exact counterexample check.

## Numbered findings

| # | severity (MAJOR/MINOR) | where (section, line) | finding | exact fix |
|---|---|---|---|---|
| 1 | MAJOR | §6.1, 747–749 and 753–756 | The sentence “the example `a=b=1`, `c=1/4` has no fourth sphere of the required kind” is **false**, not a proved negative result. The supplied `descartes_plane3d.lean` proves only a construction assuming a nonzero feet determinant; it contains no nonexistence theorem. Take the three centres `(0,0,1)`, `(2,0,1)`, `(1,0,1/4)` with radii `1,1,1/4`. Their feet are collinear and they are mutually externally tangent. The sphere with centre `(1,√3/3,1/3)` and radius `1/3` rests on `z=0` and is externally tangent to all three. Its three squared-distance identities were checked exactly with SymPy and Lean (details below). Singularity of the proposed formula does not imply nonexistence. | Replace with: “The explicit foot construction assumes non-collinear feet. The collinear case is not covered by that construction; it need not lack a completion (for radii `1,1,1/4`, a radius-`1/3` completion exists).” Remove the claimed collinear nonexistence from the Status paragraph and change “two negative results” at 721 to “one negative result” when referring to these three supplementary files. Keep the separate numerical completion-map refutation distinct. |
| 2 | MAJOR | §6.1, 743–747 | “For spheres whose centres lie in a plane … `|p−q|²=4rs`” describes the **wrong geometry**. Here `p,q` are feet on a common tangent plane, and the actual centres are `lift p r=(Re p,Im p,r)`. The next phrase, “the unit sphere of curvature `1/3`,” reverses radius and curvature: the constructed sphere has radius `1/3`, curvature `3`, and is not a unit sphere. The identification of `z=2r` is explanatory text in the supplementary report, not a theorem about a hyperplane in its Lean file. | Replace the opening by: “For positive-radius spheres resting on the common tangent plane `z=0`, with centres `(p,r)` and `(q,s)`, external tangency is equivalent to `|p−q|²=4rs`. Three mutually tangent unit spheres in this arrangement admit the explicit radius-`1/3` (curvature-`3`) sphere.” Say that the equal-radius zero root “has the geometric interpretation of the second parallel tangent plane `z=2r`; this hyperplane interpretation is not separately formalised here.” Delete “reflected in the configuration's own plane,” which does not specify the relevant reflection plane. |
| 3 | MAJOR | §6.1, 724–731 | “Under an affine-independence hypothesis … both Soddy spheres exist” omits `κ ≠ 0`. `Soddy3D.soddy_exists_3d` explicitly concludes **`κ ≠ 0 → ∃ x ρ, …`**; affine independence only makes the two roots distinct, not both nonzero. The builder explicitly lists this necessary restriction. | Say: “For four mutually tangent spheres with nonzero signed radii and affinely independent centres, every **nonzero** root `κ` of the Soddy quadratic is realised by the explicit sphere of signed radius `1/κ`. A zero root is not covered by this sphere construction.” Include the signed tangency convention and cite `soddy_exists_3d`/`soddy_exists_3d_of_root` with file and line. |
| 4 | MAJOR | §6.1, 737–741 and 755 | “There is no fourth circle enclosing three mutually tangent ones” is false without the enclosing-member setup. Three externally tangent equal circles, for example, have an enclosing Soddy circle. `no_enclosing_soddy` concerns **two positive-radius externally tangent circles already internally tangent to a given enclosing circle**; any circle containing that enclosing disc and internally tangent to both small circles equals the given circle. | Replace the conclusion with precisely that conditional statement. Before the root-positivity claim, specify `R,a,b>0`, `dist 0 ca=R−a`, `dist 0 cb=R−b`, `dist ca cb=a+b` (which imply `a+b≤R`), and the nonzero signed-radius tangency hypotheses of `soddy_enclosing_pos`. In Status, say “no distinct larger enclosing circle in this enclosing-member configuration.” |
| 5 | MAJOR | §6.1, 716–730, 740–741, 749–751 | Three prior-art correspondences are inaccurate. `cmp_exists_unique_completion` completes a **missing column of a curvature–centre matrix with all `n+2` rows already present**, not a missing sphere of an `n+1`-sphere configuration. `sphere_soddy_gosset_enclosing` states a **signed curvature identity**, not the claimed exclusion. `tangent_family_two_hyperplanes` forbids **three** zero-curvature members, not two hyperplanes; two parallel planes are allowed and are precisely relevant to the equal-radius case. I checked the cited repository's actual `Solution.lean` and `Completion.lean` via GitHub, not just the scout's paraphrase. | Describe `cmp_exists_unique_completion` as the matrix-column completion theorem and do not identify the local sphere construction with its `n=3` specialisation without an actual reduction. For the two-completion classification, cite and accurately state `two_tangent_spheres` (which starts from a full valid tangent family). Describe `sphere_soddy_gosset_enclosing` only as the enclosing-member curvature identity. Replace “two hyperplanes is excluded” by “at most two hyperplane members are permitted; the cited theorem rules out three.” Preserve the acknowledgement of prior general Descartes/Soddy work; this correction is not a new priority claim. |
| 6 | MAJOR | §6.1, 753–754; §10, 1177–1203 | “All 67 statements … with the gate and tampering conditions of Section 7” is not supported for the three added files. They are scratch certificates, absent from the four pinned library trees and their `REQUIRED` lists; their documented checks are compilation, forbidden-token search, and selected axiom reports, not the four libraries' tamper suites or batteries. The count 67 counts only unannotated public `theorem` lines: the files actually have **68 public theorems** (including `@[simp] lift_height`) and **9 private theorems**, 77 total. No pinned archive path for these additional files is given in the paper. | Replace by: “The three supplementary scratch files were compiled and checked for forbidden tokens; axiom reports for the listed main declarations use only the standard axioms. They are not covered by the four libraries' gates, tamper suites, or statement batteries.” Give the three filenames, source hashes and archive locations. If counting all theorem declarations, use 77, split 32/26/19; if counting public ones, use 68, split 32/20/16. Do not claim “same archive” until that archive actually contains them. |
| 7 | MAJOR | §7, “The survivors,” 895–905 | The **15 names/counts are right**, but “every one … a concrete existential witness, not in a theorem” and “No survivor … in a theorem” are wrong. `twin_left_exists` is a universally parametrised library theorem in Table 1, not a concrete L14 witness. Several L14 witnesses are closed conjunctions, not existentials. “Each … a weakened bound” is also wrong: `0<r → 1<r` strengthens a bound; other changes alter an exponent, a coefficient of a zero vector, an irrelevant coordinate, or the sign of a squared numeral. The circles report also explicitly records that two Johnson mutants' own proofs compile while a downstream theorem fails. | Replace the classification by: “Fourteen survivors occur in L14 concrete witness declarations; one occurs in `twin_left_exists`, where `<2a` becomes the weaker `<3a`. The witness survivors remain true at their chosen values: some strengthen still-satisfied bounds, others leave evaluated terms unchanged or replace one closed true assertion by another. No survivor occurs in a Layer-10 bridge. Two Johnson witness mutants are classified as surviving at their own declaration although downstream use fails.” Include the per-mutant explanations in the audit below rather than a universal weakening claim. |
| 8 | MAJOR | §7, Layer 10, 954–975; §9, 1163–1166; §5, 545–547 | The bridge narrative invents objects/results. `Quadrilaterals` has **no `powPt`** and no `bridge_powPt_eq_power`; its bridge file has no convex-hull-membership theorem. It proves convexity via **opposite sides of the diagonal lines** (`SOppSide`), not the stated hull/`SSameSide` bridge. The determinant/dot helpers attributed to arbelos are private definitions in **Inversion**. Meanwhile §5 says no power bridge exists although `CircleSystems.powPt_eq_power` now does. The count 51 is correct, in the order quad/circles/arbelos/inversion = 15/15/11/10. | Replace the quad description by the actual list: area-form/determinant and coordinate bridges; convexity iff the two diagonal `SOppSide` conditions; cyclicity/Mathlib sphere membership; incircle side-line tangency. Attribute `powPt_eq_power` only to CircleSystems (and `bridge_powC` to Arbelos). Attribute the private determinant/dot helpers to Inversion. Change §5 to “the library proves this definitional equality as `powPt_eq_power`.” Remove `bridge_powPt_eq_power` from §9. List unbridged internal notions per development instead of claiming only the two listed gaps cover everything. |
| 9 | MAJOR | §7, Layer 13, 993–1013 | The paper reports a completed two-way Bankoff comparison that the supplied evidence does not contain. `Blind.lean` has `blind_1`–`blind_80`, not `blind_81/82`; it began with 78 and acquired `blind_79/80` after redaction had removed the Bankoff clauses. The stored comparison proves radius equivalence but explicitly records the existence statement as weaker. Running that stored comparison against the final arbelos library via stdin now **fails** at lines 237, 260 and 262 because the centre conjunct changed the type. The final library fix is real, but it is not a successful rerun of this certificate. Also, there are 25 numbered theorem labels in the frozen paper, while the blind file covers 24: `thm:invbasic` is absent. | State the actual chronology: “78 initial statements, 80 after the Bankoff redaction repair (`blind_79/80`); 24 of the paper's 25 theorem labels, with inversion basics omitted.” Say that the original comparison exposed the centre omission and the final library now includes it, but **updated two-way comparison is pending** unless a fresh compiling certificate is supplied. Do not say “both are equivalent …” on the basis of the stale file. |
| 10 | MINOR | §7, Layer 13, 998–1007 | “Proved both implications” overstates the paired coverage, and “three in one direction (the library's statements are strictly stronger)” has the wrong direction for `apollonian_integral`. For that row the blind iterated-move statement is stronger; B→R was proved, R→B was not. The paper also says every difference is a stronger library statement despite already describing the weaker Johnson pairing. Unpaired blind statements, including radical-axis/pencil items, are not covered merely because the label appeared. | Say “attempted two-way comparisons for selected pairings.” Preserve J's 17 two-way / 1 restricted / 1 B→R-only / 1 unattempted row and M's original 21 two-way / 2 restricted / 3 one-way / 3 missing rows. Specify the directions: two stronger Steiner rows R→B; the iterated-Apollonian row B→R. Explicitly disclose that unpaired blind statements were not compared. |
| 11 | MAJOR | §7, Layer 14, 986–988 | “No Peaucellier–Lipkin linkage with rational link lengths exists” is false and greatly exceeds a bounded search. A non-degenerate classical cell with **`a=3`, `b=5`, `R=4`** exists: take `A=(√21,2)`, `B=(√21,−2)`, `P=(√21+√5,0)`, `Q=(√21−√5,0)`. Then `|A|=|B|=5`, all four rhombus sides have length 3, `A≠B`, `P≠Q`, and `b²−a²=R²=16`. A search restricted to special coordinates cannot establish general irrationality. | Replace with: “The bounded search used for selecting witnesses found no example under its search restrictions; no nonexistence result follows. The chosen witnesses have irrational link lengths and rational joint positions.” State the actual search restrictions or omit the failed-search anecdote. |
| 12 | MINOR | §7, Layer 14, 977–985 | “Supplies an explicit non-degenerate witness for each” contradicts `L14_REPORT.md` lines 31–38. It explicitly lists unwitnessed statements, including some with genuine side conditions. The source has 50 `l14_` restatements but **31 `l14w_` declarations**, some shared across several results. Also the area expansion at 979 uses `sin C` where the second triangle term is `sin ∠CAD`, not the quadrilateral's angle at C. | Say “50 Mathlib-only restatements and 31 concrete witness declarations, with shared witnesses and the omissions listed in the report,” rather than “for each.” Replace the area expression with the exact formula in Definition 1(iii). |
| 13 | MAJOR | §7, Layer 15, 1022–1028; abstract 72–73 | The remaining substantive **I5c geometric-packing gap** is hidden behind “two narrower” and “no statement that differs in substance.” `L15_COMPARE_M.md` distinguishes closure of integer Descartes quadruples under specified moves from integrality in a geometric family generated from **any mutually tangent triple**. The latter needs an unproved reachability/quadruple-extension fact. Theorem 25 is correctly limited to moves; the abstract's unrestricted “integrality of Apollonian curvatures” is less precise. | After reporting the I2b and I5b supplementary closures, add: “I5c remains narrower: we prove integrality under finite Apollonian moves on Descartes quadruples, not the classical arbitrary-triple geometric-packing construction.” Replace “no statement that differs in substance” with “no D-classified row; the stated scope gaps remain.” Qualify the abstract as “integrality under Apollonian curvature moves.” |
| 14 | MINOR | §7, gates/tampering table, 811–813 and 823–829 | The final arbelos suite has **7 tests = five gate attacks + two hypothesis removals**. It does not test weakening `IsSimpleSteinerChain` to `IsSteinerChain`; that third named defect is absent from final `tests/tamper.sh` and the final receipt. “Seven rather than nine because the two Fuss-specific tests …” also does not describe the actual difference (quad has 11). | Delete the simple-chain mutation from the final-commit table, or add/run it and update the counts. Replace the explanation by: “The final arbelos suite contains five gate attacks and two hypothesis-removal tests.” Treat any older simple-chain tamper test as historical evidence at its own revision, not part of this seven-test run. |
| 15 | MINOR | §7, 876–878 and 881–893 | Old and final battery scopes are mixed. The statement that 30 October runs “gave the same mutation figures” is contradicted by the archived reports: quad **167/167**, circles **152/152**, inversion **134/134**, and arbelos's later pre-layer run **189/190**, versus the final expanded totals. Lines 891–893 say “the battery figures … are for commit `53d0573`” and 136 ablation jobs, but the displayed arbelos row is at `0dddc6e`, with **198** jobs. The circles “59 plain and 8 simp” count is likewise pre-addition, not the final 110-target count. | Delete the same-figures claim. Label each older count explicitly as a historical, smaller-scope run. Say the final arbelos figures are at `0dddc6e` with 198 ablation jobs, and do not apply the older circles count to the final table. Keep the final table itself unchanged. |
| 16 | MINOR | §4 proof explanation, 499–502 | The stated iff for internal tangency omits **`0 ≤ ρ_s`**. The actual `isIntTangent_iff` has the squared-distance equation **and** `0 ≤ s.radius ∧ s.radius ≤ t.radius`. The paper deliberately uses Mathlib spheres, which permit negative radius values; the missing condition cannot be silently assumed in this general bridge description. | Write “internal tangency is `|c_s−c_t|²=(ρ_t−ρ_s)²` with `0≤ρ_s≤ρ_t`.” |
| 17 | MAJOR | §10, 1197–1203 | The present-tense availability claim is not reproducible. Each of the four stated GitHub repository API lookups returned **404**, as did the supporting `LEAN-verification/contents/PaperI` path under the available credentials. All four local repositories have no remote. Absence of a remote alone would not prove nonpublication, but the observed 404s mean these are not usable evidence links for this review. | Publish the pinned trees and supporting files before claiming availability, or change to “currently local; planned repository locations are …” and provide a real accessible archive/DOI. Include the supplementary §6.1 and L15 certificates in that archive. Do not present planned `blob/<commit>` anchors as already accessible. |
| 18 | MINOR | §10, 1203–1207 | The namegate is weaker than the surrounding guarantee. It compares short terminal identifiers, does not check `REQUIRED`, and prints fetched HEADs without comparing them to the TeX commit macros. Thus it would not catch the invented `bridge_powPt_eq_power` written in `\lean` font, nor establish fully qualified namespace attribution outside table rows. Its actual 159/83 pass is reproducible, but is not the full promised audit. | Say precisely that the script checks the parsed `\decl` short names and row anchors in fetched trees, with pin/clean-tree/`REQUIRED` checks performed separately. Prefer strengthening the checker to validate full qualified names, pins and gate membership; keep a negative test for a wrong namespace/commit. |
| 19 | MINOR | abstract 74–80 versus §1, 119–120 and §8, 1085–1092 | The blanket “For the remaining statements we found no earlier formal proof” includes the pedal-area identity without the arbitrary-circumcircle/Mathlib-form qualification, even though the body acknowledges the unit-circle identity in `lean-genius`. The main prior-art section otherwise gives appropriately qualified reproof credit and search limitations. | Add “The pedal-area identity also has an earlier unit-circle complex formulation; our formulation uses an arbitrary circumcircle and Mathlib projections.” Restrict “remaining statements” accordingly. |
| 20 | MINOR | §7, 1030–1032 | The author hand check and external-review disposition are deliberately unfinished. This is a known release item, not an unexplained omission. **Only one active `\PH{...}` invocation remains in this frozen TeX**: the fresh-build receipt placeholder described in the brief has already been replaced by the detailed clean-export paragraph. | Complete the hand-check/review-disposition paragraph before release, or leave it explicitly pending in a draft. Do not invent a second placeholder finding; retain the now-supported clean-export paragraph. |
| 21 | MINOR | §2, 208–209; §3, 328–330; §6.1, 759–761; §7, 838–842 | Several historical numerical measurements and old dual-machine digest claims remain **unverified independently** in this review. The supplied narratives record them, but I did not reproduce the universal 30–40-digit pre-proof checks, the stated Fuss numerical residuals, the six-run completion-map measurements, or both historical tree digests from their original inputs. The final clean-export digests are a separate matter and were reproduced. | Give each numerical driver's archive path, inputs/seed and raw output, and identify the exact historical snapshots and digest command. Until those can be replayed, describe them as reported historical measurements rather than independently reproduced checks. This is an evidence limit, not evidence that the figures are false. |

## Exact evidence for the principal mathematical findings

### Collinear feet do not give the asserted nonexistence (finding 1)

Let

`C₁=(0,0,1), r₁=1; C₂=(2,0,1), r₂=1; C₃=(1,0,1/4), r₃=1/4`.

The squared intercentre distances are `4`, `25/16`, `25/16`, exactly the squared radius sums. All spheres rest above `z=0`, and their feet `(0,0),(2,0),(1,0)` are collinear. Set

`X=(1,√3/3,1/3), r=1/3`.

Then `|X−C₁|²=|X−C₂|²=16/9=(1+1/3)²` and `|X−C₃|²=49/144=(1/4+1/3)²`. Positive radii turn these into external tangencies. Its height equals its radius, so it also touches the plane. The fourth curvature is `3`, satisfying `(1+1+4+3)²=3(1+1+16+9)=81`.

The following was checked by `lake env lean --stdin` against the final inversion project, **exit 0** (no remote file written):

```lean
import Inversion.Descartes
example : let X : EuclideanSpace ℝ (Fin 3) := !₂[1, Real.sqrt 3 / 3, 1/3];
  dist X (!₂[0,0,1]) ^ 2 = (1/3+1:ℝ)^2 ∧
  dist X (!₂[2,0,1]) ^ 2 = (1/3+1:ℝ)^2 ∧
  dist X (!₂[1,0,1/4]) ^ 2 = (1/3+1/4:ℝ)^2 := by
  dsimp
  rw [Inversion.dist_sq_fin3, Inversion.dist_sq_fin3, Inversion.dist_sq_fin3]
  change (1-0:ℝ)^2+(Real.sqrt 3/3-0)^2+(1/3-1)^2 = (1/3+1)^2 ∧
    (1-2:ℝ)^2+(Real.sqrt 3/3-0)^2+(1/3-1)^2 = (1/3+1)^2 ∧
    (1-1:ℝ)^2+(Real.sqrt 3/3-0)^2+(1/3-1/4)^2 = (1/3+1/4)^2
  have h : Real.sqrt (3:ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · nlinarith
  constructor <;> nlinarith
```

The supplementary theorem actually proved is:

```lean
theorem plane_fourth_sphere {p₁ p₂ p₃ : ℂ} {a b c k : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (t12 : dist (lift p₁ a) (lift p₂ b) = a + b)
    (t13 : dist (lift p₁ a) (lift p₃ c) = a + c)
    (t23 : dist (lift p₂ b) (lift p₃ c) = b + c)
    (hD : (p₂.re - p₁.re) * (p₃.im - p₁.im) -
      (p₃.re - p₁.re) * (p₂.im - p₁.im) ≠ 0)
    (hroot : (1 / a + 1 / b + 1 / c + k) ^ 2 =
      3 * ((1 / a) ^ 2 + (1 / b) ^ 2 + (1 / c) ^ 2 + k ^ 2)) :
    ∃ p₄ : ℂ, dist (lift p₄ (1 / k)) (lift p₁ a) = 1 / k + a ∧
      dist (lift p₄ (1 / k)) (lift p₂ b) = 1 / k + b ∧
      dist (lift p₄ (1 / k)) (lift p₃ c) = 1 / k + c
```

Source: `AFM/PaperJ/layer0/descartes_plane3d.lean:232`. The `hD` hypothesis restricts this proof; it is not a theorem of impossibility when `hD` fails.

### Other supplementary signatures (findings 2–4)

```lean
-- descartes_plane3d.lean:18,32,74
def lift (p : ℂ) (r : ℝ) : E3 := !₂[p.re, p.im, r]
theorem plane_pair_tangent {p q : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    dist (lift p r) (lift q s) = r + s ↔ dist p q ^ 2 = 4 * r * s
theorem unit_soddy :
    lift u₄ (1 / 3) = !₂[1, √3 / 3, 1 / 3] ∧ lift u₄ (1 / 3) 2 = 1 / 3 ∧
      dist (lift u₄ (1 / 3)) (lift u₁ 1) = 4 / 3 ∧
      dist (lift u₄ (1 / 3)) (lift u₂ 1) = 4 / 3 ∧
      dist (lift u₄ (1 / 3)) (lift u₃ 1) = 4 / 3

-- soddy_3d.lean:438
theorem soddy_exists_3d {c₁ c₂ c₃ c₄ : E3} {r₁ r₂ r₃ r₄ : ℝ}
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0)
    (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2)
    (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2)
    (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2)
    (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2)
    (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2)
    (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2)
    (hind : AffineIndependent ℝ ![c₁, c₂, c₃, c₄])
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let k1 := 1 / r₁; let k2 := 1 / r₂; let k3 := 1 / r₃; let k4 := 1 / r₄
    let S := k1 + k2 + k3 + k4
    let T := k1 ^ 2 + k2 ^ 2 + k3 ^ 2 + k4 ^ 2
    let κ := (S + ε * √(3 * S ^ 2 - 6 * T)) / 2
    κ ≠ 0 → ∃ x : E3, ∃ ρ : ℝ, ρ = 1 / κ ∧
      dist x c₁ ^ 2 = (ρ + r₁) ^ 2 ∧ dist x c₂ ^ 2 = (ρ + r₂) ^ 2 ∧
      dist x c₃ ^ 2 = (ρ + r₃) ^ 2 ∧ dist x c₄ ^ 2 = (ρ + r₄) ^ 2

-- descartes_degenerate.lean:581
theorem no_enclosing_soddy {R a b ρ : ℝ} {ca cb c₄ : ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hA : dist 0 ca = R - a) (hB : dist 0 cb = R - b)
    (hAB : dist ca cb = a + b) (hbig : dist c₄ 0 ≤ ρ - R)
    (h4a : dist c₄ ca = ρ - a) (h4b : dist c₄ cb = ρ - b) :
    c₄ = 0 ∧ ρ = R
```

### What the cited external completion theorem says (finding 5)

```lean
theorem cmp_exists_unique_completion {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ)
    (hM : Mᵀ * descartesQ n * M = curvatureCenterTarget n)
    (hb : ∃ i, M i (Sum.inl 0) ≠ 0) :
    ∃! W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ,
      Wᵀ * descartesQ n * W = augmentedTarget n ∧
      (∀ i, W i (Sum.inl 1) = M i (Sum.inl 0)) ∧
      ∀ i k, W i (Sum.inr k) = M i (Sum.inr k)
```

Both matrices have `n+2` rows. The missing object is a column, not the last row/sphere. The paper/scout's inference from the theorem's name is not a valid statement correspondence. The external `tangent_family_two_hyperplanes` concludes `¬(curvature (s i)=0 ∧ curvature (s j)=0 ∧ curvature (s k)=0)` for three distinct indices. These external sources were read, not compiled by this reviewer.

## Battery audit: all survivors and all unused hypotheses

The counts in the final table reproduce exactly:

| Development | Targets | Mutants | Rejected | Timeout subset | Survivors | Certified | Unresolved | Statement-invalid | Unused / ablation jobs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| quad | 118 | 273 | 272 | 0 | 1 | 35 | 80 | 3 | 1 / 132 |
| arbelos | 115 | 321 | 317 | 5 | 4 | 77 | 37 | 1 | 1 / 198 |
| circles | 110 | 298 | 292 | 7 | 6 | 47 | 63 | 0 | 6 / 149 |
| inversion | 87 | 272 | 268 | 0 | 4 | 55 | 32 | 0 | 1 / 257 |

All four contradiction probes report zero contradictions found, not a proof of universal consistency. All four Layer-8b link counts are zero. **No finding against the final satisfiability paragraph's separation of hand classification from automatic certification:** 35/118, 77/115, 47/110, 55/87 and the unresolved/invalid splits agree with the reports. The historical 64-item quad classification is supported by `FUSS_AND_FLAGS.md` plus `FUSS_INTEGRATE.md`: 20+18 hypothesis-free items, 10+16 witnessed items. It is not final-run certification and the paper correctly says so.

| Development / declaration | Mutant identifier | Actual reason it survives |
|---|---|---|
| quad `l14w_fuss` | `lit0->1@185` | Strengthens `0<r` to `1<r`; the chosen `r=24/7` satisfies both. |
| arbelos `twin_left_exists` | `lit2->3@53` | Weakens the general theorem's `<2a` to `<3a`, with `a>0`. This is a main existence theorem, not an L14 concrete example. |
| arbelos `l14w_twin` | `lit3->4@12` | Changes only the first projected real-coordinate comparison from `4/3<2` to `4/4<2`; subsequent circle terms are unchanged. |
| arbelos `l14w_twin` | `lit4->5@8` | The first comparison becomes `5/3<2`, still true. |
| arbelos `l14w_twin` | `lit2->3@15` | Changes an imaginary coordinate inside an expression projected with `.center.re`; it cannot affect that conjunct. |
| circles `l14w_radical_center_concurrent` | `lit2->3@114` | Changes one `R₁²` to `R₁³`; the selected `R₁=1` makes them equal. |
| circles `l14w_isOrthogonal_iff` | `lit0->1@34` | Stronger lower bound holds for selected `R₁=3`. |
| circles `l14w_isOrthogonal_iff` | `lit0->1@43` | Stronger lower bound holds for selected `R₂=4`. |
| circles `l14w_johnson_circle` | `lit0->1@81` | Stronger radius bound holds for selected `R=5`; downstream use fails, as the report discloses. |
| circles `l14w_johnson_circle` | `lit2->3@183` | Changes `2 • H` to `3 • H`; selected `H=0`. Own proof compiles, downstream use fails. |
| circles `l14w_steiner_line` | `lit2->3@141` | Changes `2 • O` to `3 • O`; selected `O=0`. |
| inversion `l14w_ptolemy_inequality` | `lit0->1@15` | Closed assertion `3≠0` becomes `3≠1`. |
| inversion `l14w_ptolemy_inequality` | `lit3->4@6` | Closed assertion `3≠0` becomes `4≠0`. |
| inversion `l14w_ptolemy_inequality` | `lit0->1@21` | Closed assertion `(0,4)≠0` becomes `(1,4)≠0`; other occurrences are unchanged. |
| inversion `l14w_apollonian_integral` | `neg1->1@40` | Replaces `(-1)²` by `1²` in one term, an equal value. |

Unused hypotheses, **all nine accounted for**, with no mismatch in the paper's main unused-hypothesis paragraph:

1. Quad: `fuss_opposite (hr : 0 < r)`.
2. Circles: `steiner_alg_AB (_hF1 …), (_hF2 …)`.
3. Circles: `steiner_alg_AC (_hE1 …), (_hE2 …)`.
4. Circles: `steiner_alg_BC (_hD1 …), (_hD2 …)`.
5. Arbelos: `steiner_porism (hs₀ : 0 < s₀.radius)`.
6. Inversion: `bridge_intTangent (h₂ : r₂ < 0)`; its other hypotheses are `(h₁ : 0 < r₁)` and `(h₁₂ : r₁ ≤ -r₂)`, which imply it.

The distinction between proof dependence and logical necessity is correctly stated. The final limitations summary omits the inversion item, but the verification paragraph itself reports it accurately.

Remote report identities checked:

- `jack:~/leancheck/reports/final_quad_20261110_180030.md`
- `jack:~/leancheck/reports/final_circles_20261110_192246.md`
- `john:~/leancheck/reports/final_arbelos_20261110_161255.md`
- `john:~/leancheck/reports/final_inversion_20261110_172039.md`

## Numbers and assurance boundaries

**Reproduced, no finding:** gate-list lengths 133/138/121/84; final actual tamper totals 11/7/9/9; bridge counts 15/11/15/10 in paper table order; 50 L14 restatements; all 83 table anchors; all library per-file sizes and totals; the four tracked-Lean digests; clean-export raw log totals 8718/8716/8714/8713 jobs in quad/arbelos/circles/inversion order. Raw logs show each own-project module as `Built`; dependency replay is explicitly disclosed and not misrepresented as a fully fresh dependency build.

| Development | Library files / lines (including root) | All tracked files (`git ls-files` count) | Tracked `.lean` digest |
|---|---:|---:|---|
| quad | 12 / 1913 | 30 | `8a67f0c8e1894d090bf3140add6c9c01f2b34b943e76c2145af6c24e4f3281a4` |
| arbelos | 10 / 2118 | 19 | `2b43ae51b309604c290213bfaba4d459551116d7ea079a1ab4fd9b6233506264` |
| circles | 8 / 1326 | 15 | `db7c08cac4acaed6c92671b435413c73261032f0a2a3ef07d22af1191d8a759f` |
| inversion | 7 / 1178 | 14 | `ade9a958ceeea8f4951f6db68360f96c2297ab6097a584e5af471e0f282f2243` |

The “files” column is correctly a **library-file** count, not the total repository count. Quad additionally tracks nine old scratch Lean files; those are not built by the library target, as the receipt notes. The digest was recomputed as SHA-256 of the C-sorted lines `sha256  ./relative/path` over tracked `.lean` files, including those tracked scratch files.

**Unverified numerical/provenance claims:** the universal pre-proof “30–40 digits on random configurations” assertion at 208–209 and the particular Fuss counterexample's approximate `0.571`/`0.363` values at 328–330 were found in builder narratives, not independently replayed from a supplied numerical script in this review. The old cross-machine digest prefixes `6ed3d660…` and `9f386b22…` were not independently recomputed for both historical snapshots (the former has an explicit matching receipt in `FUSS_INTEGRATE.md`). Treat these as historical reported measurements, not results reproduced here. The completion-map six-trial values agree with `PaperK/EXTENSION.md`, but its `iterate.py` computation was not replayed. Exact fix for any reproducibility claim covering these figures: identify the numerical driver, input/seed and full raw receipt, or label the figures “reported in the historical run; not independently reproduced.” These limitations are MINOR evidence items, not grounds to reverse the explicitly numerical **refuted** status of the completion-map conjecture.

## Numbered theorem / hypothesis audit

**No missing substantive hypothesis or stronger numbered conclusion found in Theorems 1–25 after applying the paper's standing conventions.** In particular, convexity, cyclicity, side-line/same-side incircle data, the plane `Fact`, Pappus non-backtracking and upward start, positive Steiner inner radius/strict nesting, Johnson affine independence, Simson non-collinearity/distinctness, inversion nonzero points/radius, Peaucellier `A≠B` and (where needed) `P≠Q`, signed-radius nonzeroness, and Vieta's distinct-root hypothesis are all present in the relevant prose. This does **not** extend to the unnumbered completion claims; findings 1–6 apply there.

Below are quoted signature excerpts from the pinned sources, one or more for each numbered theorem. Line wrapping is adjusted; omitted companion signatures are identified by name/anchor, not silently treated as stronger conclusions. The section-variable contexts are important:

```lean
-- Quadrilaterals/Main.lean and Fuss.lean:
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]
-- CircleSystems and general Inversion:
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
-- Coordinate statements additionally take b : OrthonormalBasis (Fin 2) ℝ V.
-- Arbelos uses Sphere ℂ; plane Peaucellier/Descartes use ℂ.
```

### Theorems 1–8: quadrilaterals

```lean
-- 1, Main:17
theorem bretschneider {A B C D : P} (hconv : ConvexQuad A B C D) :
  quadArea A B C D ^ 2 =
    (semiperimeter A B C D - dist A B) * (semiperimeter A B C D - dist B C) *
    (semiperimeter A B C D - dist C D) * (semiperimeter A B C D - dist D A) -
    dist A B * dist B C * dist C D * dist D A *
      Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2
-- 2, Main:66
theorem brahmagupta {A B C D : P} (hconv : ConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set P)) :
  quadArea A B C D = √((semiperimeter A B C D - dist A B) *
    (semiperimeter A B C D - dist B C) * (semiperimeter A B C D - dist C D) *
    (semiperimeter A B C D - dist D A))
-- 3, Main:130,194
theorem pitot {A B C D : P} (hconv : ConvexQuad A B C D)
    (htan : Tangential A B C D) : dist A B + dist C D = dist B C + dist D A
theorem pitot_converse {A B C D : P} (hconv : ConvexQuad A B C D)
    (h : dist A B + dist C D = dist B C + dist D A) : Tangential A B C D
-- 4, Main:269 (the elaborated type does retain the plane Fact; checked with #check)
theorem euler_quadrilateral (A B C D : P) :
  dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
    dist A C ^ 2 + dist B D ^ 2 + 4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2
-- 5, Main:277
theorem ptolemy_second {A B C D : P} (hconv : ConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set P)) :
  dist A C / dist B D = (dist A B * dist A D + dist C B * dist C D) /
    (dist B A * dist B C + dist D A * dist D C)
-- 6, Main:334
theorem van_aubel (o : Orientation ℝ V (Fin 2)) (A B C D : P) :
  dist (squareCenter o A B C D A B) (squareCenter o A B C D C D) =
    dist (squareCenter o A B C D B C) (squareCenter o A B C D D A) ∧
  ⟪squareCenter o A B C D C D -ᵥ squareCenter o A B C D A B,
    squareCenter o A B C D D A -ᵥ squareCenter o A B C D B C⟫ = 0
-- 7, Main:359
theorem newton_line {A B C D I : P} {r : ℝ} (hconv : ConvexQuad A B C D)
    (hI : IsIncircle A B C D I r) :
  Collinear ℝ ({midpoint ℝ A C, midpoint ℝ B D, I} : Set P)
-- 8, Fuss:22
theorem fuss {A B C D O I : P} {R r : ℝ} (hconv : ConvexQuad A B C D)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hD : dist D O = R) (hI : IsIncircle A B C D I r) :
  1 / (R - dist O I) ^ 2 + 1 / (R + dist O I) ^ 2 = 1 / r ^ 2
```

The “perpendicular” assertion in Theorem 6 is a zero inner product, including zero joining vectors. As the theorem allows arbitrary four points, degenerate squares/segments must be read in this algebraic sense, not as two necessarily defined perpendicular lines. The supplied formula and setting make that interpretation available; I have not counted this as a separate defect.

### Theorems 9–14: arbelos

```lean
-- 9, Twin:14,46 (right counterparts at 30,70 reverse the side condition)
theorem twin_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : s.center.re < 2 * a) (hperp : s.IsTangent (perpC a b))
    (hbig : s.IsIntTangent (bigS a b)) (hsmall : (leftS a b).IsExtTangent s) :
  s.radius = a * b / (a + b)
theorem twin_left_exists {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
  ∃ s : Sphere ℂ, 0 < s.center.im ∧ s.center.re < 2 * a ∧
    s.IsTangent (perpC a b) ∧ s.IsIntTangent (bigS a b) ∧ (leftS a b).IsExtTangent s
-- 10, Area:125
theorem arbelos_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (D : ℂ)
    (hD : D ∈ bigS a b) (hDperp : D ∈ perpC a b) :
  volume (arbelosRegion a b) =
    volume (Metric.ball (midpoint ℝ (ptC a b) D) (dist (ptC a b) D / 2))
-- 11, Pappus:173,264,298
theorem pappus_chain {a b : ℝ} (n : ℕ) :
  (pappusCircle a b n).center.im = n * (2 * (pappusCircle a b n).radius)
theorem eq_famCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (s : Sphere ℂ) (hs : 0 < s.radius) (hbig : s.IsIntTangent (bigS a b))
    (hleft : (leftS a b).IsExtTangent s) :
  s = famCircle a b (s.center.im / (2 * s.radius))
theorem pappus_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℕ → Sphere ℂ)
    (h0 : c 0 = rightS a b) (hpos : ∀ n, 0 < (c n).radius)
    (hbig : ∀ n, (c n).IsIntTangent (bigS a b))
    (hleft : ∀ n, (leftS a b).IsExtTangent (c n))
    (hsucc : ∀ n, (c n).IsExtTangent (c (n + 1)))
    (hne : ∀ n, c (n + 2) ≠ c n) (hup : 0 < (c 1).center.im) (n : ℕ) :
  c n = pappusCircle a b n
-- 12, Pappus:190,221,254
theorem inversion_bigS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
  inversion (ptA a b) (invRadius a b) '' ((bigS a b : Set ℂ) \ {ptA a b}) = vline (2 * a)
theorem inversion_leftS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
  inversion (ptA a b) (invRadius a b) '' ((leftS a b : Set ℂ) \ {ptA a b}) =
    vline (2 * (a + b))
theorem inversion_pappusCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
  inversion (ptA a b) (invRadius a b) '' (pappusCircle a b n : Set ℂ) =
    Metric.sphere (⟨2 * a + b, 2 * n * b⟩ : ℂ) b
-- 13, Bankoff:131, now exposing the centre
theorem bankoff_exists {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s₀)
    (hright : (rightS a b).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (leftS a b).IsExtTangentAt s₀ T₁)
    (hT₂ : (rightS a b).IsExtTangentAt s₀ T₂) :
  ∃ s : Sphere ℂ, ptC a b ∈ s ∧ T₁ ∈ s ∧ T₂ ∈ s ∧
    s.radius = a * b / (a + b) ∧ s.center = ⟨2 * a, a * b / (a + b)⟩
-- 14, Steiner:305
theorem steiner_porism (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius)
    (n : ℕ) (c : ZMod n → Sphere ℂ) (hchain : IsSteinerChain S₁ S₂ n c)
    (s₀ : Sphere ℂ) (hs₀ : 0 < s₀.radius)
    (h₁' : S₁.IsExtTangent s₀) (h₂' : s₀.IsIntTangent S₂) :
  ∃ d : ZMod n → Sphere ℂ, IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀
-- 14, headline disjoint form, Steiner:522
theorem steiner_porism_disjoint (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius)
    (n : ℕ) (c : ZMod n → Sphere ℂ) (hchain : IsDisjointSteinerChain S₁ S₂ n c)
    (s₀ : Sphere ℂ) (h₁' : S₁.IsExtTangent s₀) (h₂' : s₀.IsIntTangent S₂) :
  ∃ d : ZMod n → Sphere ℂ, IsDisjointSteinerChain S₁ S₂ n d ∧ d 0 = s₀
```

Also checked Theorem 11's `pappusCircle_zero`, three tangencies and `incircleChain_spec`; Theorem 13's `incircle_eq` and universal-radius `bankoff`; and Theorem 14's simple/strong/concentric variants and inversion-support signatures against all their table anchors. No additional hypothesis is concealed by those bundled prose statements.

### Theorems 15–19: circle systems

```lean
-- 15, PowerOfPoint:101,136
theorem radicalAxis_eq_mk' {O₁ O₂ : V} (R₁ R₂ : ℝ) (h : O₁ ≠ O₂) :
  radicalAxis O₁ R₁ O₂ R₂ =
    (AffineSubspace.mk' (radBase O₁ R₁ O₂ R₂) (ℝ ∙ (O₁ - O₂))ᗮ : Set V)
theorem radical_center_concurrent [Fact (finrank ℝ V = 2)]
    {O₁ O₂ O₃ : V} (R₁ R₂ R₃ : ℝ) (hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V)) :
  ∃! X : V, X ∈ radicalAxis O₁ R₁ O₂ R₂ ∧ X ∈ radicalAxis O₂ R₂ O₃ R₃ ∧
    X ∈ radicalAxis O₃ R₃ O₁ R₁
-- 16, Coaxal:40,105; pencil_radicalAxis:83 additionally takes hst : s ≠ t
theorem pencilPow_eq_powPt (O₁ O₂ : V) (R₁ R₂ t : ℝ) (P : V) :
  pencilPow O₁ R₁ O₂ R₂ t P =
    dist P (pencilCenter O₁ O₂ t) ^ 2 - pencilRadSq O₁ R₁ O₂ R₂ t
theorem isOrthogonal_iff [Fact (finrank ℝ V = 2)] {O₁ O₂ : V} {R₁ R₂ : ℝ}
    (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
  IsOrthogonal O₁ R₁ O₂ R₂ ↔ powPt O₁ O₂ R₂ = R₁ ^ 2
-- 17, Johnson:42,78; H O₁ O₂ O₃ : V, R : ℝ are section variables
theorem johnson_circle (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R)
    (h₃ : dist H O₃ = R) :
  dist (O₂ + O₃ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R ∧
  dist (O₃ + O₁ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R ∧
  dist (O₁ + O₂ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R
theorem johnson_orthocenter_eq [Fact (finrank ℝ V = 2)]
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R)
    (hind : AffineIndependent ℝ ![O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H]) :
  (⟨_, hind⟩ : Affine.Triangle ℝ V).circumcenter = O₁ + O₂ + O₃ - (2 : ℝ) • H ∧
  Affine.Triangle.orthocenter (⟨_, hind⟩ : Affine.Triangle ℝ V) = H
-- 18, SimsonSteiner:158,187; b is a Fin 2 orthonormal basis
theorem simson_det_eq_circumcircle_power (hA : dist A O = R)
    (hB : dist B O = R) (hC : dist C O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
  4 * R ^ 2 * cross b
    ((orthogonalProjection line[ℝ, C, A] P : V) -
      (orthogonalProjection line[ℝ, B, C] P : V))
    ((orthogonalProjection line[ℝ, A, B] P : V) -
      (orthogonalProjection line[ℝ, B, C] P : V)) =
    -cross b (B - A) (C - A) * powPt P O R
theorem simson_wallace [Fact (finrank ℝ V = 2)] (hA : dist A O = R)
    (hB : dist B O = R) (hC : dist C O = R)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set V)) :
  Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] P : V),
    (orthogonalProjection line[ℝ, C, A] P : V),
    (orthogonalProjection line[ℝ, A, B] P : V)} : Set V) ↔ dist P O = R
-- 19, SimsonSteiner:211,250
theorem steiner_line [Fact (finrank ℝ V = 2)] (hA : dist A O = R)
    (hB : dist B O = R) (hC : dist C O = R) (hP : dist P O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
  Collinear ℝ ({A + B + C - (2 : ℝ) • O, reflection line[ℝ, B, C] P,
    reflection line[ℝ, C, A] P, reflection line[ℝ, A, B] P} : Set V)
theorem steiner_line_orthocenter [Fact (finrank ℝ V = 2)]
    (t : Affine.Triangle ℝ V) {P : V} (hP : dist P t.circumcenter = t.circumradius) :
  Collinear ℝ ({t.orthocenter, reflection line[ℝ, t.points 1, t.points 2] P,
    reflection line[ℝ, t.points 2, t.points 0] P,
    reflection line[ℝ, t.points 0, t.points 1] P} : Set V)
```

Theorem 17 uses “orthocentre” initially to mean the three perpendicularity identities, then separately identifies the Mathlib triangle orthocentre under affine independence. This qualification is appropriate. Its membership/reflection/congruence companion signatures agree with the explicit-point interpretation. Theorem 16 carefully permits negative squared radii rather than asserting the existence of a real positive-radius circle for every pencil parameter.

### Theorems 20–25: inversion

```lean
-- 20, Basic:28,42,50,65,93
theorem invPt_eq_inversion (R : ℝ) (P : V) :
  invPt R P = EuclideanGeometry.inversion 0 R P
theorem norm_mul_norm_invPt (R : ℝ) {P : V} (hP : P ≠ 0) :
  ‖P‖ * ‖invPt R P‖ = R ^ 2
theorem invPt_invPt {R : ℝ} (hR : R ≠ 0) (P : V) : invPt R (invPt R P) = P
theorem dist_sq_invPt (R : ℝ) {P Q : V} (hP : P ≠ 0) (hQ : Q ≠ 0) :
  dist (invPt R P) (invPt R Q) ^ 2 = R ^ 4 * dist P Q ^ 2 / (‖P‖ ^ 2 * ‖Q‖ ^ 2)
theorem invPt_image_circle {R : ℝ} (hR : R ≠ 0) (C : V) :
  invPt R '' {P | ‖P - C‖ = ‖C‖ ∧ P ≠ 0} = {Y | inner ℝ Y C = R ^ 2 / 2}
-- 21, PtolemyInversion:27,40,59
theorem ptolemy_iff_dist_add_dist_invPt {R : ℝ} (hR : R ≠ 0)
    {P Q S : V} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0) :
  dist (invPt R P) (invPt R Q) + dist (invPt R Q) (invPt R S) =
    dist (invPt R P) (invPt R S) ↔
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖
theorem ptolemy_inequality {P Q S : V} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0) :
  dist P S * ‖Q‖ ≤ dist P Q * ‖S‖ + dist Q S * ‖P‖
theorem collinear_iff_dist_boundary (X Y Z : V) :
  Collinear ℝ ({X, Y, Z} : Set V) ↔
    dist X Y + dist Y Z = dist X Z ∨ dist Y Z + dist Z X = dist Y X ∨
    dist Z X + dist X Y = dist Z Y
-- 22, Peaucellier:129; section variables a b : ℝ, A B P Q : ℂ
theorem peaucellier_classic {R : ℝ} (hR : R ≠ 0) (hab : b ^ 2 - a ^ 2 = R ^ 2)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) :
  Q = invPt R P ∧ ‖P‖ * ‖Q‖ = R ^ 2
-- 23, Descartes:76
theorem descartes {c₁ c₂ c₃ c₄ : ℂ} {r₁ r₂ r₃ r₄ : ℝ}
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0)
    (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2)
    (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2)
    (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2)
    (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2)
    (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2)
    (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2) :
  (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄) ^ 2 =
    2 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2)
-- 24, Descartes:111
theorem soddy {c₁ c₂ c₃ c₄ c₅ : EuclideanSpace ℝ (Fin 3)} {r₁ r₂ r₃ r₄ r₅ : ℝ}
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0) (h₅ : r₅ ≠ 0)
    (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2)
    (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2)
    (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2)
    (h₁₅ : dist c₁ c₅ ^ 2 = (r₁ + r₅) ^ 2)
    (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2)
    (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2)
    (h₂₅ : dist c₂ c₅ ^ 2 = (r₂ + r₅) ^ 2)
    (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2)
    (h₃₅ : dist c₃ c₅ ^ 2 = (r₃ + r₅) ^ 2)
    (h₄₅ : dist c₄ c₅ ^ 2 = (r₄ + r₅) ^ 2) :
  (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄ + 1 / r₅) ^ 2 =
    3 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2 + (1 / r₅) ^ 2)
-- 25, Descartes:172,196,256
theorem descartes_solve (k₁ k₂ k₃ k₄ : ℝ) :
  descartesForm k₁ k₂ k₃ k₄ = 0 ↔ 0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁ ∧
    (k₄ = k₁ + k₂ + k₃ + 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
     k₄ = k₁ + k₂ + k₃ - 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁))
theorem descartes_vieta {k₁ k₂ k₃ kp km : ℝ}
    (hp : descartesForm k₁ k₂ k₃ kp = 0) (hm : descartesForm k₁ k₂ k₃ km = 0)
    (hne : kp ≠ km) :
  kp + km = 2 * (k₁ + k₂ + k₃) ∧
    kp * km = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2
theorem isDescartes_foldr (l : List (Fin 4)) {q : ℤ × ℤ × ℤ × ℤ} (h : IsDescartes q) :
  IsDescartes (l.foldr apolloMove q)
```

Also checked Theorem 21's complex concyclic disjunction, Theorem 22's sum/inner-product/collinearity and both straight-line variants, and Theorem 25's reflection/integer single-move lemmas. Their extra assumptions match the prose. Theorem 20 explicitly discloses the empty-set `C=0` case; no vacuity finding there.

## Category conclusions

1. **Statement versus code:** numbered statements match in their stated scope; substantial failures are in §6.1 and the verification narrative, documented above with signatures and counterexamples.
2. **Hypotheses:** numbered-theorem hypotheses are accounted for; §6.1 misses nonzero root curvature and misstates the resting-sphere/enclosing-member settings.
3. **Numbers:** final main tables and digests reproduce; historical/final scope mixing, supplementary theorem-count convention, omitted witness coverage and unavailable archive links need correction. Unreplayed historical/numerical figures are explicitly labelled unverified above.
4. **Prior art:** the main reproof disclosures and search-gap caveats are substantially sound. No affirmative “first 3D formalisation” or “beyond the plane” novelty claim is made; the occurrence of the latter wording is a denial, not a violation. The subsection's specific claims about what the cited general theorems say are nevertheless wrong (finding 5). Do not rely on the scout's mistaken matrix-completion paraphrase.
5. **Layers 10/13/14/15:** bridge totals and final Bankoff source fix are real; the area/measure gap has a concrete supplementary proof (`L15_compare_ext.lean`, SHA-256 `0a45507ecfb7d2db718b2a3fb341d50c54617a83499fd7671bf748ae6da7c9cf`). That bridge is for two-dimensional vector spaces, not a general affine torsor, and is not part of the pinned quad library. Blind-comparison completeness, witness coverage, and residual I5c scope must be reported honestly.
6. **Over-claiming:** the highest-priority fixes are the false collinear-feet nonexistence, rational-link nonexistence, unqualified “both spheres,” and overstated supplementary/Bankoff verification. The completion-map fixed-point conjecture stays **numerically refuted**, correctly separated from a published theorem and from machine-checked results; do not turn that negative result into a success claim.
