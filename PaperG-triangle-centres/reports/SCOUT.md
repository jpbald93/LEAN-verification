# Paper G prior-art scout: "Triangle centres and their lines"

- **Swept:** 2026-10-24, inline, single session (no sub-agent), ~35 min. Read-only.
- **Method:** same classes as `prior-art/CANDIDATES.md`: (a) complete proof, which defeats novelty; (b) `sorry`/assumed statement; (c) benchmark entry. **Only Lean (a) hits disqualify.** "Earliest public" = first GitHub commit date (UTC) of the file, or PR creation date.
- **Sources and what was run:**
  - **S1 Mathlib** `0df444a3` (2026-08-21), local `grep -ril` over `Mathlib/ Archive/`.
  - **S1b mathlib4 PRs**: `gh search prs`.
  - **S1c GitHub code**: `gh api search/code … language:Lean`, plus per-repo searches.
  - **lean-genius**: sparse clone at `470a7df` (2026-10-22), `proofs/Proofs` grepped.
  - **atlas-lean**: `facebookresearch/atlas-lean` at `6e4ea7a5` (2026-10-24).
  - **ProofAtlas**: `sitemap.xml` (752 URLs, fetched 2026-10-24); URL list grepped.
  - **FormalBook, Compfiles, ShadowBench, LeanGeo**: per-repo code search.
  - **Other systems**: GeoCoq and HighSchoolGeometry (local clones), HOL Light and Mizar MML (local), and the AFP via `search/code repo:isabelle-prover/mirror-afp-devel`. GitHub `language:Coq` / `language:Isabelle` code search.
  - **Web search was unavailable** in this session; it returned no live results, so GitHub/API searches stand in for it. ProofAtlas was checked through its sitemap only, not by a full HTML crawl. Both are gaps; re-run before submission.
- **Queries (case-insensitive):** `nagel`, `nagelPoint`, `nagel_point`, `nagel line`, `gergonne`, `gergonnePoint`, `symmedian`, `symmedian_point`, `lemoine`, `brocard`, `brocard_point`, `spieker`, `longchamps`, `isogonal`, `droz`, `fuhrmann`, `lamoen`, `euler_line`, `EulerLine`, `Euler line`, `incenter`, `inradius circumradius`, `excenter touchpoint`, `centroid incenter collinear`.
- **Numerical sanity check** (random triangle, `/tmp/pg_chk/c.py`). These all hold: GN = 2·IG with N−G = 2(G−I); Spieker centre = midpoint(I, Na); Ge ∈ AD (incircle contact point); Na ∈ AD′ (A-excircle contact point); K = centroid of its own pedal triangle; Brocard barycentrics and the cot ω identity.

## What Mathlib already has (pinned `0df444a3` + open PRs)

- **Euler line (O, G, H) is DONE in Mathlib.**
  - `Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter` (`Geometry/Euclidean/MongePoint.lean:82`) states that the Monge point is O + ((n+1)/(n−1))·(G − O). Per its docstring, O, G and M are collinear with OG : GM = (n−1) : 2.
  - For triangles: `Affine.Triangle.orthocenter_eq_mongePoint` (:371) and `orthocenter_eq_smul_vsub_vadd_circumcenter` (:380) give H = O + 3(G − O).
  - The nine-point centre lies on the Euler line: `ninePointCircle_center` (`NinePointCircle.lean:56`) and `ninePointCircle_center_mem_affineSpan`. PR #34420 was merged 2026-01-25, and #44218 (distance from vertex to nine-point centre) was merged 2026-09-26.
  - **There is no explicit `Collinear ℝ {O, G, H}` lemma**, but it is a one-line corollary. **Skip.**
- **Euler OI² = R(R−2r) is DONE in Lean.**
  - mathlib4 **PR #44230** (wwylele, open, created 2026-09-26, CI 11/11 green, 0 `sorry`): `Affine.Triangle.dist_incenter_circumcenter_sq` plus excentre versions and Euler's inequality r ≤ R/2.
  - Also atlas-lean `MathlibExt/Geometry/Euclidean/EulerOI.lean` (`euler_oi`, 0 `sorry`, present at 2026-10-12; that clone is shallow, so the date is an upper bound).
  - GeoCoq/HSG have the Euler line, not OI. **Skip.**
- **Infrastructure that already exists** (good for Group A):
  - `Affine.Simplex.incenter`, `excenter`, `inradius`, `exradius`, `insphere`, `exsphere`, and **`touchpoint signs i`** (`Incenter.lean:779`, the orthogonal projection of the (ex)centre onto a face).
  - `touchpointWeights`, `Simplex.medial`, `faceOppositeCentroid`, `centroid`.
  - Ceva (`LinearAlgebra/AffineSpace/Ceva.lean`).
  - PR #31981 (open): tangent lemmas.
- **No Mathlib or PR hits** for nagel, gergonne, symmedian, lemoine, brocard, spieker, longchamps, isogonal, droz, fuhrmann or lamoen.

## Table

Abbreviations: **Na** = Nagel point, **Ge** = Gergonne point, **Sp** = Spieker centre, **K** = symmedian point, **Ω** = Brocard point. Tractability means "by coordinate or complex certificate".

| Theorem | Lean status | Other systems | Tractability | Rec. |
|---|---|---|---|---|
| Euler line O,G,H (+N) | **Done**: Mathlib `mongePoint_eq_smul_vsub_vadd_circumcenter`, `orthocenter_eq_smul_vsub_vadd_circumcenter` (pinned 0df444a3) | GeoCoq `Highschool/Euler_line.v` (`Euler_line`), HSG `droite_Euler.v` | — | **N** |
| Euler OI² = R(R−2r) | **Done (a)**: mathlib4 PR #44230 (2026-09-26, open, green); atlas-lean `EulerOI.lean` (≤2026-10-12) | — | — | **N** |
| **Nagel line**: I, G, Na collinear, Na − G = 2(G − I) | **None found.** Partial: lean-genius `CevasTheoremOQ04OQ04OQ02.lean` (first commit **2026-06-25T14:03Z**, 0 `sorry`) *defines* Na and I by Ravi-barycentric formulas in an abstract ℝ-module and proves only "lies on the cevian". There, Na is not tied to excircle contacts and I is not tied to Mathlib's `incenter`. **No line or ratio statement.** | none found (AFP/GeoCoq/HSG/HOL Light/Mizar: 0) | **High.** Barycentric identity once Na and I have weight forms. The real work is bridging `touchpoint`/`incenter` to weights. | **Y** |
| **Nagel point concurrence** (A–excontact cevians concur) | **No Euclidean proof.** Same lean-genius file: an algebraic "barycentric point lies on cevian to *defined* foot" (class: partial; the foot is defined by a formula, not as an excircle tangency point). | none found | **High** (Ceva with tangent lengths s−b, s−c) | **Y** |
| **Gergonne point concurrence** (cevians to incircle contacts concur) | Same as Nagel concurrence: only the lean-genius algebraic partial (2026-06-25). Mathlib has `touchpoint` but no concurrence. | none found | **High** | **Y** |
| **Spieker centre**: incentre of medial triangle = midpoint(I, Na), hence on the Nagel line | **None found** (0 hits anywhere) | none found | **High** given Group A defs (medial triangle sides = a/2 …) | **Y** |
| **Symmedian point K**: reflections of medians in bisectors concur (K = (a²:b²:c²)) | **None found** (Lean code search `symmedian` 0 hits outside lean-genius docstring comments in `CevasTheorem*.lean`, which have no symmedian theorem) | none found | **Med–High** (angle equalities need cos/dot-product certificate, fine) | **Y** |
| **K is centroid of its pedal triangle** | **None found** | none found | **High** (feet of perpendiculars are rational in coordinates; linear identity) | **Y** |
| **Brocard point**: ∃Ω with ∠ΩAB = ∠ΩBC = ∠ΩCA = ω, cot ω = cot A + cot B + cot C = (a²+b²+c²)/(4Δ) | **None found** (Lean `brocard` hits are only Brocard's *number-theory* problem: formal-conjectures, atlas-lean `BrocardRamanujan*Wanted`, ProofAtlas `collaboration/brocard-problem`) | none found (AFP 0, Coq hits are number theory) | **Med** (angle equality via dot/cross ratios; cot identity is a polynomial certificate with Δ = cross/2) | **Y** |
| Lemoine circles (1st/2nd) | None found | none found | Med (concyclicity of 6 points, heavy) | N (backup) |
| de Longchamps point (L = 2O − H; radical centre of power circles) | None found | none found | High but thin (one-liner off Mathlib's Euler line) | N (could be a corollary) |
| Isogonal conjugation basics | None found | none found | Med–Low (needs a conjugate def, degeneracy on circumcircle) | N |
| Droz-Farny line | None found | none found | Med (two arbitrary perpendicular lines; 3 midpoints collinear, degree high) | N (backup for B) |
| Fuhrmann circle | None found | none found | Low–Med (arc midpoints → sign/branch choices) | N |
| van Lamoen circle | None found | none found | Low (6 circumcentres concyclic; big polynomials) | N |
| Feuerbach, Morley, Napoleon, Kiepert, Newton, Poncelet, Simson, Lester | skipped per brief (done elsewhere; Feuerbach also in mathlib4 PR #44236, open, 2026-09-26) | — | — | N |

## RECOMMENDED SET (5 theorems, two groups)

Common setting: `V P` with `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]`, `[Fact (finrank ℝ V = 2)]` where needed, and `t : Affine.Triangle ℝ P`. Write `A = t.points 0`, `B = t.points 1`, `C = t.points 2`; `a = dist B C`, `b = dist C A`, `c = dist A B`; `s = (a+b+c)/2`; and `G = t.centroid`. Use Mathlib's `t.incenter`, `t.excenter {i}`, and `t.touchpoint signs i`. **Hypotheses:** only `t` (affine independence is built in). There are no other side conditions, because s−a, s−b, s−c > 0 follows from the triangle's nondegeneracy.

### Group A (machine 1): the Nagel line family (shared defs: contact points, Na, Ge, Sp)

New definitions:
- `nagelPoint t := affineCombination (s−a, s−b, s−c)/s`
- `gergonnePoint t := affineCombination with weights ∝ (1/(s−a), 1/(s−b), 1/(s−c))`

The brief must also prove the characterisations A1/A2. Each point is defined by weights, and the theorem shows it is the concurrence point of the geometric cevians.

- **A1. Gergonne point.** For each i, `t.gergonnePoint ∈ line[ℝ, t.points i, t.touchpoint ∅ i]`. Consequently the three cevians from each vertex to the incircle contact point on the opposite side are concurrent. (Optionally also `t.touchpoint ∅ 0 = lineMap B C ((s−b)/a)`.)
- **A2. Nagel point.** For each i, `t.nagelPoint ∈ line[ℝ, t.points i, t.touchpoint {i} i]`. This is the cevian from vertex i to the contact point of the i-excircle with the opposite side, so the three cevians are concurrent.
- **A3. Nagel line + Spieker centre.**
  - (i) `Collinear ℝ {t.incenter, G, t.nagelPoint}` and `t.nagelPoint -ᵥ G = (2:ℝ) • (G -ᵥ t.incenter)`, i.e. GN = 2·IG with G between I and Na.
  - (ii) `t.medial.incenter = midpoint ℝ t.incenter t.nagelPoint`. So the Spieker centre lies on the Nagel line, and `G -ᵥ t.medial.incenter = (1/2:ℝ) • (t.incenter -ᵥ G)` (medial is the homothety of ratio −1/2 about G).
  - Here `t.medial` is Mathlib's `Affine.Simplex.medial`; check its vertex indexing (face-opposite centroids).

### Group B (machine 2): symmedian and Brocard (shared defs: K, Ω, side-squared barycentrics, cot via dot/area)

New definitions:
- `symmedianPoint t := affineCombination with weights ∝ (a², b², c²)`
- `brocardPoint₁ t := affineCombination with weights ∝ (1/b², 1/c², 1/a²)` on (A, B, C)
- `area t` (= `EuclideanGeometry` half cross-product, or via Mathlib `t.volume` once PR #44230 lands)

The angle `∠` below is the unoriented `EuclideanGeometry.angle`.

- **B1. Symmedians concur (Lemoine point).** For each vertex, e.g. at A: `∠ B A K = ∠ (midpoint ℝ B C) A C` and `∠ C A K = ∠ (midpoint ℝ B C) A B`, and likewise at B and C, with K = `t.symmedianPoint`, which lies in the interior of t. So the reflection of each median in the corresponding angle bisector passes through K.
- **B2. K is the centroid of its pedal triangle.** Let `F i := (t.faceOpposite i).orthogonalProjectionSpan K` (foot on each side line). Then `Finset.univ.centroid ℝ F = K`. An optional converse: any point equal to the centroid of its pedal triangle is K, which is the unique solution of a linear system.
- **B3. Brocard point and angle.** Let Ω = `t.brocardPoint₁`.
  - (i) `∠ Ω A B = ∠ Ω B C` and `∠ Ω B C = ∠ Ω C A`.
  - (ii) Let ω be this common angle, and write the vertex angles as `∠ B A C`, `∠ A B C`, `∠ A C B`. Then `Real.cot ω = Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B)`, and also `Real.cot ω = (a²+b²+c²)/(4·area)`.
  - Optionally add the second Brocard point Ω′ (weights ∝ (1/c², 1/a², 1/b²)) with the mirrored angle equalities `∠ Ω′ A C = ∠ Ω′ C B = ∠ Ω′ B A` and the same ω, plus ω ≤ π/6.

**Why this set:** each group shares one definitional bridge.
- **Group A** bridges `touchpoint` (contact) to barycentric weights, using Mathlib's `touchpointWeights`.
- **Group B** bridges side-squared barycentrics to angles via dot products.

After the bridge, every statement is a polynomial or rational identity, which is High/Med for certificates. The only Lean prior art is the lean-genius algebraic partial for Na/Ge cevians (2026-06-25). It works in an abstract module with formula-defined feet, so it is not a Euclidean theorem. **Cite it in the paper and note it as partial.**

**Backups:** Droz-Farny (Group B), de Longchamps as a corollary of Mathlib's Euler line, and the first Lemoine circle.
