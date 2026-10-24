**Result: all four VERIFIED, no blocking defects.** Each repo builds, gates with only the three standard axioms, rejects every tamper case, and passes my own numeric checks. None of the four has an existing complete formal proof in the sources I could reach.

**lester: VERIFIED**
- Statement (`Lester/Basic.lean`):
  ```
  theorem lester (t : Affine.Triangle ℝ ℂ)
      (h01 : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2))
      (h12 : dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0))
      (h20 : dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
      (F₁ F₂ : ℂ) (h₁ : IsFermatOuter … F₁) (h₂ : IsFermatInner … F₂) :
      Concyclic ({ninePointCenter t, t.circumcenter, F₁, F₂} : Set ℂ)
  ```
- **Hypotheses:** scalene only, which is the classical condition. I checked that for an isosceles triangle the four points really are collinear on the symmetry axis, so the exclusion is needed.
  - The Fermat points are defined as the meeting point of the three vertex-to-apex lines; numerically the apexes are on the correct side of each edge.
  - The circumcentre is Mathlib's; the nine-point centre is the midpoint of circumcentre and orthocentre, and the repo proves this equals Mathlib's `ninePointCircle.center`.
  - Nothing is added or strengthened.
- **Numeric:** 2000 random triangles at 50 digits; worst concyclicity residual 1.9e-50, worst concurrency residual 1.6e-50. Negative control (centroid in place of the nine-point centre): 500 of 500 violated.
- **Harness:** gate PASS, 19 declarations, `Lester.lester` uses only `[propext, Classical.choice, Quot.sound]`. Tamper: all 6 cases rejected (sorry, ax2line, evalfake, macro, brokenbridge, wrap).

**thebault3: VERIFIED**
- Statement:
  ```
  theorem sawayama_thebault (A B C D P Q : Pt) (h : AffineIndependent ℝ ![A, B, C])
      (hD : Sbtw ℝ B D C) (hP : IsThebaultCircle A B C D B P h)
      (hQ : IsThebaultCircle A B C D C Q h) :
      Collinear ℝ {P, Q, (tri A B C h).incenter}
  ```
- `IsThebaultCircle … X P` means there is an r > 0 with:
  - distance from P to line AD = r, and distance from P to line BC = r;
  - `dist P O = R - r` (internal tangency to the circumcircle);
  - P strictly on the same side of AD as X, and strictly on the same side of BC as A.
- **Hypotheses:** this matches the classical theorem. "D strictly between B and C" is the standard setting. The incentre is Mathlib's. Numerically each side has exactly one circle meeting these conditions (1989 of 1989 samples), so the definition picks out the intended circle.
- **Numeric:** worst collinearity residual 1.0e-47. Negative control (centroid instead of incentre): 1989 of 1989 violated.
- **Harness:** gate PASS, 12 declarations, standard axioms only. Tamper: all 6 rejected.

**Fivecircles: VERIFIED**
- Statement:
  ```
  theorem fivecircles (A T M : Fin 5 → ℂ) (hA : Injective A) (hT : Injective T) (hM : Injective M)
      (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j) (hTM : ∀ i j, T i ≠ M j)
      (hL : ∀ i, Collinear ℝ {A (i-1), A i, T (i+1), T (i-1)})
      (hC : ∀ i, Concyclic {A (i-1), A i, T i, M (i-1), M i}) :
      Concyclic (Set.range M) ∨ Collinear ℝ (Set.range M)
  ```
- **Hypotheses:** the incidences encode the pentagram correctly. The extra conditions are distinctness only:
  - M points pairwise distinct;
  - no A, T or M point coincides with a point of another family.
  - `hAM` also excludes the tangent-circles case, where the second intersection coincides with A i. That is a mild, legitimate exclusion of degenerate configurations.
- **Conclusion:** "circle or line". The line case is real: I found a non-degenerate pentagram (minimum point separation 0.52) where all five M points are collinear (residual 1e-39). So the disjunction is needed, not a weakening.
- **Numeric:** 1000 random pentagrams; worst residual 5.3e-47, and the generated configurations satisfy the circle hypotheses. Negative control (wrong pair of circles for M 0): 999 of 1000 violated.
- **Harness:** gate PASS, 6 declarations, standard axioms only. Tamper: all 6 rejected.

**Kosnita: VERIFIED (with two justified non-degeneracy hypotheses)**
- Statement:
  ```
  theorem kosnita (A B C O Oa Ob Oc : Plane)
      (hABC : ¬ Collinear ℝ {A, B, C}) (hOA : dist O A = dist O B) (hOC : dist O A = dist O C)
      (hOBC : ¬ Collinear ℝ {O, B, C}) (hOCA : ¬ Collinear ℝ {O, C, A}) (hOAB : ¬ Collinear ℝ {O, A, B})
      (hOa1 : dist Oa O = dist Oa B) (hOa2 : dist Oa O = dist Oa C)
      (hOb1 …) (hOb2 …) (hOc1 …) (hOc2 …)
      (hS : dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2 ≠ 5 * dist O A ^ 2) :
      ∃ P, Collinear ℝ {A, Oa, P} ∧ Collinear ℝ {B, Ob, P} ∧ Collinear ℝ {C, Oc, P}
  ```
- **Not quite the theorem described in your brief.** The brief speaks of six triangles and concyclicity. The Lean file proves the standard Kosnita theorem: with O the circumcentre of ABC and Oa, Ob, Oc the circumcentres of OBC, OCA, OAB, the lines AOa, BOb, COc are concurrent. Circumcentres are given by equidistance, which in the plane is equivalent.
- **Extra hypotheses:**
  - `hOBC`, `hOCA`, `hOAB` exclude right triangles, where Oa does not exist. Necessary.
  - `hS` (AB² + BC² + CA² ≠ 5R²) excludes the case where the Kosnita point is at infinity. I confirmed it numerically on three triangles on that boundary: the three lines are pairwise parallel (determinants about 1e-61) and distinct (separation about 0.18). So the affine conclusion really is false there and the exclusion is needed. This is a weakening only relative to a projective "concurrent at a point at infinity" statement.
- **Numeric:** 2000 triangles; worst residual 4.6e-50. Negative controls: centroid in place of circumcentre 500 of 500 violated; Oa and Ob swapped 500 of 500 violated.
- **Harness:** gate PASS, 11 declarations, standard axioms only. Tamper: all 6 rejected, including dropping `hS`, which then fails to build.

**Step 4 (soundness):** the forbidden-token grep (sorry, admit, axiom, native_decide, #eval, run_cmd, set_option, macro, elab, syntax, notation, infix, prefix, postfix, initialize, import Lean) is clean on all library sources. The only hits are `sorry` in `thebault3/scratch/{br,mr,mf,mr2}.lean`, which the library does not import.

**Step 0 (prior art):** no complete formal proof of any of the four found.
- **Mathlib:** a grep of the pinned checkout (0df444a3) found nothing. On current master (105b9b1c, 2026-10-13), GitHub code search finds only titles in `docs/1000.yaml`: "Lester's theorem" (Q1631749) and "Miquel's theorem" (Q2449984), with no proof attached. Issue/PR search for Lester, Thébault, Sawayama, Kosnita, Miquel five, five circles and Fermat point: no relevant hits.
- **AFP:** https://www.isa-afp.org/entries/Miquel.html is a complete proof, but of Miquel's *pivot* theorem (three circles, August 2026), not the five-circles theorem. Nothing else relevant in the AFP sitemap.
- **Rocq/Coq:** https://github.com/rocq-community/HighSchoolGeometry (`applications_cocyclicite.v:270`, `Theorem Miquel`) is Miquel's four-lines theorem, not five circles. GeoCoq has nothing.
- **Other GitHub Lean/Coq code search:** nothing (only name collisions such as "David Lester" and "Rina Sawayama").
- **HOL Light:** nothing (only an author name, "David Lester", in a comment).
- **Metamath (set.mm):** nothing. **Mizar:** the MML index page and the MizarProject/mml search found nothing.
- **Lean Zulip archive:** a search of the GitHub mirror (leanprover-community/archive) found nothing.
- **Limits of this search:**
  - The WebSearch tool did not work in this session (it returned no results), so all of the above came from direct fetches and the GitHub API.
  - I did not check HOL4 itself: its sparse clone produced no files, so the empty grep there proves nothing.
  - ProofAtlas could not be searched properly: its home page and its "landmark theorems" / "explore" pages contain no mention of these theorems, but the site has no searchable index I could use.
  - Zulip was only checked through that GitHub mirror, not the live site's search.

**DEFECTS:**
- None in the proofs or statements.
- Kosnita: the theorem described in your brief (six triangles, concyclicity) is not what the repo proves; it proves the standard concurrency theorem, with the needed no-right-angle and ≠ 5R² exclusions.
- Process note: the copy at `~/lean/mathlib-master` on john is at the same commit as the pin (0df444a3), not current master.

My scripts are in `/tmp/vdnum` on this machine; the john logs are in `/tmp/vd`.
