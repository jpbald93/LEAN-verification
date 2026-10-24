# Prior-art sweep: machine-checked proofs of complete-quadrilateral theorems

Date of sweep: 2026-10-14. Every source below was searched by this agent directly, with no subagents.

## Headline

**Two of the eight target theorems already have complete machine-checked proofs.**

- **T1, the Newton–Gauss line (midpoints of the three diagonals are collinear).**
  - **HOL Light**, `Complex/grobner_examples.ml`, theorem `GAUSS` ("Gauss's theorem (Chou, example 15)"). Proved by `GEOM_TAC THEN CONV_TAC GROBNER_REAL_ARITH`, which is kernel-checked. It is loaded by `Complex/make.ml`. File last changed 2010-02-13.
  - **Coq/Rocq area-method library**, `examples_2.v`, `Theorem gauss_line`. Proved by `area_method. Qed.` File last changed 2009-08-10.
- **T5, the four-line Miquel theorem (Miquel point of a complete quadrilateral).**
  - **Coq/Rocq HighSchoolGeometry**, `theories/applications_cocyclicite.v:270`, `Theorem Miquel`, ending in `Qed`. This is the **four-line form**, not the triangle pivot theorem (checked below). File last changed 2023-11-26.
  - **Newclid/JGEX** also has `miquel_quadrangle_theorem1/2`, but that is a synthetic-engine proof, not a proof-assistant proof.

**Nothing found for T2, T3, T4, T6, T7 or T8** in any searched source. Mathlib, Lean in general and every Lean repo searched contain **none of T1–T8**.

Control (T9, the triangle Simson line) was FOUND in AFP, HOL Light, lean-genius and Coq, so the search method works.

---

## Exact statements of the hits

### T1: HOL Light `GAUSS`
https://github.com/jrh13/hol-light/blob/master/Complex/grobner_examples.ml (around line 516)
```
let GAUSS = time prove
 (`collinear x a0 a3 /\ collinear x a1 a2 /\
   collinear y a2 a3 /\ collinear y a1 a0 /\
   is_midpoint m1 (a1,a3) /\ is_midpoint m2 (a0,a2) /\ is_midpoint m3 (x,y)
   ==> collinear m1 m2 m3`,
  GEOM_TAC THEN CONV_TAC GROBNER_REAL_ARITH);;
```
- The setting is ℝ×ℝ coordinates. `collinear`, `is_midpoint` etc. are `new_definition`s in that file; they are **definitions, not axioms**, despite the file's comment calling them "axiomatic".
- x = a0a3 ∩ a1a2 and y = a2a3 ∩ a1a0. The three diagonals are a1a3, a0a2 and xy, so this is exactly the Newton–Gauss line.
- No nondegeneracy hypotheses are needed: `collinear` is the determinant condition, so degenerate cases hold trivially.
- **Status: COMPLETE.** It is a kernel theorem produced by a proof-producing Gröbner-basis procedure.

### T1: Coq area-method `gauss_line`
https://github.com/rocq-archive/area-method/blob/master/examples_2.v (line 319)
```
Theorem gauss_line :
 forall A0 A1 A2 A3 X Y M1 M2 M3 : Point,
 inter_ll X A0 A3 A1 A2 -> inter_ll Y A2 A3 A1 A0 ->
 is_midpoint M1 A1 A3 -> is_midpoint M2 A0 A2 -> is_midpoint M3 X Y ->
 S A0 A1 A2 <> 0 -> Col M1 M2 M3.
Proof. area_method. Qed.
```
- **Status: COMPLETE (`Qed`)**, with these caveats:
  - The result is relative to the library's axiomatised field `F` and its Chou–Gao–Zhang area axioms (`chou_gao_zhang_axioms.v`, `field.v`), not to Rocq's real numbers.
  - The library has 3 `Admitted` lemmas in `area_coords_elimination.v`: `elim_py_a_ratio_right`, `elim_signed_area_a_ratio` and `elim_py_a_ratio_middle`. They are only used when there is an `a_ratio` hypothesis, which `gauss_line` does not have. I could not run `Print Assumptions`, because no coqc is installed.
- It is an automated proof (Chou–Gao–Zhang area method, Narboux's Coq implementation).

### T5: HighSchoolGeometry `Miquel`
https://github.com/rocq-community/HighSchoolGeometry/blob/master/theories/applications_cocyclicite.v (line 270)
```
Theorem Miquel : forall A B C D E F M : PO,
 A <> C -> A <> F -> B <> E -> B <> C ->
 alignes A D F -> alignes A E C -> alignes B D E -> alignes B F C ->
 triangle A E D -> triangle A E M -> triangle B D M -> triangle B F M ->
 sont_cocycliques A C F M -> sont_cocycliques A E D M ->
 sont_cocycliques E C B M /\ sont_cocycliques D F B M.
```
- **Why this is the four-line form.** The four lines are ℓ1 = ADF, ℓ2 = AEC, ℓ3 = BDE and ℓ4 = BFC. Their six intersection points are A = ℓ1∩ℓ2, D = ℓ1∩ℓ3, F = ℓ1∩ℓ4, E = ℓ2∩ℓ3, C = ℓ2∩ℓ4 and B = ℓ3∩ℓ4. Dropping one line at a time gives the four triangles AED, ACF, DFB and ECB. The theorem says: if M lies on the circles (ACF) and (AED), then M also lies on (ECB) and (DFB). That is the four-circle concurrence, in conditional form, with some nondegeneracy hypotheses.
- **Status: COMPLETE (`Qed`).** The whole repo has 0 `Admitted` and 0 `admit`. Like the rest of HSG, it rests on the library's axiomatic plane (158 `Axiom` declarations across the repo).
- The same file has `droite_Simson` at line 483, which is the T9 control.

---

## Table: theorem × source

Key: N = NOTHING; FC = FOUND-COMPLETE; FP = FOUND-PARTIAL; U = UNREACHABLE.

| Thm | Mathlib pinned 0df444a3 | Mathlib master ef61520 (+PRs/issues, 100/1000.yaml) | Lean Zulip | AFP / Isabelle | Mizar MML | HOL4 | HOL Light | ProofAtlas | GitHub code search (Lean/Coq/Isabelle) | Metamath | GeoCoq | lean-genius | FormalBook | compfiles / formal-conjectures / LeanEuclid / EG | Coq area-method / HSG / proj.-geom. | Automated, non-kernel (Newclid/AG/JGEX) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 Newton–Gauss | N | N (1000.yaml lists "Newton's theorem (quadrilateral)", i.e. the tangential one, with no decl) | N | N | N | N | **FC** `GAUSS` | N* | **FC** area-method `gauss_line` | N | N | N | N | N | **FC** `gauss_line` | N |
| 2 Orthocentres collinear | N | N | N | N | N | N | N | N* | N | N | N | N | N | N | N | N |
| 3 Bodenmiller (coaxal) | N | N | N | N | N | N | N | N* | N | N | N | N | N | N | N | N |
| 4 Ortho-line ⟂ Gauss line | N | N | N | N | N | N | N | N* | N | N | N | N | N | N | N | N |
| 5 Four-line Miquel | N | N ("Miquel's theorem" and "Pivot theorem" in 1000.yaml have no decl) | N (2024 thread: not in Mathlib) | near-miss: pivot form only (AFP Miquel) | N | N | N | N* | **FC** HSG `Miquel` | N | N | near-miss: pivot only | N | N | **FC** HSG `Miquel` | machine proof (Newclid `miquel_quadrangle_theorem1/2`) |
| 6 Miquel/Steiner circle | N | N | N | N | N | N | N | N* | N | N | N | N | N | N | N | near-miss (Newclid `centers_of_miquels_circles_are_concyclic` is the triangle-pivot case) |
| 7 Quadrilateral Simson line | N | N | N | N | N | N | N | N* | N | N | N | N | N | N | N | N |
| 8 Simson ∥ ortho line | N | N | N | N | N | N | N | N* | N | N | N | N | N | N | N | N |
| 9 Triangle Simson (control) | N | N | N | **FC** AFP Simson | N | N | **FC** `SIMSON` | N* | **FC** | N | N | **FC** | N | N | **FC** HSG `droite_Simson` | Newclid rule r45 |

\* ProofAtlas: partial access only (see the unreachable list). The site search, its index and the sitemap were all grepped.

### Near-misses (wrong theorem, same name)
- **AFP `Miquel`** (2026-08-11, Ramos/Hulak/de Queiroz): `miquel_pivot`, `miquel_concurrent`, `miquel_point_exists`. All three are the **triangle pivot theorem** (points P, Q, R on the side lines of triangle ABC), not the four-line version. COMPLETE (0 sorry/oops). https://isa-afp.org/entries/Miquel.html
- **AFP `Steiner_Line_Theorem`** (2026-10-06): the **triangle** Steiner line. For a point on the circumcircle, its reflections in the side lines are collinear and the line passes through the orthocentre. Not T2. https://isa-afp.org/entries/Steiner_Line_Theorem.html
- **AFP `Steiner_Deltoid`** (2026-08-12): the envelope of Simson lines. Not relevant.
- **lean-genius `MiquelPivotTheoremOQ01.lean`** (PR #25056, merged): the pivot theorem, sorry-free. Its `meta.json` lists "Miquel point of a complete quadrilateral" only as an **open question**, not as something proved.
- **rocq-archive/projective-geometry `Plane/P09_complete_quadrilateral.v`**: `Lemma complete_quadrilateral`, a projective harmonic/collinearity property (Col P Q R), proved with no `Admitted`. It is a different theorem (projective, not metric).
- **Mathlib master PRs:** "Newton-Gauss" matched only toolchain chores (#16433, #16425, #16402), a name collision. Geometry PRs found: Euler's quadrilateral theorem #43745 (open), Varignon #43702 (open), nine-point circle #34420 (merged). None of these is T1–T8.
- **Newton line of a tangential quadrilateral:** no hit anywhere apart from the unfilled `docs/1000.yaml` title "Newton's theorem (quadrilateral)".

### Machine proofs not checked in a proof assistant
- **Newclid / JGEX** (`newclid/problems_datasets/large_examples.txt`): `miquel_quadrangle_theorem1/2`. Statement: `a b c d = quadrangle; e = ab∩cd; f = bc∩ad; circles (bce),(cdf),(ade),(abf); m = (bce)∩(cdf) ? cyclic m a b f` (and `? cyclic m a d e`). This is the four-line Miquel theorem, proved by the DDAR synthetic engine. **It is not kernel-checked.**
- **Chou, *Mechanical Geometry Theorem Proving* (1988):** HOL Light cites it as the source of example 15 (Gauss line) and example 288 (Simson). Wu's-method proofs, not kernel-checked. I did not inspect the book's other examples.
- **AlphaGeometry repo:** no hits for any of the names.
- **GeoGebra/Coq exports:** not searched separately beyond the GitHub code search.

---

## Verdict per theorem

1. **Newton–Gauss line: PRIOR ART.**
   - HOL Light `GAUSS`: https://github.com/jrh13/hol-light/blob/master/Complex/grobner_examples.ml
   - Coq area-method `gauss_line`: https://github.com/rocq-archive/area-method/blob/master/examples_2.v
   - Neither is in Lean; both are automated algebraic or area-method proofs.
2. **Collinearity of the four orthocentres:** no complete formal proof found in any searched source.
3. **Bodenmiller (circles on the diagonals are coaxal):** no complete formal proof found in any searched source.
4. **Orthocentre line ⟂ Newton–Gauss line:** no complete formal proof found in any searched source.
5. **Four-line Miquel point: PRIOR ART** in Coq HighSchoolGeometry `Miquel`: https://github.com/rocq-community/HighSchoolGeometry/blob/master/theories/applications_cocyclicite.v (line 270). It is the conditional form: M on two of the circles implies M on the other two. Not in Lean. AFP and lean-genius have only the pivot form.
6. **Miquel/Steiner circle (four circumcentres and M concyclic):** no complete formal proof found in any searched source.
7. **Simson line of the complete quadrilateral (feet from M on the four lines are collinear):** no complete formal proof found in any searched source.
8. **That Simson line is parallel to the orthocentre line:** no complete formal proof found in any searched source.
9. **Control:** FOUND-COMPLETE in AFP `Simson` (`simson_line`, 2026-08-03), HOL Light `SIMSON`, lean-genius `SimsonLineTheorem.lean` (sorry-free), and Coq HSG `droite_Simson`. The search method works.

**For a Lean paper:** no Lean 4 or Mathlib formalisation of any of T1–T8 was found, so a "first in Lean" claim holds for all eight. A "first machine-checked proof" claim holds **only for T2, T3, T4, T6, T7 and T8**. T1 and T5 must cite HOL Light and area-method (T1) and HighSchoolGeometry (T5).

---

## What was searched (how)

- **Mathlib pinned 0df444a3** (local checkout, commit dated 2026-08-21): `rg` over `Mathlib/` and `docs/` for quadrilateral, Gauss, Newton, Miquel, Simson, Steiner, orthocent, coaxal, radicalAxis and Bodenmiller.
  - Only unrelated hits: Ptolemy, cyclic-quadrilateral angle lemmas, NinePointCircle and MongePoint (the triangle orthocentre), and Gauss sums.
- **Mathlib master ef61520** (2026-10-14):
  - `docs/100.yaml` and `docs/1000.yaml` fetched. "Miquel's theorem", "Pivot theorem" and "Newton's theorem (quadrilateral)" are present with **no decl**.
  - `gh search prs/issues` for 11 terms.
- **Lean Zulip:** the live API needs login. Instead I code-searched the `leanprover-community/archive` repo (public-stream JSON, pushed 2026-10-05) for 10 terms.
  - The only relevant thread: "Is there code for X? › Six circle theorem" (2024-06). Ashvni Narayanan asked whether Miquel's six-circle/pivot theorem was in Mathlib; Johan Commelin and Joseph Myers said no.
  - The other "Miquel" hits refer to the type theorist Alexandre Miquel.
- **AFP:**
  - Shallow clone of `isabelle-prover/mirror-afp-devel` (HEAD 352a4e0, 2026-10-13), full `rg` over `thys/*.thy` for all requested terms.
  - Plus the isa-afp.org Geometry topic page (36 entries listed) and the abstracts of Miquel, Simson, Steiner_Line_Theorem and Steiner_Deltoid.
  - Hits: Miquel (pivot), Simson, Feuerbach and IsaGeoCoq (triangle orthocentre), Optimal_BST (quadrilateral inequality). No Gauss, Newton-line, Bodenmiller, coaxal or radical-axis hits.
  - The mirror grep for "Steiner" did not hit the Steiner_Line_Theorem entry, so that entry was checked via the website instead.
- **Mizar:** downloaded **all 1500** `.miz` files from https://mizar.uwb.edu.pl/version/current/mml/ (120 MB) and grepped them.
  - Only `euclid13.miz` matched: "Altitude, Orthocenter of a Triangle and Triangulation", by Coghetto.
  - Also checked: projective quadrangles in `projpl_1` and `projdes1`.
  - No complete quadrilateral, Miquel, Simson, Steiner, Gauss line or coaxal.
- **HOL4:** shallow **full** clone (7823 files, HEAD 2026-10-14) and grep. The only hit was a comment in `hilbertScript.sml`. Nothing relevant.
- **HOL Light:** shallow full clone (1786 files, HEAD 2026-10-06), grep across everything including `100/` and `Multivariate/`. Found `GAUSS` and `SIMSON` in `Complex/grobner_examples.ml`; otherwise only Richter's `Quadrilateral` definitions.
- **ProofAtlas:**
  - `sitemap.xml` (752 URLs): no matching slugs.
  - `/search/`: the 808 KB page with the embedded client-side index was grepped. Only Ptolemy, Steiner systems and the Gauss circle problem.
  - `/api/search` returns 404.
  - Google `site:` search not possible (see below).
- **GitHub code search:**
  - 18 terms × {Lean, Coq, Isabelle}. The first pass hit rate limits; it was **re-run paced at 7 s**, with 0 rate-limit errors.
  - Plus 8 terms with no language filter.
  - Real hits are listed above. Name collisions:
    - "Simson" in Lean: TauCeti, where it is an author name.
    - "newton_line" in Lean: competemath/tengoku, an LP Newton system.
    - "Simson" in Coq: CoRN SimpsonIntegration.
  - Also inspected:
    - MATPBench `Q1030`: a triangle-Simson benchmark statement.
    - ITPEval: no target theorems.
    - jjdishere/EG: convex quadrilaterals and parallelograms only.
- **Metamath:** set.mm shallow clone and grep of all `.mm` files. Only symmetric quadrilaterals and parallelograms (Tarski geometry). Nothing relevant.
- **GeoCoq:** shallow clone (HEAD 2025-11-18). Only `orthocenter.v` and `Euler_line.v` (triangle) and `quadrilaterals.v` (parallelograms). Nothing relevant.
- **lean-genius:** shallow clone (HEAD 2026-10-12), plus PR search for Miquel, complete quadrilateral, Newton, Gauss line and Steiner. Found Simson (sorry-free), Miquel pivot (sorry-free) and the open question noted above. Nothing for T1–T8.
- **mo271/FormalBook** (HEAD 2026-10-12): clone and grep found **0 hits**.
- **compfiles** (HEAD 2026-10-13): only the IMO 2025 P2 and USA 2025 P4 orthocentre problems.
- **formal-conjectures** (HEAD 2026-10-14): only Steiner *systems*.
- **LeanEuclid:** only UniGeo quadrilateral exercises.
- **AlphaGeometry:** nothing.
- **Newclid:** Miquel examples (machine proofs; see above).
- **Freek Wiedijk's 100 theorems:** none of T1–T9 is on the list. Feuerbach and Morley are present but not relevant.

## Sources that could not be reached, or only partly

1. **Lean Zulip live search:** the API returns HTTP 401 "Not logged in: API authentication or user session required", including for web-public narrows. The public archive was used instead (via the GitHub repo). That covers public streams only, and only up to 2026-10-05.
2. **Google `site:proofatlas.ai …` and general web search:** the WebSearch tool is not available in this session. ProofAtlas was covered only through its sitemap and search index; it has no reachable API (`/api/search` returns 404).
3. **AFP site full-text search** (`isa-afp.org/search/`): the search is client-side JavaScript and was not run. It was replaced by the full grep of the AFP mirror plus the Geometry topic page.
4. **Coq kernel re-check:** coqc is not installed, so I could not run `Print Assumptions gauss_line` or `Print Assumptions Miquel`. The "COMPLETE" status comes from `Qed` in the source and the absence of `Admitted` on the relevant path. It was not re-checked.
5. **GitHub code search** only indexes default branches and returns at most ~100 results per query. Forks and non-default branches are not covered.
