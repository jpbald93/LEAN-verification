# Prior-art gap closing — 8 classical geometry theorems (searched 2026-10-13)

Legend: **NOTHING** = source searched, no formalization of this theorem. **FOUND-COMPLETE** = machine-checked, no sorry/Admitted. **FOUND-PARTIAL** = stated only, or a proof that doesn't capture the geometric theorem. **UNREACHABLE** = couldn't search.

Theorems: T1 Clifford chain (n ≥ 4) · T2 Miquel five circles · T3 Lester · T4 Sawayama–Thébault · T5 Kosnita · T6 Blundon · T7 Steiner–Lehmus · T8 Miquel 3-circle (control)

## Table

| Source | T1 Clifford | T2 5-circles | T3 Lester | T4 Thébault | T5 Kosnita | T6 Blundon | T7 Steiner–Lehmus | T8 Miquel (control) |
|---|---|---|---|---|---|---|---|---|
| a. Lean Zulip (public archive, full JSON) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING formalized; 2024-06-05 thread "Six circle theorem" says Miquel is not in Mathlib (control hit, so the search worked) |
| b. Isabelle AFP (full mirror, 2026-10-07, + live site front page) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | **FOUND-COMPLETE** AFP `Miquel` (2026-08-11) |
| c. Mizar MML (all 1500 .miz files) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| d1. HOL4 (full shallow clone, 7822 files) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| d2. HOL Light (full, incl. 100/, Multivariate/) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| e. ProofAtlas (sitemap 752 URLs, /search index 427 entries, /api/*, DDG `site:`) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (API = 404; Google `site:` UNREACHABLE, DDG used instead) |
| f. GitHub code search (all languages) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | non-kernel only (Hasclid, see h) | **FOUND-PARTIAL** lean-genius (algebraic core only); acornlib stated only | **FOUND-COMPLETE** (AFP mirror; lean-genius) |
| g1. Metamath set.mm | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| g2. Freek's 100 / Lean 100 pages | NOTHING (not on the list) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (not on the list) |
| g3. GeoCoq | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (it's in HighSchoolGeometry, below) |
| g3'. Rocq HighSchoolGeometry / area-method | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | **FOUND-COMPLETE** `Theorem Miquel` |
| g4. lean-genius (full tree, 39k paths, + PR search) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (Gerretsen only, weaker) | **FOUND-PARTIAL** | **FOUND-COMPLETE** PR #25056 |
| g5. mathlib4 master (code, docs/100.yaml, docs/1000.yaml, issues/PRs) | NOTHING (1000.yaml lists it, no decl) | NOTHING (listed, no decl) | NOTHING (listed, no decl) | NOTHING (listed, no decl) | NOTHING | NOTHING | NOTHING (listed, no decl) | NOTHING (listed, no decl) |
| g6. compfiles, google-deepmind/formal-conjectures (code + issues/PRs) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| g7. acornlib (Acorn prover) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | **FOUND-PARTIAL** (stated only, commented out) | has `theorem_miquel.ac` (not inspected) |
| h. Automated / synthetic provers | NOTHING found | NOTHING found | NOTHING found | NOTHING found | NOTHING found | machine proof, not a proof assistant: Hasclid | machine proof, not a proof assistant: JGEX examples | n/a |

## Details of every hit

**T8 control (the searches worked):**
- Isabelle AFP `Miquel`: https://www.isa-afp.org/entries/Miquel.html (repo: `isabelle-prover/mirror-afp-devel/thys/Miquel/Miquel.thy`). Date 2026-08-11. Main results are `theorem miquel_pivot` and `theorem miquel_concurrent`: for P, Q, R on lines BC, CA, AB, the circumcircles of AQR, BRP, CPQ share a point. No `sorry`/`oops`. COMPLETE.
- Rocq HighSchoolGeometry: https://github.com/rocq-community/HighSchoolGeometry, `theories/applications_cocyclicite.v:270`, `Theorem Miquel`. Ends in `Qed`, no `Admitted` in the file. COMPLETE.
- lean-genius: https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/MiquelPivotTheoremOQ01.lean (PR #25056, merged 2026-06-16). 3-circle pivot via cross-ratio.

**T7 Steiner–Lehmus:**
- lean-genius `SteinerLehmusTheoremOQ01.lean`: https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/SteinerLehmusTheoremOQ01.lean (PR #25041, merged 2026-06-16). Statement: `theorem steiner_lehmus (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (heq : bisectorSq a b c = bisectorSq a c b) : b = c`, where `bisectorSq a b c := a*c*(1-(b/(a+c))^2)` is *defined* by the bisector-length formula. No `sorry`, no axioms. But it is only the algebraic core: nothing connects it to Euclidean points, angle bisectors, or Mathlib geometry. Classify as **PARTIAL**. It is not a geometric Steiner–Lehmus, but you should cite it and distinguish your work from it.
- acornlib: https://github.com/acornprover/acornlib/blob/master/src/theorems1000/theorem_steiner_lehmus.ac. Statement given in R² with the bisector feet defined through the angle-bisector ratio. The theorem is **commented out** and the proof is left as a sketch ("the sine law and the angle-bisector length formula ... are not yet in the library"). Stated only, not proved.
- JGEX (Java Geometry Expert): `steiner-lehmus.gex` and `steiner-lehmus1.gex` are listed among its examples. This is an automated prover, not kernel-checked: *machine proof, not in a proof assistant*.
- SRI-CSL/PVS `src/nlyices/nlyices.lisp` mentions a `steiner-lehmus-theorem.ys` benchmark for a nonlinear Yices SMT experiment. That is an SMT benchmark, not a PVS proof.

**T6 Blundon:**
- TACITVS/Hasclid `examples/Blundon.euclid`: https://github.com/TACITVS/Hasclid/blob/main/examples/Blundon.euclid. A Haskell Gröbner/inequality prover, run in `:proof-mode unsafe`, targeting s ≤ 2R + (3√3 − 4)r. I did not check whether it succeeds. Not a proof assistant: *machine proof attempt, not kernel-checked*.
- Related but not Blundon: lean-genius `HeronsFormulaOQ06OQ02.lean` proves **Gerretsen's** s² ≤ 4R² + 4Rr + 3r², which is strictly weaker than Blundon. Gerretsen is implied by Blundon, not the other way round. Worth citing as nearest prior work.

**T1–T5:** no formalization (complete, partial, or stated-only) in any reachable source. mathlib4 `docs/1000.yaml` has entries for "Clifford's circle theorems" (Q5132839), "Five circles theorem" (Q5456213), "Lester's theorem" (Q1631749), "Thébault's theorem" (Q2500408), "Steiner–Lehmus theorem" (Q1631992) and "Miquel's theorem" (Q2449984), all with no `decl`/author, i.e. not formalized in Mathlib. Kosnita and Blundon aren't on the list.

**Name collisions dismissed:** "Lester" in HOL Light/Freek's list is David Lester (PVS NASA library author), not Lester's theorem. "Clifford" hits are Clifford algebras / quantum Clifford gates. "Sawayama" hits are a solitaire game. "Thebault" hits are a person's surname. "Kosnita" hits are ETC data / Asymptote figures. "Miquel" in Zulip is Alexandre Miquel (type theory). "FermatPoint" Lean hits are unrelated (number theory / RH projects).

## Verdicts

1. **Clifford chain, n ≥ 4:** no complete formal proof found in any searched source.
2. **Miquel five circles:** no complete formal proof found in any searched source.
3. **Lester's circle theorem:** no complete formal proof found in any searched source.
4. **Sawayama–Thébault:** no complete formal proof found in any searched source.
5. **Kosnita:** no complete formal proof found in any searched source.
6. **Blundon's inequalities:** no complete formal proof found in any searched source. Nearest: Gerretsen (weaker) in lean-genius; a non-kernel Hasclid attempt.
7. **Steiner–Lehmus:** no complete *geometric* formal proof found. **Partial prior art you must cite:** https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/SteinerLehmusTheoremOQ01.lean. It is sorry-free Lean 4, 2026-06-16, but it proves only the algebraic core over side lengths with a defined bisector-length formula. Also acornlib (stated only) and JGEX (automated, not kernel-checked).
8. **Miquel 3-circle (control):** PRIOR ART, as expected: https://www.isa-afp.org/entries/Miquel.html ; https://github.com/rocq-community/HighSchoolGeometry (theories/applications_cocyclicite.v) ; lean-genius PR #25056. Since the control is found in three systems, the search method is validated.

## Sources not fully reached (exact reasons)

- **Lean Zulip live search:** the API returns `UNAUTHORIZED: Not logged in` and no credentials are available. Substitute: the complete JSON of the public archive (`leanprover-community/archive`, `zulip_json/`, 61,968 files, last commit 2026-10-02, newest message seen 2026-09-25) was grepped. Gap: private streams, and anything posted after about 2026-10-02.
- **Google `site:proofatlas.ai`:** there is no Google access (the WebSearch tool is unavailable here). DuckDuckGo HTML `site:` search was used instead and returned no target hits. The ProofAtlas sitemap and the embedded search index were scanned in full. ProofAtlas has no public `/api/` (404).
- **AFP `/search/`:** it is a client-side page, so it was not queried directly. Substitute: a full-text grep of the complete AFP mirror (1045 entries, 2026-10-07), plus a check of the live AFP front page for entries newer than the mirror. Of those, only `Steiner_Line_Theorem` and `Steiner_Deltoid` are new, and both are unrelated.
- **GitHub code search:** the first pass was rate-limited (HTTP 403) and gave false empty results, so it was discarded and re-run with pacing. Caveats: GitHub's code index doesn't cover all repos/forks, and returns at most about 50 results per query. Language-qualified queries (Lean/Coq/Isabelle) were dropped because they hit the limiter; unqualified queries were used and filtered by hand.
- **MML query / abstracts index:** not used, but superseded by grepping all 1500 MML article sources (current version).
- **HOL4:** a full (non-sparse) shallow clone was grepped. The scan is complete.
