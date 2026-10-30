VERDICT: MINOR. BLOCKER 0 / MAJOR 2 / MINOR 9

Referee review of Paper H DRAFT v1 (paperh.tex, 1108 lines). Reviewer: Claude Opus 5.5 (claude-opus-5-5), 2026-10-28.
Done inline, no subagents. Read-only. The 13 \PH placeholders are not counted.
Why MINOR overall: every numbered theorem is true, and every Lean statement matches its prose
statement. The two MAJOR items are false mathematical statements in the explanatory prose (one
displayed identity, one "counterexample" claim). Each is a one-line fix and neither affects any
Lean result.

## Findings

1. MAJOR — l.345 (core identity of the quartic). The displayed equation
   `s^3(4r^2 f(s^2)) + ((y-x)(z-y)(x-z))^2 = 0` is FALSE. Checked at Ravi (x,y,z)=(1,2,3.5), where
   the left side is -3847.85; it is not zero. The Lean `core_identity` (Main.lean:272-275) has the
   bracket around both terms: `s^3 * (4 r^2 f(s^2) + P) = 0`, i.e. 4r^2 f(s^2) + P = 0. I checked
   P/(r^2 f(s^2)) = -4 to 40 digits on 3 triangles. The deduction in l.348-349 is correct only for
   the bracketed form.
   Fix: change it to `s^3\bigl(4r^2 f(s^2)+\bigl((y-x)(z-y)(x-z)\bigr)^2\bigr)=0`, or simply
   `4r^2 f(s^2)+((y-x)(z-y)(x-z))^2=0` with the remark that Lean carries a factor s^3.
2. MAJOR — l.519-520. The claim "b d_B + c d_C ≤ a|XA| is false in general (a numerical check found
   counterexamples)" is wrong for X in the closed triangle. That inequality is the elementary one:
   |XA| + d_A ≥ h_a, and a·h_a = 2Δ = a d_A + b d_B + c d_C, give a|XA| ≥ b d_B + c d_C.
   I sampled 200,000 random triangles and interior points: 0 violations. (REPORT_H2.md:22 and
   mordell PROGRESS.md:4 repeat the claim; the "counterexamples" were probably a mislabelled
   computation.) What is true is that the unpaired form is too weak to sum to Erdős–Mordell.
   Fix: "The pairing matters for the proof: the unpaired form b d_B + c d_C ≤ a|XA| is also true
   (it is |XA| + d_A ≥ h_a), but summing it does not give Erdős–Mordell. The reflected pairing
   b d_C + c d_B ≤ a|XA| is the one needed." Also correct REPORT_H2.md.
3. MINOR — l.637 says "(iii) holds for *any* F on two of the lines". Lean `napoleon_fermat`
   (Main.lean:111) assumes F on AA' and BB' specifically, and no relabelled versions are proved
   (see also l.894). Fix: "for any F on the lines AA' and BB' (by symmetry, any two of the lines;
   only this pair is formalised)".
4. MINOR — l.745-746. "for paperh_mordell the harness reported one probe statement as invalid" is
   ambiguous. In the mordell report (paperh_mordell_20261028_164005.md:36,73) the contradiction
   probe has invalid 0. The invalid statement is in the *satisfiability* step (stmt-invalid 1,
   `em_eq_scalar`), so 35 unresolved + 1 stmt-invalid. Fix: "(…; for paperh_mordell the
   satisfiability certifier rejected its own restatement of `em_eq_scalar` as ill-formed)".
5. MINOR — l.708 and l.721-725 (evidence trail). The paperh_fermat "9 of 9" is correct; it is not
   just the default list. /tmp/pf_tamper.log on x86 (21:10 UTC) has 9 `ok` lines plus
   "ALL TAMPERING TESTS REJECTED". However, Ptolemy.lean was edited at 21:11, after that run. Only
   falsehyp3 was re-run then (/tmp/pf_tamper3.log). The leancheck run at 22:31
   (paperh_fermat_20261028_223117.log) repeats the full default suite on the final tree and ends
   "ALL TAMPERING TESTS REJECTED". That banner is printed only if all 9 pass, but its excerpt shows
   only 8 `ok` lines because the `sorry` line is truncated. Fix: in the supporting material, cite
   the 22:31 log (or a fresh-clone log) as the tamper receipt, not the 21:10 one.
   Cross-builds: arm64 /tmp/xpe_gate.log reads PASS (60) and /tmp/xpf_gate.log reads PASS (47), at
   times after the final x86 edits. x86 /tmp/xph_gate.log reads PASS (48). I re-checked the
   mordell SHA-256 per file: it agrees on both machines. I could not locate the arm64 copies of
   euler/fermat to compare digests, so the paper is right not to claim digests for those two.
   Covered by the fresh-clone \PH; no text change needed beyond that.
6. MINOR — l.848-851 and l.119 ("no formal proof of the Fermat–Napoleon statements"). According to
   DRAFT_REPORT Q5, the scout sweep did not cover Fermat–Napoleon. Only the AFP page, the
   atlas-lean file and a GitHub code search were checked, while GeoCoq, HOL Light and the Isabelle
   Napoleon theory sources were not grepped for the concurrence. l.866-867 says this only for
   Napoleon. Fix: add to l.851 "(this claim rests on a narrower search than the rest of this
   section: …)", or grep GeoCoq, HOL Light and the AFP Napoleon/Triangle theories for
   Fermat/Torricelli/concurrence before submission.
7. MINOR — notation clashes that an ITP/JAR referee will trip over:
   - l.592: G is "twice the area", but G is the centroid (l.162).
   - l.557: r = ⟨XA,XB⟩, but r is the inradius.
   - l.566: Wolstenholme's variables X,Y,Z, but X is the point.
   - l.511: V is a foot point, but V is the vector space.
   Fix: rename to, e.g., 2Δ or g, ρ_C, (ξ,η,ζ), and U,V′,W (the Lean already uses V').
8. MINOR — l.84 vs l.952: the coauthor's name is spelled "\v{D}ordevi\'c" in the text and
   "\DJ{}or\dj{}evi\'c" in the bibliography. Fix: use `\DJ{}or\dj{}evi\'c` in both places.
9. MINOR — l.488. The paper honestly says the docstring mentions Mathlib's `inversion`, which the
   proof does not use. That is a defect in the artifact, not the paper. Fix: correct the module
   docstring (FermatNapoleon/Ptolemy.lean:16) before publishing, then delete the sentence.
10. MINOR — l.598-599: "so F is a genuine interior point" is not a formalised statement, and no
    Lean theorem asserts that F lies in the triangle. Fix: "so the weights are positive (F is
    interior; this is not stated in Lean)".
11. MINOR — l.999-1000: the pr44230 entry has no "accessed 28 October 2026", unlike the other web
    entries, and the trailing URL comes after the full stop. Also l.780: the PR now carries the
    labels blocked-by-other-PR, merge-conflict and file-removed (checked via the GitHub API). Fine
    as written; give the access date.

Not findings (verified correct): DRAFT_REPORT §bib says Paper G has "no DOI". That is outdated:
10.5281/zenodo.23741528 resolves to record 23741529, "Triangle centres in Lean 4 the Nagel line
family…", 2026-10-28, which matches l.1105. Repository state: euler has HEAD 90c1950 plus 12
uncommitted entries, fermat reports "not a git repo" to leancheck, and mordell has no commits. So
the batteries are not tied to any commit. This is covered by the \PH at l.765 and l.923, but must
be done before submission.

## Checks completed
1. Mathematics, mpmath at 40 digits on 3 non-special triangles ((0,0),(7,0),(2,5); (0,0),(5,0),
   (1.3,2.1); (1,2),(-3,.5),(4,-1); the last two are obtuse with max angle .51π and .64π).
   Residuals were ≤1e-37 or the inequality held strictly, for:
   - Euler OI²; R ≥ 2r; excircle OI_a² (I_a from weights (-a,b,c), and its distance to BC = r_a)
   - OG², OH² (H checked orthogonal to BC), IG²
   - Gerretsen both sides, cross-check, Kooi and Kooi ≤ Gerretsen, the quartic
   - Weitzenböck, Hadwiger–Finsler, isoperimetric; Leibniz at an off-plane-like far point
   - Neuberg–Pedoe: strict for a dissimilar pair, 0 for a scaled copy
   - key lemma ×3 and Erdős–Mordell at interior, edge and vertex points; Barrow at 3 interior
     points per triangle
   - explicit Fermat point (l.592-597): three angles 2π/3 to 40 digits
   - Ptolemy equality on a tilted circle in R³ for separated order (0) vs non-separated (≠0), and
     the collinear cases. All 24 orders enumerated: equality ⇔ (b) ⇔ exactly the 8 orders of
     l.466.
   - Napoleon–Fermat: outwardness, AA'=BB'=CC', CC' through AA'∩BB', angles 2π/3, FA+FB+FC=AA',
     vector angles 2π/3 and π/3, Napoleon equal sides with centroid G.
   SymPy exact checks: Euler key identity (l.307), HF identity (l.407), AM–GM (l.418),
   iso-Heron (l.414), Kooi identity (l.369) and K formula, G−K = 3r²(R−2r)/(2(2R−r)), roots of f
   (disc = 4R(R−2r)³), key_scalar_sq (l.535), Pedoe certificate (l.439) modulo both Herons. All
   residuals 0. The only failure was the l.345 display (Finding 1).
2. Prose vs Lean. I opened every File:line in Table 1 (l.238-276); all 33 line numbers point at
   the named declaration. Checked: binders (no Fact/finrank outside FermatNapoleon; Ptolemy files
   have no dimension assumption); closed vs strict weights (mordell); Wbtw/angle hypotheses of
   barrow; the six ≠ hypotheses and both disjuncts of ptolemy_eq_iff; hFA/hFB and 3 angle
   hypotheses of napoleon_fermat; triSign/outerApex definitions; Pedoe's P'; leibniz X : P;
   equilateral as d01=d12 ∧ d12=d20. Every \decl name occurs in a gate.sh REQUIRED list (grep).
   Lean v4.33.1 and Mathlib 0df444a360ea… are confirmed in all three toolchain/manifest files.
   Line counts 1159/1185/1102 and the per-file counts match wc.
3. Verification numbers:
   - gates PASS 60/48/47 (REPORT.md, /tmp logs, leancheck md)
   - tamper 9/7/9 (logs; mordell PROGRESS "7/7" and leancheck md; the test names match l.703-715)
   - batteries 56/228/225 (2 timeout)/3, 47/162/161/1, 43/165/163/2 (leancheck md TOTAL lines)
   - ablation 29/0, 211/0, 60/0; probes ok 11/42/20, no-hyp 45/5/23; sat 7/11/17; linter 0
   - the 6 survivors match l.750-761 verbatim
   - cross-build PASS lines (Finding 5)
4. Related work vs SCOUT.md. There are no first-claims on Euler OI², R ≥ 2r, excircle, Ptolemy's
   inequality, the EM inequality or key lemma, or Napoleon: each is marked R and credited in
   l.95-110, l.776-851 and l.885-888, consistent with SCOUT §1/§4. The Weitzenböck/HF "geometric
   packaging only" claim matches SCOUT row 13/14 and l.824-825. References checked:
   - 13 DOIs resolve (curl), and Crossref metadata (title, volume, pages, year, authors) matches
     for Weitzenböck, Finsler–Hadwiger, Erdős 1935, Erdős–Mordell–Barrow 1937, Kazarinoff,
     Pedoe ×2, Blundon and Lean 4.
   - 3 Zenodo records exist with the cited titles.
   - all 19 GitHub/AFP/Wiedijk/arXiv URLs return HTTP 200; the specific files exist (GitHub API).
   - AFP Napoleon authors, Aug 2026, complex coordinates and both orientations confirmed.
   - PR #44230 open, opened 2026-09-26, by wwylele.
   - arXiv 1708.02993 authors Kovács, Vajda, Montag confirmed.
5. Clarity/referee: Findings 3, 7, 10. Overall the paper is unusually candid about reproofs,
   search gaps and unformalised equality cases. With Findings 1–2 fixed and the placeholders
   discharged, I would recommend acceptance.
DONE
