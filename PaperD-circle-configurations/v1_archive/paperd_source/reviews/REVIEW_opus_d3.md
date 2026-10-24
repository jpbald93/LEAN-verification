VERDICT: MINOR REVISION. BLOCKER 0 / MAJOR 2 / MINOR 8. The new math is correct; the blind-check prose oversells two points.

# REVIEW_opus_d3: Paper D, round 3 (chainfail + blind section + battery refresh)

Line numbers refer to the current paperd.tex.

## 1. sec:chainfail (l.291–330) vs Counter6 / Classify / GENERAL_REPORT
Supported:
- The six centres (l.302) are the same as `Counter6.cx` (Counter6.lean:19). The src/ and pub/ copies of Clifford/ are identical (diff -rq is empty).
- The theorem's decls exist with the stated content: `not_cliffordChain_six` (Counter6:227), `not_cliffordChain_of_six_le` (Classify:219), `cliffordChain_iff : CliffordChain n ↔ n ≤ 5` (Classify:227).
- I recomputed in mpmath (50 digits, independent of the repo):
  - The omit-4 points all have Re = 4, and the omit-5 points all have Im = −4.
  - The five points of every one of the six subfamilies are collinear to about 1e-48 and pairwise distinct (minimum spacing 1.49).
  - 4−4i is off the omit-0 line (the collinearity determinant is 29.6, not 0).
  - So l.311–315 is correct.
- The n≥7 propagation (l.319–322) matches `not_chain_of_extends` (Classify:57) and `GenPosN.exists_snoc` (Classify:167, the parabola `par t = t + t²i`).
- The perturbation figure 2.4e-2/ε and the "chain exists for n≤8" claim (l.317, l.326) match GENERAL_REPORT. pub/cliffordchain/numerics/ contains chain.py, gq.py, d6*.py and cex2.py, so "archived" is fine.
- thm:cliff6 is unaffected (l.328–330). In this configuration every five-point set is collinear, so every designated triple is collinear and m1–m6 fail. The claim is correct, but it is argued, not machine-checked; that is acceptable.

Issues:
- **MINOR (overstates what the kernel checks), l.309–316.** The kernel checks less than the paragraph says:
  - It checks only **9** of the 15 level-4 points (`q0134…q2345`).
  - It checks only **3** of the six level-5 objects (omit 4, 5 and 0), each through 3 points.
  - "Every level-4 object is forced" and "for each of the six subfamilies the five points are distinct and collinear" rest on the external exact computation (GENERAL_REPORT), not on Lean.
  - "All the arithmetic is exact over Q(i) and is checked by the kernel" (l.315) reads as covering all of this.
  - Fix: "the kernel checks the nine level-4 points and three lines the proof needs; the full picture (all 15 points, six lines) was checked in exact rational arithmetic."
- **MINOR (indexing).**
  - l.312 counts circles from 0; everywhere else the paper uses c_1…c_6 (l.208–243, the m1–m6 lists).
  - "c_5" at l.317 is not marked as 0-based. Read 1-based, it is −4i, not 4.
  - The displayed tuple at l.302 has no indices.
  - Suggest c_0,…,c_5 in the display and "(counting from 0)" once, at the display. Better still, renumber to 1..6: the lines become omit 5 → Re z=4, omit 6 → Im z=−4, omit 1.
- **MINOR (citation), l.322.** Classify:219 is the three-line wrapper. Cite Classify:57 (`not_chain_of_extends`) and Classify:167 (`exists_snoc`), where the argument the sentence describes actually is.
- **MINOR (wording), l.323.** "So Theorem~\ref{thm:chain} is the whole truth about this predicate": the whole truth is `cliffordChain_iff`, i.e. thm:chainfail together with thm:chain. Also, "the finite-plane predicate has no point at infinity" (l.296) explains the failure but is not proved. That is fine, since it is framed as the classical picture.

## 2. sec:blind (l.484–518) vs layer13/
Accurate:
- 10/12 equivalent; the two conditional pairs are blind_3/blind_4 (cliff5 explicit, cliff6).
- The conditions are stated correctly: B→R needs the *statement* of `cliffordPoint_mem_gams` as a premise; R→B needs `uniq_stmt` (L13_cliff5x:156,169,234; L13_cliff6:140,210,379).
- The designated-triple guess matched all six sets (`abd0..abd5`, L13_cliff6:362–372). The writer itself had expected the guess to be wrong.
- Coverage: 12 statements for 10 theorems. The listed range "five to steiner" plus cliff4, chain×2 and cliff5-existential gives 10.
- layer13/paperd_blind.txt is identical to ./paperd_blind.txt and still contains the pre-round-3 sentence at l.161. That is consistent with "produced before sec:chainfail".

Spot-check of three files for published theorems inside proof bodies:
- L13_chain: `cliffordChain_four/_five` appear only in `type_of%` premises and conclusions. The only lemmas used are `transversal_iff` and `genTriple_iff`.
- L13_cliff6: `clifford_three` and `cliffordPoint_mem_gams` appear only via `type_of%` as premise or goal. Lemmas used: `mem_circumcircle_*` (basic lemmas, not bridge lemmas).
- L13_kosnita: `Kosnita.kosnita` appears only in `example : real10_stmt := @Kosnita.kosnita` (l.41), which only type-checks the statement.
- Claim holds.

Issues:
- **MAJOR (framing), l.505–513 and l.516.** "Artefacts of the redaction" plus "No difference between prose and Lean was found" is not fair.
  - The redaction removed nothing relevant. The blind text (paperd_blind.txt l.114–116) has exactly the paper's sentence, with no formula for cp.
  - The paper itself says, two sentences earlier, "Our prose does not give the formula" (l.506).
  - So the blind check *did* find a prose–Lean gap. The prose of thm:cliff5 (explicit part) and thm:cliff6 does not determine the Lean statement unless cp is unique, and uniqueness is unproved.
  - Fix: call it "an underspecification in our prose" (not "of the redaction"); delete or qualify "No difference ... was found"; and either give the cp formula in the prose or prove uniqueness.
  - Uniqueness looks cheap to prove. Γ_123 and Γ_124 meet exactly in {P_12, cp}, and Γ_134 and Γ_234 meet exactly in {P_34, cp}. So a second common point forces P_12 = P_34, unless two Γ coincide.
- **MAJOR (unsourced and off-target evidence), l.511–512.** I found no archived source for "5000 random configurations … minimum separation 6×10⁻³". I searched the numerics/, reports/, layer13/ and pub/*/numerics directories, FIX_LOG.md and REFAUDIT.md.
  - The test is also the wrong one. Four *distinct* circles can share two points (a coaxal pencil), so "never close to coinciding" does not test uniqueness.
  - Fix: archive the script and output, and test the right condition (a second common point / P_12 = P_34 type coincidences); or replace this with the short proof above.
- **MINOR (tool-log claim), l.488–489.** "Its tool log confirms that the only file it read was the prepared text":
  - No tool log is archived in layer13/. The evidence there is the writer's *self-report* (WRITER_REPORT "Files read").
  - That report also says the writer wrote and compiled a `#check` probe of Mathlib names on the x86 machine, i.e. it queried Mathlib.
  - Either archive the log or say "by its own report", and mention the Mathlib name probe. l.717 ("shown by its tool log") has the same problem.
- **MINOR (verifiability), l.500–501.** "We recompiled the comparison files ourselves": the only compile record in layer13 is the comparer's own table from the jack machine. Archive the recompile log.

## 3. Battery totals (l.~600–690): all add up
- Mutants:
  - Per development: clifford 129, cliffordchain 284, five 36, lester 82, thebault 65, kosnita 33, blundon 21, steiner 6; total **656** ✓.
  - Rejected by error: 102+279+36+82+64+30+19+6 = **618** ✓.
  - Rejected by timeout: 27+4+0+0+0+3+2+0 = **36** ✓.
  - Survivors: **2** ✓ (cliffordChain_one 1→2; thebault σX<0→<1).
  - cliffordchain **283/284** ✓ (john_clifford_j_20261014_full.md:34,113).
  - "Proof that uses the lemma failed to build" = "downstream errors at lines [233]", which is `exact cliffordChain_one` in Classify ✓.
- Satisfiability:
  - Per development: clifford 73/103, cliffordchain 112/161, five 15/20, lester 20/31, thebault 13/28, kosnita 7/11, blundon 1/5, steiner 0/3.
  - Total **362** ✓; certified **241** ✓; unresolved **121** ✓.
  - With hypotheses: 8+19+11+3+10+5+1+0 = **57** ✓. Hypothesis-free binders: 65+68+4+8+3+2 = **150** ✓. Closed: 25+9 = **34** ✓.

## 4. Consistency and over-claims
- Library counts, all ✓:
  - Files: 3+7+2+4+2+2+2+2 = **24**.
  - Lines: 1271+1679+428+506+559+249+228+129 = **5,049**. cliffordchain = 6 (root) + 1673 = 1679, matching wc on pub/.
  - Declarations: 20+32+19+12+11+6+5+3 = **108**; GENERAL_REPORT also gives the gate as 32 declarations.
- **MINOR (abstract), l.60–80.** The abstract does not mention the n≥6 result. It is not an over-claim, since the abstract only claims n=4,5,6. But a machine-checked proof that the natural finite-plane predicate is false for n≥6 is a notable and citable negative result, and it is in the contributions list. Suggest one sentence.
- **MINOR (intro), l.133.** "We do not prove Clifford's chain for general n (Section~\ref{sec:chain})": point to sec:chainfail as well, and say that the natural finite-plane statement is false.
- **MINOR (contributions), l.110–112.** The sentence now has four clauses and mentions n=5 twice ("proves the cases n=4,5 … and proves the n=5 case with no hypothesis beyond general position"). Tighten it, e.g. "proves n=4,5 (n=5 with no hypothesis beyond general position) and proves that the predicate fails for every n≥6".
- No new over-claims found elsewhere:
  - l.150 table, l.289, the limitations at l.708–719 and the battery text at l.~690 ("at the published commit") are consistent with the new result.
  - l.710 "proved for n≤6, and for n=6 only when the five-point circles are not lines" is accurate.
- Still open from before (not this round): the \PH placeholder for the hand check at l.703.
