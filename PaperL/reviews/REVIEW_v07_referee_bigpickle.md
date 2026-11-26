
> build · big-pickle

→ Read DRAFT.md [offset=717, limit=900]
◈ Parallel Web Search "arXiv 1509.04109 Bobenko Schief Clifford circle theorem"
## 1. VERDICT

MAJOR REVISION — The formalisation record is often carefully hedged, but several absolute/novelty claims, an invalid satisfiability inference, and contradictory version/provenance statements would mislead a reader.

## 2. FINDINGS

1. **MAJOR — §1.** Quote: “This paper therefore claims **first machine-checked treatment of the chain for arbitrary n**, and nothing about the mathematics.”  
   Wrong: This is an absolute novelty claim, but §5.10 records major search gaps (MathSciNet/zbMATH not searched, Google Scholar unreachable, Mizar body not full-text searched, etc.) and narrows the claim to “no formal statement … found in any of the sources logged”. A reader may believe the search was exhaustive.  
   Fix: Replace “first” with “first found in the sources searched” or move the §5.10 qualification into §1 and state the gaps at the point of claim.

2. **MAJOR — §1.1.** Quote: “The corner is not empty: a numerical search produced `GenPosN` configurations in it with the grandchildren's level points collinear to 1e-8.”  
   Wrong: Floating-point residuals cannot establish exact `GenPosN` membership or exact membership in the corner. The next sentence disclaims only exact vanishing of `V`, not the earlier exact-sounding claims.  
   Fix: Say “numerical search found approximate configurations satisfying the corner conditions to about 1e-8; exact non-emptiness remains **OPEN**,” or provide an exact certificate.

3. **MAJOR — §5.2.** Quote: “A certificate is an accepted instance: Lean checks a proof of `∃ binders, True` in which every hypothesis of the declaration is assumed, so the certificate establishes that those hypotheses are simultaneously satisfiable.”  
   Wrong: Assuming hypotheses and proving `True` does not establish their satisfiability; e.g. `False ⊢ ∃ x, True`. The curated-witness discussion also says the instrument must “discharge the propositional side conditions”, which conflicts with “every hypothesis … is assumed”.  
   Fix: State precisely whether certificates are open terms with hypotheses as parameters or closed instances with proved hypotheses. If the former, remove “satisfiability” and vacuity language; if the latter, quote the actual proof obligation.

4. **MAJOR — §5.2.** Quote: “so no declaration's existential statement failed to elaborate and none is known to be vacuous.”  
   Wrong: `stmt-invalid = 0` supports only successful elaboration. It does not rule out vacuous truth, especially under the preceding invalid inference.  
   Fix: “`stmt-invalid = 0` means all statements elaborated; this layer does not assess vacuity.”

5. **MAJOR — §5.3.** Quote: “Five rows (S1, S4, S5, S6, S7) are **definitional** differences: the two sides assert the same geometric content over independently invented predicates.”  
   Wrong: The same item later says S1 has a strictly weaker hypothesis, is separated by a concrete configuration, and is unsettled. The S1 sides therefore do not assert the same content.  
   Fix: Remove S1 from the definitional rows; classify it as a hypothesis-strength difference that remains open.

6. **MAJOR — §5.11.** Quote: “Nothing in this appendix was run twice on two machines.”  
   Wrong: Directly contradicted by §5.5 and Appendix B, which report john reproducing layers 4 and 5 at the same pin and a byte-identical layer-13 comparison compiling there; §5.2 reports two-machine satisfiability passes.  
   Fix: Update the provenance summary for v0.7: specify which layers were reproduced on john, which were re-run on new inputs, and which remain jack-only.

7. **MAJOR — §5.11.** Quote: “Layer 11 ran on v0.1 and was re-run on v0.2 and again on this v0.3 text — every re-run is a corrected re-run on a new input, not a reproduction.”  
   Wrong: In a v0.7 draft this is stale: Appendix B says layer 11 was also re-run on v0.4. The paragraph generally describes v0.3/v0.4-era events as current.  
   Fix: Rewrite as a v0.7 input-version table: layer 11 through v0.4; v0.5–v0.7 changed evidence only; name any citations added after v0.4.

8. **MINOR — Appendix A.** Quote: “`L11_NAMEGATE.md` (regenerated for v0.3).”  
   Wrong: Appendix B and Appendix C say it was regenerated for v0.4.  
   Fix: Relabel to v0.4, or state that it was regenerated again for v0.7.

9. **MINOR — Appendix C heading.** Quote: “## Appendix C — changes in v0.3 and v0.4”  
   Wrong: The appendix also contains v0.5, v0.6 and v0.7 sections, as the introduction promises.  
   Fix: Rename to “changes in v0.3–v0.7”.

10. **MINOR — §1.2.** Quote: “(Longuet-Higgins 1972; Bobenko–Schief 2016) are all classical.”  
    Wrong: §1 cites Bobenko–Schief as `arXiv:1509.04109` (a 2015 identifier), and the “higher-polytope picture” is not obviously the same contribution as the cross-ratio/dCKP paper cited there.  
    Fix: Give one consistent bibliographic year/version and separate the polytope citation from the cross-ratio citation.

## 3. NOTES

- The “all n” claim is explicitly presented as a composition of two theorems plus `check/allN.lean`, with “No single declaration” stated; this is honest, but the check file should be part of the pinned upload for journal review.
- The layer-13 two-direction language for S6/S7 is qualified in the text: blind⇒real is admitted to be vacuous because the real propositions are theorems; real⇒writer for S7 is unconditional and S6 is the `Counter6` instance. This should not be read as a universal bridge.
- No Lean source was available, so file:line citations, declaration existence, compilation receipts, and artifact hashes were not independently checked.

## 4. VERIFIED

- Mutation arithmetic: `535 + 95 + 1 = 631`; `872 + 3 + 16 = 891`; `61 + 257 = 318`; `343 − 318 = 25`; `6 + 19 = 25`.
- Contradiction-probe arithmetic: `147 + 163 = 310` `ok`; `125 + 93 = 218` no-hypothesis; `310 + 218 + 22 + 1 = 551`; `551/577 ≈ 95.4%`.
- John’s rerun arithmetic: `1058 + 9 + 16 = 1083`; `228 + 114 + 1 = 343`.
- Satisfiability arithmetic: `400/596 ≈ 67.1%`; `394/584 ≈ 67.5%`; `397 + 180 = 577`; `397/577 ≈ 68.8%`; `560 + 17 = 577`, consistent with 380 shared certified and 180 shared unresolved.
- File-size arithmetic: the nine `Clifford/*.lean` line counts sum to 8,311.
- Several limits are honestly stated: finite-plane failure for `n ≥ 6`, false `UniqEven`, Carver classification not formalised, layer-5 `ok` not a satisfiability certificate, unresolved satisfiability not refutation, and layer-9 counts labelled heuristic.
EXIT=0
