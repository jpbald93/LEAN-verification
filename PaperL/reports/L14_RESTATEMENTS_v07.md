# Layer 14 — independent restatement re-run on draft v0.7

**Date:** 2026-11-26. **Instrument:** `opencode/big-pickle` (headless `opencode run`, jack, fresh
session), given only `DRAFT_blind_v07.txt` — the mathematical prose of v0.7 with every identifier,
file name and citation removed. It was told nothing about the Lean development and had no access to
it. Output: `layer13/run6/l14_bigpickle.log` (verbatim below), 7 statements in the required
`HYPOTHESES / STRENGTH / TRAP` form.

Why a re-run was needed: the previous restatements (`layer13/L14_RESTATEMENTS.md`, 2026-11-24) were
produced from a blind text cut from **v0.2**. Section 2 grew from 9,300 to 16,608 characters between
v0.2 and v0.5 (and is byte-identical from v0.5 through v0.7), so the old restatements were checked
against prose the paper no longer contains. `DRAFT_blind_v07.txt` is the v0.7 re-cut: the carrier
(§2.1), the chain recursion (§2.1), the canonical level point (§2.1, §2.3 note) and the seven
statements (§2.2–§2.5).

## 1. What the restatements say (condensed, verbatim in §3)

| row | restatement, in the instrument's own words | Lean signature it must match |
|---|---|---|
| 1 | ∀ n≥1 ∀ c [GP(c) ⇒ ∃ X⊆S, Clₙ(X,c)]; existential at every level | `cliffordChainS_inf (n) (3 ≤ n)` + `cliffordChainS_of_le_five (n ≤ 5)`; the paper's `check/allN.lean` is their composition |
| 2 | ∀ k≥0 ∀ d (2k+5 centres) [GP ⇒ ∃ Y generalized circle, ∀ i, P₂ₖ₊₄(d∘δᵢ) ∈ Y] | `hodd_inf_all' : ∀ k d, GenPosN d → ∃ Y, IsGCircleS Y ∧ ∀ i, EptInf (2k+4) (d∘i.succAbove) ∈ Y` |
| 3 | ∀ k≥0 ∀ c (2k+6) ∀ i [GP ⇒ ∃ Y, P₂ₖ₊₆(c) ∈ Y ∧ ∀ j, P₂ₖ₊₄((c∘δᵢ)∘δⱼ) ∈ Y] | `heven_inf_all : ∀ k c, GenPosN c → ∀ i, ∃ Y, IsGCircleS Y ∧ EptInf (2k+6) c ∈ Y ∧ ∀ j, EptInf (2k+4) ((c∘i.succAbove)∘j.succAbove) ∈ Y` |
| 4 | ∀ n≥1 [(∀ c, GP ⇒ ∃ X⊆ℂ, FPClₙ) ⇔ n ≤ 5] | `cliffordChain_iff (n) : CliffordChain n ↔ n ≤ 5` |
| 5 | GP(c₆) ∧ ¬[∀ c, GP ⇒ ∃ X⊆ℂ, FPCl₆] | `cx_genPosN`; `not_cliffordChain_six : ¬ CliffordChain 6`; `not_cliffordChain_of_six_le : 6 ≤ n → ¬ CliffordChain n` |
| 6 | Cl₆({∞},c₆) ∧ ∀ X, Cl₆(X,c₆) ⇒ X = {∞} | `chainS_six : ChainS 6 Counter6.cx {∞}`; `chainS_six_unique` |
| 7 | ∀ c (3 centres) [GP ⇒ ∃ Y, ∀ pairs, pᵢⱼ ∈ Y] | `cliffordChain_threeS : CliffordChainS 3` |

**Verdict: 7 of 7 restatements are faithful.** For every row the restatement's quantifier order,
carrier (sphere vs plane), article (∃ vs the canonical point) and conjunct structure match the
signature. The instrument independently reproduced the two things the prose does *not* spell out but
the Lean does: the canonical point is a determinate function of the configuration (rows 2–3), and
`GP` includes the second, non-collinearity clause, without which level 3 would allow a line (row 7).

## 2. Two notes (neither is a defect in the draft)

1. **Row 3, index range of `j`.** The instrument recorded an `AMBIGUITY`: `j` could be read as an
   original index in `{1,…,2k+6}\{i}` rather than an index of the deleted configuration. The draft
   §2.4 says "for every index `j` of the configuration obtained by deleting `c i`", which is the
   deleted-configuration reading and matches `Fin (2k+5)`. The text is correct; the ambiguity is in
   the arithmetic of indices, and a one-word tightening ("index `j` of the remaining `2k+5`") would
   remove it.
2. **Row 5, strength.** The instrument read the second conjunct as `¬[∀c, GP ⇒ ∃X]` — the failure of
   the *universal* level-6 predicate — and not as "the fixed six-centre configuration has no level-6
   object". That is exactly right against `not_cliffordChain_six`, and the draft's §2.2 narration
   ("the level-6 object is `{∞}`") does not contradict it, but a reader can slide from the narration
   to the stronger statement. The v0.2 restatement carried the same warning as its `TRAP` line.

## 3. Verbatim instrument output

See `layer13/run6/l14_bigpickle.log` (sha256 in `layer13/run6/SHA256SUMS`). It is the seven blocks
quoted in condensed form in §1; no statement is missing, merged or split.

## 4. Layer verdict

**PASS on v0.7.** The seven statements of the current draft, read blind, formalise to the seven Lean
signatures. The differences the layer exists to catch — quantifier hoisting, indefinite article,
carrier, missing conjunct — are absent, and the two items recorded above are wording notes for v0.8,
not content defects. The comparison remains one-directional in the sense of §5.3 of the draft: this
layer tests that the prose *means* what the Lean says; it does not prove the bridge, which is layer
13's job and is closed for rows S6/S7 only.
