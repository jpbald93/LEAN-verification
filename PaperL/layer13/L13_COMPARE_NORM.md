> **Correction (2026-11-24, v0.3 pass).** This record stands as what was run, with three corrections
> established after the paper's review round: (i) the blind writer's own N2/N3 are **universal-incidence**
> statements (`∃p ∧ ∀p`, `~/reformal/PaperLBlind.lean:98–118`); the rows below restate them in
> **existential** form, so the table is a comparison against a re-typed proposition, not against the
> writer's statement; (ii) `N2_RB` uses `hodd_inf_all'` together with `h4_pt_inf` and `heven_inf_all`, so it
> is not a consequence of that row's theorem alone; (iii) `UniqEven` is **not open but false**
> (`AFM/PaperL/check/not_UniqEven.lean`, rc 0 in about 28 s, std axioms), so "strictly stronger unless `UniqEven`
> holds" must be read as "the converse route is dead", not as a pending equivalence. Only N1–N3 of the seven
> rows were compared. See `AFM/PaperL/L13_REPORT.md` (corrected) and DRAFT.md §5.3.

# Layer 13 stage 4b (narrow): definition-normalised comparison

Blind statements with the library's `GenPosN`, `ChainS`, `IsGCircleS` substituted, in
`scratch/BlindCompareNorm.lean` (`lake env lean` exit 0, no sorry/admit/native_decide/axiom).
Library theorems enter only as hypotheses whose types are read with `type_of%`; no library proof body is invoked.

| row | B→R | R→B | result | reason |
|---|---|---|---|---|
| N1 | closed (`N1_BR`) | closed (`N1_RB`) | EQUIVALENT | Same `∃ X, ChainS n c X` over `GenPosN`. Real is `n ≥ 3` only; the blind `n = 1, 2` cases hold by `rfl` (`ChainS 1/2` is an equation that names `X`). |
| N2 | NOT closed; the `N2_BR_of_uniq` route needs `UniqEven` (false) | closed (`N2_RB`), from `hodd_inf_all'`, `h4_pt_inf`, `heven_inf_all` | ONE DIRECTION | The blind form needs each `p_i` to be a certified level object. The real form names `EptInf`, and `canon_chain` shows `EptInf` is certified. The converse needs `p_i = EptInf`, which is a uniqueness claim. |
| N3 | NOT closed; the `N3_BR_of_uniq` route needs `UniqEven` (false) | closed (`N3_RB`), from `heven_inf_all`, `h4_pt_inf` | ONE DIRECTION | Same pattern, at both the parent point and the grandchild points. |

`UniqEven` is the statement: `GenPosN d → ChainS (2k+4) d {p} → p = EptInf (2k+4) d`, for every `k`.
It is not proved here; it was later refuted (`AFM/PaperL/check/not_UniqEven.lean`).

## N2 / N3 question

The two versions are different claims, and the canonical one is the stronger. The R→B direction is
proved. It uses the induction `canon_chain`, which rebuilds `ChainS (2k+4) c {EptInf ..}` from `h4_pt_inf`
and `heven_inf_all`. The existential statement is then witnessed by the canonical points and the same `Y`.
Note that `hodd_inf_all'` alone (the literal real N2) does not give a `ChainS` certificate for `EptInf`.
The certificate comes from `h4` plus `heven`, so R→B for N2 uses the whole real package and not only the
row's theorem. B→R fails to go through by unfolding. Blind N2/N3 only say that some certified singleton lies
on `Y`, and nothing identifies it with `EptInf`. The bridge is exactly `UniqEven`, uniqueness of the
even-level Clifford point. I did not check whether uniqueness is available at any level other than the `Counter6` level-6 instance
(`chainS_six_unique`). It is not established in general here. So I have not shown a
counterexample to B→R. I report that B→R is open. The earlier sentence "strictly stronger unless `UniqEven` holds" is
withdrawn: `UniqEven` is false, so that route to equivalence is unavailable, and what is proved is the
one-directional implication canonical ⇒ existential. Both blind statements are true as propositions, because both are implied by the real
theorems. So "B→R" is only informative as a derivation from the blind statement alone, which is what was tested.

## `sha256sum Clifford/*.lean`

Before and after are identical (verified by `diff`):

```text
d5c14edbf2da8ec8288484b4eeee54e30e85cf04e5c440c406b4c7144ca0cb16  Clifford/Basic.lean
097722f3d2ff994965dcb1ccff5180d8a62404ea3dfc362bef345934c1ab6054  Clifford/BridgeL10.lean
93eb80b639791dc7e271249a79e0439dd3fd08c831eb71e367129c52c8cecf5b  Clifford/Bridge.lean
ba4fc1b3c567f5d69ca33ea2bcbab0dfaed3a54a779e3405efdb4241be65b83b  Clifford/Classify.lean
2a7cf40b4c473e56c97db8b1485aa5ad468c9cbb5c9a56b5b7ac9adaf33cc463  Clifford/Clean.lean
d6bf1cc913841fd487c539c61e4db62054e62d4b861af3a3cb9eaac8cf35d57a  Clifford/Counter6.lean
90b42ad2f407f49b7ebc955573af3823727cef5403047ccd2467222afd36eeff  Clifford/General.lean
f8c9f013188f7767b8c2f5850b0f761cfb689d0e490a782d5c9e10ddaec83200  Clifford/Mobius.lean
dce7b011a8f224699f7ea1e879a159fc8066e15f3cb8c6e7664c03a779990a76  Clifford/MorleyKernel.lean
```
