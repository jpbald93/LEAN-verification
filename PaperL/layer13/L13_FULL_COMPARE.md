# Layer 13 Full Normalised Comparison

The blind propositions below preserve the writer's definitions and quantifiers verbatim. The real
propositions universally close the paired library theorem types.

| row | writer type | paired real theorem(s) and type(s) | B→R | R→B | verdict | evidence |
|---|---|---|---|---|---|---|
| 1 | `PaperLBlind_writer_v2.lean:89-90`: `∀ n, 1 ≤ n → ∀ c, BlindGenPos c → ∃ X, BlindClifford n c X` | `Clifford/MorleyKernel.lean:5592`: `cliffordChainS_inf (n) : 3 ≤ n → CliffordChainS n`; `Clifford/Mobius.lean:178`: `cliffordChainS_of_le_five : n ≤ 5 → CliffordChainS n` | **CLOSED** (`N1_BR`) | **UNCLOSED**: needs bridges `BlindGenPos c → GenPosN c` and `ChainS n c X → BlindClifford n c X` | **DIFFERENCE DEFINITIONAL** (`BlindGenPos`, `BlindSecond`, `BlindIsGCircle`, `BlindCliffordP`) | `N1_BR` splits at `3 ≤ n`; the real theorems cover both ranges. The converse reaches independently defined geometric predicates immediately. |
| 7 | `PaperLBlind_writer_v2.lean:147-151`: `∀ c, BlindGenPos c → ∃ Y, BlindIsGCircle Y ∧` incidence of the three `BlindSecond` points | `Clifford/Mobius.lean:181`: `cliffordChain_threeS : CliffordChainS 3` | **CLOSED** (`N7_BR`) | **UNCLOSED**: needs `GenPosN → BlindGenPos`, `second = BlindSecond` under transversality, and `IsGCircleS → BlindIsGCircle` for the produced circle | **DIFFERENCE DEFINITIONAL** (`BlindGenPos`, `BlindSecond`, `BlindIsGCircle`) | The real level-3 theorem is unconditional as a proposition and closes B→R. Unfolding its witness has the same three-incidence shape but library predicates. |
| 6 | `PaperLBlind_writer_v2.lean:141-143`: `BlindClifford 6 BlindSix {∞} ∧ ∀ X, BlindClifford 6 BlindSix X → X = {∞}` | `Clifford/Mobius.lean:651`: `chainS_six : ChainS 6 Counter6.cx {∞}`; `:734`: `chainS_six_unique : ChainS 6 Counter6.cx X → X = {∞}` | **CLOSED** (`N6_BR`) | **UNCLOSED**: needs `ChainS 6 Counter6.cx X → BlindClifford 6 BlindSix X` and the converse to transfer uniqueness | **DIFFERENCE DEFINITIONAL** (`BlindCliffordP`, hence `BlindSecond` and `BlindIsGCircle`) | `BlindSix` and `Counter6.cx` are the same vector. The paired real existence and uniqueness theorems prove RealN6 without the blind premise; no recursive-predicate bridge exists. |
| 2 | `PaperLBlind_writer_v2.lean:98-102`: `∀ k d, BlindGenPos d → ∃ Y, BlindIsGCircle Y ∧ ∀ i, (∃ p, BlindClifford ... {p}) ∧ ∀ p, BlindClifford ... {p} → p ∈ Y` | `Clifford/MorleyKernel.lean:4643`: `hodd_inf_all' : ∀ k d, GenPosN d → ∃ Y, IsGCircleS Y ∧ ∀ i, EptInf ... ∈ Y` | **CLOSED** (`N2_BR`) | **UNCLOSED**: needs all blind/library definition bridges and a theorem that every certified even-level point lies on the selected `Y`; uniqueness cannot supply it because general `UniqEven` is false | **DIFFERENCE REAL** (universal incidence versus canonical `EptInf`; also definitional gaps) | The real theorem proves RealN2 independently. It certifies incidence of one canonical point, not the writer's universal incidence over every certified singleton. |
| 3 | `PaperLBlind_writer_v2.lean:111-117`: for each `k,c,i`, one `Y` with existence plus universal incidence for the level `2k+6` parent and every twice-deleted level `2k+4` singleton | `Clifford/MorleyKernel.lean:5586`: `heven_inf_all : ∀ k c, GenPosN c → ∀ i, ∃ Y, IsGCircleS Y ∧ EptInf (2k+6) c ∈ Y ∧ ∀ j, EptInf (2k+4) (...) ∈ Y` | **CLOSED** (`N3_BR`) | **UNCLOSED**: needs definition bridges and universal incidence for every certified parent and child singleton; false general uniqueness cannot identify them all with `EptInf` | **DIFFERENCE REAL** (universal incidence at two levels versus canonical `EptInf`; also definitional gaps) | `heven_inf_all` proves RealN3 independently. Canonical chain certificates provide existential witnesses only, not either universal clause. |
| 5 | `PaperLBlind_writer_v2.lean:132-136`: blind general position of `BlindSix`; no `BlindClifford 6` top set contained in `BlindPlane`; and failure of universal `BlindCliffordFin` existence for every `n ≥ 6` | `Clifford/Counter6.lean:33`: `cx_genPosN`; `:227`: `not_cliffordChain_six`; `Clifford/Classify.lean:219`: `not_cliffordChain_of_six_le : 6 ≤ n → ¬ CliffordChain n` | **CLOSED** (`N5_BR`) | **UNCLOSED**: needs `GenPosN cx → BlindGenPos BlindSix`, translation between plane `Chain` and both top-contained `BlindClifford` and recursively restricted `BlindCliffordFin` | **DIFFERENCE DEFINITIONAL** (plane encoding and blind predicates) | The three real results prove RealN5 independently. Writer clause two restricts only the top sphere object, while clause three restricts every recursive level; neither is the real plane predicate definitionally. |
| 4 | `PaperLBlind_writer_v2.lean:122-123`: `∀ n, 1 ≤ n → ((∀ c, BlindGenPos c → ∃ X, BlindCliffordFin n c X) ↔ n ≤ 5)` | `Clifford/Classify.lean:227`: `cliffordChain_iff (n) : CliffordChain n ↔ n ≤ 5` | **CLOSED** (`N4_BR`) | **UNCLOSED**: for each `n ≥ 1`, needs equivalence of universal blind finite-plane existence and `CliffordChain n`, including `BlindGenPos`/`GenPosN` and recursive plane/sphere translation | **DIFFERENCE DEFINITIONAL** (`BlindCliffordFin` plane encoding; `BlindIsGCircle` radius restriction) | The real classification proves RealN4 independently, including `n = 0`. The blind side is sphere-valued with containment at every recursion node; real `Chain` is plane-valued. |

## Row 1

Both statements assert existence of a sphere-valued level object, but under different general-position
and recursive-object definitions. The real pairing covers all `n ≥ 1`: `cliffordChainS_inf` handles
`n ≥ 3`, while `cliffordChainS_of_le_five` handles the remaining `n = 1,2`. Thus B→R closes even
without using its blind hypothesis. R→B needs geometric equivalences for transversality, second
intersection, triple general position and generalized circles, followed by an induction relating
`BlindCliffordP false` to `ChainS`; today's library has no such blind-definition bridge.

## Row 7

The writer directly asks for one blind generalized circle through the three chosen geometric second
intersections. `CliffordChainS 3` unfolds to a library generalized circle through the three
algebraic `second` values (with deletion order reversed but `second` symmetric under the relevant
hypotheses). B→R closes using `cliffordChain_threeS`. R→B needs the full general-position bridge,
identification of `BlindSecond` with `second`, and conversion of the resulting `IsGCircleS`; these
are mathematical lemmas not currently supplied by the library. The strict `0 < r` in
`BlindIsGCircle` is also stronger than the real circle branch, which allows any radius.

## Row 6

The two statements have exactly the same top-level existence-and-uniqueness shape and the six centre
vectors reduce to the same entries. B→R closes directly from `chainS_six` and
`chainS_six_unique`. R→B is not mere rewriting: the blind recursion uses the choice-based
`BlindSecond`, requires `BlindIsGCircle` in even-level child witnesses, and carries a redundant
vacuous plane conjunct. A bidirectional induction between `BlindCliffordP false` and `ChainS`, plus
the underlying second-point and generalized-circle lemmas, would close it; no such lemma exists.

## Row 2

The writer requires both existence of at least one even-level singleton for every deletion and
incidence of **every** such singleton on one blind generalized circle. The real theorem instead
places the canonical `EptInf` for each deletion on one `IsGCircleS`, and its type contains no
`ChainS` certificate. B→R closes because `hodd_inf_all'` already proves the real proposition.
R→B would first require all blind/library predicate bridges and canonical chain certificates from
`h4_pt_inf`/`heven_inf_all`; even those establish only one witness. The remaining universal clause
needs a direct universal-incidence theorem. Reducing it to equality with `EptInf` is invalid:
general even-level `UniqEven` is false, as checked in `scratch/not_UniqEven.lean`.

## Row 3

This is the same quantifier mismatch as row 2 at two places: the writer demands existence and
incidence of every certified singleton both for the full even-level configuration and for each
twice-deleted configuration. `heven_inf_all` names only the corresponding canonical `EptInf`
values. B→R closes directly from that theorem. For R→B, `h4_pt_inf` and `heven_inf_all` can build
canonical `ChainS` certificates, but after all absent definition bridges were supplied they would
still prove only the existential halves. Both universal halves need a new universal-incidence
result; they cannot be derived by the refuted general uniqueness principle.

## Row 5

The tuples `BlindSix` and `Counter6.cx` coincide, and the real side supplies general position,
level-6 failure, and failure for every `n ≥ 6`; hence B→R closes without its premise. The writer's
second conjunct is not merely `BlindCliffordFin 6`: it forbids a sphere-recursive blind object whose
**top** set lies in `BlindPlane`, whereas the third conjunct uses the recursion that imposes plane
containment at every level. Real `Chain` is plane-valued throughout. R→B therefore needs the
general-position bridge and two separate transport results relating plane `Chain` to these blind
sphere encodings. `liftS` and `coe_mem_liftS` bridge real `Chain` to real `ChainS`, but do not mention
the blind definitions, so today's library does not close the translation.

## Row 4

Both classifications have cutoff five, but classify different predicates. The writer ranges over
`n ≥ 1` and recursively stores sets in `OnePoint ℂ`, requiring each to be contained in
`BlindPlane`; consequently its odd-level line branch is impossible because it contains `∞`, and
its circle branch additionally requires `0 < r`. Real `CliffordChain` uses `Set ℂ` and
`IsGCircle`, whose circle branch has no positive-radius condition. B→R closes from
`cliffordChain_iff` alone (which also covers `n = 0`). R→B requires a new equivalence between
universal `BlindCliffordFin` existence and `CliffordChain` for each positive `n`, plus the
general-position bridge. Existing `liftS`/`coe_mem_liftS` do not establish that blind translation.

## Update 2026-11-25 — bridge layer (supersedes the R→B column for rows 7, 6, 1)

`layer13/BridgeBlind.lean` (sha256 `9cc060d7…`, compiles, 3 `sorry`s) now supplies the predicate
bridges. Signatures were diffed against the frozen skeleton: all eleven identical, nothing weakened.

- **Row 7 R→B: CLOSED in Lean.** `N7_RB` is proved and needs no hypothesis at all — `BlindN7` holds
  outright. Row 7 is now a two-directional Lean equivalence.
- **Row 6 R→B: HALF.** Uniqueness proved (`chainS_of_blind` + `BlindSix_eq` (`rfl`) +
  `chainS_six_unique`); existence still `sorry`, blocked on the radius-zero branch below.
- **Row 1 R→B: OPEN.** `BlindGenPos` is strictly weaker than `GenPosN` (concrete `n = 3` witness in
  `BRIDGE_NOTES.md`), so `RealN1` plus a transport cannot reach `BlindN1`. `blindOfChainS` is also
  still open: `IsGCircleS` allows `r = 0` (finite singleton) where `BlindIsGCircle` does not.
- Rows 2, 3, 4, 5 unchanged.

Detail: `layer13/L13_BRIDGE_STATUS.md`.

## Update 2026-11-25 13:05Z — row 6 closed

The second pass on `layer13/BridgeBlind.lean` (sha `f3819d69…`, 829 lines, compiles, 2 `sorry`s)
closed the existence half of `N6_RB` by an explicit per-level construction over the fixed
`BlindSix = Counter6.cx`: level 6 as the even singleton `{∞}`, the six level-5 children by
`blindCliffordP5_of_chainS`, and every level-4 child as a finite singleton via fifteen concrete
`chainS4_finite_XXXX` lemmas covering all four-subsets of `Fin 6`. `#print axioms N6_RB` is std.
**Row 6 is now closed in both directions**, like row 7. Rows 2, 3, 4, 5 and 1 are unchanged; S1 remains
the only definitional row whose real ⇒ writer direction has no proof, and its obstruction is the
`BlindGenPos`/`GenPosN` gap, not a missing bridge.

## Update 2026-11-25 15:50Z — S1 direct proof, first pass

`layer13/BlindChain.lean` (sha `3a05d805…`, compiles, 2 `sorry`s) proves the writer's level-3
object for every `BlindGenPos` triple (`blindChain_three`, collinear branch included) and the
level-4 object whenever all four triples are non-degenerate (`blindChain_four_of_genPos4`).
Still open, with named obstructions: the mixed-degenerate level-4 branch (a `cD` identity for a
collinear triple) and all `n ≥ 5` (a degenerate Clifford second theorem). Row 1 therefore remains
open — nothing in `L13_BRIDGE_STATUS.md`'s row-1 verdict changes.

## Update 2026-11-25 16:58Z — S1 level 4 closed

`layer13/BlindChain.lean` (sha `85fe68f5…`, 927 lines, compiles exit 0, **1 `sorry`**) now proves
`blindChain_four`: the level-4 blind object exists for every `BlindGenPos` quadruple, including the
mixed-degenerate case where some triples have collinear second points. Route: generic case reuses
`blindChain_four_of_genPos4`; exactly-one-degenerate goes through the new
`miquel_gcircles_of_one_degenerate` (+ `degenerate_gcircle_of_cycP_zero`); all-degenerate takes
`p = ∞`; two degenerate triples is impossible under `BlindGenPos`. Standard axioms only, signature
byte-identical to the pre-run file. **The `cD` identity proposed in the 15:50Z update is false**
(sympy counterexample `cD = 256/5`) and was not used — that target is retired.

Row 1 verdict unchanged in kind but narrowed: levels 1–4 proved, the open part is now the `n ≥ 5`
induction alone (a degenerate Clifford second theorem plus the transport). Rows 2/3 and 4/5
unchanged; rows 6 and 7 unchanged (both closed).

## Update 2026-11-25 17:45Z — S1 level 5 (general position + finite Miquel) and the all-n reduction

`layer13/BlindChain.lean` (sha `6d5bfe5d…`, 1296 lines, exit 0, **1 `sorry`**) now proves level 5
under `Clifford.GenPosN` (`blindChain_five_of_genPos5`), level 5 for every `BlindGenPos` 5-tuple in
which no deletion has four degenerate triples (`clifford_two_clean_blind` +
`blindChain_five_of_finite_miquel`), and the all-`n` induction `blindN1_direct` — with its single
remaining `sorry` isolated in `blindClifford_second`, the per-level statement "the `m` level-`m`
objects of the deletions lie on one blind generalized circle (odd case) / are concurrent (even
case)". All new lemmas except that one are on standard axioms; the statements of levels 1–4 are
unchanged.

Consequence for row 1: the paper can now say S1 is proved through level 5 and that the all-`n`
statement reduces to one named lemma, with the degenerate all-four-triples case (`mD = 0`,
level-4 object `∞`, line + `∞` as the level-5 object) the concrete instance that is checked
numerically in `run5/BRIDGE_REPORT5.md` but not yet proved.
