> **Correction (2026-11-24, v0.3/v0.4 pass).** This record is what stage 4a ran, with one provenance
> correction: although it used the writer's definitions, it did **not** use all the writer's
> propositions. `BlindCompare.lean:89–107` already replaced the two universal-incidence payloads by
> existential ones, and its `blind_5` (`:129–131`) omits the writer's final
> `∀ n, 6 ≤ n → …` clause present at `reformal/PaperLBlind.lean:132–136`. The stage-4b record
> (`L13_COMPARE_NORM.md`) carries its own correction. Both stages therefore compared reconstructed
> propositions; the full seven-row comparison against the writer's real types is
> `L13_FULL_COMPARE.md`.

# Layer 13 Statement Comparison

| pair | B→R | R→B | result | one-line reason |
|---|---|---|---|---|
| S1 | stopped | stopped | DIFFERENCE REAL | The independently defined general-position and recursive-object predicates require geometric bridge theorems in both directions. |
| S2 | stopped | stopped | DIFFERENCE REAL | Blind S2 existentially chooses certified level objects, while real S2 names `EptInf` without a `ChainS` certificate, in addition to predicate-definition gaps. |
| S3 | stopped | stopped | DIFFERENCE REAL | Blind S3 existentially chooses certified parent and grandchild objects, while real S3 states incidence of the canonical `EptInf` points. |
| S4 | stopped | stopped | DIFFERENCE ARTEFACT | The blind finite-plane recursion lives in `OnePoint ℂ` and enforces plane containment at every level, whereas real `Chain` is plane-valued; this follows the recorded finite-plane redaction choice. |
| S5 | stopped | stopped | DIFFERENCE ARTEFACT | Blind S5 forbids a sphere object whose top set lies in the plane, while the real pair negates the global finite-plane `CliffordChain 6`; this is the recorded Statement 5 redaction choice. |
| S6 | stopped | stopped | DIFFERENCE REAL | The six centres are definitionally the same tuple, but `BlindClifford` and `ChainS` use distinct intersections, generalized-circle predicates, and recursion. |
| S7 | stopped | stopped | DIFFERENCE REAL | Blind S7 directly states incidence of `BlindSecond` points; real S7 is recursive `ChainS 3` using algebraic `second` and `IsGCircleS`. |

## Difference Details

### S1

Neither direction is proposition repackaging. `BlindGenPos` uses unique geometric intersections and explicit triple incidence conditions, whereas `GenPosN` uses algebraic `Transversal` and `GenTriple`. The object predicates also use separate second-intersection and generalized-circle definitions. Neither side is logically stronger without genuine bridge mathematics. Classification: **REAL**.

### S2

The blind statement says that for each deletion there exists some singleton carrying a recursively certified blind level object and lying on the chosen generalized circle. The real theorem instead puts the canonical `EptInf` value on an `IsGCircleS`, without including a `ChainS` certificate in this theorem's type. Recovering either formulation from the other needs substantive existence, identification, and definition-bridge results. Classification: **REAL**.

### S3

The same canonical-versus-existential distinction occurs at both the parent level and the twice-deleted level. Blind S3 includes recursive object certificates; real S3 only records incidences of `EptInf`. Neither implication follows by unfolding and repackaging. Classification: **REAL**.

### S4

Blind `BlindCliffordFin` recursively uses sphere-valued sets and adds `X ⊆ BlindPlane` at every level. Real `CliffordChain` uses plane-valued `Chain` directly. The blind generalized-circle definition also forces a finite-plane odd object to be a Euclidean circle because its line branch contains `∞`; this is exactly the ambiguity recorded at `PaperLBlindDefs.lean:84-85`. Real S4 additionally includes `n = 0`, but that extra range does not overcome the predicate mismatch. Classification: **ARTEFACT**.

### S5

Following `PaperLBlindDefs.lean:100-102`, blind S5 means that no sphere-chain top object is contained in the plane; it does not mean failure of `BlindCliffordFin`, whose lower levels are also plane-restricted. The real theorem pair states `GenPosN cx` and global failure of `CliffordChain 6`. This mismatch traces directly to the documented redaction choice. Classification: **ARTEFACT**.

### S6

`BlindSix` and `Counter6.cx` reduce to the same vector, and both uniqueness clauses have the same logical shape. Their object predicates are not definitionally related, however: they recurse through independent notions of second intersection and generalized circle, with an additional blind generalized-circle witness restriction. Bridging them is genuine mathematics. Classification: **REAL**.

### S7

At level three, unfolding exposes similarly shaped incidence claims, but the points are `BlindSecond` versus the algebraic `second`, the circle predicates differ, and the general-position hypotheses differ. Those identities require geometry rather than repackaging. Classification: **REAL**.

## Unattempted Pairs

None. All seven proposition pairs were restated and inspected. Every implication hit the mandated genuine-mathematics stop condition before a valid proof body could be written.

## Clifford Hashes

Before:

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

After:

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

The before and after hash lists are identical.
