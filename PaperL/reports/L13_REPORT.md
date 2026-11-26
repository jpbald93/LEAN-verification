# Layer 13 — blind re-formalisation of Paper L (report)

**Run 2026-11-24** on `jack` (Mathlib-only project `~/reformal` for the blind side, `~/paperL_jack` for
the real side). **Corrected 2026-11-24 (v0.3 pass)** after the paper's review round: the stage-4b
section below now reports what was compared rather than what was assumed, and stage 5 records that
`UniqEven` has since been *refuted*, not left open.

The point of the layer is the interpretation gap that layers 1–9 cannot see: they show the proofs are
accepted and use no non-standard axioms, but they do not certify non-vacuity (layer 8's satisfiability
pass was disabled by `--fast`, and layer 5 is a failed proof search), and none of them shows that the
Lean *says* what the prose says.

Input instrument: `AFM/PaperL/DRAFT_blind.txt` — a prose-only reduction of `DRAFT.md` §1–§2: no Lean
identifiers, no file names, no code, seven numbered statements (the chain; the two payloads; the
finite-plane classification; the six-centre counterexample; its sphere repair; the level-3 base).
The blind text says "**the** point which is the Clifford object of level 2k+4 [resp. 2k+6]", with the
definite article; that is the sentence the whole layer turns on (see stage 4b).

## Stage 1 — the blind text itself (a finding)

The first blind text was **wrong**: its clauses 4–5 inverted the parity of the chain recursion (even
levels a circle, odd levels a point) while the code — and the draft's own §2.5 — has odd levels a
circle and even levels a point. The blind writer of stage 2 detected the inconsistency from the text
alone (it observed that level 3 would need a level-2 object that is a circle, which cannot exist) and,
as instructed, formalised the text *literally* rather than silently repairing it: seven statements,
`lake env lean` rc 0, seven `sorry` warnings, with a `-- PARITY WARNING` block in the header.

That is a defect of the instrument, not of the paper, and it is reported as such. `DRAFT_blind.txt` was
corrected, the blind writer re-run from the corrected text, and the v1 file is kept at
`AFM/PaperL/layer13/PaperLBlind_writer_v1_parity.lean` (host copy:
`jack:~/reformal/PaperLBlind_v1_parity.lean.bak`) as evidence. Consequence for the paper: nothing in
§2 changed; consequence for the method: a blind writer that is asked to be faithful is also an
inconsistency detector, and the redaction step needs its own check.

## Stage 2 — the blind writer (v2)

Writer: `claude-opus-5-5` via `opencode run`, brief restricted to `BLIND.txt` plus the `~/reformal`
project's build files, explicitly forbidden from reading `~/paperL_jack`, `~/lean`, `~/clifford*` and
from any network search; self-report: it read nothing else. Deliverable `~/reformal/PaperLBlind.lean`
(packet copy: `AFM/PaperL/layer13/PaperLBlind_writer_v2.lean`): 7 statements `blind_1 … blind_7`,
each `:= by sorry`, 12 `Blind…` definitions, **5** `-- AMBIGUOUS:` annotations, `lake env lean`
**exit 0**, 7 `sorry` warnings only.

Its ambiguities are the interesting part: whether "the point which is the Clifford object" is
existential or universal; whether a generalized circle admits radius 0; whether "subsets of the plane
rather than of S" restricts every level or only the top object.

**How the writer resolved the payload ambiguity matters for stage 4b:** it formalised `blind_2` and
`blind_3` with **existence plus universal incidence** — `(∃ p, BlindClifford … {p}) ∧ ∀ p,
BlindClifford … {p} → p ∈ Y` (lines 98–118, self-report lines 30–37) — not with a bare existential.

## Stage 3 — pairing (done here, not by either model)

| paper statement | blind | real |
|---|---|---|
| S1 chain, all n | `blind_1` | `cliffordChainS_inf` (n ≥ 3) + `cliffordChainS_of_le_five` (n ≤ 5) |
| S2 odd payload | `blind_2` | `MorleyKernel.hodd_inf_all'` |
| S3 even payload | `blind_3` | `MorleyKernel.heven_inf_all` |
| S4 finite-plane iff | `blind_4` | `cliffordChain_iff` |
| S5 six-centre failure | `blind_5` | `Counter6.cx_genPosN` + `Counter6.not_cliffordChain_six` |
| S6 sphere repair | `blind_6` | `Mobius.chainS_six` + `chainS_six_unique` |
| S7 level 3 | `blind_7` | `CliffordChainS 3` |

## Stage 4a — comparison as written (`gpt-5.6-sol`)

Result: **0 EQUIVALENT, 5 DIFFERENCE REAL, 2 DIFFERENCE ARTEFACT**, compile exit 0. Every row stopped on
the same obstacle: the blind writer's own definitions (`BlindSecond` as a unique geometric
intersection, `BlindIsGCircle` with `0 < r`, `BlindGenPos` with explicit triple incidence) are not
definitionally the library's (`second`, `IsGCircleS`, `GenPosN`), so no direction is repackaging. S4
and S5 were classified ARTEFACT (the finite-plane encoding was the redaction's choice, not the paper's).
Files: `AFM/PaperL/layer13/L13_COMPARE.md` and `BlindCompare.lean` (host:
`jack:~/paperL_jack/scratch/`).

This is a definitional-divergence result, not a statement-divergence result, and it says so.

## Stage 4b — definition-normalised comparison (`claude-sonnet-5-5`)

**What was actually done, stated precisely.** The stage-4b pass re-stated N1–N3 with the library's
predicates substituted and — for the two payloads — **replaced the writer's universal-incidence
clauses by existential witnesses** (`∃ p, ChainS … {p} ∧ p ∈ Y`). So:

* "structure untouched" is **withdrawn**: the payload rows were not the writer's statements.
  `BlindCompare.lean` and `BlindCompareNorm.lean` (`jack:~/paperL_jack/scratch/`) carry the existential
  form; `~/reformal/PaperLBlind.lean` carries the universal one.
* Only **N1–N3 of the seven rows** were compared in normalised form; S4–S7 were not re-run in stage 4b.
* The names below are the file's own (`N1_BR`, `N1_RB`, `N2_RB`, `N3_RB`); `N2_RB` is derived from
  `hodd_inf_all'`, `h4_pt_inf` and `heven_inf_all` — the whole package, not that row's theorem alone —
  and `N3_RB` from `heven_inf_all` and `h4_pt_inf`.

Result, compile exit 0:

| row | B→R | R→B | result |
|---|---|---|---|
| N1 (chain, all n) | closed | closed | **EQUIVALENT** (real covers n ≥ 3; the blind n = 1, 2 cases are equations in `X`, discharged by `rfl`) |
| N2 (odd payload, existential restatement) | open | closed | **canonical ⇒ existential proved; converse open** |
| N3 (even payload, existential restatement) | open | closed | **canonical ⇒ existential proved; converse open** |

The N2/N3 finding is the layer's real output, in this corrected form: the reference theorem names the
canonical point `EptInf (2k+4) …`, so it implies the existential restatement (the canonical witness is
a witness). The converse needs a derivation that the existential witness *is* `EptInf` — the candidate
route is

    UniqEven : GenPosN d → ChainS (2k+4) d {p} → p = EptInf (2k+4) d,

and **UniqEven is false** (stage 5). "Strictly stronger" is therefore withdrawn as a comparison
result: what is proved is the implication in one direction plus the failure of the uniqueness step the
other direction was thought to need. The writer's actual universal-incidence reading was never
compared; under it the counterexample of stage 5 is a configuration in which two certified level-6
points (`{4i}` and `{∞}`) would both have to lie on `Y`.

## Stage 5 — what the paper must do with it (corrected)

1. §2.3/§2.4 must say that the payload theorems name the canonical point, not merely "a point", and
   that the chain certificates come from `h4_pt_inf` and the induction, not from the payloads alone.
2. The prose's definite article ("**the** point") presupposes uniqueness of the even-level object;
   `check/not_UniqEven.lean` shows that presupposition fails for `ChainS` (centres `2t − 2it²`, both
   `{4i}` and `{∞}` at level 6; rc 0 in about 28 s, **std** axioms; two runs: 27.6 s and 26.9 s). So the gap between the prose and the
   code is not closed by proving uniqueness — it cannot be. The paper states the canonical selection
   and the existential recursion instead, and says so in §5.4.
3. The stage-4a result stands as the record that a blind formalisation of *prose without definitions*
   will not be definitionally comparable: the layer only bites after predicate normalisation, and the
   first comparison should be read as a measure of the redaction's lossiness, not of the paper.

## Stage 6 — the full seven-row comparison against the writer's real types (2026-11-24)

Writer file: `reformal/PaperLBlind.lean` (its own `Blind…` definitions and quantifiers, unchanged).
Comparison: `layer13/L13_FULL_COMPARE.md`; witness file `layer13/BlindCompareFull.lean`
(host `jack:~/paperL_jack/scratch/BlindCompareFull.lean`), `lake env lean` exit 0 in 2.8 s, no
`sorry`/`admit`/`axiom`/`native_decide`, `sha256sum Clifford/*.lean` identical before and after.
Run by `gpt-5.6-sol` on jack; each row was compiled as it was added (STATUS record in
`layer13/L13_FULL_STATUS.md`).

| row | verdict on the writer's types | why |
|---|---|---|
| S1 chain, all n | DEFINITIONAL | real covers n ≥ 3 plus n ≤ 5; no `BlindGenPos ↔ GenPosN` or `BlindCliffordP ↔ ChainS` bridge |
| S2 odd payload | REAL difference (quantifier) | writer: existence + incidence of **every** certified point; real: incidence of `EptInf` only |
| S3 even payload | REAL difference (quantifier) | same at parent and grandchild levels |
| S4 finite-plane iff | DEFINITIONAL | blind finite-plane encoding lives on `OnePoint ℂ` with containment at every node; real `Chain` is plane-valued |
| S5 six-centre failure | DEFINITIONAL | blind clause 2 restricts the top object only, clause 3 restricts every level; neither is `CliffordChain` |
| S6 sphere repair + uniqueness | DEFINITIONAL | same six centres (`BlindSix = Counter6.cx`), different recursive predicate |
| S7 level 3 | DEFINITIONAL | blind `BlindSecond`/`BlindIsGCircle` versus `second`/`IsGCircleS` |

Because the real propositions are theorems, "writer ⇒ real" closes for all seven rows trivially and
says nothing about the paper. The informative direction, real ⇒ writer, is closed **nowhere**: the
definitional bridges the writer's types need do not exist in the library. Under predicate
normalisation (stage 4b) N1 is equivalent and the payload rows are one-directional; that remains the
only non-trivial implication proved in this layer.

## Verdict

**Layer 13: PASS AS A COMPARISON — all seven rows compared against the writer's real types; not a
faithful-preservation result.** Six rows (S1, S4–S7) differ only in definitions; S2/S3 differ in
quantifier form as well, and the uniqueness step that would reconcile them is false. No row shows a
mathematical divergence beyond that, and no non-trivial implication from the real theorem to the
writer's statement is available without a bridge layer:
`GenPosN ↔ BlindGenPos`, `second = BlindSecond` under transversality,
`IsGCircleS → BlindIsGCircle` away from point circles, and `ChainS ↔ BlindCliffordP false`. With
those, S1 and S4–S7 become decidable; S2/S3 additionally need a universal-incidence theorem, not
uniqueness. The parity defect of the instrument (stage 1) and the stage-4a/4b provenance corrections
(R-03 of the v0.3 review) stand as recorded. Second-machine reproduction was not attempted: john has
been unreachable since 2026-11-19.
