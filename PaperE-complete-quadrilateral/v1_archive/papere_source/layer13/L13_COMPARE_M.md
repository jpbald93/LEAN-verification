# L13 COMPARE (M): blind_7..blind_10 vs the real QuadMiquel statements

Blind file: `scratch/PaperEBlind.lean` (copied from jack `~/reformal/PaperEBlind.lean`, read-only reference)
Scratch file: `~/lean/quadmiquel_l13/scratch/L13_compare.lean` (`import QuadMiquel`). The Blind definitions are copied verbatim into namespace `Blind`. Each `blindK_stmt : Prop` is `∀ L₁ L₂ L₃ L₄ : BlindLine, BlindGenPos … → <verbatim conclusion>`. The real side is `type_of% @<RealDecl>`.

## Results

| pair | R→B | B→R | difference | note |
|---|---|---|---|---|
| blind_7 / `QuadMiquel.miquel` | ✅ `rb_7` | ✅ `br_7` | none | Same radius convention: in both, each sphere is centred at `circ T` with radius `dist (first vertex) (circ T)`. Triangle vertex orders match: T₁=(A23,A24,A34), T₂=(A13,A14,A34), T₃=(A12,A14,A24), T₄=(A12,A13,A23). The `-- AMBIGUOUS` radius comment does not matter here. Proof: premise + `genPos_agree`; the rest is closed by defeq. |
| blind_8 / `QuadMiquel.steiner_circle` | ✅ `rb_8` | ✅ `br_8` | none | Same 5-point set in the same order (circ T₁..T₄, Miquel point), and the same `EuclideanGeometry.Cospherical`. |
| blind_9 / `QuadMiquel.simson` | ✅ `rb_9` | ✅ `br_9` | none | Same `Collinear ℝ` of the 4 feet from the Miquel point. Rewriting with `miquel_agree`/`foot_agree` was needed only to avoid a whnf heartbeat timeout; mathematically it is still pure defeq. |
| blind_10 / `QuadMiquel.steiner_parallel_line` | ✅ `rb_10` | ✅ `br_10` | none | Same `line[ℝ, F₁, F₂].Parallel (affineSpan ℝ {H₁,H₂,H₃,H₄})`. The H_k unfold to the same `ortho` triples as the real statement, in the same order. |

All 8 directions were proved. No DIFFERENCE was found (no REAL, no ARTEFACT, no SAFE-generality gap). The pairing table looks correct.

The blind `GenPos` has an `-- AMBIGUOUS` comment about which pair to pick within each concurrency triple. It turned out to be harmless: the blind choice (12∉3, 12∉4, 13∉4, 23∉4) is exactly the real `GenPos` fields c123, c124, c134, c234.

## Agreement lemmas used (all in the scratch file)
The map is `toL L := ⟨L.p, L.d⟩ : QuadMiquel.Line`, with inverse `ofL`, and `toL_ofL : toL (ofL L) = L` (rfl).
- `cr_agree : BlindCr = cr` — rfl
- `carrier_agree : L.carrier = (toL L).carrier` — rfl
- `meet_agree : BlindMeet L M = meet (toL L) (toL M)` — rfl
- `circ_agree : BlindCirc = circ` — rfl
- `ortho_agree : BlindOrtho = ortho` — rfl
- `foot_agree : BlindFoot z L = foot z (toL L)` — rfl
- `miquel_agree : BlindMiquel = miquelPt ∘ toL` — rfl
- `circumcircle_agree : BlindCircumcircle (a,b,c) = sphere (circ a b c) (dist a (circ a b c))` — rfl (the radius convention is identical to the real `miquel`)
- `genPos_agree : BlindGenPos ↔ GenPos (toL …)` — field-by-field repackaging of the 14 conjuncts into the 14 structure fields

Every agreement holds definitionally. No repository theorems and no Bridge.lean lemmas were used. Proof bodies use only the premise, the lemmas above, `rw`/`simp only` with them, and `exact`.

## Checks
- Compile: `cd ~/lean/quadmiquel_l13 && ~/lean/jl lake env lean scratch/L13_compare.lean` → **exit 0** (no errors or warnings).
- `#print axioms` (run in a temporary copy, since deleted) for all 8 theorems and `genPos_agree`: `[propext, Classical.choice, Quot.sound]` only.
- `grep -nE "sorry|admit|native_decide|axiom" scratch/L13_compare.lean` → one hit, line 5, inside the module doc comment ("sorry'd theorems replaced by …"). There are none in code.
- Library hash before: `6d8896a0d9412b802c6652a3f1fd894ad25fbab727ea5a729ca07dd9c6f945e8`
- Library hash after:  `6d8896a0d9412b802c6652a3f1fd894ad25fbab727ea5a729ca07dd9c6f945e8` (unchanged)

## Files
- `~/lean/quadmiquel_l13/scratch/L13_compare.lean`
- `~/lean/quadmiquel_l13/scratch/PaperEBlind.lean` (reference copy)
- `~/lean/quadmiquel_l13/L13_COMPARE_M.md` (this report)
