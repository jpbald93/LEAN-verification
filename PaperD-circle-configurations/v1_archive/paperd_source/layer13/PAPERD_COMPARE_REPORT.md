# PAPER D — Layer 13 comparer report (blind_1..blind_12 vs published Lean)

Machine: <user>@<host>, Lean v4.33.1, Mathlib pinned (no `lake update`, no cache get).
Each scratch file imports the repo root and copies the needed Blind definitions **verbatim**. The real
statement is used either as `type_of% @Decl` or restated verbatim as `realK_stmt` (checked by an
`example : realK_stmt := @Decl`, which only type-checks the statement and is not used in any proof).
No repository *theorem* is used in any rb_/br_ proof body. The only repo facts used are the
definitional and bridge lemmas listed below.

## Summary table

| pair | R→B | B→R | difference | note |
|---|---|---|---|---|
| blind_1 / Clifford.clifford_one | ✅ `rb_1` | ✅ `br_1` | none | `BlindP` is `secondInter` by `rfl`. `BlindOnCircum` (some equidistant centre) ↔ `∈ circumcircle` for non-collinear triples. Fin 4 indexing ↔ 4 named centres. |
| blind_2 / Clifford.clifford_two | ✅ `rb_2` | ✅ `br_2` | none | `BlindOnGenCircle (range P)` ↔ `Cospherical ∨ Collinear` (a degenerate direction `v = 0` becomes a radius-0 circle). |
| blind_3 / Clifford.clifford_two_explicit | ✗ (proved only conditionally: `rb_3_given_uniq`) | ✗ (proved only conditionally: `br_3_given_cp`) | ARTEFACT (the blind file's `-- AMBIGUOUS` cp line) | Blind quantifies over **any** common points `P k` of the four Γ. Lean uses the explicit `cliffordPoint`. R→B needs *uniqueness* of the common point (`uniq_stmt`, not proved anywhere, real geometry). B→R needs "cliffordPoint is a common point" (the statement of `Clifford.cliffordPoint_mem_gams`, i.e. Clifford's theorem itself). Both conditional implications compile with that premise as an explicit hypothesis. So the statements are incomparable at statement level. If the cp is unique they coincide. I did not establish uniqueness and have no counterexample. If some admissible configuration had all four Γ coincident (infinitely many cps), blind_3 would be strictly stronger than the Lean. |
| blind_4 / Clifford.clifford_three | ✗ (proved only conditionally: `rb_4_given_uniq`) | ✗ (proved only conditionally: `br_4_given_cp`) | ARTEFACT (same cp ambiguity) | Same any-cp vs explicit-cp gap as blind_3. Nothing else differs. **The guessed designated triples ("drop the 3 largest") match the Lean exactly for all six S**: lemmas `des0..des5` plus the compiled conditional proofs, which map `hnc` onto `m6..m1` and each `C_S` onto the Lean `circumcircle` triple. The "∀ T ⊆ S" clause covers exactly the five points the Lean lists. The "common point of the six C_S" clause matches `Q`. |
| blind_5 / Clifford.cliffordChain_four | ✅ `rb_5` | ✅ `br_5` | none | Object-valued `BlindChain` ↔ set-valued `Clifford.Chain`, translated level by level (3, 4). `BlindGeneralPosition` ↔ `GenPosN` via the bridge lemmas. Blind requires `i<j`; Lean requires `i≠j` (symmetry of `Transversal`). |
| blind_6 / Clifford.cliffordChain_five | ✅ `rb_6` | ✅ `br_6` | none | As above, level 5. Lean `IsGCircle` allows any radius; blind requires `r ≥ 0`. This is harmless because the circle contains a point. |
| blind_7 / Fivecircles.fivecircles | ✅ `rb_7` | ✅ `br_7` | none | Syntactically identical hypotheses and conclusion. |
| blind_8 / Lester.lester | ✅ `rb_8` | ✅ `br_8` | none | Blind works in `EuclideanSpace ℝ (Fin 2)`; Lean works in `ℂ`. Transported along `Complex.orthonormalBasisOneI.repr.symm` (an affine isometry equiv): `circumcenter_map`, `ninePointCircle_map`, side/line maps, `Isometry.cospherical`. Blind apex (equilateral + correct side of BC) ↔ Lean explicit `apexOut`/`apexIn` (`capex_iff`). Proved by elementary coordinates: an equilateral apex is `B+(C−B)ω` or `B+(C−B)ω̄`, and the side is the sign of `Im(conj(C−B)(z−B))`. Set order {O, N, F₁, F₂} vs {N, O, F₁, F₂}. |
| blind_9 / Thebault3.sawayama_thebault | ✅ `rb_9` | ✅ `br_9` | none | `BlindThebaultCentre t` = `IsThebaultCircle` with `tri A B C h = t`. |
| blind_10 / Kosnita.kosnita | ✅ `rb_10` | ✅ `br_10` | none | Blind uses `O ≠ midpoint` for non-collinear `{O,B,C}`. Equivalent because O is equidistant from B, C (`collinear_iff_midpoint`; the blind writer's AMBIGUOUS note is consistent). Blind uses lines `X ∈ line[A,Oa]`; Lean uses `Collinear {A,Oa,X}`. R→B needs `A ≠ Oa`, which follows from `hS` by a short algebraic lemma (`sumSq_of_eq`: Oa = A ⇒ AB²+BC²+CA² = 5R²), proved in the scratch file. Lean's `O` with `dist O A = dist O B = dist O C` ↔ `t.circumcenter` (`eq_circumcenter_of_dist_eq`). |
| blind_11 / Blundon.blundon | ✅ `rb_11` | ✅ `br_11` | none | `Blundon.semiperimeter` unfolds to the blind `s`. Same universe-polymorphic `V P`. |
| blind_12 / SteinerLehmus.steiner_lehmus | ✅ `rb_12` | ✅ `br_12` | none | `AffineIndependent ![A,B,C]` ↔ `¬Collinear` (`affineIndependent_iff_not_collinear_set`). `E ∈ affineSegment` is definitionally `Wbtw`. |

**Result:** 10/12 pairs are proved equivalent unconditionally in both directions. blind_3 and blind_4 differ
only by the known any-cp vs explicit-`cliffordPoint` gap (ARTEFACT, flagged AMBIGUOUS by the blind writer).
For each of them both directions compile *conditionally*, with the missing geometric fact as an explicit premise.
**No REAL difference was found**, and none of the pairings looks wrong.

## Bridge / definitional repo facts used (statement-level only)
- clifford: definitions `secondInter`, `gam`, `circumcircle`, `ccenter`, `cliffordPoint`. Lemmas
  `Clifford.mem_circumcircle_middle`, `Clifford.mem_circumcircle_right` (the circumcircle passes through its
  defining points), used in `eq_ccenter` / `onCircum_iff`. In the *conditional* theorems the type of
  `Clifford.cliffordPoint_mem_gams` appears only as a premise; the theorem itself is never applied.
- clifford_j: `Clifford.transversal_iff`, `Clifford.genTriple_iff` (Bridge.lean). Definitions `Chain`,
  `IsGCircle`, `GenPosN`, `CliffordChain`, `second`.
- lester: `Lester.bridge_ninePointCenter`, `Lester.bridge_apexIn`, `Lester.bridge_apexOut` (distance facts
  for the explicit apex). Definitions `ω`, `Ccw`, `apexOut`, `apexIn`, `IsFermatOuter/Inner`,
  `ninePointCenter`.
- Kosnita: `Kosnita.dist_sq`, `Kosnita.cross_of_collinear`, `Kosnita.collinear_of_cross` (coordinate
  descriptions of dist / Collinear).
- thebault3_j: definitions `IsThebaultCircle`, `tri` only. Blundon: definition `semiperimeter` only.
  SteinerLehmus, Fivecircles: none.

## Compile results (`cd ~/<repo> && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/<file>`)
| file | exit | errors | forbidden-token grep (sorry/admit/native_decide/axiom) |
|---|---|---|---|
| ~/Blundon/scratch/L13_blundon.lean | 0 | 0 | empty |
| ~/SteinerLehmus/scratch/L13_steiner.lean | 0 | 0 | empty |
| ~/Kosnita/scratch/L13_kosnita.lean | 0 | 0 | empty |
| ~/Fivecircles/scratch/L13_five.lean | 0 | 0 | empty |
| ~/lester/scratch/L13_lester.lean | 0 | 0 | empty |
| ~/thebault3_j/scratch/L13_thebault.lean | 0 | 0 | empty |
| ~/clifford_j/scratch/L13_chain.lean | 0 | 0 | empty |
| ~/clifford/scratch/L13_cliff4.lean | 0 | 0 | empty |
| ~/clifford/scratch/L13_cliff5.lean (blind_2) | 0 | 0 | empty |
| ~/clifford/scratch/L13_cliff5x.lean (blind_3, conditional) | 0 | 0 | empty |
| ~/clifford/scratch/L13_cliff6.lean (blind_4, conditional; ~2 min) | 0 | 0 | empty |

Warnings are only unused variables, unused simp args, and a `push_neg` deprecation. `L13_cliff5*.lean` and
`L13_cliff6.lean` use `set_option maxHeartbeats` for the big case splits. `decide` is the ordinary
elaborator `decide`, not `native_decide`.

## Repository library hashes (find *.lean excluding .lake and scratch | sort | sha256sum | sha256sum)
| repo | before | after |
|---|---|---|
| clifford | bb53ed5aa005078a6d9c3f24379c427f850b96e39f05e5268e7911601f29472a | same |
| clifford_j | d7464f13579e39d7a2696e19e2dbe409fd1e75703ddfd69a82e1f64c7964015e | same |
| Fivecircles | 1cddd210ca590ece1325206106d79b455e05b61de8fa10e8d6f71da22a474cbf | same |
| lester | 6e768745d69ddd3276f02f51e6d62e6bd4d1075c7907b64f8ecb6c47063f36c0 | same |
| thebault3_j | 06432c5a80ad20e9bf1289902c9aae64c3e9310d300600be83da0e0672b897c7 | same |
| Kosnita | e98f36b540e0288412b4d5e2ebbf80a7671d1256f95e52bcf4ab71eeb3a606c6 | same |
| Blundon | 89ec32d88994fac7ac8afb5802ca2d200c7bcf8d77f8f7e3008fda9bfe5e0729 | same |
| SteinerLehmus | feaf54dcf171b4eb7086aa4800c0f8e24b3ad4402acfa91a0664f0dfbf358813 | same |

(`~/clifford_j/scratch/` and `~/thebault3_j/scratch/` were created by me; they are outside the library build.)

## Scratch files
~/Blundon/scratch/L13_blundon.lean,
~/SteinerLehmus/scratch/L13_steiner.lean,
~/Kosnita/scratch/L13_kosnita.lean,
~/Fivecircles/scratch/L13_five.lean,
~/lester/scratch/L13_lester.lean,
~/thebault3_j/scratch/L13_thebault.lean,
~/clifford_j/scratch/L13_chain.lean,
~/clifford/scratch/L13_cliff4.lean,
~/clifford/scratch/L13_cliff5.lean,
~/clifford/scratch/L13_cliff5x.lean,
~/clifford/scratch/L13_cliff6.lean
