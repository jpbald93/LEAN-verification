# PAPERE_COMPARE_N — Layer 13 statement-level comparison (blind_1 … blind_6)

Machine: jack. Repo `~/quadnewton` (namespace `QuadNewton`). Blind file: `~/reformal/PaperEBlind.lean`.
Scratch file: `~/quadnewton/scratch/L13_compare.lean` (starts with `import QuadNewton`, namespace `Blind`).
Auxiliary: `~/quadnewton/scratch/L13_axioms.lean` (the same file plus `#print axioms` for the 12 theorems).

The scratch file copies the blind model section **verbatim**. A script checked that the whole
`/-! ## The model … -/` block appears byte-for-byte. Each `blindK_stmt` has the form
`∀ L₁ L₂ L₃ L₄ : BlindLine, BlindGenPos … → <conclusion>`. A whitespace-normalised script
comparison confirmed that each conclusion matches the blind file exactly, for K = 1..6.
The real side is always `type_of% @<RealDecl>`.

## Results

| pair | real decl | R→B | B→R | difference | note |
|---|---|---|---|---|---|
| blind_1 | `newton_gauss` | ✅ `rb_1` | ✅ `br_1` | none | M1, M2, M3 unfold to the real midpoints in the same order |
| blind_2 | `diag_midpoints_ne` | ✅ `rb_2` | ✅ `br_2` | none | M1 ≠ M2 is exactly `(A12+A34)/2 ≠ (A13+A24)/2` |
| blind_3 | `orthocentres_collinear` | ✅ `rb_3` | ✅ `br_3` | none | H1..H4 = `ortho` of T1..T4 with the same vertex order and the same set order |
| blind_4 | `orthocentres_not_all_eq` | ✅ `rb_4` | ✅ `br_4` | none | Real: `ortho(T3) ≠ ortho(T4) ∨ ortho(T2) ≠ ortho(T4)`. This is the same as the blind H3≠H4 ∨ H2≠H4 |
| blind_5 | `bodenmiller` | ✅ `rb_5` | ✅ `br_5` | none | Second conjunct differs in form. Blind: pw(13,24) = pw(14,23). Real: pw(12,34) = pw(14,23). They are equivalent given the shared first conjunct, by transitivity of `=` (pure logic). Also needs `pw_agree` |
| blind_6 | `orthocentre_line_perp` | ✅ `rb_6` | ✅ `br_6` | none | Same `(m₂ − m₁) · conj(H′ − H)` with the same quantifier order; `starRingEnd ℂ` is the same term as `conj` |

**Result: all 6 pairs are equivalent at statement level.** No REAL difference, no ARTEFACT,
and no "Lean more general" case. The pairing table looks correct.

The two `-- AMBIGUOUS` notes in the blind file make no difference here:
- **GenPos triple choice:** the blind version uses exactly the four conditions `c123, c124, c134, c234` that the real `GenPos` uses.
- **Circumcircle radius:** only blind_7..10 use it, and those are out of scope.

## Agreement / bridge lemmas (all in the scratch file)

- `toR : BlindLine → QuadNewton.Line := ⟨L.p, L.d⟩` and `toB` (its inverse); `toR_toB` holds by `rfl`.
- **Hold by `rfl` (definitional):**
  - `cr_agree : BlindCr = cr`
  - `carrier_agree : L.carrier = (toR L).carrier`
  - `meet_agree : BlindMeet L M = meet (toR L) (toR M)`
  - `circ_agree : BlindCirc = circ`
  - `ortho_agree : BlindOrtho = ortho`
- **`genPos_agree : BlindGenPos ↔ GenPos (toR …)`** — repacking 14 conjuncts into the `structure` fields, which are identical and in the same order.
- **`pw_agree : BlindPw z P Q = pw z P Q`** — not `rfl`, but an unfolding fact. The blind version uses `normSq x - (1/4)·normSq y`; the real one uses `‖x‖^2 - ‖y‖^2/4`. Proved with Mathlib's `Complex.normSq_eq_norm_sq` and `ring`. This is a notational difference, not a mathematical one.
- **No repository theorems or Bridge.lean lemmas were used:** none of `newton_gauss` etc., and none of `carrier_eq_line`, `genPos_iff`, `pw_eq_power`, …. The proofs use only the premise, unfolding of the blind definitions plus the lemmas above, and `simp only` / `exact`.

## Checks

- **Compile:** `lake env lean scratch/L13_compare.lean` gave exit code **0**, with no errors or warnings. `scratch/L13_axioms.lean` also gave exit code **0**.
- **`#print axioms`:** all 12 theorems (`rb_1..6`, `br_1..6`) depend only on `[propext, Classical.choice, Quot.sound]`.
- **Forbidden tokens:** `grep -nE "sorry|admit|native_decide|axiom" scratch/L13_compare.lean` found nothing (grep exit 1).
- **Library hash** (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`):
  - before: `b9e7fd2a70ac294e0d882e6536117b71cfbef4dea301a31836ef838494da751d`
  - after:  `b9e7fd2a70ac294e0d882e6536117b71cfbef4dea301a31836ef838494da751d` (unchanged)
- No library files were edited, and `lake update` / `cache get` were not run.
