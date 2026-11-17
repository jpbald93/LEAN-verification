# L13 — Bankoff pair (machine john)

File: `~/lean/l13_arbelos/scratch/L13_bankoff_compare.lean` (sha256 `dbd46998a74f3d31…`)
Blind source: `~/lean/reformalH/PaperIBlind.lean` (sha256 `61a67c73df6c093e…`, identical to `Blind.lean` in the working dir),
`blind_79`, `blind_80` (`-- thm:bankoff`, section "bankoff addendum").
Library: `Arbelos.bankoff`, `Arbelos.bankoff_exists` (`Arbelos/Bankoff.lean`).

Method as in L13: blind defs copied verbatim (namespace `L13CmpBankoff`); `blind79_stmt`,
`blind80_stmt` are closed Props; real statements only via `type_of%`. Proof bodies use Mathlib
lemmas only (`Sphere.isIntTangent_iff_dist_center`, `IsExtTangentAt.isExtTangent`,
`IsExtTangent.dist_center`, `dist_add_dist_eq_iff`, `Complex.dist_eq_re_im`, …) plus unfolding
of library *definitions* (`bigS`, `leftS`, `rightS`, `ptC` — all `rfl`). No `Arbelos.*` theorem
appears in any proof body.

## Rows

| # | Library | Blind | R→B | B→R | Verdict |
|---|---------|-------|-----|-----|---------|
| 1 | `bankoff` (radius) | `blind_79` | ✅ `bankoff_R_to_B` | ✅ `bankoff_B_to_R` | **EQUIVALENT** |
| 2 | `bankoff_exists` (existence) | `blind_80` | ❌ needs real maths | ✅ `bankoffEx_B_to_R` | **DIFFERENCE — REAL** (library weaker) |

### Row 1 — equivalent
Hypotheses differ only in packaging; each direction is repackaging plus a few lines of coordinates:
- Blind requires strict positivity everywhere (`BlindIsCircle`, radii `> 0`); the library allows radius `0`.
  For B→R: the incircle's radius `> 0` follows from the tangency hypotheses (a radius-0 "circle" in the open
  upper half-plane can't sit on both small circles, which meet only at `C`); and the library's `s` must have
  radius `> 0` because `C` and `T₁` both lie on it and differ (`T₁.im > 0 = C.im`).
- Blind `BlindExtTangentAtPoint` adds `0 ≤ p.im`. That follows from the library hypotheses
  (`T = lineMap centre s₀.center μ` with `μ > 0`, so `T.im = μ·s₀.center.im > 0`).
- The library's `hleft`/`hright` (`IsExtTangent`) are redundant given `hT₁`/`hT₂` (`IsExtTangentAt.isExtTangent`).

### Row 2 — DIFFERENCE, REAL
`blind_80` names the circle explicitly: centre `2a + (ab/(a+b))·i`, radius `ab/(a+b)`.
`bankoff_exists` only gives `∃ s, C ∈ s ∧ T₁ ∈ s ∧ T₂ ∈ s ∧ s.radius = ab/(a+b)`, so the centre is not in
its statement. (The proof does use that centre as its witness, but the statement doesn't expose it.)
Getting from R to B means showing that this particular circle passes through `T₁` and `T₂`. That needs
the incircle identified and `T₁`, `T₂` computed, which is exactly the content of the library proof. Pinning
the centre down from the radius alone would also need `C, T₁, T₂` to be non-collinear. Neither is repackaging.
- Not an ambiguity artefact: the prose names the centre ("the circle with centre 2a + (ab/(a+b))i").
- What R does give in blind vocabulary is proved: `bankoffEx_R_to_Bweak : bankoff_exists → blind80_weak_stmt`
  (blind_80 with the circle existentially quantified, radius `ab/(a+b)`, `BlindIsCircle`), plus
  `blind80_to_weak`. So the blind statement is strictly stronger.
- Suggested fix (library, not done — no library edits allowed): add `s.center = 2a + (ab/(a+b))·i` to the
  conclusion of `bankoff_exists`. The existing proof already uses that centre as its witness, so it closes with `rfl`.

## Do the regenerated blind definitions match what the library needs?
- `BlindCirclePoints c : Set ℂ := {z | dist z c.1 = c.2}`, used as `BlindCirclePoints k z`. This is
  definitionally `z ∈ (⟨c.1, c.2⟩ : Sphere ℂ)` (`pts_iff` is `Iff.rfl`). It matches the library exactly.
- `BlindInternallyTangent inner outer := inner.2 > 0 ∧ outer.2 > 0 ∧ dist inner.1 outer.1 + inner.2 = outer.2`.
  The library's `IsIntTangent` ⇔ `dist = R − r ∧ 0 ≤ r ∧ 0 ≤ R`. The only difference is strict versus weak positivity:
  blind ⇒ library always holds, and library ⇒ blind needs `r > 0`, which comes from the other hypotheses (above).
- `BlindExtTangentAtPoint c d p` = both radii `> 0`, `dist c.1 d.1 = c.2 + d.2`, `0 ≤ p.im`, `p` on both circles.
  The library's `IsExtTangentAt d c p` = `p` on both, plus `Wbtw d.center p c.center`. These are equivalent up to
  the extra positivity and `0 ≤ p.im` (via `dist_add_dist_eq_iff`; `extAt_iff`). The argument order is flipped:
  blind puts the incircle first, the library puts the small semicircle first.
- `BlindOuterCircle a b`, `BlindFirstCircle a`, `BlindSecondCircle a b`, `BlindCommonPoint a` are
  definitionally `bigS a b`, `leftS a b`, `rightS a b`, `ptC a b` (all `rfl`). They use the same coordinates
  (A = 0, C = 2a, B = 2(a+b)), so this addendum doesn't need the `BlindDiameterCircle` bridge from the main L13 file.
- The truncation issue is fixed: both statements are complete and carry every hypothesis the library uses.
  None is missing, and the only extras (`0 ≤ T.im`, strict positivity) are derivable.

## Gate
```
$ ssh john@100.101.160.66 'cd ~/lean/l13_arbelos && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/L13_bankoff_compare.lean'
(no output)   exit 0
$ grep -nE "sorry|admit|native_decide|axiom" scratch/L13_bankoff_compare.lean
(no matches)  grep exit 1
```
Axiom check (run on a temporary copy with `#print axioms`, so the gated file has no `axiom` token):
all five theorems (`bankoff_R_to_B`, `bankoff_B_to_R`, `bankoffEx_B_to_R`, `bankoffEx_R_to_Bweak`,
`blind80_to_weak`) depend only on `[propext, Classical.choice, Quot.sound]`.

Note: `Arbelos/Bankoff.lean` and `Arbelos/Steiner.lean` already show as modified in git (they contain
`bankoff_exists`). This run didn't change them; the compiled `.olean` is newer than the source.
