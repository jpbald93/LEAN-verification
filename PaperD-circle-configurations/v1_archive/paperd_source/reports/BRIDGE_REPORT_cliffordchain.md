# Clifford layer 10 — definition bridges (Clifford/Bridge.lean)

## Status per bridge
1. transversal_iff — PROVED as stated.
2. triP_ne_zero_iff — PROVED as stated.
3. cycP_ne_zero_iff — CORRECTED: added the hypothesis `htri : ¬ Collinear ℝ {a, b, c}`.
   The statement as given is FALSE when the centres are collinear. Counterexample: a=1+i, b=2+i,
   c=3.5+i. All three pairs are transversal and cycP = -7.5i ≠ 0, but every second intersection
   is 2i (the reflection of M=0 in the line of centres), so the three points coincide and are collinear.
4. onCircleM_iff_mem_sphere — PROVED as stated.
5. genTriple_iff — PROVED as stated (no extra hypothesis needed). It uses the corrected (3) on the
   `¬Collinear {a,b,c}` part, which both sides already contain.
Extra helper theorems, also in gate REQUIRED: collinear_iff_conj_mul, cross_second.

## Numeric / symbolic check (before writing Lean)
- Key identity, checked symbolically with sympy (exact) and on 2000 random complex triples
  (max relative error 2e-14). Write X = conj(P13-P12)(P23-P12) - (P13-P12)conj(P23-P12),
  which equals 2i·Im((P23-P12)·conj(P13-P12)). Then
    X · ∏|ci-cj|² = triP² · cycP.
  So the multiple is triP²/∏|ci-cj|², which is nonzero only when the centres are not collinear.
  That is the reason for the correction in (3).
- triP = (b-a)conj(c-a) - conj(b-a)(c-a) (exact). Transversal ⇔ Im(conj c·d) ≠ 0 (random check).
  OnCircleM ⇔ |z-c|² = |c|² (random check).
- Degenerate inputs: collinear centres gave the counterexample above. Centres concyclic with 0
  gave cycP ≈ 0 and Im ≈ 0, as predicted.

## Final statements
theorem collinear_iff_conj_mul (x y z : ℂ) :
    Collinear ℝ ({x, y, z} : Set ℂ) ↔ conj (y - x) * (z - x) = (y - x) * conj (z - x)
theorem transversal_iff (c d : ℂ) : Transversal c d ↔ ¬ Collinear ℝ ({0, c, d} : Set ℂ)
theorem triP_ne_zero_iff (a b c : ℂ) :
    triP a b c (conj a) (conj b) (conj c) ≠ 0 ↔ ¬ Collinear ℝ ({a, b, c} : Set ℂ)
theorem cross_second {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (conj (second a c - second a b) * (second b c - second a b) -
        (second a c - second a b) * conj (second b c - second a b)) *
      ((conj a - conj b) * (conj a - conj c) * (conj b - conj c) * ((a - b) * (a - c) * (b - c))) =
      triP a b c (conj a) (conj b) (conj c) ^ 2 * cycP a b c (conj a) (conj b) (conj c)
theorem cycP_ne_zero_iff {a b c : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c) (htri : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    cycP a b c (conj a) (conj b) (conj c) ≠ 0 ↔
      ¬ Collinear ℝ ({second a b, second a c, second b c} : Set ℂ)
theorem onCircleM_iff_mem_sphere (c z : ℂ) : OnCircleM c z ↔ z ∈ Metric.sphere c ‖c‖
theorem genTriple_iff {a b c : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c) :
    GenTriple a b c ↔ (¬ Collinear ℝ ({a, b, c} : Set ℂ) ∧
      ¬ Collinear ℝ ({second a b, second a c, second b c} : Set ℂ))

## Checks
- ~/lean/jl build: Build completed successfully (8710 jobs).
- ~/lean/jl gate: PASS (21 declarations, standard axioms only)   [was 14; +7]
- ~/lean/jl tamper: sorry, ax2line, evalfake, macro, wrap, falsehyp, cleanand all rejected —
  "ALL TAMPERING TESTS REJECTED".
- grep -nE "sorry|admit|axiom|native_decide" Clifford/Bridge.lean: empty.
- Changes: new Clifford/Bridge.lean; one line `import Clifford.Bridge` appended to Clifford.lean;
  7 names appended to REQUIRED in gate.sh.

## Hashes (shasum -a 256), before = after
d5c14edbf2da8ec8288484b4eeee54e30e85cf04e5c440c406b4c7144ca0cb16  Clifford/Basic.lean
2a7cf40b4c473e56c97db8b1485aa5ad468c9cbb5c9a56b5b7ac9adaf33cc463  Clifford/Clean.lean
