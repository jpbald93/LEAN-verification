# Paper Prime: L14 report (Mathlib-only restatement + witnesses)

**Status: COMPLETE.** Machine: jack (`jack`). All work was done inline, with no subagents.
Start 2026-10-22 09:06 EDT, end about 09:16 EDT (clock times from `date`, local and remote).

## Source
| item | value |
|---|---|
| repo | https://github.com/jpbald93/primitive-root-families |
| pinned (paper) | `e30457a` → `git rev-parse` = `e30457aff1e6a2c638341bf3e08b382f82b5ceef` |
| clone | `~/l14Prime_primitive-root-families` (fresh `git clone` + `git checkout`) |
| lean-toolchain | `leanprover/lean4:v4.33.1` |
| Mathlib rev (lake-manifest) | `0df444a360eaa60ab8c11dca51a86af692955474` (matches the target) |
| packages | `.lake/packages -> ~/barbier/.lake/packages` (symlink; no `lake update`, no cache download) |

## Approach to (A)
All 17 published statements **already mention only Mathlib constants**. They use `IsPrimitiveRoot`, `legendreSym`, `ZMod`, `IsLeast`, `Nat.Prime` and `Fact`, and the paper's repository defines nothing. So (A) is close to trivial here. To make the restatements independent of the repo's conventions anyway, each `l14_*` theorem uses:
* explicit `Nat.Prime p` hypotheses instead of `[Fact p.Prime]` instances;
* `orderOf a = p - 1` (the textbook definition: multiplicative order) instead of `IsPrimitiveRoot a (p - 1)`. Bridge: `IsPrimitiveRoot.iff_orderOf`;
* `jacobiSym a p` instead of `legendreSym p a`. Bridge: `jacobiSym.legendreSym.to_jacobiSym`. This also makes the symbol `norm_num`-evaluable in the witnesses;
* Theorem `legendreSym_ten…` no longer takes the instance argument `[Fact (Nat.Prime 5)]`.

Each `l14_*` is proved from the library theorem plus the bridges above. No library statement was re-proved, weakened or strengthened.

## Table (repo primitive-root-families; file `PrimitiveRootFamilies/L14.lean`, 376 lines)
| theorem (paper) | l14 | namespace-free | witness `l14w_*` | distinctness / non-vacuity | notes |
|---|---|---|---|---|---|
| isPrimitiveRoot_iff_of_eq_four_mul_add_one (Lem 3.1) | ✔ | ✔ | p=3, q=13 | a=2: both sides true (ord 12); a=3: both sides false | both truth values of ↔ |
| legendreSym_ten_of_eq_four_mul_add_one (Lem 3.2) | ✔ | ✔ | (3,13) and (7,29) | (10\|13)=+1, (10\|29)=−1 | both values occur; Fact(5) arg removed |
| isPrimitiveRoot_ten_iff_mod_five_eq_two (Thm 3.3) | ✔ | ✔ | (7,29) and (3,13) | ord(10 mod 29)=28 with 7%5=2; ord(10 mod 13)≠12 with 3%5≠2 | both directions |
| isPrimitiveRoot_ten_of_mod_five_eq_two (Cor 3.4) | ✔ | ✔ | (7,29) | ord=28, 10≠1, 28>1 | proved via the ↔ (see tamper note) |
| isPrimitiveRoot_iff_of_eq_two_mul_add_one (Lem 4.1) | ✔ | ✔ | p=11, q=5 | a=2 true; a=10 (=−1) false | both truth values |
| isPrimitiveRoot_of_legendreSym_eq_neg_one (Lem 4.2) | ✔ | ✔ | p=23, q=11, x=5 | (5\|23)=−1, ord=22, 5≠1 | |
| prime_of_isLeast_isPrimitiveRoot (Thm 4.3) | ✔ | ✔ | p=23 | IsLeast … 5 proved explicitly (1–4 checked by `interval_cases`+`decide`); 5 prime; 4 not a root | hypothesis IsLeast is genuinely realised |
| exists_isLeast_isPrimitiveRoot (Lem 4.4) | ✔ | ✔ | p=23 | explicit least element 5 | |
| exists_isLeast_isPrimitiveRoot_and_prime (Thm 4.5) | ✔ | ✔ | p=23, q=11 | g=5, prime, 5≠2 (not the trivial root 2) | |
| isPrimitiveRoot_two_of_mod_four_eq_one (Cor 4.6) | ✔ | ✔ | p=11, q=5 | ord(2)=10, 2≠1 | |
| isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one (Thm 5.1) | ✔ | ✔ | p=41=2³·5+1 | a=6 true; a=3 false although (3\|41)=−1 | shows the second condition is essential |
| isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd (Cor 5.2) | ✔ | ✔ | p=41, k=3, l=5, a=6 | (6\|41)=−1, 41∤6⁸−1, ord=40, 6≠1 | |
| isPrimitiveRoot_two_of_eq_four_mul_add_one (Cor 5.3a) | ✔ | ✔ | l=3, p=13 | ord(2)=12, 2≠1 | |
| isPrimitiveRoot_three_of_eq_eight_mul_add_one (Cor 5.3b) | ✔ | ✔ | l=11, p=89 | ord(3)=88; also l=5, p=41: ord(3)≠40 | generic odd branch (not just p=17); exclusion l≠5 genuine |
| isPrimitiveRoot_three_of_eq_sixteen_mul_add_one (Cor 5.3c) | ✔ | ✔ | l=7, p=113 | ord(3)=112, 3≠1 | |
| isPrimitiveRoot_iff_of_eq_two_mul_add_one' (Thm 5.1, k=1) | ✔ | ✔ | p=23, l=11 | a=5 true; a=−1 false although (−1\|23)=−1 | |
| isPrimitiveRoot_iff_of_eq_four_mul_add_one' (Thm 5.1, k=2) | ✔ | ✔ | p=13, l=3 | a=2 true; a=5 false although (5\|13)=−1 | |

Coverage: 17/17 restated, 17/17 witnessed.

## Bridges (in L14.lean)
* `l14_setOf_orderOf_eq` : `{a : ℕ | 0 < a ∧ orderOf (a : ZMod p) = p - 1} = {a | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}`
* helper witness `l14w_isLeast_twentythree` : `IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} 5`
* Mathlib bridges used: `IsPrimitiveRoot.iff_orderOf`, `jacobiSym.legendreSym.to_jacobiSym`.
* Extra Mathlib imports in L14.lean: `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol` and `Mathlib.Tactic.NormNum.LegendreSymbol`.

## FINDINGS
* **No Mathlib-only statement turned out false or to need an extra hypothesis.** Every restatement is the library theorem plus definitional bridges, with exactly the same hypotheses (instances became explicit `Nat.Prime`).
* (minor, artifact robustness) My first L14 version proved `l14_isPrimitiveRoot_ten_of_mod_five_eq_two` directly from `isPrimitiveRoot_ten_of_mod_five_eq_two`. That made `tests/tamper.sh` test `wrap` fail at the wrong stage: `NOT OK wrap expected "FAIL: nonstandard axioms", got "FAIL: build"`. The test replaces that declaration with `True` in the tampered copy, so any downstream file that uses it no longer builds. I fixed this by deriving it from the `↔` theorem `isPrimitiveRoot_ten_iff_mod_five_eq_two` (a code comment says why). The re-run passes. This is a fragility of the tamper script for downstream extensions, not a mathematical issue.
* (observation) Published types are already Mathlib-only, so namespace-freeness was not in question for the originals. The value added by L14 here is the `orderOf`/`jacobiSym`/explicit-prime phrasing and the explicit witnesses. The ↔ witnesses show both truth values, and two show that the second condition (`a^(2^k) ≠ 1`) is genuinely needed.

## Type-check output (mechanical namespace check)
Scratch files were in `~/l14Prime_scratch/` (`set_option pp.fullNames true` only there). Output: `~/l14Prime_typecheck.out`.
* Textual: after stripping each leading declaration name, `grep -c PrimitiveRootFamilies` = **0**.
* Constant-level, also in scratch (`~/l14Prime_constcheck.out`): for all 36 `l14*` declarations, `ci.type.getUsedConstants` filtered to the `PrimitiveRootFamilies` prefix gives `[]` (36/36).

Full `#check` output:
```
@PrimitiveRootFamilies.l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → q = 4 * p + 1 → ∀ {a : ZMod q}, a ≠ 0 → (orderOf a = q - 1 ↔ a ^ (2 * p) ≠ 1 ∧ a ^ 4 ≠ 1)
@PrimitiveRootFamilies.l14_legendreSym_ten_of_eq_four_mul_add_one : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → q = 4 * p + 1 → jacobiSym 10 q = -jacobiSym (↑q) 5
@PrimitiveRootFamilies.l14_isPrimitiveRoot_ten_iff_mod_five_eq_two : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → q = 4 * p + 1 → (orderOf 10 = q - 1 ↔ p % 5 = 2)
@PrimitiveRootFamilies.l14_isPrimitiveRoot_ten_of_mod_five_eq_two : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → q = 4 * p + 1 → p % 5 = 2 → orderOf 10 = q - 1
@PrimitiveRootFamilies.l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → p = 2 * q + 1 → ∀ {a : ZMod p}, a ≠ 0 → (orderOf a = p - 1 ↔ a ^ q ≠ 1 ∧ a ^ 2 ≠ 1)
@PrimitiveRootFamilies.l14_isPrimitiveRoot_of_legendreSym_eq_neg_one : ∀ {p q x : ℕ},
  Nat.Prime p → Nat.Prime q → p = 2 * q + 1 → 1 < x → x < p - 1 → jacobiSym (↑x) p = -1 → orderOf ↑x = p - 1
PrimitiveRootFamilies.l14_setOf_orderOf_eq : ∀ (p : ℕ),
  {a | 0 < a ∧ orderOf ↑a = p - 1} = {a | 0 < a ∧ IsPrimitiveRoot (↑a) (p - 1)}
@PrimitiveRootFamilies.l14_prime_of_isLeast_isPrimitiveRoot : ∀ {p q g : ℕ},
  Nat.Prime p → Nat.Prime q → p = 2 * q + 1 → IsLeast {a | 0 < a ∧ orderOf ↑a = p - 1} g → Nat.Prime g
@PrimitiveRootFamilies.l14_exists_isLeast_isPrimitiveRoot : ∀ {p : ℕ},
  Nat.Prime p → ∃ g, IsLeast {a | 0 < a ∧ orderOf ↑a = p - 1} g
@PrimitiveRootFamilies.l14_exists_isLeast_isPrimitiveRoot_and_prime : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → p = 2 * q + 1 → ∃ g, IsLeast {a | 0 < a ∧ orderOf ↑a = p - 1} g ∧ Nat.Prime g
@PrimitiveRootFamilies.l14_isPrimitiveRoot_two_of_mod_four_eq_one : ∀ {p q : ℕ},
  Nat.Prime p → Nat.Prime q → p = 2 * q + 1 → q % 4 = 1 → orderOf 2 = p - 1
@PrimitiveRootFamilies.l14_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one : ∀ {p l k : ℕ},
  Nat.Prime p →
    Nat.Prime l →
      l ≠ 2 → 1 ≤ k → p = 2 ^ k * l + 1 → ∀ {a : ℤ}, ↑a ≠ 0 → (orderOf ↑a = p - 1 ↔ jacobiSym a p = -1 ∧ ↑a ^ 2 ^ k ≠ 1)
@PrimitiveRootFamilies.l14_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd : ∀ {p l k : ℕ},
  Nat.Prime p →
    Nat.Prime l →
      l ≠ 2 →
        1 ≤ k → p = 2 ^ k * l + 1 → ∀ {a : ℤ}, ↑a ≠ 0 → jacobiSym a p = -1 → ¬↑p ∣ a ^ 2 ^ k - 1 → orderOf ↑a = p - 1
@PrimitiveRootFamilies.l14_isPrimitiveRoot_two_of_eq_four_mul_add_one : ∀ {p l : ℕ},
  Nat.Prime l → Nat.Prime p → p = 4 * l + 1 → orderOf 2 = p - 1
@PrimitiveRootFamilies.l14_isPrimitiveRoot_three_of_eq_eight_mul_add_one : ∀ {p l : ℕ},
  Nat.Prime l → Nat.Prime p → p = 8 * l + 1 → l ≠ 5 → orderOf 3 = p - 1
@PrimitiveRootFamilies.l14_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one : ∀ {p l : ℕ},
  Nat.Prime l → Nat.Prime p → p = 16 * l + 1 → orderOf 3 = p - 1
@PrimitiveRootFamilies.l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one' : ∀ {p l : ℕ},
  Nat.Prime p →
    Nat.Prime l → l ≠ 2 → p = 2 * l + 1 → ∀ {a : ℤ}, ↑a ≠ 0 → (orderOf ↑a = p - 1 ↔ jacobiSym a p = -1 ∧ ↑a ^ 2 ≠ 1)
@PrimitiveRootFamilies.l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one' : ∀ {p l : ℕ},
  Nat.Prime p → Nat.Prime l → p = 4 * l + 1 → ∀ {a : ℤ}, ↑a ≠ 0 → (orderOf ↑a = p - 1 ↔ jacobiSym a p = -1 ∧ ↑a ^ 4 ≠ 1)
PrimitiveRootFamilies.l14w_isPrimitiveRoot_iff_of_eq_four_mul_add_one : Nat.Prime 3 ∧
  Nat.Prime 13 ∧
    13 = 4 * 3 + 1 ∧
      2 ≠ 0 ∧
        3 ≠ 0 ∧ (orderOf 2 = 13 - 1 ∧ 2 ^ (2 * 3) ≠ 1 ∧ 2 ^ 4 ≠ 1) ∧ orderOf 3 ≠ 13 - 1 ∧ ¬(3 ^ (2 * 3) ≠ 1 ∧ 3 ^ 4 ≠ 1)
PrimitiveRootFamilies.l14w_legendreSym_ten_of_eq_four_mul_add_one : Nat.Prime 3 ∧
  Nat.Prime 13 ∧
    13 = 4 * 3 + 1 ∧
      Nat.Prime 7 ∧
        Nat.Prime 29 ∧
          29 = 4 * 7 + 1 ∧
            jacobiSym 10 13 = -jacobiSym 13 5 ∧
              jacobiSym 10 29 = -jacobiSym 29 5 ∧ jacobiSym 10 13 = 1 ∧ jacobiSym 10 29 = -1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_ten_iff_mod_five_eq_two : Nat.Prime 7 ∧
  Nat.Prime 29 ∧
    29 = 4 * 7 + 1 ∧
      Nat.Prime 3 ∧ Nat.Prime 13 ∧ 13 = 4 * 3 + 1 ∧ orderOf 10 = 29 - 1 ∧ 7 % 5 = 2 ∧ orderOf 10 ≠ 13 - 1 ∧ 3 % 5 ≠ 2
PrimitiveRootFamilies.l14w_isPrimitiveRoot_ten_of_mod_five_eq_two : Nat.Prime 7 ∧
  Nat.Prime 29 ∧ 29 = 4 * 7 + 1 ∧ 7 % 5 = 2 ∧ orderOf 10 = 29 - 1 ∧ 10 ≠ 1 ∧ 1 < 29 - 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_iff_of_eq_two_mul_add_one : Nat.Prime 11 ∧
  Nat.Prime 5 ∧
    11 = 2 * 5 + 1 ∧
      2 ≠ 0 ∧ 10 ≠ 0 ∧ (orderOf 2 = 11 - 1 ∧ 2 ^ 5 ≠ 1 ∧ 2 ^ 2 ≠ 1) ∧ orderOf 10 ≠ 11 - 1 ∧ ¬(10 ^ 5 ≠ 1 ∧ 10 ^ 2 ≠ 1)
PrimitiveRootFamilies.l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one : Nat.Prime 23 ∧
  Nat.Prime 11 ∧ 23 = 2 * 11 + 1 ∧ 1 < 5 ∧ 5 < 23 - 1 ∧ jacobiSym 5 23 = -1 ∧ orderOf ↑5 = 23 - 1 ∧ ↑5 ≠ 1
PrimitiveRootFamilies.l14w_isLeast_twentythree : IsLeast {a | 0 < a ∧ orderOf ↑a = 23 - 1} 5
PrimitiveRootFamilies.l14w_prime_of_isLeast_isPrimitiveRoot : Nat.Prime 23 ∧
  Nat.Prime 11 ∧ 23 = 2 * 11 + 1 ∧ IsLeast {a | 0 < a ∧ orderOf ↑a = 23 - 1} 5 ∧ Nat.Prime 5 ∧ orderOf ↑4 ≠ 23 - 1
PrimitiveRootFamilies.l14w_exists_isLeast_isPrimitiveRoot : Nat.Prime 23 ∧
  (∃ g, IsLeast {a | 0 < a ∧ orderOf ↑a = 23 - 1} g) ∧ IsLeast {a | 0 < a ∧ orderOf ↑a = 23 - 1} 5
PrimitiveRootFamilies.l14w_exists_isLeast_isPrimitiveRoot_and_prime : Nat.Prime 23 ∧
  Nat.Prime 11 ∧
    23 = 2 * 11 + 1 ∧
      (∃ g, IsLeast {a | 0 < a ∧ orderOf ↑a = 23 - 1} g ∧ Nat.Prime g) ∧
        IsLeast {a | 0 < a ∧ orderOf ↑a = 23 - 1} 5 ∧ Nat.Prime 5 ∧ 5 ≠ 2
PrimitiveRootFamilies.l14w_isPrimitiveRoot_two_of_mod_four_eq_one : Nat.Prime 11 ∧
  Nat.Prime 5 ∧ 11 = 2 * 5 + 1 ∧ 5 % 4 = 1 ∧ orderOf 2 = 11 - 1 ∧ 2 ≠ 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one : Nat.Prime 41 ∧
  Nat.Prime 5 ∧
    5 ≠ 2 ∧
      1 ≤ 3 ∧
        41 = 2 ^ 3 * 5 + 1 ∧
          ↑6 ≠ 0 ∧
            ↑3 ≠ 0 ∧
              (orderOf ↑6 = 41 - 1 ∧ jacobiSym 6 41 = -1 ∧ ↑6 ^ 2 ^ 3 ≠ 1) ∧
                orderOf ↑3 ≠ 41 - 1 ∧ jacobiSym 3 41 = -1 ∧ ↑3 ^ 2 ^ 3 = 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd : Nat.Prime 41 ∧
  Nat.Prime 5 ∧
    5 ≠ 2 ∧
      1 ≤ 3 ∧ 41 = 2 ^ 3 * 5 + 1 ∧ ↑6 ≠ 0 ∧ jacobiSym 6 41 = -1 ∧ ¬↑41 ∣ 6 ^ 2 ^ 3 - 1 ∧ orderOf ↑6 = 41 - 1 ∧ ↑6 ≠ 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_two_of_eq_four_mul_add_one : Nat.Prime 3 ∧
  Nat.Prime 13 ∧ 13 = 4 * 3 + 1 ∧ orderOf 2 = 13 - 1 ∧ 2 ≠ 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_three_of_eq_eight_mul_add_one : Nat.Prime 11 ∧
  Nat.Prime 89 ∧
    89 = 8 * 11 + 1 ∧
      11 ≠ 5 ∧ orderOf 3 = 89 - 1 ∧ 3 ≠ 1 ∧ Nat.Prime 5 ∧ Nat.Prime 41 ∧ 41 = 8 * 5 + 1 ∧ orderOf 3 ≠ 41 - 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one : Nat.Prime 7 ∧
  Nat.Prime 113 ∧ 113 = 16 * 7 + 1 ∧ orderOf 3 = 113 - 1 ∧ 3 ≠ 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_iff_of_eq_two_mul_add_one' : Nat.Prime 23 ∧
  Nat.Prime 11 ∧
    11 ≠ 2 ∧
      23 = 2 * 11 + 1 ∧
        ↑5 ≠ 0 ∧
          ↑(-1) ≠ 0 ∧
            (orderOf ↑5 = 23 - 1 ∧ jacobiSym 5 23 = -1 ∧ ↑5 ^ 2 ≠ 1) ∧
              orderOf ↑(-1) ≠ 23 - 1 ∧ jacobiSym (-1) 23 = -1 ∧ ↑(-1) ^ 2 = 1
PrimitiveRootFamilies.l14w_isPrimitiveRoot_iff_of_eq_four_mul_add_one' : Nat.Prime 13 ∧
  Nat.Prime 3 ∧
    13 = 4 * 3 + 1 ∧
      ↑2 ≠ 0 ∧
        ↑5 ≠ 0 ∧
          (orderOf ↑2 = 13 - 1 ∧ jacobiSym 2 13 = -1 ∧ ↑2 ^ 4 ≠ 1) ∧
            orderOf ↑5 ≠ 13 - 1 ∧ jacobiSym 5 13 = -1 ∧ ↑5 ^ 4 = 1
```

## Gate before → after
* before (fresh clone): `PASS (17 theorems, standard axioms only)`
* after: `PASS (53 theorems, standard axioms only)`

## Tamper (`bash tests/tamper.sh`, final run)
```
ok    sorry     rejected: FAIL: forbidden token
ok    ax2line   rejected: FAIL: forbidden token
ok    evalfake  rejected: FAIL: forbidden token
ok    macro     rejected: FAIL: forbidden token
ok    falsehyp  rejected: FAIL: build
ok    wrap      rejected: FAIL: nonstandard axioms: PrimitiveRootFamilies.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ALL TAMPERING TESTS REJECTED
```

## Hashes (sha256, pre-existing library files; fresh clone = after)
```
6b27335ade4ff8cceb73eb6bf7a1b098ac5deed3edcda1ce107ee3ab1b7115f2  PrimitiveRootFamilies/Chebyshev.lean   (unchanged)
2075da126aa124ad5c5e7591d8755e237836ddda854f9671090991ef324161b4  PrimitiveRootFamilies/General.lean     (unchanged)
9fd4a70c588eeb61e6f911c0e085da4ad5cab5439a0390fc05d2fbdcbb3b742f  PrimitiveRootFamilies/SafePrime.lean   (unchanged)
c8f310a90970c0b84d8aae599fe96492e8be2edb1cb8a935b46a2e7f7b1dfb48  PrimitiveRootFamilies/L14.lean         (new)
```
`sha256sum -c` against the full pre-clone list: every tracked file is OK except the two intended edits. `git diff --stat` shows exactly `PrimitiveRootFamilies.lean | 1 +` (the appended `import PrimitiveRootFamilies.L14`) and `gate.sh | 2 +-` (the REQUIRED line only). Forbidden-token scan of L14.lean: no hits. Nothing committed or pushed.

## REQUIRED added (36)
`l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one l14_legendreSym_ten_of_eq_four_mul_add_one l14_isPrimitiveRoot_ten_iff_mod_five_eq_two l14_isPrimitiveRoot_ten_of_mod_five_eq_two l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one l14_isPrimitiveRoot_of_legendreSym_eq_neg_one l14_setOf_orderOf_eq l14_prime_of_isLeast_isPrimitiveRoot l14_exists_isLeast_isPrimitiveRoot l14_exists_isLeast_isPrimitiveRoot_and_prime l14_isPrimitiveRoot_two_of_mod_four_eq_one l14_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one l14_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd l14_isPrimitiveRoot_two_of_eq_four_mul_add_one l14_isPrimitiveRoot_three_of_eq_eight_mul_add_one l14_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one' l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one' l14w_isPrimitiveRoot_iff_of_eq_four_mul_add_one l14w_legendreSym_ten_of_eq_four_mul_add_one l14w_isPrimitiveRoot_ten_iff_mod_five_eq_two l14w_isPrimitiveRoot_ten_of_mod_five_eq_two l14w_isPrimitiveRoot_iff_of_eq_two_mul_add_one l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one l14w_isLeast_twentythree l14w_prime_of_isLeast_isPrimitiveRoot l14w_exists_isLeast_isPrimitiveRoot l14w_exists_isLeast_isPrimitiveRoot_and_prime l14w_isPrimitiveRoot_two_of_mod_four_eq_one l14w_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd l14w_isPrimitiveRoot_two_of_eq_four_mul_add_one l14w_isPrimitiveRoot_three_of_eq_eight_mul_add_one l14w_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one l14w_isPrimitiveRoot_iff_of_eq_two_mul_add_one' l14w_isPrimitiveRoot_iff_of_eq_four_mul_add_one'`

## Wall time
About 10 minutes on the clock (09:06 to 09:16 EDT). Baseline gate about 1 min, final gate about 1 min, tamper about 3 min.
