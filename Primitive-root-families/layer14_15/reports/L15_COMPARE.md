# L15 classical comparison: Paper Prime ("Primitive roots modulo primes 2^k ℓ+1")

**Inputs**
- Classical statements from the blind writer: `/tmp/blindPrime/Classical.lean` (md5 `58d51408…`, the same file as `jack:~/reformal/PaperPrimeClassical.lean`).
- 26 `classical_*` statements.

**Repository**
- `jpbald93/primitive-root-families`, pinned at `e30457a`, which resolves to `e30457aff1e6a2c638341bf3e08b382f82b5ceef`.
- It is the only repository named in prf.tex.
- The "pascal-hexagon 726da4d" note in the brief does not apply to this paper: prf.tex cites no second repository.

**Fresh clone and gate**
- Clone: `jack:~/l15Prime_primitive-root-families`.
- `.lake/packages` is a symlink to `~/barbier/.lake/packages` (Mathlib `0df444a3…` matches).
- Gate line: `PASS (17 theorems, standard axioms only)`, rc=0, 6.7 s (already built).

**Scratch file**
- On jack: `~/l15Prime_primitive-root-families/scratch/L15_compare.lean` (sha256 `6c8e6ee9…b035`).
- Local copy: `AFM/L14L15/Prime/L15_compare_primitive-root-families.lean`.
- It imports `PrimitiveRootFamilies` and Mathlib.
- The writer's definitions and statements are copied verbatim. The only change is packaging: `theorem classical_X <binders> : S := by sorry` became `def classical_X : Prop := ∀ <binders>, S`. A diff confirms nothing else changed.

## Table

| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| Prime1_a (Euler) | O→E | `cov_Prime1_a` | — | Background. The paper uses Mathlib `legendreSym.eq_pow` and does not claim this. Proved from Mathlib. |
| Prime1_b | O→E | `cov_Prime1_b` | — | From `ZMod.euler_criterion`. |
| Prime1_c | O→E | `cov_Prime1_c` | — | From `ZMod.euler_criterion` and `pow_div_two_eq_neg_one_or_one`. |
| Prime2_a (prime-divisor test) | O→E | `cov_Prime2_a` | — | The paper uses Mathlib `orderOf_eq_of_pow_and_pow_div_prime`. Proved. |
| Prime2_b | O→E | `cov_Prime2_b` | — | Primitive root ⇒ (g/p) = −1. |
| Prime2_c | O→E | `cov_Prime2_c` | — | |
| Prime2_d | O→E | `cov_Prime2_d` | — | |
| Prime3_a (Fermat primes) | O→E | `cov_Prime3_a` | — | Not in the paper (it has no p−1 = 2^k case). NEW PROOF from Mathlib. |
| Prime3_b (safe primes, including p = 5) | N→E | `cov_Prime3_b` | — | The repository has `isPrimitiveRoot_iff_of_eq_two_mul_add_one'`, which requires q ≠ 2 and uses the condition a² ≢ 1. The case q = 2 (p = 5) and the translation a² ≢ 1 ⇔ a ≢ −1 (given (a/p) = −1) are NEW PROOF here. With them the classical statement is fully covered. |
| Prime3_b_remark5 | O→E | `cov_Prime3_b_remark5` | — | Checked by `decide`. |
| Prime3_b_remark7 | O→E | `cov_Prime3_b_remark7` | — | Uses `legendreSym.at_neg_one`, `χ₄`, `orderOf_neg_one`. |
| Prime3_c (Wertheim, k, l ≥ 1) | **D** | `not_classical_Prime3_c`; `cov_Prime3_c_part` (l = 1); `new_Prime3_c_corrected` | — | **The statement as written is false** whenever l ≥ 2. Counterexample: p = 19 = 2·3²+1 and a = 8. Here (8/19) = −1 and 8² = 64 ≢ 1, but ord₁₉(8) = 6 (8⁶ ≡ 1). The textbook text has the same error, so this is a fault in the source statement, not the writer's. The correct condition is a^(2^k·q^(l−1)) ≢ 1, proved as NEW PROOF `new_Prime3_c_corrected`. The paper only claims l = 1 (Theorem 5.1: p = 2^k ℓ + 1). `cov_Prime3_c_part` derives the l = 1 case from `isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one`. Paper vs classical: the paper is narrower (l = 1) but correct. |
| Prime4 (2 is a primitive root mod 4q+1) | E | `cov_Prime4` | — | From `isPrimitiveRoot_two_of_eq_four_mul_add_one`. The repository version is stronger: it does not need q ≠ 2. |
| Prime5_a | E | `cov_Prime5_a` | — | From `isPrimitiveRoot_ten_iff_mod_five_eq_two`. |
| Prime5_b | E | `cov_Prime5_b` | — | Same theorem (the converse direction, which the paper claims). |
| Prime5_iff | E | `cov_Prime5_iff` | — | Same theorem. |
| Prime5_reptend | O→E | `cov_Prime5_reptend` (with `decimalPeriod_eq_orderOf`, `ndig_periodic_iff`) | — | Not in the paper. NEW PROOF: for prime q with q ∤ 10, the writer's `decimalPeriod (1/q)` equals `orderOf (10 : ZMod q)`. Combined with `IsPrimitiveRoot.iff_orderOf` this gives the iff. The writer's pure-period definition is the right one here, so the AMBIGUOUS mark is harmless. |
| Prime5_examples | E | `cov_Prime5_examples` | — | Instances of `cov_Prime5_a` (7, 37 and 67 are ≡ 2 mod 5). |
| Prime5_note | E | `cov_Prime5_note` | — | p odd, 4p+1 ≡ 5 (mod 8), 4p+1 ≠ 5. The paper states this in §3 (private lemma `odd_of_eq_four_mul_add_one`); reproved here. |
| Prime6 (Ramesh–Makeshwari) | E | `cov_Prime6` | — | From `prime_of_isLeast_isPrimitiveRoot`. |
| Prime6_obligation | E | `cov_Prime6_obligation` | — | From `exists_isLeast_isPrimitiveRoot`. |
| Prime6_examples | O→E | `cov_Prime6_examples` | — | Uses the repository criterion `isPrimitiveRoot_iff_of_eq_two_mul_add_one` plus `decide` on finite ZMod checks. |
| Prime6_a (least QNR is prime) | O→E | `cov_Prime6_a` | — | The paper does not state this (its proof uses the analogous argument for primitive roots). NEW PROOF. |
| Prime6_a_obligation | O→E | `cov_Prime6_a_obligation` | — | NEW PROOF from `FiniteField.exists_nonsquare` and `Nat.find`. |
| Prime6_b (least primitive root = least QNR) | O→E | `cov_Prime6_b` | — | NEW PROOF. Uses the repository's `isPrimitiveRoot_of_legendreSym_eq_neg_one` (Lemma 4.2) together with `cov_Prime6_b_aux` and `cov_Prime2_d`. |
| Prime6_b_aux (least QNR < p−1) | O→E | `cov_Prime6_b_aux` | — | NEW PROOF: p−1 = 2q, and 2 and q are smaller, hence squares, so their product is a square. |

**Summary**
- E (directly from repository theorems): 10 — Prime4, Prime5_a, Prime5_b, Prime5_iff, Prime5_examples, Prime5_note, Prime6, Prime6_obligation, plus Prime3_b and Prime3_c_part, which rely on repository theorems.
- N closed to E: Prime3_b.
- D: Prime3_c. The classical statement is false for l ≥ 2. This is a source/textbook mis-statement; the paper is correct and narrower (l = 1).
- O (background or not claimed), all proved anyway: Prime1_a/b/c, Prime2_a–d, Prime3_a, the two remarks, Prime5_reptend, Prime6_examples, Prime6_a, Prime6_a_obligation, Prime6_b, Prime6_b_aux.
- **Every one of the 26 statements is resolved:** 25 are proved, and Prime3_c is refuted with a corrected version proved.

## NEW PROOFS (not in the repository)
- `cov_Prime3_b`: the p = 5 case and the "≢ −1" form of the safe-prime criterion.
- `not_classical_Prime3_c`: explicit counterexample p = 19, a = 8.
- `new_Prime3_c_corrected`: correct Wertheim criterion for general l.
- `cov_Prime3_a`: Fermat primes.
- `cov_Prime5_reptend`: decimal period of 1/q = ord_q(10). This needed digit recursion and an injectivity-by-size argument.
- `cov_Prime6_a`, `cov_Prime6_a_obligation`, `cov_Prime6_b_aux`, `cov_Prime6_b`.
- Prime1/Prime2 background: thin wrappers around Mathlib.

## Obligations
- `classical_Prime6_obligation` and `classical_Prime6_a_obligation` are both **proved**.
- No obligation is carried as a hypothesis.
- No construction obligations remain.

## Checks
- **Compile:** `flock ~/l15jack.lock lake env lean scratch/L15_compare.lean` → rc=0, 0 errors, 66 warnings (linter: unused binder names, deprecations), 3.7 s.
- **Forbidden grep:** `grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b" scratch/L15_compare.lean` → no matches (rc=1). No `declaration uses 'sorry'` in the output.
- **#print axioms** (28 theorems: 26 `cov_*`, plus `not_classical_Prime3_c` and `new_Prime3_c_corrected`): every one reports `[propext, Classical.choice, Quot.sound]`. The full list is in `AFM/L14L15/Prime/L15_axioms.txt`.
- **Library hash** (`find … -not -path ./.lake/* -not -path ./scratch/* | sort | xargs sha256sum | sha256sum`):
  - before: `ecd0a52502ef6acf967bdbe8b51943b437ea8f4adacffd9b79595cdd876f323f`
  - after: `ecd0a52502ef6acf967bdbe8b51943b437ea8f4adacffd9b79595cdd876f323f` (unchanged)
  - `git status`: only `?? scratch/`. HEAD is `e30457af…`.
- **Logs on jack:** `~/l15Prime_gate.log`, `~/l15Prime_c3.log` (final), `~/l15Prime_axioms.txt`, `~/l15Prime_hash.pre`.

## Incidents
- The first compile attempt hung: lean sat at 2 s of CPU in `futex_do_wait` for about 10 minutes.
- I killed only my own PIDs (627978/9, 627981, 628030).
- Rerunning with `< /dev/null`, output to a log and `timeout 900` worked: each later compile took about 4 s.

## Wall time
Started 21:29 UTC and finished about 22:10 UTC, roughly 41 minutes.
