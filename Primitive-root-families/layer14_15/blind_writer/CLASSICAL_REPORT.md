# CLASSICAL_REPORT — Paper Prime (blind classical writer, layer 15)

Output: `/tmp/blindPrime/Classical.lean`, which is byte-identical to `jack:~/reformal/PaperPrimeClassical.lean` (both have md5 58d5140893c2505bc622fffed2437982).
Everything is in `namespace PaperPrimeClassical`, and every theorem is `:= by sorry`.

## Conventions
- Congruences use `Int.ModEq` (`a ≡ b [ZMOD p]`). The Legendre symbol is Mathlib's `legendreSym p a`, which needs `[Fact p.Prime]`.
- "p odd" is written `p ≠ 2`.
- The primitive-root and QR/QNR notions are Mathlib notions in `ZMod p`, wrapped in `abbrev`s:
  - `IsPrimRootMod p g := IsPrimitiveRoot (g : ZMod p) (p - 1)`. This says the order is p−1. For prime p it also forces p ∤ g.
  - `IsQR p a := (a : ZMod p) ≠ 0 ∧ IsSquare (a : ZMod p)`
  - `IsQNR p a := (a : ZMod p) ≠ 0 ∧ ¬ IsSquare (a : ZMod p)`

## Invented definitions (OWN DEFINITION)
- `IsSafePrime p := p.Prime ∧ ∃ q, q.Prime ∧ p = 2*q+1`
- `decimalDigit x k := ⌊10^k · x⌋ mod 10`, the k-th digit after the decimal point.
- `decimalPeriod x := sInf {n > 0 | ∀ k ≥ 1, digit (k+n) = digit k}`. This is the period of a purely periodic expansion; the junk value is 0.
  **AMBIGUOUS:** "period" could also mean the eventual period. For 1/q with gcd(q,10)=1 the two coincide.

## Statements
| Name | Content |
|---|---|
| Prime1_a | Euler's criterion: a^((p−1)/2) ≡ (a/p) mod p, for p odd and p ∤ a |
| Prime1_b / _c | QR ↔ a^((p−1)/2) ≡ 1; QNR ↔ a^((p−1)/2) ≡ −1 |
| Prime2_a | primitive root ↔ g^((p−1)/r) ≢ 1 for every prime r ∣ p−1 (with p ∤ g) |
| Prime2_b / _c | if g is a primitive root and p is odd: (g/p) = −1, and g^((p−1)/2) ≡ −1 |
| Prime2_d | for odd p, no QR is a primitive root |
| Prime3_a | Fermat primes (p−1 = 2^k, k ≥ 1): primitive root ↔ (a/p) = −1 |
| Prime3_b | p = 2q+1: primitive root ↔ (a/p) = −1 ∧ a ≢ −1 |
| Prime3_b_remark5 / remark7 | −1 is a QR mod 5; for a safe p ≥ 7, (−1/p) = −1 and ord(−1) = 2 |
| Prime3_c | Wertheim: p = 2^k q^l + 1 with q an odd prime and k, l ≥ 1; (a/p) = −1 and a^(2^k) ≢ 1 imply a is a primitive root |
| Prime4 | q an odd prime and 4q+1 prime ⇒ 2 is a primitive root mod 4q+1 |
| Prime5_a / _b / _iff | p and 4p+1 prime: 10 is a primitive root mod 4p+1 ↔ p ≡ 2 (mod 5) |
| Prime5_reptend | 10 is a primitive root mod q ↔ decimalPeriod(1/q) = q−1 (for q = 4p+1) |
| Prime5_examples | 10 is a primitive root mod 29, 149, 269 |
| Prime5_note | p odd, q ≡ 5 (mod 8), q ≠ 5 |
| Prime6 | safe prime p: the least positive primitive root (`IsLeast`) is prime |
| Prime6_examples | 5→2, 7→3, 11→2, 23→5, 47→5 |
| Prime6_a | odd prime p: the least positive QNR is prime |
| Prime6_b | safe prime: least positive primitive root = least positive QNR (stated as an iff of `IsLeast`) |
| Prime6_b_aux | for a safe prime, the least QNR is < p−1 |

## Obligations (well-formedness)
- `classical_Prime6_obligation`: for prime p, a least positive primitive root exists.
- `classical_Prime6_a_obligation`: for an odd prime p, a least positive QNR exists.
- The main statements are phrased with `IsLeast`, so they type-check without these obligations; the obligations show that the statements are not vacuous.

## AMBIGUOUS / EXTRA HYPOTHESIS marks
- AMBIGUOUS: the period in `decimalPeriod` (pure vs eventual), as explained above.
- No EXTRA HYPOTHESIS was needed. Specific choices:
  - Prime3_c has no explicit p ∤ a, because (a/p) = −1 already implies it.
  - Prime5 has no oddness hypothesis on p, because the note says it follows from the other hypotheses.
  - Prime2_d needs p odd because the source corollary assumes it (for p = 2, 1 is both a QR and a primitive root).

## Compiler summary
`lake env lean PaperPrimeClassical.lean` on jack produces 26 warnings, all `declaration uses 'sorry'`, and no errors. Both the first version and the final version (using Mathlib's `IsPrimitiveRoot`/`IsSquare`) compiled cleanly.

## Files read
- `/tmp/blindPrime/classical_statements.txt`, the only file read.
- I also ran `ls /tmp/blindPrime`, which showed the names `brief.txt` and `scratch`. I did not open `brief.txt`.
- I wrote `/tmp/blindPrime/Classical.lean` and this report. No scratch files were needed. There was no web access.
