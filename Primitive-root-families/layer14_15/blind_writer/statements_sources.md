# Sources and notes for classical_statements.txt

## Prime1 (Euler's criterion)
- Any standard text, e.g. D. M. Burton, *Elementary Number Theory*, Ch. 9 (Euler's criterion, Theorem 9.1); Hardy & Wright, *An Introduction to the Theory of Numbers*, Thm 83.
- Wikipedia, "Euler's criterion": https://en.wikipedia.org/wiki/Euler%27s_criterion

## Prime2 (primitive-root test)
- L. E. Dickson, *History of the Theory of Numbers*, Vol. I, Ch. VII, p. 188. It records that P. L. Tchebychef (*Teoria sravnenii*, 1849; German transl. *Theorie der Congruenzen*, 1889) "proved that if α, β, … are the distinct prime factors of p−1 … a is a primitive root of p if and only if no one of the congruences x^α ≡ a, … (mod p) has an integral root." That is equivalent to the stated power test. Text: https://archive.org/details/HistoryOfTheTheoryOfNumbersI
- Burton, *Elementary Number Theory*, Ch. 8.

## Prime3 (Legendre-symbol characterisations)
- Wikipedia, "Safe and Sophie Germain primes" (section on modular restrictions/primitive roots): "For a safe prime, every quadratic nonresidue, except −1 (if nonresidue), is a primitive root." Note [a] there: −1 is a residue only for the safe prime 5. https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes
- Dickson, *History*, Vol. I, p. 196: M. Frolov noted that the quadratic non-residues of a prime m are primitive roots if m = 2^n+1 or m = 2n+1 ... with n an odd prime [Tchebychef]. Also p. 196: G. Wertheim (Acta Math. 1894/5) showed that if p = 2^k q^l + 1 is prime with q an odd prime, then any non-residue m with m^(2^k) − 1 not divisible by p is a primitive root. This is the source for Prime3(c).
- **Disagreement / caution:** Dickson's summary of Frolov also lists m = 4n+1 (n an odd prime) without an extra condition. Read literally that is false: for m = 13 = 4·3+1, 5 is a non-residue of order 4. Wertheim's form with the condition a^(2^k) ≢ 1 (here a^4 ≢ 1) is the correct version, so I gave that form. For safe primes the literature usually says "except −1", which matches (b). Some sources state (b) only for p > 5, or for p ≥ 7. My statement covers p = 5 as well, where the condition is vacuous.
- Fermat primes (a): standard. The group (Z/p)^* is cyclic of 2-power order, so the generators are exactly the non-squares. See also Pépin's test (3 is a primitive root of every Fermat prime F_n, n ≥ 1). Wikipedia, "Pépin's test": https://en.wikipedia.org/wiki/P%C3%A9pin%27s_test

## Prime4 (2 is a primitive root of 4q+1)
- Dickson, *History*, Vol. I, p. 188, on Tchebychef's *Theorie der Congruenzen*, second supplement: "2 is a primitive root of any prime 4N+1 such that N is an odd prime". Same place: "±2 is a primitive root of any prime 2a+1 such that a is a prime 4k±1"; "3 is a primitive root of any prime 2^m+1".
- Burton, *Elementary Number Theory*, Ch. 8 exercises (attributed to Chebyshev).

## Prime5 (10 as a primitive root of 4p+1)
- Direct source: Dickson, *History*, Vol. I, p. 192 (V. Bouniakowsky) and p. 197 (G. Wertheim). Both record criteria for 10 being a primitive root of primes 2q+1, 4q+1, 8q+1, 16q+1 in terms of the residue of q mod 10, as corollaries of the Tchebychef/Wertheim non-residue theorem (Prime3(c)). E.g. Bouniakowsky: "10 is a primitive root of p = 40n+7, 19, 23 … if (p−1)/2 is a prime". Wertheim: "10 is a primitive root of … primes 16g+1 for which g is a prime 10k+1 or 10k+7".
- I did **not** find an online, verbatim source giving exactly "p ≡ 2 (mod 5) ⇔ 10 is a primitive root of 4p+1" under Chebyshev's name. The statement follows from Prime3(c) with k = 2, l = 1. Since q ≡ 5 (mod 8), (2/q) = −1. By reciprocity (5/q) = (q/5), and q ≡ 4p+1 ≡ 4 (mod 5) iff p ≡ 2 (mod 5). Also q ∤ 10^4 − 1 = 3²·11·101, because 101 = 4·25+1 with 25 not prime. Converse: if p ≢ 2 (mod 5), then either q = 5 (impossible, since p = 1) or p = 5 (q = 21, not prime), or q ≡ 2, 3 (mod 5), so (10/q) = +1 and 10 is not a primitive root.
- The "classical form" (direction (a)) is the one usually quoted as an exercise. Direction (b) is the converse. Both are included, as asked in the brief.
- Background: Wikipedia, "Full reptend prime" (10 is a primitive root mod p ⇔ 1/p has period p−1): https://en.wikipedia.org/wiki/Full_reptend_prime

## Prime6 (Ramesh–Makeshwari)
- V. P. Ramesh and M. Makeshwari, "Least Primitive Root of any Safe Prime is Prime", *The American Mathematical Monthly* 129 (2022), no. 10, p. 971 (published 16 Sept 2022). Cited in Wikipedia, "Safe and Sophie Germain primes": "It follows that for a safe prime, the least positive primitive root is a prime number."
- Lemma (a) is classical: a product of residues is a residue, so the least non-residue cannot be composite. See e.g. Burton Ch. 9, or Wikipedia "Quadratic residue".
- Note: the convention on whether 5 counts as a safe prime varies. Wikipedia includes 5 (q = 2). The theorem holds for p = 5 too (least primitive root 2).
