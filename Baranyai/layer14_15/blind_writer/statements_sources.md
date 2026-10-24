# Sources and notes for Baranyai statements

## Citations
1. Zs. Baranyai, "On the factorization of the complete uniform hypergraph", in
   A. Hajnal, R. Rado, V. T. Sós (eds.), *Infinite and Finite Sets* (Proc. Colloq.
   Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10, North-Holland, 1975,
   pp. 91–107. (Original paper; proves the general almost-regular form via
   network flows / integrality.)
2. J. H. van Lint and R. M. Wilson, *A Course in Combinatorics*, 2nd ed.,
   Cambridge University Press, 2001, Chapter 38 ("Baranyai's theorem"),
   Theorem 38.1 and its corollary (the k | n parallel-class form).
3. Wikipedia, "Baranyai's theorem",
   https://en.wikipedia.org/wiki/Baranyai%27s_theorem (hypergraph form:
   K_k^r with r | k decomposes into 1-factors; count C(k-1,r-1)).

## Notes
- Baranyai1 and Baranyai2 are the same theorem in two languages (hypergraph
  1-factorization vs. partition of the k-subsets into parallel classes).
  The number of classes C(n-1,k-1) is forced by counting: C(n,k) / (n/k).
- Hypotheses: the only real hypothesis is k | n. Wikipedia states it with
  2 <= r < k (i.e. 2 <= k < n in our notation); the degenerate cases are
  trivial and usually included implicitly: k = n gives the single class {X};
  k = 1 gives the single partition into singletons (C(n-1,0) = 1). Some
  sources also allow n = 0 / k arbitrary vacuously; the most common form is
  "positive integers k | n". The case k = 2 is the classical 1-factorization
  of K_n for even n; k = 3 was done by Peltesohn (1936); the case
  n = 2k is "easy" (pair each k-set with its complement).
- Baranyai3 (van Lint–Wilson Thm 38.1, as recalled; based on Baranyai 1975) is
  the general almost-regular-partition form; it does not need k | n.
  The exact wording in van Lint–Wilson is from memory, not verified against
  the printed page; the divisible-case statements (Baranyai1/2) were checked
  against Wikipedia.
