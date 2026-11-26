# Restatements

## 1. Spherical Clifford chain in all levels at least three

For every natural number n with n at least 3, the spherical Clifford-chain assertion holds at level n: for every n-indexed configuration of complex centres in general position, there exists a subset of the Riemann sphere which is a spherical Clifford object of level n for that configuration. The objects are those defined recursively on the Riemann sphere: level 0 is the singleton containing the origin, level 1 is the corresponding circle through the origin embedded in the sphere, level 2 is the singleton containing the second intersection point, odd levels at least 3 are generalized circles in the sphere containing suitable lower-level points for all one-entry deletions, and even levels at least 4 are singletons whose point lies on suitable lower-level generalized circles for all one-entry deletions.

HYPOTHESES: n is at least 3.
STRENGTH: universal
TRAP: Stating this for all n, or as a finite-plane result; the signature only covers the spherical version and only assumes n >= 3.

## 2. Odd spherical incidence for the canonical projective points

For every natural number k and every configuration d of 2k + 5 complex centres in general position, there exists a generalized circle in the Riemann sphere such that, for each choice of one centre to delete from d, the canonical projective level point of the resulting 2k + 4 centre configuration lies on that generalized circle. The canonical projective level point is the point on the Riemann sphere obtained from the cross-vector formula: it is the finite ratio point when the relevant middle coordinate is nonzero and is the point at infinity when that coordinate vanishes.

HYPOTHESES: none beyond general position of the 2k + 5 centre configuration.
STRENGTH: existential
TRAP: Saying merely that some level-(2k + 4) Clifford point from each deletion lies on a circle; the theorem names the specific canonical projective point for each deletion.

## 3. Even spherical incidence for the canonical projective point

For every natural number k, every configuration c of 2k + 6 complex centres in general position, and every index i of the configuration, there exists a generalized circle in the Riemann sphere which contains the canonical projective level point of the full 2k + 6 centre configuration and, for every index j of the configuration obtained by deleting the i-th centre, also contains the canonical projective level point of the 2k + 4 centre configuration obtained by deleting first i and then j from the remaining entries.

HYPOTHESES: none beyond general position of the 2k + 6 centre configuration and the chosen deletion index i.
STRENGTH: existential
TRAP: Forgetting the first incidence condition: the circle must contain the full level-(2k + 6) canonical projective point as well as all the doubly-deleted level-(2k + 4) canonical projective points.

## 4. Exact finite-plane classification

For every natural number n, the finite-plane Clifford-chain assertion at level n holds if and only if n is at most 5. Here the assertion is: every n-indexed configuration of complex centres in general position has some finite-plane Clifford object of level n, with the recursive Clifford objects taken as subsets of the complex plane rather than of the Riemann sphere. The finite-plane recursion uses the same base levels and odd/even alternation: odd levels at least 3 require a generalized circle in the plane containing lower-level points, and even levels at least 4 require a singleton point lying on lower-level objects.

HYPOTHESES: none beyond the natural number n in the statement of the classification.
STRENGTH: universal
TRAP: Reading this as a classification of the spherical predicate; it classifies the finite-plane predicate, not the sphere-valued one.

## 5. The six-centre finite-plane counterexample, as typed

The displayed six-centre configuration with centres (3,-6), (6,-3), (1,2), (-2,-1), (0,-4), and (4,0), regarded as complex numbers with those real and imaginary parts, is in general position. Separately, the universal finite-plane Clifford-chain assertion at level 6 is false: it is not true that every general-position configuration of six complex centres has a finite-plane Clifford object of level 6.

HYPOTHESES: none; the six centres are fixed explicitly.
STRENGTH: canonical witness
TRAP: Claiming from these two theorem types alone that the fixed six-centre configuration itself has no finite-plane level-6 object; that is the intended witness, but the exported negative theorem is typed only as the failure of the universal level-6 predicate.

## 6. The same six-centre configuration on the sphere

For the fixed six-centre configuration (3,-6), (6,-3), (1,2), (-2,-1), (0,-4), and (4,0), the singleton consisting of the point at infinity is a spherical Clifford object of level 6. Moreover, it is unique: every spherical Clifford object of level 6 for this fixed configuration is exactly that singleton.

HYPOTHESES: none; the six centres are fixed explicitly.
STRENGTH: canonical witness
TRAP: Restating this as mere existence of a spherical level-6 object; the pair of signatures asserts the specific object and its uniqueness.

## 7. Level three of the spherical chain predicate

The level-three spherical Clifford-chain assertion says that every general-position configuration of three complex centres has a spherical Clifford object of level 3. Unfolding the recursion, this means that there exists a generalized circle in the Riemann sphere such that, for each of the three ways of deleting one centre, there is a level-2 spherical Clifford singleton for the remaining pair and its point lies on that generalized circle. Since level 2 is the singleton containing the second intersection point of the corresponding pair of circles, this is the assertion that the three pairwise second intersection points, embedded in the Riemann sphere, lie on some generalized circle.

HYPOTHESES: none beyond general position of the three-centre configuration.
STRENGTH: existential
TRAP: Forgetting that this is the predicate for all three-centre configurations, not a statement about one fixed triple.

# Where The Signatures Are Weaker Than A Reader Would Expect

The all-level spherical chain theorem starts at n >= 3. Anyone quoting it for levels 0, 1, or 2 must use the definitions or separate base results, not this signature.

The odd and even incidence theorems assert only existence of a generalized circle containing the specified canonical projective points. They do not assert that the witness circle is unique, nor that it is the same as any independently defined Clifford object except insofar as the named canonical points are used.

The even incidence theorem gives a separate generalized circle for each chosen deletion index i. It does not assert one circle working uniformly for all i.

The finite-plane classification is about the universal predicate for all general-position configurations at level n. It does not, by itself, identify which configurations fail when n >= 6.

The six-centre counterexample is split into a general-position theorem for the fixed configuration and a theorem that the universal level-6 finite-plane predicate is false. The negative theorem's type does not explicitly state that this very configuration lacks a finite-plane level-6 object, so quoting that specific failure requires an additional theorem or inspection beyond these two exported types.

The spherical six-centre uniqueness theorem is only for the fixed six-centre configuration. It does not claim uniqueness of spherical level-6 Clifford objects for arbitrary six-centre configurations.

The level-three item, as a predicate, asserts existence of some generalized circle through the three second intersections. It does not specify a canonical circle or uniqueness, and generalized circles include lines through the point at infinity in the spherical setting.
