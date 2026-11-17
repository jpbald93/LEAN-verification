# L13 WRITER REPORT — Paper I

Writer model: **gpt-6.1-terra** via the Genspark LLM proxy (streaming), 2026-11-09. Not the paper's
author model (Claude Opus 5.5) and not one of its three reviewers (Gemini 4 Argon, GPT-6 Astra,
Claude Opus 5.5). No tools, no repository access, no web access: the model was given only the
contents of `paperi_blind.txt` (the paper with Lean names, code listings, repo URLs and the
code/verification sections stripped) plus the writing rules. Files the writer "read": only the text
placed in its prompt; it had no file-system or browsing capability.

Output: `Blind.lean` — 78 statements, all `:= by sorry`, names `blind_1..blind_78` in
paper order, each preceded by its paper label and the theorem's first sentence.
Type-check on john (arm64, Lean v4.33.1 + Mathlib, `~/lean/reformalH/PaperIBlind.lean`):
**0 errors, 78 "declaration uses sorry" warnings** (one per statement).

Ambiguous readings flagged by the writer: 13
-- AMBIGUOUS: The omitted condition on X could instead be stated using
-- AMBIGUOUS: The arbelos may instead mean only its three semicircular arcs.
-- AMBIGUOUS: The twin circles may be specified by their explicit centers and
-- AMBIGUOUS: A Pappus chain may be indexed from the other inner semicircle.
-- AMBIGUOUS: A Steiner chain may also be defined for two non-nested circles.
-- AMBIGUOUS: “Simple” can instead mean that the chain has no self-intersections.
-- AMBIGUOUS: A coaxal pencil may include oriented circles, lines, or
-- AMBIGUOUS: Inversion can instead be a partial map undefined at its center.
-- AMBIGUOUS: A Peaucellier cell may include an additional driving linkage
-- AMBIGUOUS: Curvature may mean the unsigned reciprocal of the radius.
-- AMBIGUOUS: The points may also be required to occur in the stated order on the circumcircle.
-- AMBIGUOUS: The passage does not explicitly define the inversion or its radius.
-- AMBIGUOUS: Tangency without a positive radius may instead be interpreted using a nonnegative-radius convention.

## Statement list (name → paper label → first sentence)
| name | label | gloss |
|---|---|---|
| blind_1 | thm:bretschneider | For every convex quadrilateral ABCD, Bretschneider's formula holds. |
| blind_2 | thm:brahmagupta | For every convex quadrilateral ABCD with A, B, C, D concyclic, Brahmagupta's formula holds. |
| blind_3 | thm:pitot | Let ABCD be convex. |
| blind_4 | thm:pitot | Conversely, if a + c = b + d, then ABCD is tangential. |
| blind_5 | thm:euler4 | For any four points, a² + b² + c² + d² = |AC|² + |BD|² + 4|MN|², where M and N are the midpoints of AC and BD. |
| blind_6 | thm:ptolemy2 | For every convex quadrilateral ABCD with A, B, C, D concyclic, Ptolemy's second theorem holds. |
| blind_7 | thm:vanaubel | Let o be an orientation of the plane and A, B, C, D any four points. |
| blind_8 | thm:vanaubel | Let o be an orientation of the plane and A, B, C, D any four points. |
| blind_9 | thm:newton | If ABCD is convex and (I, r) is an incircle, then the midpoints of AC and BD and the centre I are collinear. |
| blind_10 | thm:fuss | Let ABCD be convex, let A, B, C, D lie at distance R from a point O, and let (I, r) be an incircle of ABCD. |
| blind_11 | thm:fuss | In Theorem thm:fuss nothing is assumed about d or R; the proof shows that R² - d² > 0. |
| blind_12 | thm:fuss | For a convex tangential quadrilateral with O the circumcentre of ABC the relation fails in general. |
| blind_13 | thm:fuss | AMBIGUOUS: The points may also be required to occur in the stated order on the circumcircle. |
| blind_14 | thm:twin | Let a,b>0 and let s be a circle tangent to ℓ, internally tangent to Γ and externally tangent to Γ₁, with centr |
| blind_15 | thm:twin | The same holds with Γ₂ for a circle to the right of ℓ. |
| blind_16 | thm:twin | Both circles exist, with centres in the upper half plane. |
| blind_17 | thm:area | Let a,b>0 and let D be a point of Γ on ℓ. |
| blind_18 | thm:pappus | Let a,b>0 and n∈ℕ. |
| blind_19 | thm:pappus | Let a,b>0 and n∈ℕ. |
| blind_20 | thm:pappus | Let a,b>0 and n∈ℕ. |
| blind_21 | thm:pappus | Let a,b>0 and n∈ℕ. |
| blind_22 | thm:pappus | Let a,b>0 and n∈ℕ. |
| blind_23 | thm:pappus | Every circle of positive radius internally tangent to Γ and externally tangent to Γ₁ is φₜ with t equal to its |
| blind_24 | thm:pappus | If (c'ₙ)ₙ∈ℕ is a sequence of circles of positive radius with c'₀=Γ₂, each internally tangent to Γ and external |
| blind_25 | thm:pappus | In the indexing that starts from the incircle, cₙ₊₁, the height is (n+1) times the diameter. |
| blind_26 | thm:pappus | The height formula itself is an identity of the family and holds for all real a,b. |
| blind_27 | thm:pappusinv | Then ι maps Γ∖{A} onto the line Re z=2a, Γ₁∖{A} onto the line Re z=2(a+b), and cₙ onto the circle of radius b  |
| blind_28 | thm:pappusinv | Then ι maps Γ∖{A} onto the line Re z=2a, Γ₁∖{A} onto the line Re z=2(a+b), and cₙ onto the circle of radius b  |
| blind_29 | thm:pappusinv | Then ι maps Γ∖{A} onto the line Re z=2a, Γ₁∖{A} onto the line Re z=2(a+b), and cₙ onto the circle of radius b  |
| blind_30 | thm:bankoff | Let a,b>0. |
| blind_31 | thm:steiner | Let S₁,S₂ be circles with S₁ of positive radius and strictly inside S₂, i.e. |O₁O₂|<ρ₂−ρ₁. |
| blind_32 | thm:steiner | If the given chain is simple, d can be chosen simple; if it is simple with disjoint discs, d can be chosen sim |
| blind_33 | thm:steiner | If the given chain is simple, d can be chosen simple; if it is simple with disjoint discs, d can be chosen sim |
| blind_34 | thm:steiner | AMBIGUOUS: Tangency without a positive radius may instead be interpreted using a nonnegative-radius convention |
| blind_35 | thm:steiner | The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), th |
| blind_36 | thm:steiner | The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), th |
| blind_37 | thm:steiner | The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), th |
| blind_38 | thm:steiner | The identity that drives everything is |cₜ−cᵤ|²−(ρₜ+ρᵤ)²=4ρₜρᵤ((t−u)²−1). |
| blind_39 | thm:steiner | The identity that drives everything is |cₜ−cᵤ|²−(ρₜ+ρᵤ)²=4ρₜρᵤ((t−u)²−1). |
| blind_40 | thm:radical | In any V, the radical axis of (O₁,R₁) and (O₂,R₂) is the stated level set. |
| blind_41 | thm:radical | If O₁ ≠ O₂, the radical axis is an affine subspace with the stated direction. |
| blind_42 | thm:radical | If O₁ ≠ O₂, the radical axis is a line when dim V = 2. |
| blind_43 | thm:radical | If dim V = 2 and O₁,O₂,O₃ are not collinear, there is exactly one point on the three pairwise radical axes. |
| blind_44 | thm:coaxal | In any V, the member t of the pencil has the stated centre and squared radius. |
| blind_45 | thm:coaxal | Any two members with distinct parameters have the radical axis of the generators. |
| blind_46 | thm:coaxal | A common point of the generators lies on every member. |
| blind_47 | thm:coaxal | If dim V = 2 and R₁,R₂ > 0, the circles are orthogonal if and only if the stated power equality holds. |
| blind_48 | thm:johnson | In any V, let three circles of the same radius R have centres O₁,O₂,O₃ and pass through a common point H. |
| blind_49 | thm:johnson | In any V, let three circles of the same radius R have centres O₁,O₂,O₃ and pass through a common point H. |
| blind_50 | thm:johnson | In the plane, when the circles are distinct and not tangent, these are their second pairwise intersections. |
| blind_51 | thm:johnson | Moreover H is the orthocentre of ABC. |
| blind_52 | thm:simson | Let |AO|=|BO|=|CO|=R with A,B,C pairwise distinct. |
| blind_53 | thm:simson | If dim V = 2 and A,B,C are not collinear, then D,E,F are collinear if and only if |PO|=R. |
| blind_54 | thm:simson | The foot D of the perpendicular from P to the chord XY of the circle |z|=R satisfies the stated identity. |
| blind_55 | thm:steinerline | Let dim V=2, |AO|=|BO|=|CO|=|PO|=R with A,B,C pairwise distinct. |
| blind_56 | thm:ptolemyinv | In any V, let P,Q,S≠0 and R≠0. |
| blind_57 | thm:ptolemyinv | In any V, let P,Q,S≠0 and R≠0. |
| blind_58 | thm:ptolemyinv | Three points are collinear if and only if one of the three triangle inequalities between them is an equality. |
| blind_59 | thm:ptolemyinv | In ℂ, if 0,P,Q,S lie on one circle (|P-K|=|Q-K|=|S-K|=|K|) with P,Q,S≠0, then P',Q',S' are collinear and one o |
| blind_60 | thm:ptolemyinv | In ℂ, if 0,P,Q,S lie on one circle (|P-K|=|Q-K|=|S-K|=|K|) with P,Q,S≠0, then P',Q',S' are collinear and one o |
| blind_61 | thm:peaucellier | Under these hypotheses, 0, P, Q are collinear; if moreover P≠Q, then P+Q=A+B and ⟨P,Q⟩=b²-a². |
| blind_62 | thm:peaucellier | Under these hypotheses, 0, P, Q are collinear; if moreover P≠Q, then P+Q=A+B and ⟨P,Q⟩=b²-a². |
| blind_63 | thm:peaucellier | Under these hypotheses, 0, P, Q are collinear; if moreover P≠Q, then P+Q=A+B and ⟨P,Q⟩=b²-a². |
| blind_64 | thm:peaucellier | If b²-a²=R² (the classical cell), then Q=inv_R(P) and |P||Q|=R²; if moreover P lies on a circle through the pi |
| blind_65 | thm:peaucellier | If b²-a²=R² (the classical cell), then Q=inv_R(P) and |P||Q|=R²; if moreover P lies on a circle through the pi |
| blind_66 | thm:peaucellier | If b²-a²=R² (the classical cell), then Q=inv_R(P) and |P||Q|=R²; if moreover P lies on a circle through the pi |
| blind_67 | thm:peaucellier | If a²-b²=R², then Q=-inv_R(P), |P||Q|=R², and under |P-C|=|C| the point Q lies on the line ⟨Q,C⟩=-R²/2. |
| blind_68 | thm:peaucellier | If a²-b²=R², then Q=-inv_R(P), |P||Q|=R², and under |P-C|=|C| the point Q lies on the line ⟨Q,C⟩=-R²/2. |
| blind_69 | thm:peaucellier | If a²-b²=R², then Q=-inv_R(P), |P||Q|=R², and under |P-C|=|C| the point Q lies on the line ⟨Q,C⟩=-R²/2. |
| blind_70 | thm:descartes | Let c₁,…,c₄∈ℂ and r₁,…,r₄≠0 with |cᵢcⱼ|²=(rᵢ+rⱼ)² for all i<j. |
| blind_71 | thm:soddy | Let c₁,…,c₅∈ℝ³ and r₁,…,r₅≠0 with |cᵢcⱼ|²=(rᵢ+rⱼ)² for all i<j. |
| blind_72 | thm:apollonian | For reals k₁,…,k₄, the Descartes relation holds if and only if k₁k₂+k₂k₃+k₃k₁≥0 and k₄=k₁+k₂+k₃±2√(k₁k₂+k₂k₃+k |
| blind_73 | thm:apollonian | Two distinct solutions k⁺ and k⁻ satisfy k⁺+k⁻=2(k₁+k₂+k₃) and k⁺k⁻=2(k₁²+k₂²+k₃²)-(k₁+k₂+k₃)². |
| blind_74 | thm:apollonian | Two distinct solutions k⁺ and k⁻ satisfy k⁺+k⁻=2(k₁+k₂+k₃) and k⁺k⁻=2(k₁²+k₂²+k₃²)-(k₁+k₂+k₃)². |
| blind_75 | thm:apollonian | If (k₁,k₂,k₃,k₄) satisfies the relation, so does (k₁,k₂,k₃,2(k₁+k₂+k₃)-k₄). |
| blind_76 | thm:apollonian | Consequently every quadruple reached from an integral Descartes quadruple by such moves (in any coordinate, an |
| blind_77 | thm:apollonian | Consequently every quadruple reached from an integral Descartes quadruple by such moves (in any coordinate, an |
| blind_78 | thm:apollonian | An unnamed result in the library checks that the move on the first curvature takes (-1,2,2,3) to (15,2,2,3). |
