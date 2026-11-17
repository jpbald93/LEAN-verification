# Paper K — draft-v1 review triage (`REVIEW_k_draft1.md`)

Reviewer: claude-opus-5-5, 2026-11-16, against `paperk.tex` sha `6d1eb2df` and the pinned snapshot
`repo_snapshot_62ccf87` (no ssh). Verdict: **major revision**, 12 MAJOR / 25 MINOR, no new Lean required.
Every row below is dispositioned; nothing dropped.

Result: **all 36 applied** in the draft now at 15 pp. Numbers rows (#11, #12) were re-quoted at the new pin
`464a59d`, where the general-n file is inside the gate — so the "needs update after promotion" caveat is
resolved rather than deferred. Standing negative result kept visible in the abstract and §7: the completion
map does not fix `P_X`.

| # | sev | where | disposition |
|---|---|---|---|
| 1 | MAJOR | §4 Thm 1, spanning hypothesis | **APPLIED**: statement now quantifies over vectors $Y\in\RR^5$ and says no null-cone hypothesis on $X_1..X_4,A,A'$ is used — which is what `PaperK.prop31` proves |
| 2 | MAJOR | §6 Thm 4 "Let $P$ be a cycle" | **APPLIED**: "any vector with $P_3\neq0$", since `power_eq_of_B_eq_zero` has no null hypothesis on $P$ (a null $P$ would make the constant 0). Same change in §7's equal-circles sentence |
| 3 | MAJOR | §8 the "fifth cycle" | **APPLIED**: `(0,(1/2,1/2),1,3/2)` is `cex_P`, i.e. $P$ itself; the extra cycle is $X_0$ of radius 3 at $(3,3)$. Text now says four cycles and $X_0$ |
| 4 | MAJOR | §5 caution 1, the hand derivation | **APPLIED**: rewritten. The obvious derivation is *wrong* (rows $(r,a,b,s,1)$ are not cycles; $G\cdot$cofactor of that matrix is $B$-orthogonal to the rows, and on a random instance gives $(1.266,-4.738)$ against $p=(1.821,-6.819)$). Text now gives L15's vector $P=(q_0,-q_1,-q_2,2q_3,-q_4)$, notes $P_3=-2D$, and drops "the whole of the missing content" |
| 5 | MAJOR | §5 Thm 2 title, abstract, §1 | **APPLIED**: title "Explicit equal-power point and radius"; abstract and §1 now say the identification with $P_X$ is a hand derivation, not a theorem |
| 6 | MAJOR | abstract + §2 signature | **APPLIED**: $(n+1,2)$ in both, with the two negative directions named |
| 7 | MAJOR | abstract/§1/§11 cofactor scope | **APPLIED**: cofactor "at $n=2$, from $n+2$ cycles"; §11 bullet 1 says cofactor at $n=2$ |
| 8 | MAJOR | abstract/§1 "characterisation" | **APPLIED**: "the equal-power property of $P_X$" — one direction is what is proved |
| 9 | MAJOR | abstract "we prove is necessary" | **APPLIED**: "cannot be dropped: a Lean counterexample at $n=2$" |
| 10 | MAJOR | §11 prior art | **APPLIED**: first-pass search named (arXiv, GitHub, Mathlib, AFP; zbMATH/MathSciNet not searched), pre-draft re-run stated as not made, "October 2026" dropped, `\cite{augdescartes}` added |
| 11 | MAJOR | abstract "gated (60 declarations)" | **APPLIED** and re-based on the promotion: "gated (73 declarations, the general-$n$ file included)" |
| 12 | MINOR | every sentence depending on the pin | **APPLIED**: `\pkcommit` → `464a59d`; gate 73; battery re-run at the new pin; `\S` availability five files (272/332/217/438/294); two-machine receipt at 464a59d; §9 intro says all figures come from one commit |
| 13 | MAJOR | §6 Thm 3 "space of cycles" | **APPLIED**: "space of *vectors*", neither spanning vector null, and the source-gap sentence is qualified to affine cycles with the line case named as a hand argument |
| 14 | MAJOR | §9 Layer 14 credit | **APPLIED**: naming error → L14c audit + L15; equal-norm → general-$n$ run; determinant sign → §5 numerics, both before Layer 14 |
| 15 | MINOR | §3 tangency error term | **APPLIED**: $-\bigl((Y_3)^2B(X,X)+(X_3)^2B(Y,Y)\bigr)$ — the $v$-slots with a minus sign |
| 16 | MINOR | §5 "$w$-slot read as a radius" | **APPLIED**: "$r$-slot divided by its $v$-slot" |
| 17 | MINOR | §5 powers to $10^{-15}$ "in the K1 report" | **APPLIED**: cites `k0/FORMULA.md`, and says K1 quotes the common value without a tolerance |
| 18 | MINOR | §10 plane encoding | **APPLIED**: $(1,n_1,\dots,n_n,0,h)$ is the cycle of the plane $\{x:n\cdot x=-h\}$ |
| 19 | MINOR | §10 residual $\le5\times10^{-14}$ | **APPLIED**: $\le8.7\times10^{-14}$, `EXTENSION.md` §1 |
| 20 | MINOR | §2 $(n+2)\times(n+3)$ system | **APPLIED**: orthogonality to all $n+2$ cycles; complement of the other $n+1$ is 2-dimensional |
| 21 | MINOR | §6 `Sphere.power` radius | **APPLIED**: radius $\rho-r$, i.e. the Laguerre power of the two cycles |
| 22 | MINOR | §7 "neither of which the source excludes" | **APPLIED**: the source excludes equality but not concentricity |
| 23 | MINOR | §7 removability | **APPLIED**: the pair of the three equal circles is always concentric, so their centre-line never exists; the point is fixed; continuity is numerical (`EXTENSION.md` §2) |
| 24 | MINOR | §7 tetrahedron | **APPLIED**: "two Apollonius cycles … centred at $P_X$" (no "exactly two"), and tangency verified in the B-form, as two real identities, and against Mathlib's *unsigned* predicates via `bridge_sph_isExtTangent` |
| 25 | MINOR | §7 rename paragraph | **APPLIED**: text records that the docstring still says "Thm 3.6 conclusion…" (queued for the next commit) and that L15 ran on the pre-rename file |
| 26 | MINOR | §7 simplex | **APPLIED**: $P_v\neq0$, the unused extra-cycle hypothesis named, and the circumcentre identification restricted to $n=2$ with `dist_sq_const` cited for general $n$ |
| 27 | MINOR | §9 gate meaning | **APPLIED**: "checks axioms, not meaning", and says the other theorems are covered by the token scan and the build only |
| 28 | MINOR | §9 battery | **APPLIED**: baseline build added (nine layers), 444/460 with 16 survivors, 73/127 satisfiable, ablation 238/4, linter 0 + the `unnecessarySeqFocus` warning, Layer 9 24/3/21 with the matcher caveat, and the three theorems with no mutants |
| 29 | MINOR | §9 tamper wording | **APPLIED**: "an axiom declaration split across two lines"; "one explicit counterexample and the reason for a second" |
| 30 | MINOR | §9 "13 declarations" | **APPLIED**: 13 axiom-checked of 32 theorem/lemma declarations |
| 31 | MINOR | §3 hyperplanes | **APPLIED**: "no theorem is stated for hyperplane cycles or uses $v=0$ non-trivially" |
| 32 | MINOR | §9 L14 part 1 | **APPLIED**: seven planar plus one $\RR^3$ claim, with the unused-hypothesis finding noted |
| 33 | MINOR | appendix row 3 | **APPLIED**: all three names listed ($n=2$, $n=3$, general) |
| 34 | MINOR | abstract "numerical claim … refuted" | **APPLIED**: "our conjecture … refuted numerically" |
| 35 | MINOR | bibliography | **APPLIED**: the scout's title and arXiv version; unused `lmw`/`soddy`/`gosset`/`mathlib` items dropped; `augdescartes` names the owner |
| 36 | MINOR | §4 (iii) | **APPLIED**: the orthogonal complement is the projective line, which meets the quadric in exactly $A,A'$ |

## Evidence for the two claims the reviewer could not verify

- **Gate and battery at the new pin.** `464a59d`: gate `PASS (73 declarations, standard axioms only)`,
  tamper 9/9, tree clean; battery `paperK_20261116_211403.md` (copied as `battery_paperK_464a59d.md`).
- **Second machine.** `git archive 464a59d` → john (arm64 macOS): build rc=0, gate same PASS line, tamper
  ALL TAMPERING TESTS REJECTED, five library files byte-identical (`RECEIPT_export_464a59d_john.log`).
- **Name gate at the new pin**: `NAME GATE PASS`, 56 `\decl` names, 18 `\src` anchors, 0 declarations left
  ungated (the general-n names are now in the repository).

## Still open (not review findings)

- The docstring of `tetra_E1_apollonius` (ThreeD.lean:140) still says "Thm 3.6 conclusion"; fix in the next
  commit, which moves the pin and the receipts with it.
- L13 (blind re-formalisation) has not been run on this draft; it needs the text frozen first.
- No public remote yet; the anchors are text, not links, exactly as §Availability says.
