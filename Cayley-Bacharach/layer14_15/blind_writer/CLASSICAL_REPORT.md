# Paper CB — Classical-source blind formalisation report

Output: `/tmp/blindCB/Classical.lean` (byte-identical to `jack:~/reformal/PaperCBClassical.lean`, md5 66612baf08a7c075fb5f1d9e4455c9e5).

## Setting
- Plane: `ℙ k (Fin 3 → k)` (Mathlib `Projectivization`), `k` a field.
- Curves: nonzero homogeneous `MvPolynomial (Fin 3) k` of degree d (`IsHomogeneous`).
- "Passes through": `eval P.rep F = 0`.

## Statements
| Name | Content |
|---|---|
| `classical_CB1_a` | Cubics F₁,F₂ (`IsRelPrime` = no common component) share 9 distinct points; cubic F through P₁..P₈ ⇒ F(P₉)=0 |
| `classical_CB1_a_linear` | same hypotheses ⇒ F = aF₁ + bF₂ (the bracketed equivalent) |
| `classical_CB1_b` | multiplicity version: `intMult F₁ F₂ = Σ δ_{Pᵢ}`, all Pᵢ simple on F₁, `intMult F₁ F = Σ_{i≤8} δ_{Pᵢ} + δ_Q` ⇒ Q = P₉ |
| `classical_CB1_b_irreducible` | same with "F₁ irreducible" in place of simple points |
| `classical_CB2_a` | no 4 on a line, no 7 on a conic, distinct ⇒ `finrank (cubicsThrough P) = 2` |
| `classical_CB2_b` | (k alg. closed) ∃! P₉ s.t. every two independent pencil members have intersection cycle P₁+…+P₈+P₉ |
| `classical_CB2_b_distinct` | (any k) if two coprime pencil members share a 9th point Q ∉ {Pᵢ}, then ∃! P₉ ∉ {Pᵢ} common to all cubics through P₁..P₈ |
| `classical_CB3_a` | Pascal, irreducible conic, six distinct points; X,Y,Z by defining property ⇒ collinear |
| `classical_CB3_b` | Braikenridge–Maclaurin: no 3 collinear, X,Y,Z collinear ⇒ ∃ conic through A..F |
| `classical_CB4_a` | Pappus |
| `classical_CB4_b` | Pappus, hexagon form (V0,V2,V4 on L; V1,V3,V5 on M) |

## Obligations (well-formedness, separate theorems)
- `classical_CB3_a_obligation`, `classical_CB3_b_obligation`, `classical_CB4_a_obligation`, `classical_CB4_b_obligation`: each pair of opposite sides meets in a unique point. (The main theorems take X,Y,Z by defining property, so they are well-formed without these.)

## OWN DEFINITIONS
- `Vanishes F P` — F(P)=0 at the representative `P.rep`.
- `IsCurveOfDegree d F` (+ `IsCubic`, `IsConic`, `IsLine`) — homogeneous of degree d, nonzero.
- `PCollinear p q r` — representatives linearly dependent in k³.
- `pointIdeal v` — kernel of F ↦ F(t·v) ∈ k[t] (homogeneous prime of the point); prime instance via `RingHom.ker_isPrime`.
- `intMult F G P` — `Module.length` of `R_𝔭/(F,G)` with R = k[x,y,z], 𝔭 = `pointIdeal P.rep`; ℕ∞-valued (⊤ when there is a common component through P). Equals the classical (Fulton) multiplicity, dim 𝒪_{P²,P}/(f,g), because R_𝔭 is flat local over 𝒪_{P²,P} with closed fibre a field. Intersection cycles are written as `∀ X, intMult … X = Nat.card {i // P i = X}`.
- `IsSimplePoint F P` — F(P)=0 and some partial derivative nonzero at P.
- `cubicsThrough P` — degree-3 homogeneous submodule ⊓ kernels of evaluation at the Pᵢ.
- `EightPointGeneral P` — injective, no 4 on a line, no 7 on a conic.

## AMBIGUOUS marks
- CB1(a): "meet in nine distinct points" read as "nine distinct common points" (alternative: common zero locus exactly {P₁..P₉}; Bézout makes these equivalent).
- CB1(b): "C₁ irreducible (or more generally simple points)" — formalised both ways (two theorems). Fulton assumes both; the irreducible-only version is noted.
- CB2(b): "uniquely determined ninth point" read as the residual point of the base cycle (may coincide with some Pᵢ) in `classical_CB2_b`; the distinct-nine-points reading is `classical_CB2_b_distinct`.
- CB3(a): "nondegenerate" read as `Irreducible q` over k (alternative: nonsingular).

## EXTRA HYPOTHESIS marks
- CB1(b) (both versions): `[IsAlgClosed k]` (Fulton's standing convention) so the intersection cycle lives on k-points.
- CB4(b): distinct lines, distinct vertices, none at L∩M (non-degenerate hexagon; mirrors CB4(a)).

## Compiler summary
`lake env lean PaperCBClassical.lean` on jack: no errors; only 15 `declaration uses 'sorry'` warnings (one for each theorem).

## Files read
- `/tmp/blindCB/classical_statements.txt` (only file read). `ls /tmp/blindCB` showed `brief.txt` and `scratch/` but I did not open them. Nothing else was read, and no web search was done. Only the scp copy of my own file and the compile ran on jack.
