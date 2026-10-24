# Paper D — Layer 15 gap-closing pass

Input: `PAPERD_L15_COMPARE.md`. All work was done inline on jack (BatchMode SSH). New files are `~/l15D_<repo>/scratch/L15_gaps.lean`. Each one is a verbatim copy of that repo's `L15_compare.lean` (all writer definitions, `classical_*` statement packages and earlier `cov_` proofs) with new material appended. `L15_compare.lean` and the library files were not edited.

## Gap 1 — D3 Fermat definitions — **CLOSED**

Repo `~/l15D_lester`, file `scratch/L15_gaps.lean`.

```lean
theorem cov_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)
theorem cov_D3_exact ... : classical_D3 a b c h hab hbc hca F₁ F₂ hF₁ hF₂
```

The signature is exactly the writer's. The extra premises `ho`/`hi` of `cov_D3_part` are discharged by these lemmas:
- `gap_apex_char`: if `dist q X = dist q r = dist r X` and `q ≠ r`, then `X` is `q + (r−q)·ω` when the signed area `gcross q r X > 0`, and `q + (r−q)·conj ω` when it is `< 0`. The algebra is in `gap_apex_alg`.
- `gap_ccw_iff`: `Lester.Ccw (ι p) (ι q) (ι r) ↔ 0 < gcross q r p`.
- `gap_opp_cross_neg` / `gap_same_cross_pos`: `SOppSide` / `SSameSide` force the signs of the signed-area product.
- `gap_outer_apex` / `gap_inner_apex`: the writer's `IsOuterApex p q r X` gives `ι X = Lester.apexOut (ι p) (ι q) (ι r)`, and likewise for the inner apex. Non-degeneracy `q ≠ r` follows from the strict side condition.
- `gap_mem_line_map`, `gap_fermat_outer`, `gap_fermat_inner`: `IsFirstFermatPoint` gives `Lester.IsFermatOuter`, and `IsSecondFermatPoint` gives `IsFermatInner`.

Compile rc 0. All 22 `#print axioms` lines in this file are `[propext, Classical.choice, Quot.sound]`. Forbidden-token grep: no match (rc 1).

## Gap 2 — D2 redundant distinctness premises — **CLOSED** (no genuine narrowing; none needed)

Repo `~/l15D_fivecircles`, file `scratch/L15_gaps.lean`.

```lean
theorem cov_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    (hnc : ¬ Collinear ℝ (Set.range Q)) :
    Cospherical (Set.range Q)
theorem cov_D2_exact ... : classical_D2 ℓ hℓ hpar hconc V T hV hT ω hω Q hQ hnc
```

How the six extra premises of `cov_D2_part` were removed:
- **`gap_D2_distinct`**: from `hconc`, `hV`, `hT`, `hω`, `hQ` and `hℓ` alone, it derives `Injective V`, `Injective T`, `∀ i j, V i ≠ T j`, `V i ≠ Q j` and `T i ≠ Q j`.
  - V/T facts: a coincidence would put one point on three distinct lines, contradicting `hconc`.
  - Collisions with Q: a sphere meets a line of the family (finrank-1 direction) in at most two points (`gap_sphere_line`, via Mathlib `Cospherical.affineIndependent_of_mem_of_ne`). Each line `ℓ(k−1)`, `ℓ k`, `ℓ(k+1)` already carries two known distinct points of `ω k`.
  - Finite index cases are closed by `decide` lemmas `gap_idx_*`.
  - This also handles the global Q collisions the earlier report left untreated.
- **Injectivity of `Q`**: this premise is not derived. It is made unnecessary, for these reasons:
  - Distinctness of Q is genuinely not implied by the hypotheses: in the "five tangents of a parabola" configuration all Miquel points coincide.
  - Under the writer's `hnc`, that configuration is excluded anyway, but `cov_D2` does not rely on this.
  - `gap_core_distinct` is the repository's `Fivecircles.core` proof text, copied verbatim with one change: `Injective M` is replaced by pairwise distinctness of `M 0..M 3`, the only instances used.
  - `gap_core` drops even that, because `cd a b c d = 0` holds trivially when two arguments coincide (`gap_cd_degen`).
  - `gap_cd_perms` / `gap_cd_all` close `cd` under all 24 permutations and the five cyclic shifts, giving `cd (M a) (M b) (M c) (M d) = 0` for all indices.
  - `gap_fivecircles` then picks any non-collinear triple, which exists by `hnc`, and concludes concyclicity with repository `concyclic_of`.
- Also recorded: `cov_D2_injQ`, the intermediate theorem with only `hQi` extra.

No library file was edited. The copied `core` proof lives in the scratch file.

Compile rc 0. When this gap was closed, the file had 20 `#print axioms` lines; the final file, which also contains the D2 obligation, has 25. Every one is a subset of `[propext, Classical.choice, Quot.sound]`. All main and bridge theorems print exactly that triple. The `decide` index lemmas `gap_idx_V/T/VT/ne/VQ/TQ/obl` print `[propext]` only. Forbidden-token grep: no match.

## Gap 3 — D1(c) canonical identification — **CLOSED**

Repo `~/l15D_clifford`, file `scratch/L15_gaps.lean`.

```lean
theorem cov_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) :
    ∃ Y : Pt, ∀ m, Y ∈ C m
theorem cov_D1_c_exact ... : classical_D1_c c M P h X hX hXu C hC hCnc
```

All twelve `hcanonical_nc*` / `hcanonical_circle*` premises of `cov_D1_c_part` are derived:
- `gap_X_eq`: the repository's `cliffordPoint` of four circles lies on all four Γ circles (`Clifford.cliffordPoint_mem_gams` plus `gap_gamma_of_four6`, a `Fin 6` copy of the earlier `cov_gamma_of_four`). By the writer's uniqueness `hXu`, `normalizeAt M (X m l)` equals the explicit `cliffordPoint` of the four remaining centres.
- `gap_five_circle`: suppose five Clifford points lie on a sphere `S` and are not all collinear.
  - Then `WW ≠ 0`; otherwise all five coincide, by the repository's `eq_of_cross`/`cross**` identities.
  - So the three canonical points are pairwise distinct (`ne_of_cross`).
  - Being on a sphere, they are affinely independent, hence not collinear. This is the canonical nc premise.
  - Two distinct circles in the plane share at most two points (Mathlib `eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two`), so `S` equals the canonical `circumcircle`. This is the canonical circle premise.
- `gap_canon`: applies the two lemmas above for each `m`, using `hC` (membership) and `hCnc` transported through `normalizeAt M`.
- `cov_D1_c` instantiates `gap_canon` for the six `m` and feeds the results to `cov_D1_c_part`.

Compile rc 0. All 20 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`. Forbidden-token grep: no match. The log contains only linter warnings (unused simp args inherited from the copied `cov_gamma_of_four`).

## Gap 4 — construction obligations

### D2_obligation — **CLOSED** (repo `~/l15D_fivecircles`, same `L15_gaps.lean`)

```lean
theorem cov_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) :
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)
theorem cov_D2_obligation_exact ... : classical_D2_obligation ℓ hℓ hpar hconc
```

- `gap_lines_meet`: two non-parallel lines in the plane meet. Their directions differ, so `dim(d₁ ⊓ d₂) = 0`, hence `d₁ ⊔ d₂ = ⊤` and `inter_nonempty_of_nonempty_of_sup_direction_eq_top` applies.
- Non-collinearity: if `V(i−1), V i, T i` were collinear, `T i` would lie on `ℓ i = line[V(i−1), V i]` (these are distinct by `hconc`) as well as on `ℓ(i−1)` and `ℓ(i+1)`, contradicting `hconc`.

Compile rc 0, 25 axiom lines. All are ⊆ `[propext, Classical.choice, Quot.sound]`: the `decide` index lemmas print `[propext]`, every other line the full triple.

### D3_obligation — **CLOSED** (repo `~/l15D_lester`, same `L15_gaps.lean`)

```lean
theorem cov_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) :
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)
theorem cov_D3_obligation_exact ... : classical_D3_obligation a b c h hab hbc hca
```

Explicit construction:
- `apx q r K` rotates `r − q` by ±60° (`K = ±√3`).
- `gap_apx_dist`: equilateral distances.
- `gap_apx_cross`: signed area `K/2·|qr|²`.
- `gap_apx_outer` / `gap_apx_inner`: the side conditions follow via new converse lemmas `gap_opp_of_cross_neg` / `gap_same_of_cross_pos`.
- Choosing `K` with `K·g < 0` gives the outer apices on all three sides, since the signed area `g` is cyclically invariant. `−K` gives the inner ones.
- `gap_concurrent`: the three vertex–apex lines meet. This is an explicit `linear_combination` identity, checked beforehand with sympy, whose third-line residual is identically 0.
  - Its non-degeneracy condition is `K·S ≠ 3g`, where `S` is half the sum of squared sides.
  - `gap_nondeg` establishes it from `(p−q)²+(q−r)²+(r−p)² = 2(S²−3g²)`. So `K·S = 3g` would force `p = q = r`, contradicting `dist a b ≠ dist b c`.
- Only one scalene inequality is used.

Compile rc 0. All 37 axiom lines are `[propext, Classical.choice, Quot.sound]`. Forbidden-token grep: no match.

### D4_obligation — **CLOSED** (repo `~/l15D_thebault`, file `scratch/L15_gaps.lean`)

```lean
theorem cov_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a
theorem cov_D4_obligation_exact ... : classical_D4_obligation a b c d h hd
```

`gap_thebault_one` runs a continuity argument on the internal bisector at `d` of the angle between the ray `d→X` (`X = b` or `X = c`) and the ray `d→a`:
- Set `P s = d + s·(û_X + û_a)` with unit vectors û. Both line distances equal `k·s` with `k = |g|/(|bc|·|da|) > 0`, using the repository's `infDist_line_eq`.
- Define `F s = dist(P s, O) + k s − R`. It is continuous. `F 0 < 0` because `d` is strictly inside the circumcircle (Mathlib `Sphere.dist_center_lt_radius_of_sbtw`). `F((R+1)/k) > 0`.
- `intermediate_value_Icc` gives `s > 0` with `dist(P s, O) = R − ks`.
- `ks < R` follows from `ks ≤ dist(P s, d) ≤ dist(P s, O) + dist(O, d) < R − ks + R`.
- Sides: `cross b c (P s) = (s/|da|)·g`, so the centre is on `a`'s side of BC. `cross a d (P s) = μ·λ·g` with μ > 0, where `λ = −tt` for `X = b` and `λ = 1−tt` for `X = c`. This gives opposite signs, so the two centres are on opposite sides of AD (new `gap_opp_of_cross_neg`).

Compile rc 0. All 10 axiom lines are `[propext, Classical.choice, Quot.sound]`. Forbidden-token grep: no match.

## Gap 5 — D1(d), all n — double-check only (no proof attempted; **STILL OPEN** as an all-n theorem)

Re-checked on jack by recompiling the unchanged `~/l15D_cliffordchain/scratch/L15_compare.lean`:
- Exit 0.
- All 10 axiom lines are `[propext, Classical.choice, Quot.sound]`, including `cov_D1_d_large_repository_failure`, `cov_D1_d_repository_counterexample`, `cov_D1_d_no_spherical_level_five` and `cov_D1_d_counterexample_not_writer_data`.

I also read the relevant source:
- `Clifford/Clean.lean`: `Chain`, `IsGCircle`, `GenPosN`, `CliffordChain`.
- `Clifford/Counter6.lean`: `not_chain6`, which goes through `chain5_mem` and `q1234/q0234/q0134`.

The report's claim is confirmed with one precision:
- **Proved:** any repository level-5 object for the five centres `(3,−6),(6,−3),(1,2),(−2,−1),(0,−4)` contains the three distinct collinear points `(2/3,−4), (−8/3,−4), (−6,−4)`. Such an object therefore lies on no sphere. In particular the writer's premise `odd_mem` at `S = univ.erase 5` (|S| = 5 < 6) cannot be met by any writer sphere whose point set *is the complex image of* such an object.
- **Not proved:** that the writer's `CliffordChain 6 c M pt circ` is *uninhabitable* for these six circles. The theorem takes the object identification as a hypothesis. The writer's level-4 points `pt S` are only required to be the unique common point of their four level-3 spheres. These are exactly the repository's Clifford points, so the three points above would be forced into `circ (univ.erase 5)`. The full recursive translation that would formalise this was not done.

**How the two notions of general position differ.**
- **Repository `GenPosN c`** constrains only level ≤ 3 data:
  - every pair of circles is transversal at `M` (`conj cᵢ·cⱼ ≠ cᵢ·conj cⱼ`);
  - every increasing triple satisfies `GenTriple`: centres non-collinear and the three second intersections non-collinear.
  - Higher levels are then forced to exist inside `Chain`. There, an odd-level object may be any *generalized* circle (a metric sphere or an affine line, `IsGCircle`), and an even level must be one finite point lying on one chosen predecessor object for each omitted index. Nothing excludes lines at level 5, or requires a level-4 point to be the *unique* intersection.
  - So `CliffordChain n` asserts existence for every configuration generic only at levels ≤ 3. It is false for n ≥ 6 (`not_cliffordChain_of_six_le`) because the six-centre configuration forces a level-5 line, whose level-6 "common point" would have to be the point at infinity, which `Chain` cannot represent.
- **Writer `CliffordChain n c M pt circ`** is a general-position hypothesis at *every* level below `n`:
  - every odd level 3 ≤ |S| < n carries a genuine `Sphere Pt` containing its predecessor points, and those points are non-collinear (`odd_mem`, `odd_gp`);
  - every even level 4 ≤ |S| < n carries a point that is the *unique* common point of its predecessor spheres (`even_mem`, `even_gp`).
  - The odd top step additionally assumes `hnc`.
  - The writer's premises thus exclude exactly the degenerations (lines, non-unique or missing intersections) that make the repository predicate fail.
  - The repository counterexample is therefore not a counterexample to the writer's D1(d). Equally, the repository's n ≤ 5 positive results do not cover the writer's all-n statement.

## Summary

| Gap | Status | Theorem(s) (namespace `PaperDClassical`) | Repo |
|---|---|---|---|
| 1. D3 Fermat definitions | **CLOSED**: exact writer signature | `cov_D3`, `cov_D3_exact` | lester |
| 2. D2 distinctness | **CLOSED**: exact writer signature, no extra premises | `cov_D2`, `cov_D2_exact` (also `gap_D2_distinct`, `cov_D2_injQ`) | fivecircles |
| 3. D1(c) canonical identification | **CLOSED**: exact writer signature | `cov_D1_c`, `cov_D1_c_exact` | clifford |
| 4a. D2_obligation | **CLOSED** | `cov_D2_obligation`, `_exact` | fivecircles |
| 4b. D3_obligation | **CLOSED** | `cov_D3_obligation`, `_exact` | lester |
| 4c. D4_obligation | **CLOSED** | `cov_D4_obligation`, `_exact` | thebault |
| 5. D1(d) all n | **STILL OPEN** (not attempted, per instructions); separation claim re-verified with the precision above | (existing) `cov_D1_d_*` | cliffordchain |

No **genuine narrowing** was found. In particular, D2 needs none of the six extra distinctness premises.

With the earlier report, every writer statement except D1(d) for general n is now proved with its exact signature, and every `_obligation` is proved. That covers D1(a–c), D2–D7 and all of D2–D7_obligation.

## Receipts

Compile command, run in each repo on jack: `cd ~/l15D_<repo> && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/L15_gaps.lean`.

| Repo | `L15_gaps.lean` rc | `#print axioms` lines | non-triple lines | forbidden grep | library hash (unchanged) |
|---|---:|---:|---|---|---|
| clifford | 0 | 20 | 0 | no match | `bb53ed5aa005078a6d9c3f24379c427f850b96e39f05e5268e7911601f29472a` |
| fivecircles | 0 | 25 | 7 `decide` index lemmas print `[propext]` only (⊆ allowed set) | no match | `1cddd210ca590ece1325206106d79b455e05b61de8fa10e8d6f71da22a474cbf` |
| lester | 0 | 37 | 0 | no match | `6e768745d69ddd3276f02f51e6d62e6bd4d1075c7907b64f8ecb6c47063f36c0` |
| thebault | 0 | 10 | 0 | no match | `06432c5a80ad20e9bf1289902c9aae64c3e9310d300600be83da0e0672b897c7` |
| cliffordchain (recheck of L15_compare) | 0 | 10 | 0 | not edited | `d7464f13579e39d7a2696e19e2dbe409fd1e75703ddfd69a82e1f64c7964015e` |

- The hashes for kosnita, blundon and steinerlehmus are also unchanged (`e98f36b5…`, `89ec32d8…`, `feaf54dc…`), and all commits match the earlier report.
- `L15_compare.lean` in all eight repos is byte-identical to the comparer's local copies (sha256 prefixes checked).
- Each `L15_gaps.lean` begins with the verbatim `L15_compare.lean` text, minus only its final `end PaperDClassical`, checked with `cmp`. So all writer definitions and `classical_*` packages are present unchanged.
- Hash command: `find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`.
- Forbidden grep: `grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide|axiom)([^[:alnum:]_]|$)'` → rc 1 for every file.
- One non-default option is used: `set_option maxHeartbeats 4000000 in` on `gap_cd_all` (fivecircles), a 625-case finite check.
- No `lake update` or cache get was run. No library or `L15_compare.lean` was edited. No foreign processes were touched. The only process started besides foreground compiles was my own cliffordchain recheck, now finished.

Evidence copies: `<ws>/AFM/PaperD/layer15/gaps/l15D_<repo>/L15_gaps.{lean,log,rc}` and `gaps/axioms_all.txt` (all 96 axiom lines grouped by repo, including the 4 header lines).
