# Paper L — plan

**Title (working):** Clifford's chain for every n: point–circle configurations on the Riemann sphere, in Lean 4.

**Gap:** Paper D proves C₄, C₅, C₆ in the finite plane and proves the finite-plane predicate false for n ≥ 6
(`cliffordChain_iff : CliffordChain n ↔ n ≤ 5`, `cliffordgen`). The all-n theorem, and the corrected predicate on
the Riemann sphere, are unformalised anywhere (see `SCOUT.md`). The mathematics is classical: Clifford
(1871/1882), Coxeter (1969), Longuet-Higgins (1972), Martini–Spirova (2008); the combinatorial route via Miquel and
cross-ratios is stated in Bobenko–Schief (arXiv:1509.04109).

## Claim set

| id | claim | status in scout |
|---|---|---|
| C1 | C₃ base: three circles through M, the three second intersections lie on a generalized circle | trivial (API) |
| C2 | C₄ = Clifford I (four level-3 circles concurrent) | ours (Paper D) |
| C3 | C₅ (five level-4 points concyclic) | ours (Paper D) |
| C4 | C₆ (six level-5 circles concurrent) | ours (Paper D) |
| **C5** | **all n, on the Riemann sphere: level objects alternate point ∈ OnePoint ℂ / generalized circle, lines allowed** | new |
| **C6** | **uniform step lemma Cₙ ⟹ Cₙ₊₁ (hypercube extension)** | new |
| **C7** | **improper-set classification (Carver 1920, Thm 13): the level object is a line / ∞ exactly when a key minor of the characteristic matrix vanishes** | classical mathematics (Carver 1920, read in full); formalisation new |

Paper may not claim the mathematics as new — the all-n chain (Clifford 1870; Morley 1900; Carver 1920; Longuet-Higgins
1972), the failure phenomena (Kantor 1878; Carver 1920) and the Möbius-plane repair (Carver 1920 §6) are all classical —
and may not claim first formalisation of Miquel (atlas-lean, AFP 2026, Coq HSG, lean-genius). See SCOUT.md §3 and §5.

**State the theorem in Carver's form** (n lines; odd n a circle through the n Clifford points, even n a point on the n
circles; proper sets) and derive the inverted circles-through-a-point form as a corollary. The characteristic-matrix
machinery is Morley's (1900) — cite it; the "Morley-type formula" in `GENERAL_REPORT.md` is Morley's, not ours.

## Route

1. **Corrected predicate.** Carrier `Set (OnePoint ℂ)`; even levels `{p}` with `p : OnePoint ℂ` (∞ allowed);
   odd levels a generalized circle in `OnePoint ℂ` (a line contains ∞). Port Clean.lean's `Chain` and re-prove
   C1–C4; prove `Chain 6 Counter6.cx {∞}` on D's exact Gaussian-integer configuration — the corrected predicate
   proves the instance the old one refuted.
2. **All-n engine.** After inversion at M a circle becomes a line `w = a_k + t_k \bar w`; the Clifford object is
   the kernel of the n×(n+1) matrix `[t_k^j | −a_k t_k^j]`, with the closed forms of `GENERAL_REPORT.md` §(a)
   (even n=2m: point `−Q_{m−1}/P_m`; odd n: coefficient `P_0` multiplies `z\bar z`). Prove the kernel/rank lemma
   in general n and show the closed form satisfies the level-n membership equations; the step n → n+1 is a
   bordering/Schur-complement statement about the same matrix.
3. **Layers.** Standard 1–15 on the frozen repo: gate + tamper + battery, L10 bridges, L14 restatements, L11 name
   gate, L13 blind re-formalisation (writer sees only the frozen .tex), L15 against Clifford/Longuet-Higgins/
   Coxeter, two-machine receipt.

## Dispatch — round 1 (launched 2026-11-17 03:45Z)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j1_mobius` | jack | `~/paperL_jack/Clifford/Mobius.lean` | corrected predicate on `OnePoint ℂ`; C1–C4 ported; `Chain 6 Counter6.cx {∞}`; all-n stated |
| `paperL/j2_kernel` | john | `~/lean/paperL_john/scratch/MorleyKernel.lean` | Morley interpolation matrix at general n: rank/kernel lemma, closed form, agreement with n=4,5,6, step-lemma shape |

Round 2 depends on which of C5/C6 is closed: if C5+C6 close, round 2 = packaging, layers, paper; if C6 only
reduces, round 2 = finish the reduction on the machine that got furthest, and freeze the paper's claim at
"all n modulo the reduction" only with Josh's agreement.

## Risks

- The step lemma is the mathematical crux; the kernel formulation makes it concrete but not automatic.
- `OnePoint ℂ` plumbing (membership at ∞, generalized circles as subsets) is fiddly; if it costs too much, fall
  back to stating the chain directly in the line model with an explicit "no object is a line" hypothesis per level
  and a separate at-infinity lemma.
- Machine hygiene: `~/cliffordgen` (both machines), `~/clifford`, `~/paperK` are artifacts — copies only.

## Round 1 result (verified 2026-11-17 06:10Z) — collection in `layer0/COLLECT_2026-11-17.md`

Both jobs landed, both recompiled by me on their hosts, both sha-matched, no forbidden tokens, axioms standard.
- **jack `Mobius.lean`** (79 decls, rc 4.8 s, `f8c9f013…`): `Counter6S.chainS_six : ChainS 6 Counter6.cx {∞}` proved
  literally, plus `chainS_six_unique`/`chainS_six_iff`; C1–C4 ported (`…_ofS`, `cliffordChainS_of_le_five`);
  all-n shipped as the **reduction** `cliffordChainS_all_of`, conditional on `h4` + `hodd` + `heven` for an abstract
  `E`. C5 is therefore REDUCED, not proved.
- **john `MorleyKernel.lean`** (61 decls, rc 11.6 s, `bfdde276…`): line model, rank/kernel with the exact hypothesis,
  closed form at n = 4 (equality: `−Q₁/P₂ = miquel`) and n = 5 (membership via the proved 5×5 Plücker relation
  `plucker5` / `k0k3_sub_k1k2`), bordering `Kf_border_even/odd`, and the two step statements registered as
  `def StepEven m : Prop` / `def StepOdd m : Prop` (unproved). C6 is OPEN.

**Corrections this round forces on the plan (now authoritative):**
1. The working matrix is **`Kf n`** — `n × (n+1)`, `P`-block `j = 0…⌊n/2⌋`, `Q`-block `j = 0…n−⌊n/2⌋−1`. The literal
   `K n` with `j = 0…⌊n/2⌋` in both blocks is `n × (n+2)` for even n and has `finrank ker ≥ 2` (`K_finrank_ker_ge_two`).
2. **Rank hypothesis = one nonzero maximal minor** (`P_m ≠ 0` even n, `P₀ ≠ 0` odd n). No Vandermonde/distinctness
   condition; `GenPos4` suffices at 4, `CliffordNondeg` (k3 ≠ 0) at 5.
3. The kernel description needs **`P₀ ≠ 0`**: at k3 = 0 the cross-vector form vanishes identically and the line case
   is not recovered (k0 is not a kernel coordinate). Odd-step statements are conditional on the minor.

## Dispatch — round 2 (launched 2026-11-17 06:14Z, 9000 s boxes)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j3_stepeven` | john | `scratch/StepIdentities.lean` | `StepOdd 2`, **`StepEven 2`** (the 6×7-minor identity), `StepOdd 3`, then general m via bordered + Sylvester/Desnanot–Jacobi |
| `paperL/j4_inversion` | jack | `Clifford/Inversion.lean` | `invS` on `OnePoint ℂ`, circle-through-0 ↔ line, `ChainS → ChainL` functoriality for the Carver n-lines form, assembly `cliffordChainL_all_iff` if it lands |

Collection: one-time schedule 2026-11-17 03:55 EST (`rem_6630f11cab0440a0b2805162841976f2`). The spine is **not**
ready; layers 1–15 not started. C7 stays classical mathematics (Carver 1920) — the paper claims formalisation only.

## Round 2: FAILED at the dispatcher (2026-11-17 06:44Z)

`j3_stepeven` (john) and `j4_inversion` (jack) were both terminated at 06:44:34Z, 30 minutes after launch, in the
same second, with no file written on either host and no error in the logs. No result of any kind — the round-1
verdicts (C5 reduced via `cliffordChainS_all_of`; C6 open; C7 partial at n = 6) stand unchanged. Non-inversion
deliverables were not affected; neither host was left dirty.

**Round 2b (08:57Z)** replaces it with one narrower job: `j5_stepeven2` on john, 3600 s, single target `StepEven 2`,
10-minute checkpoint copies, `StepOdd 3`/general `m` deferred. jack's inversion work is deferred too. Collection
`rem_7d841de660b04966a9c5211a5ee0ea0c` at 2026-11-17 05:05 EST.

**Operational lesson (write this into every dispatch):** launch from a call that returns in seconds; put the command
in a `launch.sh` that `exec`s `setsid nohup opencode run …` itself, never in a call that can hit the tool timeout.
Require checkpoint copies at fixed intervals so a reaped session still leaves a partial artifact.

## Round 2b: `StepEven 2` proved (2026-11-17 10:06Z)

`stepEven_two : StepEven 2` verified on john (rc=0, 11.0 s, axioms standard, sha `e78213cb…`; the file is the frozen
`MorleyKernel.lean` byte-for-byte plus the new section). C6 moves from "open" to **one instance closed**; C5 unchanged
(reduced); C7 unchanged (partial at n=6, Carver 1920).

Proof shape (now the template for general `m`): conjugation (`conj P₃ = P₀`, `conj Q₃ = −Q₀`) + two Cramer relations
cancelling `A57` + a formal linear combination. No `GenPos6`, no `c k ≠ 0` needed. The general case needs (a) a general
column-permutation lemma for `conj crossVec`, (b) "Cramer = cross vector of a bordered matrix"; j6 (10:07Z) targets (a).

## Round 3: general conjugation CLOSED, `StepOdd 2` still open (2026-11-17 10:55Z)

j6_general_step (john, 10:07Z) finished on its own at 13 min — no kill. `scratch/GeneralStep.lean`, 1002 lines,
sha `3f6bf1aff8bd15564c071a4bbabddd9563176f81f8a2dfe1cb81eaee3900037c`, first 707 lines byte-identical to
`StepEven2.lean`; 30 new decls; rc=0 11.3 s; axioms standard; numeric cross-check of the signs for m = 0…4.

- **Closed (general `m`, no determinant expansion):** `crossVec_colPerm` (abstract: `d_j·crossVec B j =
  (∏d)·sign σ·crossVec A (σ j)`), `conj_crossVec_even` (conj P_{m+1} = +P₀), `conj_crossVec_even_Q`
  (conj Q_m = −Q₀), `crossVec_even_P0_ne_zero`, `conj_levelPointN_even` (conj z = Q₀/P₀), `conj_crossVec_KP` (all n).
  Signs are independent of `m`.
- **New reusable toolkit:** `border`/`det_border` (`det [w;A] = ∑ w_l·crossVec A l`, Laplace on row 0 — **this is
  Cramer's numerator**), `det_border_single`, `sign_revPerm_succ`, `blockRev`/`sign_blockRev` (`(−1)^(m+1)`),
  `blockSign`/`prod_blockSign` (∏d = 1), `KP_swap_entry`, `crossVec_KP_swap_P/Q`.
- **Not closed:** `stepOdd_two_triP` is `StepOdd 2` **plus `triP ≠ 0`** (collinearity of the first three subfamily
  centres), needed because `cliffordEq_miquel` divides by `triP`. `StepOdd 2` stays OPEN. Removal route named:
  polynomial-domain/density transport (`F·triP·∏x_iy_i = 0` in a domain) through `MvPolynomial`/`eval`.
  New usable: `levelPointN_four_cross` (Miquel from `P₂ ≠ 0` alone, no `GenPos4`).

Verdicts: **C5 REDUCED**, **C6 PARTIAL** (StepEven 2 closed; general conjugation closed; StepOdd 2 open; general
StepEven m open), **C7 PARTIAL at n = 6** (Carver 1920 — classical, never ours). Spine not ready. No freeze.

## Dispatch — round 4 (j7_cramer, 2026-11-17 10:48Z, john)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j7_cramer` | john | `scratch/CramerStep.lean` (= `GeneralStep.lean` verbatim + new section) | (A) general Cramer identification of the `(2m+1)` subfamily cross-vector coordinates as bordered determinants + one general row-relation lemma specialising to `rowRel1`; (B) `stepEven_three : StepEven 3` |

Collection: one-time `rem_092ba9a9ccf7435a9964431e84a53a2e` 2026-11-17 06:35 EST. The route to general `StepEven m`
is now: A (identification) → general row relations → the same two-term combination as `stepEven_two`.

## Round 4: general Cramer row relations landed, `stepEven_three` still open (2026-11-17 11:40Z)

j7_cramer (john, 10:48Z) finished on its own at 17 min. `scratch/CramerStep.lean`, 1350 lines, sha
`f206d64a87213a2014b70c5e93bde0eebf9ca1a5dc8020fdbc3995b8fd0a8182`, first 1350−348 = 1002 lines byte-identical to
`GeneralStep.lean`; rc=0 (~12 s) with only linter warnings; axioms standard on all 22 new theorems; my numpy check
shows `rowRelGen1/2` vanish with generically nonzero coefficients (not vacuous).

- **`KP_sub_eq`** — `KP (2m+1) (x∘i.succAbove) (y∘i.succAbove) = (subRows m x y i).submatrix id (Fin.succAbove ⟨m+1,_⟩)`:
  the subfamily matrix is the parent with row `i` and column `P_{m+1}` removed. This was the structural gap.
- **Generic Cramer kit:** `colBorder`, `cramerCoef`, `det_colBorder`, `cramerCoef_self`, `cramer_sum`,
  `cramer_three`, `cramerCoef_eq_crossVec` (+ `colFront`/`det_colFront`).
- **General row relations** `rowRelGen1`, `rowRelGen2` (+ `cramer1_Q0`, `cramer1_Qm`, `cramer2_P0`, `cramer2_Qm`
  identifying each coefficient as `±` a coordinate of `w`), and **`stepEven_cleared_gen`** — the general-`m` cleared
  two-term combination with the `A57`-type coefficient cancelled.
- `rowRel1_m2`/`rowRel2_m2` are the `m = 2` instances of the general lemmas, matching the existing `rowRel1/2`.
- **Not done:** `C₁ = −k0`, `C₂ = k2` (needs a `(2m+1)` closed form); `stepEven_three` (needs the odd-size analogue of
  `oddCircleEq_five_cross`: conj `w₀ = ±w₀`, conj `w_{m+1} = ±C₂`, conj `w_last = ±A′`, and the Plücker relation
  `C₁·w₀ − w_{m+1}·C₂ = ±A′·w_last`).

## Dispatch — round 5 (j8_oddrev, 2026-11-17 11:37Z, john)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j8_oddrev` | john | `scratch/OddStep.lean` (= `CramerStep.lean` verbatim + new section) | odd-size `blockRev`/`blockSign` and `conj w₀ = ±w₀`, `conj w_last = ±A′` (targets 1), `conj w_{m+1} = ±C₂` (2), Plücker (3), then `stepEven_three` (4) |

Collection: one-time `rem_81f908cad48040ee9b75435fd77b2137` 2026-11-17 07:15 EST.

## Round 5: **`StepEven m` PROVED FOR ALL `m ≥ 1`** (2026-11-17 12:18Z)

j8_oddrev (john, 11:37Z) finished on its own at 18 min. `scratch/OddStep.lean`, 1704 lines, sha
`ebc5a2f3df07e29b0bfb88b6f76cd2a1f52c630f967e504dae3ec2387b92c8aa`; first 1350 lines byte-identical to
`CramerStep.lean`; rc=0 (~12.6 s, linter warnings only); axioms standard on all 23 theorems; `#check @stepEven_gen`
gives `∀ (m : ℕ), 1 ≤ m → StepEven m`.

- **`stepEven_gen (hm : 1 ≤ m) : StepEven m`** and `stepEven_three : StepEven 3`. The even side of the step lemma is
  now a general theorem for every `m ≥ 1` — no instance-by-instance work left on that side.
- Structure: `KPhi m` (`KPhi_sub_eq`) — the correct odd-size carrier, because **swapping `x ↔ y` does not permute the
  columns of `KP (2m+1)`** (the swap makes a `P_{m+1}`-type column the matrix does not have); `blockRevOdd` with
  `sign = 1`; `crossVec_KP_odd_swap`; then `conj w₀ = (−1)^m w₀`, `conj w_last = −A′`
  (`A′ = crossVec (KPhi m x y) ⟨m+1⟩`, the `kA46` analogue), `conj w_{m+1} = (−1)^m C₂`, and
  `plucker_odd : w₀C₁ + (−1)^m w_{m+1}C₂ + w_last A′ = 0` (via `cramer_three` on `w` with a zero re-inserted at
  `P_{m+1}`, no Plücker algebra); then one field-level `linear_combination` in `stepEven_alg`.
- Signs depend only on `m mod 2`. The round-4 guess `C₁w₀ − w_{m+1}C₂ = ±A′w_last` is right only for odd `m`.
- `StepEven 0` (m = 0) not covered (the `1 ≤ m` is inherited from `stepEven_cleared_gen`).
- My numpy check of the **literal** `StepEven m` statement (m = 1…5, all subfamilies) gives residuals 3e-15…5e-11.

Verdicts: **C5 REDUCED**, **C6 HALF CLOSED IN GENERAL** (even side done for all m; `StepOdd 2` still needs
`triP ≠ 0`), **C7 PARTIAL at n = 6** (Carver). Spine not ready — the chain needs both parities.

## Dispatch — round 6 (j9_stepodd, 2026-11-17 12:18Z, john)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j9_stepodd` | john | `scratch/OddStepTwo.lean` (= `OddStep.lean` verbatim + new section) | `stepOdd_two : StepOdd 2`, no extra hypothesis — remove `triP ≠ 0` by a division-free (Desnanot–Jacobi multiplied through) / polynomial-domain argument |

Collection: one-time `rem_9fe2a39f43e84eb78748a02e21009915` 2026-11-17 07:55 EST.

## Round 6: **`stepOdd_two : StepOdd 2` UNCONDITIONAL** (2026-11-17 12:57Z)

j9_stepodd (john, 12:18Z) finished on its own at 7 min. `scratch/OddStepTwo.lean`, 1805 lines, sha
`7ac5fc499d1b7ac160ba5fdcab02c09a4ff77c9a603eae80d5c47dd5eb0aabca`; first 1704 lines byte-identical to
`OddStep.lean`; rc=0 (13 s, 0 errors); axioms standard; `#check @stepOdd_two : StepOdd 2` with **no extra
hypothesis**. My numpy check covers the degenerate `triP = 0` case (residuals 3e-15…5e-14).

- `kK_dj_hom` (any `CommRing`): Desnanot–Jacobi homogenised at the Miquel point and multiplied through by
  `∏xᵢyᵢ·triP` — four `kK_dj` instances at `(z,Z) ∈ {0,1}²` + `kK_expand`, combined by bilinear interpolation. No division.
- `miquel_clifford_poly`: the cancellation, in the domain `MvPolynomial (Fin 10) ℂ` — instantiate at the generators,
  witness the prefactor nonzero at one point, conclude the bracket is the zero polynomial, then `MvPolynomial.eval`.
  **This is the density argument rounds 4–5 kept deferring; it works and is reusable.**
- `cliffordEq_miquel_noT`: Miquel point on the Clifford circle under `mD ≠ 0` only (no `triP`).
- `stepOdd_two`: `stepOdd_two_triP` with that lemma substituted.

Verdicts: **C5 REDUCED**, **C6 even side closed for all `m ≥ 1` + odd side closed at `m = 2`**, **C7 PARTIAL at n = 6**.

## Dispatch — round 7 (j10_oddgen, 2026-11-17 12:58Z, john)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j10_oddgen` | john | `scratch/OddGen.lean` (= `OddStepTwo.lean` verbatim + new section) | (A) mirror of `KP_sub_eq` for an **even** subfamily inside the **odd** parent + the Cramer identifications of `v 0`, `v ⟨m+1⟩`, `v last`; (B) `stepOdd_cleared_gen`; (C) `stepOdd_three : StepOdd 3` |

`stepOdd_two`'s proof uses `fin_cases` over `i` and `kK_p*` row permutations — it does not scale, which is why the odd
side now needs its own Cramer kit (the even side got one in round 4).

Collection: one-time `rem_bc2826145eb347eeb01a3e50ad0d0d27` 2026-11-17 08:30 EST.

## Round 7: **`stepOdd_gen (m) : StepOdd (m+1)` — the odd side is general** (2026-11-17 13:18Z / 08:18 EST)

j10_oddgen (john, 12:58Z) finished on its own at 20 min, all three targets. `scratch/OddGen.lean`, 2111 lines,
sha `f4b6a6b966648aad721755fde81c01ccb70181ec3d9ed33d78c9e4079fe4f7ae`; first 1805 lines byte-identical to
`OddStepTwo.lean`; rc=0 (14 s, 0 errors); 19 new declarations; axioms standard; `#check @stepOdd_gen :
∀ (m : ℕ), StepOdd (m + 1)`; `stepOdd_three : StepOdd 3`. My numpy check of the **literal** `StepOdd n` covers
n = 1…4, every subfamily, plus collinear-triple and near-degenerate configs (worst 6.3e-12).

- **Target A.** The subfamily matrix is **not** an exact submatrix of the odd parent: entries differ by one
  degree, so the identity is `(subRowsOdd …).submatrix id (last).succAbove = subScaled`, with row scalars
  `y (i.succAbove r)`; `crossVec_subScaled` then pulls the product out of the cross vector. `cramerO_P0/Q0/QL`
  are the three kept columns' coefficients, scaled by `∏y` / `∏(−x)`. General `m`, `i` symbolic, `[CommRing R]`.
- **Target B.** `rowRelOdd` + `stepOdd_cleared_gen` (the mirror of `stepEven_cleared_gen`).
- **Target C.** `stepOdd_alg` (field-level: the two conjugate cleared relations multiply to the circle equation
  times a nonzero product), `stepOdd_core`, `stepOdd_gen`. No case split over `i`, no Miquel argument, no
  `det7`/`det8`.

Verdicts: **C5 REDUCED**, **C6 BOTH SIDES ALL `n ≥ 1`** — no `Step*` statement is open any more — **C7 PARTIAL at
n = 6** (Carver 1920). No freeze: the chain is still not assembled.

## The assembly — what C5 still needs (three pieces, named)

`Clifford/Mobius.lean` and the Morley kernel are different models; `cliffordChainS_all_of` takes `h4`, `hodd`,
`heven` about a candidate point `E`. Pieces:

1. `Clifford.IsGCircleS ((↑) '' {z | oddCircleEq m v z = 0})` for `v 0 ≠ 0` — the kernel circle as a generalized
   circle (algebra: centre `Q/P`, radius `‖v last‖/‖P‖`). **Dispatched as j11.**
2. `E (2k+4) c = levelPointN (2k+4) (crossVec (KP (2k+4) c c̄))` — the even-level point identification against
   jack's `second`/`miquel`. Only `n = 4` exists (`levelPointN_four`).
3. Hypothesis bookkeeping: `GenPosN c` vs `(∀ k, c k ≠ 0)` + the subfamily `P ≠ 0`; a parent-side `v 0 ≠ 0`
   lemma for the odd parent.

## Dispatch — round 8 (j11_circles, 2026-11-17 13:36Z, jack)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j11_circles` | jack | `scratch/ChainOddBridge.lean` (= line 1 `import Clifford.Mobius` + `OddGen.lean` lines 2…2111 verbatim + new section) | (A) `kernelCircle_eq` completed square + `kernelCircle_isGCircleS` in `Clifford.IsGCircleS`; (B) if A lands, `hodd_levelPoint` (the `hodd` payload with `E` still written as `levelPointN`) |

First job on jack since round 1 — the bridge has to live in jack's namespace to use the real `IsGCircleS`.
Collection: one-time `rem_a7e8110099b145ec99d757f67dbb32bf` 2026-11-17 09:10 EST.

## Dispatch budget

Empirical: sessions end at ~30 min. Every brief from now on: one primary target, a compiling file at all times,
`scp` back every 10 minutes, no second target before the first compiles.

## Round 8: **`kernelCircle_isGCircleS` + `hodd_levelPoint` — the kernel circle is a generalized circle** (2026-11-17 14:10Z / 09:10 EST)

j11_circles (jack, 13:34Z) finished on its own in ~3 min, both targets. `scratch/ChainOddBridge.lean` sha
`8459bd5ad121d79ff803646b60330da10e337bcf17c6b6a7953a0dd2c11810bc`, 2,196 lines = line 1 `import Clifford.Mobius`
+ `OddGen.lean` lines 2…2111 byte-identical (`cmp` clean) + new section 2112…2196. rc=0, 18 s, 0 errors; axioms
`[propext, Classical.choice, Quot.sound]` on all four new theorems; `Clifford/Mobius.lean` `f8c9f013…` and
`gate.sh` untouched (hash + mtime; jack has no git). Collection `layer0/COLLECT_2026-11-17_r8.md`, files
`layer0/r8_jack/`, ledger `paperL_j11_circles_collect_20261117`.

- **Target A:** `kernelCircle_eq` (completed square, **no hypothesis**), `kernelCircle_eq_dist`,
  `kernelCircle_zeroSet`, `kernelCircle_isGCircleS (m) (v) (hv0 : v 0 ≠ 0)` via the sphere branch of `IsGCircleS`.
- **Target B:** `hodd_levelPoint` — the `hodd` payload with `E` written as `levelPointN`, witness = the parent
  kernel circle, membership from `stepOdd_gen (k+1)`, under `hd` + `hP0` + `hPi`.
- **Correction to the brief (and to round 7 §5): the centre is `conj Q / conj P`, not `Q/P`.** The `Q/P` form is
  false — rejected in 2,000/2,000 numeric trials. Paper prose must say `Q̄/P̄`.

### The assembly list, corrected (C5 still REDUCED)

1. ~~Kernel circle `IsGCircleS`~~ — **CLOSED**.
2. **`E` identification** — `E (2k+4) c = levelPointN (2k+4) (crossVec (KP (2k+4) c c̄))` against jack's
   `second`/`miquel`; only `n = 4` exists (`levelPointN_four`). **Next job.**
3. **Bookkeeping — three hypothesis families, not two:** `v 0 ≠ 0`; `v ⟨n/2⟩ ≠ 0` (the `levelPointN` denominator,
   which is also `StepEven`/`StepOdd`'s own premise); and the *determinants* `hP0`/`hPi`. `hd : ∀ j, d j ≠ 0` is
   free from `GenPosN` (`Transversal c d := conj c * d ≠ c * conj d` fails if either side is `0`). `hP0`/`hPi` are
   `crossVec` coordinates, so `GenTriple`'s `triP`/`cycP` is where they must come from.
4. **`heven_levelPoint`** (new, was missing from the three-piece list): `heven` is **not** `StepEven`. `StepEven m`
   puts the parent's level point on each subfamily's kernel circle; `heven` wants **one** circle through
   `E (2k+6) c` and all level-`(2k+4)` points of the sub-subfamilies — that circle is the `(2k+5)`-subfamily's
   kernel circle, so `StepEven` + `StepOdd` + Target A give it with **no new geometry**. Statement unwritten.

Then `cliffordChainS_all_of` is instantiated and C5 leaves REDUCED.

### Dispatch rule confirmed

Single target, compiling file at all times, `scp` back every 10 min. j11 = 3 min, no kill, one extra hypothesis
surfaced by the runner (both targets in one session). Next: the `E` identification on jack — it needs jack's
`second`/`miquel` and our `levelPointN` in one namespace, so jack again, same bridge shape
(`import Clifford.Mobius` + native file prefix). One-time follow-up scheduled for the next job.

## Round 9: **`E := Ept`, `h4` discharged**, and the obstruction that decides the next work (2026-11-17 11:50 EST)

j12_miquel (jack, 11:06 EST) finished on its own in ≈6 min, both targets. `scratch/ChainMiquel.lean`
sha `aa04c71a6e5f2d460a6e78a807325f843251cae09cdfd8e12d05e45beda96f1f`, 2,262 lines = `ChainOddBridge.lean`
lines 1…2196 byte-identical + new section 2197…2262; rc=0, 18 s, 0 errors; axioms standard on all four new
theorems; jack's `gate.sh` PASS 32; `Clifford/Mobius.lean` + `gate.sh` unchanged. Collection
`layer0/COLLECT_2026-11-17_r9.md`, files `layer0/r9_jack/`, ledger `paperL_j12_miquel_collect_20261117`.

- `Ept n c = ↑(levelPointN n (crossVec (KP n c c̄)))` — the point `E` finally exists.
- **`h4_pt : GenPosN c → ChainS 4 c {Ept 4 c}`, no carried hypothesis** (`P₂ = mD` and `GenPos4.mD_ne_zero`).
- **`heven_levelPoint`** in the exact `heven` shape, carrying `hc`, `hPc`, `hP0`, `hPij`.

### The obstruction: `GenPosN ⇏ P₀ ≠ 0`

Both payloads carry `P₀ ≠ 0` because `kernelCircle_isGCircleS` is sphere-branch only. I found an **exact**
counterexample at n = 5 (`layer0/r9_jack/p0_counterexample_exact.py`):

```
c = [-203/100 + 609/400i, -1659/676 + 2765/2704i, -2667/1156 + 1778/1445i,
     -6483/2500 + 15127/20000i, -6051/3364 + 10085/5887i]
crossVec (KP 5 c c̄) 0 = 0  exactly;   min Transversal 1.321, min triP 0.0205, min cycP 0.0776
```

So the degenerate case is a codim-1 family **inside** general position. Two consequences:

1. "Prove `hP0` from `GenPosN`" is **closed as a route** — do not spend a session on it.
2. The geometry is still right: those five subfamily level points are **collinear** (9.8e-12 residual vs 1.6e-4 for
   a 0.1 % perturbation), so the **line branch** of `IsGCircleS` covers the degenerate case.

### Dispatch — round 10 (j13_degenerate, jack)

`scratch/ChainDegenerate.lean` = `ChainMiquel.lean` lines 1…2262 byte-identical + new section. Two targets, both
**concrete and checkable by `norm_num`**, so the round produces Lean facts rather than another numeric claim:

- (A) `genpos_p0_zero` — the counterexample as a Lean theorem: the five explicit Gaussian-rational points satisfy
  `GenPosN` and `crossVec (KP 5 c c̄) 0 = 0`. This makes the negative result first-class.
- (B) `p0_levelpts_collinear` — for that same configuration, the five subfamily level points are collinear, with an
  explicit rational direction; the line-branch (`IsGCircleS`) packaging then follows.

If both land, the general statement to attack next is the collinearity lemma at arbitrary `k` (the limit of the kernel
circle as `P → 0`), which is the last piece of the `hodd`/`heven` payloads; `hc`/`hPc`/`hPij` still follow it.

## Round 10: the degenerate cases are Lean theorems, and the defect is at both ends of the cross vector (2026-11-17 12:45 EST)

j13_degenerate (jack, 11:57 EST) finished on its own in 12 min, all three targets. `scratch/ChainDegenerate.lean`
sha `1c75b247…`, 2,495 lines = `ChainMiquel.lean` 1…2262 byte-identical + new section 2263…2495; rc=0, 22 s, 0
errors; 41 axiom lines all standard; jack's gate PASS 32; `Clifford/Mobius.lean` + `gate.sh` unchanged.

- **`genpos_p0_zero`** — the r9 counterexample is now Lean: `c5` (five Gaussian rationals) with `GenPosN c5` and
  `crossVec (KP 5 c5 c̄) 0 = 0`. P₀ was *not* expanded: the proof exhibits the kernel vector `(1, −1, 1, −7/2, 1)`
  (the coefficient vector of the radial cubic the centres lie on) and uses `Matrix.exists_mulVec_eq_zero_iff`.
- **`p0_levelpts_collinear`** — `z5 i = z5 0 + (t5 i) • d5`, exact rationals; `z5 i` rewritten as `mN/mD` with each
  `mD ≠ 0` shown.
- **`p0_levelpts_gcircleS`** — `∃ Y, IsGCircleS Y ∧ ∀ i, ↑(z5 i) ∈ Y` via the **line branch** (`Y = lineS …`).

**The same defect at the middle coordinate.** My probe (`r10_jack/midcoordinate_probe.py`, corrected `cycP`, with
`n = 4` as a sanity test against `crossVec_KP4_P2_ne_zero`) finds an `n = 6` general-position family with
`crossVec (KP 6 c c̄) ⟨3⟩ = 0`. Made exact (`r10_jack/mid_zero_exact.py`): `c6` = six Gaussian rationals on the curve
`x y² + x² y − y² + 3xy − x² = 0` (the column relation `(0,−1,1,1,3,1)` with column 3 dropped), parametrised by
`z = r e^{iθ}`, `r = (2cos2θ − 3)/(2cosθ)`; `crossVec … ⟨3⟩ = 0` exactly, min margins 1.562 / 0.272 / 3.590.

That coordinate is the `levelPointN` denominator and `heven`'s `hPc` at `k = 0`, so `hPc`/`hPij` are dead ends like
`hP0` — and worse: there `Ept` returns the junk value `0` instead of a point. **The fix is projective:**
`Ept∞ n c := if crossVec (KP n c c̄) ⟨n/2⟩ = 0 then ∞ else ↑(levelPointN …)`. One statement in ℂP¹ covers both
degeneracies: the level points are concyclic with ∞ exactly when they are collinear.

### Dispatch — round 11 (j14_projective, jack)

`scratch/ChainProjective.lean` = `ChainDegenerate.lean` 1…2495 byte-identical + new section.

- (A) `genpos_mid_zero` — the exact `n = 6` witness in Lean (same `fin_cases` + kernel-vector pattern as r10).
- (B) `EptInf` (projective), `EptInf_eq_coe`, `h4_pt_inf`; optional `hc_of_genPos`.

Then the two *general* degeneracy lemmas are the last mathematical content of the payloads.

## Round 11: `Ept∞` + the middle-coordinate witness are in Lean (2026-11-17 13:45 EST)

j14_projective (jack, 12:49 EST) finished on its own in **4 min 44 s**, both targets, no kill. `scratch/ChainProjective.lean`
sha `077f4832…b012ad`, 2,602 lines = `ChainDegenerate.lean` 1…2495 byte-identical + new section 2496…2602; rc=0, 25.85 s,
0 errors; 50 axiom lines, all standard except the pre-existing `KP_sub_eq_odd` (subset); my own prefix `cmp` on jack
`PREFIX_OK`; forbidden-token grep clean; jack's `gate.sh` **PASS 32**; `Clifford/Mobius.lean` `f8c9f013…` and `gate.sh`
`fa304f45…` unchanged (mtimes 03:31Z / 04:02Z, hours before the launch; no git in `~/paperL_jack`).

- **`genpos_mid_zero : GenPosN c6 ∧ crossVec (KP 6 c6 c̄) ⟨3⟩ = 0`** — the r10 witness exact in Lean, via the kernel
  vector `(0,−1,1,1,3,1)` and `Matrix.exists_mulVec_eq_zero_iff` (no 6×6 expansion). Both ends of the cross vector are
  now unprovable from general position, in Lean.
- **`EptInf`** (projective, `∞` when the middle coordinate vanishes), `EptInf_eq_infty`, `EptInf_eq_coe`,
  `EptInf_c6 : EptInf 6 c6 = ∞`, **`h4_pt_inf : GenPosN c → ChainS 4 c {EptInf 4 c}`**, and
  **`hc_of_genPos`** which needs the extra `2 ≤ n` (at `n = 1` general position is vacuous and `c 0 = 0` is allowed —
  the brief's signature was false; the job said so rather than weakening it silently).
- B is infrastructure, not geometry: `h4_pt_inf` is cheap because `n = 4` never degenerates
  (`crossVec_KP4_P2_ne_zero`). `hodd`/`heven` are still stated with `Ept` and `hPc`/`hP0`/`hPij`.
- `layer0/COLLECT_2026-11-17_r11.md`, files `layer0/r11_jack/`. Ledger `paperL_j14_projective_collect_20261117`.

## Dispatch — round 12 (2026-11-17 13:45 EST): the two general degeneracy lemmas

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j15_p0general` | jack | `scratch/ChainP0Line.lean` (= `ChainProjective.lean` 1…2602 + new section) | **Target A** `child_levelPt_kernel_line` at **k = 0**: for *arbitrary* five centres, `GenPosN`, `P₀ = 0` ⟹ every `levelPointN 4` child satisfies `oddCircleEq 2 v z = 0`, i.e. lies on the kernel **line** (`v 0` is the quadratic coefficient of `kernelCircle_eq`, so `P₀ = 0` kills it). **Target B** `p0_children_gcircleS` — the line-branch `IsGCircleS` packaging in the exact `hodd` shape. Stretch: `k = 1`. |
| `paperL/j16_midgeneral` | john | `scratch/MidDegenerate.lean` (= same prefix) | **Target A** the `c6` instance: for each `i`, the five `levelPointN 4` children are collinear with explicit rationals (my probe: residual `~1e-14` for all six `i`, so the statement is true at the witness). **Target B** `heven_mid_line` at `k = 0`: `EptInf 6 c = ∞` and the five children on one line, in the exact `heven` shape with `hPc` replaced by `GenPosN` + `hmid`. |

john's `~/lean/paperL_john` gained `Clifford/Mobius.lean` (sha `f8c9f013…`, copied from jack) plus
`lake build Clifford.Mobius` so the prefix compiles there — verified rc=0, 19.7 s, 0 errors. That is also the
second-machine receipt for `ChainProjective.lean`.

If both general lemmas land, r13 = the two wrappers (`hodd_inf`, `heven_inf`) and the instantiation
`cliffordChainS_all_of EptInf h4_pt_inf …`, i.e. **C5 closes** and Paper L moves to the paper.

## Round 12: `hodd` k=0 unconditional; `heven` n=6 proved; the kernel line is dead (2026-11-17 14:40 EST)

j15_p0general (jack, 35 min) and j16_midgeneral (john, 32 min), both finished on their own.
`ChainP0Line.lean` `3787c85d…` (2,827 lines, rc=0, 28 s, 18 theorems), `MidDegenerate.lean` `177cfe13…` (3,296 lines,
rc=0, 27 s, 44 theorems); prefixes `PREFIX_OK`, tokens clean, axioms standard, `Clifford/*` + `gate.sh` untouched.

- **My r12 mechanism was wrong, and that is now a Lean theorem.** With `v 0 = P₀ = 0` the kernel-circle equation is
  **constant in `z`** (`oddCircleEq_of_P0_zero`, `kernel_eq_zero_of_P0` — the linear terms also carry `v 0`, and the
  odd Plücker relation kills the constant). Nothing can be read off the kernel vector. Never re-propose it.
- **The brief's Target B was false**: `p0_children_gcircleS_false` with `dX` (nonzero centres, `P₀ = 0`, one child
  with `mD = 0` → level point `0`, four distinct children with `cD = 2/45 ≠ 0`). Only `GenPosN` (or `hPi`) carries
  the statement.
- **`hodd` at k = 0 is unconditional** (`hodd_five`, `p0_children_gcircleS_genPos`): child level point = Miquel
  point → `clifford_two_clean` → `exists_gcircleS`. No kernel circle. **This is the template for general k.**
- **`heven` at n = 6 proved** (`heven_mid_line`, `heven_mid_line_c6`, all six `i` exact): `hmid ⟹ P₀(v)=conj P₃(v)=0
  ⟹ rowRel2 ⟹ Q₂(v)·P₀(w)=0 ⟹ children P₀-degenerate ⟹ cleared Clifford equation real-linear ⟹ lineS through ∞`.
  Left: `v ≠ 0` and the subfamily's `k1 ≠ 0`.
- Third degeneracy: `v ≡ 0` (six `GenPosN` centres on a non-circular conic through 0) — `hv` is not free.
- Probes for r13: `P₀ = 0` at k=1 ⟹ seven children **collinear** (8e-14…6e-12); `P₀ ≠ 0` ⟹ concyclic (1e-16).

## Dispatch — round 13 (2026-11-17 14:39 EST)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j17_oddone` | jack | `scratch/ChainOddOne.lean` (= `ChainP0Line.lean` 1…2827 + new section) | **A** exact 7-centre instance `d7` (`GenPosN`, `P₀ = 0`, seven `levelPointN 6` children collinear with explicit `p,u,t7`). **B** `hodd_one_P0_line`: general 7 centres, `GenPosN` + `P₀ = 0` + `hPi` ⟹ the seven children on one line (`IsGCircleS`). General `k` needs the parent's `k0/k1` minors; if that stalls, a precise obstruction is the deliverable. |
| `paperL/j18_midclose` | john | `scratch/MidClose.lean` (= `MidDegenerate.lean` 1…3296 + new section) | **A** `heven_mid_line_vzero`: the `v ≡ 0` case — do the 30 children coincide, and does `lineS p u` (which contains `∞`) close it? **B** derive `k1 ≠ 0` for a 5-subfamily from `GenPosN` + `P₀ = 0`, or map the exception exactly; then `heven_mid_line_all` = `heven` at k=0 with no extra hypotheses. |

After r13: if `hodd_one_P0_line` lands, r14 = the `k`-uniform version of the Miquel/`exists_gcircleS` route (the real
general-k question), and the wrappers `hodd_inf`/`heven_inf` + `cliffordChainS_all_of` instantiation. C5 stays
REDUCED until the general statements land — the base cases alone do not close it.

## Round 13: seven-centre line instance landed; one null run, and the lesson (2026-11-17 15:40 EST)

j17_oddone (jack, 47 min) **partial**: `ChainOddOne.lean` `f0d1fb58…` (3,343 lines, rc=0, 48 s, 0 errors, 36 theorems)
with Target A — `d7`, seven exact centres on `z = −w·B(w)/A(w)` where `P₀ = 0` **identically**, `GenPosN` exact,
`d7_children_P3`, explicit `p7/u7/t7`, `d7_children_collinear`, `d7_children_gcircleS`. Target B (general row relation
+ `hodd_one_P0_line`) was in flight when the session was reaped. Residue: `symB.py`'s symbolic identity
`Σ(columns·u) − (yi·x − xi·y)·g = yi·x³·hz − xi·y³·hZ` (the seven-centre analogue of `k0 − z k1 − z̄ k2`).

j18_midclose (john) = **NULL**: reaped at 18 min, no file, no report, only prefix reads and a Mathlib grep. Cause is
my brief ("analyse `k1 = 0`" is not a deliverable).

**Brief rules adopted from this round** (they apply to every future job on this project):
1. One target, stated as a theorem with a signature — no "analyse X" as a deliverable.
2. A mandatory compiling checkpoint in the first 15 minutes.
3. Explicit ban on reading/grepping Mathlib sources unless the brief names the lemma needed.
4. If a goal resists for more than ~10 minutes, the report must state the residual goal state and the job moves on.

## Dispatch — round 14 (2026-11-17 15:37–15:40 EST)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j19_oddgen` | jack | `scratch/ChainOddGen.lean` (= `ChainOddOne.lean` 1…3343 + new section) | **A** prove `symB.py`'s seven-row relation in Lean, then the consequence that with `P₀ = 0` the degenerate parent object is the line `hz = 0` and every child level point lies on it. **B** `hodd_one_P0_line` (general seven centres, `GenPosN` + `P₀ = 0` + `hPi`). |
| `paperL/j20_midvzero` | john | `scratch/MidVZero.lean` (= `MidDegenerate.lean` 1…3296 + new section) | one narrow target: `heven_mid_line_vzero` (six `GenPosN` centres with `v ≡ 0`, the five children per `i` on a line, `∞` in it). No Mathlib reading, checkpoint in 15 min. |

Then: if the row relation lands at `k = 1`, r15 = the same statement at general `k` (that is the last mathematical
piece of `hodd`), and separately the wrappers `hodd_inf`/`heven_inf` + `cliffordChainS_all_of` instantiation.
C5 stays REDUCED.

## Round 14: **`hodd_one_P0_line` PROVED** — the odd side is closed at k = 0 and k = 1 (2026-11-17 16:50 EST)

j19_oddgen (jack) finished on its own in 70 min, **both targets, no extra hypothesis, no `sorry`**. Verified and
collected `scratch/ChainOddGen.lean` `d2dafdb3…`, 3,692 lines = `ChainOddOne.lean` 1…3343 byte-identical
(`PREFIX_OK`) + 349 new lines / 20 declarations; my own `lake env lean` rc=0 in 50 s, 0 errors, forbidden-token grep
clean, all 16 new theorems on standard axioms, `gate.sh`/`Clifford/*` untouched. (A 16:38 Target-A-only checkpoint
`2661948c…` was verified too and is kept as `ChainOddGen_1638_targetA.lean`.)

- **Target A, general in the seven centres** (r13 had the `d7` instance only): `rowRel7_scalar` = `symB.py`'s
  `Σ(columns·u) − (yi·x−xi·y)·g7 = yi·x³·hz + xi·y³·hZ` in any `CommRing`; `M7g_mulVec`; `det_M7_expand`
  (`E₀ + zD + ZG + zZF`); `det_M7_D` (`= Q₀(v)`); `det_M7_F` (`= ±P₀`); `child_det_M7` (all rows vanish at a child
  point ⇒ `det = 0`); `child_line_P0` (`P₀ = 0` ⇒ real-linear `E₀ + Q₀(v)z + G z̄ = 0`); `collinear_of_reallin`.
- **SIGN CORRECTION**: the identity's `hZ` term is `+ xi·y³·hZ`; the r13 brief/report had `−`. `symB.py` and
  `rowRel7_scalar` agree on `+`. Paper prose must use `+`.
- **Target B `hodd_one_P0_line`**: split on `Q₀(v) = crossVec (KP 7) 4`. `Q₀ ≠ 0` → line via `child_line_P0` +
  `collinear_of_reallin`. `Q₀ = 0` → `Q3_zero_of_P0_Q0` (odd Plücker `|Q₀|² = |Q₃|²`) ⇒ singular minor ⇒ kernel `V`
  ⇒ `child_mulVec_of_parent` + `levelPointN_six_of_ker` ⇒ all seven children coincide ⇒ `lineS p 1`. The branch is
  non-empty (40-digit families with `P₀ = Q₀ = 0`). `d7_children_gcircleS'` re-derives r13's instance from it.

j20_midvzero (john) = **NULL** (stub `MidVZero.lean` `1b7098e4…`, compiles, nothing proved, reaped at 25 min).
**Do not re-dispatch it as such**: with `v ≡ 0` all 30 children collapse (r12) — it is a lemma, and `heven_inf` or a
second-machine receipt of `ChainOddGen.lean` is better value.

**Round 15 (next, jack)**: the `k`-uniform row relation — `rowRel7_scalar` → `M7g_mulVec` → `child_det` →
`child_line` with `2k+5` centres and level-`2k+4` children, built on the existing general Cramer kit
(`rowRelGen1/2`, `KP_sub_eq`, `cramerCoef_eq_crossVec`); second target `k`-uniform `Q3_zero_of_P0_Q0`. Then the
wrappers `hodd_inf`/`heven_inf` + `cliffordChainS_all_of` instantiation.

Verdicts: **C5 REDUCED, materially advanced** (odd side closed at k = 0 and k = 1; general k open, so C5 does not
move), **C6 both sides all n ≥ 1**, **C7 PARTIAL at n = 6** (Carver 1920 — never ours). Collection
`layer0/COLLECT_2026-11-17_r14.md`; ledger `paperL_j19_oddgen_collect_20261117` (full),
`paperL_j20_midvzero_NULL_20261117` (null).

## Dispatch — round 15 (2026-11-17 16:51 EST, jack)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j21_oddgenk` | jack | `scratch/ChainOddGenK.lean` (= `ChainOddGen.lean` 1…3692 byte for byte + new section) | **A** the `k`-uniform parent row relation (`rowRelN`/`MN_mulVec`/det expansion generalising `rowRel7_scalar`, `M7g`, `u7v` from 7 to `2k+5` rows; `D = crossVec (KP (2k+5)) ⟨k+2⟩`, `F = ±` the 0-coordinate). **B** `hodd_P0_line` at general `k`, with the **mandatory `k = 1` corollary** re-deriving `hodd_one_P0_line` (that is what pins the indexing). No Mathlib source reading; compiling checkpoint every 10 min; `head -n 3692 \| cmp - ChainOddGen.lean`. |

`hodd_P0_line` at general `k` is the first statement this project has had that would close the odd side for all `k` —
if it lands, C5's odd half is general and what is left is the two `heven` hyps plus the wrappers
(`hodd_inf`/`heven_inf`) and the `cliffordChainS_all_of` instantiation.

Collection: one-time `rem_993e3fefc07a40cf9b327b8291824aa4` at 2026-11-17 18:20 EST.

**Second-machine receipt for round 14, taken by me**: `ChainOddGen.lean` `d2dafdb3…` scp'd unchanged to john,
`lake env lean scratch/ChainOddGen_receipt.lean` rc=0, 40 s, 0 errors, 120 axiom lines.

## Round 15: **`hodd_P0_line` at general `k`** — the odd side is general (2026-11-17 18:25 EST)

j21_oddgenk (jack) finished on its own in 35 min, **both targets, no `sorry`**. Collected `scratch/ChainOddGenK.lean`
`e1eb09be…`, 4,236 lines = `ChainOddGen.lean` 1…3692 byte-identical + 544 new lines / 38 declarations; my own
recompile rc=0, 52 s, 0 errors; forbidden-token grep clean; 141 axiom lines all standard; `gate.sh` + `Clifford/*`
unchanged; the identical bytes compile on john (rc 0, 42 s) — two-machine receipt.

- **Target A**: `rowRelN` (`Σ colN·uN − (yi·x−xi·y)·gN = −yi(−x)^{k+2}(z w_{k+2}+w_{2k+4}) + xi y^{k+2}(Z w₀−w_{k+3})`,
  any `CommRing`), `MN_mulVec`, the two column linearities, `det_MN_expand`, `det_MN_D = (−1)^{k+3}·crossVec ⟨k+3⟩`,
  `det_MN_F = sign (sigN k)·crossVec 0`, `sign_sigN = (−1)^{k+2}`, `sigN_one = sig7`, `MN_one = M7g`, `uN_one = u7v`.
- **Index correction to my brief**: parent `Q₀` is `⟨k+3⟩`, not `⟨k+2⟩` (at k = 1 that is 4 = J19's `hQ0`). Child `hPi`
  index `⟨k+2⟩` was correct; no statement changed.
- **Target B**: `child_det_MN`, `child_line_P0N`, `child_mulVec_of_parentN`, `levelPointN_of_ker`,
  `QL_zero_of_P0_Q0`, `children_eq_of_P0_Q0N`, `hodd_P0_line (k)`; the mandatory `k = 1` corollary
  `hodd_one_P0_line' := hodd_P0_line 1 …` typechecks against J19's exact statement, and `d7_children_gcircleS''`
  recovers the r13 witness.

**C5: the odd side is general** (P₀ = 0 here, P₀ ≠ 0 in r8), still REDUCED overall — even payload only at n = 6 with
two extra hyps, chain not assembled.

## Dispatch — round 16 (2026-11-17 18:27 EST)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j22_hoddasm` | jack | `scratch/ChainOddHodd.lean` (= `ChainOddGenK.lean` 1…4236 + new section) | assemble **`hodd` itself** at general `k`: one statement covering `P₀ ≠ 0` (`kernelCircle_isGCircleS`) and `P₀ = 0` (`hodd_P0_line`), with `hPi` discharged from the prefix's `GenTriple`/`triP` where possible; residual report if the bookkeeping resists. |
| `paperL/j23_hevenall` | john | `scratch/MidHevenAll.lean` (= `MidDegenerate.lean` 1…3296 + new section) | **`heven_mid_line_all`**: `heven` at n = 6 with **no** `v ≠ 0` and **no** `k1 ≠ 0`, using the collapse lemmas for the degenerate branches (`children_eq_of_P0_Q0` pattern). |

Collection: one-time `rem_3ad8c4db049a4e88a366a9d82e912b34` at 2026-11-17 19:55 EST.

After r16: even general-`k` row relation (the mirror of r15), then the wrappers and the `cliffordChainS_all_of`
instantiation — that is the whole of what remains of C5.

## Round 16: the odd payload is assembled; the chain assembly typechecks (2026-11-17 19:59 EST)

j22_hoddasm (jack, 5 min) delivered `scratch/ChainOddHodd.lean` `187d190e…`, 4,396 lines = `ChainOddGenK.lean`
1…4236 byte-identical + 160 new lines / 8 declarations; my recompile rc=0, 54 s, 0 errors; 149 axiom lines all
standard; `gate.sh`/`Clifford/*` unchanged; identical bytes compile on john (43 s). j23_hevenall (john) = **NULL**
(24 min of sympy numerics, stub only).

**Structural finding:** `hodd`/`heven` are not theorems — they are the binder names of the two hypotheses of
`cliffordChainS_all_of` (`Mobius.lean` 330–336), with `E` abstract:
```
cliffordChainS_all_of E h4 hodd heven : ∀ n, 3 ≤ n → CliffordChainS n
hodd  : ∀ k d, GenPosN d → ∃ Y, IsGCircleS Y ∧ ∀ i, E (2k+4) (d ∘ i.succAbove) ∈ Y
heven : ∀ k c, GenPosN c → ∀ i, ∃ Y, IsGCircleS Y ∧ E (2k+6) c ∈ Y ∧ ∀ j, E (2k+4) ((c∘i)∘j) ∈ Y
```
So the deliverable is the `hodd` argument at `E := EptInf` (chosen because a child with `P_{k+2} = 0` is `∞` and
every `lineS` contains `∞` — that is what makes the `P₀ = 0` branch hypothesis-free).

Delivered: `hodd_inf` (both branches, one explicit `hPi : P₀ ≠ 0 → ∀ i, child P_{k+2} ≠ 0`), `hodd_inf_all`,
`hodd_inf_zero` (k = 0, unconditional), `hodd_inf_P0_eq` (**P₀ = 0, unconditional** — better than r15, which needed
`hPi` for all `i`), `hodd_inf_P0_ne`, `EptInf_child_eq_coe/infty`, and **`cliffordChainS_of_inf hPi heven :
∀ n ≥ 3, CliffordChainS n`** — the consumer check that the whole assembly typechecks.

`hPi` cannot come from `GenTriple` (a metric circle does not contain `∞`; `c6_P3_zero` is a `GenPosN` family with
`P₃ = 0`). The route: under `P₀ ≠ 0`, a vanishing child `P_{k+2}` forces the finite children onto a line.

**C5 now has exactly two inputs**: `hPi` (odd) and the even payload. C6 unchanged, C7 Carver 1920.

## Dispatch — round 17 (2026-11-17 20:02 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j24_hoddnohPi` | jack | `scratch/ChainOddHodd2.lean` (= `ChainOddHodd.lean` 1…4396 + new section) | (1) `child_line_of_P3_zero` — `GenPosN`, `P₀ ≠ 0`, some child `P_{k+2} = 0` ⟹ the finite children are collinear; (2) `hodd_inf'` with **no** `hPi`; (3) `hodd_inf_all'` + `cliffordChainS_of_inf' heven` — the whole odd side hypothesis-free. |

No john job: three null runs on even-side work (j18, j20, j23) — the even payload goes to jack after this.

Collection: one-time `rem_7dcf19312e344053abbdec2dda5b6e26` at 2026-11-17 20:55 EST.

## Round 17: the odd payload is hypothesis-free (2026-11-17 21:05 EST)

j24_hoddnohPi (jack, ≈28 min, all three targets, finished on its own) delivered `scratch/ChainOddHodd2.lean`
`f520f214…b7e5b0`, 4,691 lines = `ChainOddHodd.lean` 1…4396 byte-identical + 295 new lines / 15 declarations; my
recompile rc=0, 54.87 s, 0 errors; 163 axiom lines all standard; `gate.sh`/`Clifford/*` unchanged; identical bytes
compile on john (43 s).

- **`hPi` is gone.** New: `hodd_inf_P0_ne_some` (third branch), **`hodd_inf'` (no hypothesis)**, `hodd_inf_all'`,
  **`cliffordChainS_of_inf' (heven) : ∀ n ≥ 3, CliffordChainS n`**.
- **Stronger than asked:** under `P₀ ≠ 0` one vanishing child `P_{k+2}` forces **all finite children to coincide**:
  `child_crossVec_zero_of_P3` → `parent_ker_zero_of_P0` → `parent_detL_zero` → `children_eq_of_P3_zero` →
  `child_line_of_P3_zero`. Helpers `rowV_N`, `rowS_N`, `kpe_odd_eq_mul_y`, `kpe_odd_succ_eq_mul_x`, `shN`, `gN_range`.
- Branch non-empty (numerics, `k = 1, 2`, ≈1e-13 agreement); `c6` is in the `P₀ = 0` branch, not this one.

**C5 now has exactly one input: the even payload `heven`.** C6 unchanged, C7 Carver 1920.

## Dispatch — round 18 (2026-11-17 21:02 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j25_hevengen` | jack | `scratch/ChainEvenHeven.lean` (= `ChainOddHodd2.lean` 1…4691 + new section) | (0) numeric branch survey of `heven`; (1) `heven_kernel` — generic branch, witness = the subfamily's kernel circle, children from `hodd_levelPoint`, **parent from `stepEven_gen (k+2)`**; (2) `heven_inf` at general k with no hypothesis (degenerate branches: parent `∞` → `lineS`; subfamily `P₀ = 0` + parent finite → parent must lie on the children's line; some child `P_{k+2} = 0` → children coincide → any circle through parent and `p`); (3) `heven_inf_all` + `cliffordChainS_of_inf''` = **C5 CLOSED**. |

Collection: one-time `rem_b642d28870a34d45a9e6dd887d53bc39` at 2026-11-17 22:10 EST.

**Why this is one step, not a new theory:** with `m := k+2`, `StepEven m` (`stepEven_gen`) already says the parent
level point `levelPointN (2m+2)` lies on the kernel circle of every `(2m+1)`-subfamily, and the odd machinery puts the
children on that same circle. The even payload = C6's closed even step + r17's odd payload + branch bookkeeping.

After r18: if C5 closes, Paper L moves to layers/paper (round 2 in the plan's terms); if a branch is false, the
counterexample is a negative result and `heven` gets the smallest honest hypothesis set.

## Round 18: NULL run — and the brief rule it produced (2026-11-17 22:11 EST)

j25_hevengen (jack) was reaped at ≈62 min with **nothing delivered**: no `scratch/ChainEvenHeven.lean`, no report. It
spent ~25 min on numerics and then re-derived the general-`k` even row relation (`MN_mulVec`, `MN_col_*`, `det_MN_*`)
that already exists in the prefix (`rowRelN` 3732, `MN_mulVec` 3834). Its stretch Target 2 invited the detour.

**Numerics it did leave (partial):** at `n = 6, 8` every converged branch had residual ≤ 1e-36 — parent `∞`
(2e-42…6e-43), **subfamily `P₀ = 0` with parent finite (1.9e-42 — the parent lies on the children's line, the one
fact that is not free in Lean)**, subfamily `P₀ = 0` + degenerate child (7.1e-54), generic (4e-38…6e-62). No
counterexample; most constructed degenerate families failed to solve, so the degenerate coverage is thin.

**Brief rule (r18), now standing:** one theorem per job; say explicitly which lemmas already exist in the prefix and
must not be re-derived; require the prefix + `#check` checkpoint **on the host** inside 15 minutes.

Verdicts unchanged: **C5 REDUCED, one input (`heven`)**, C6 both sides all `n ≥ 1`, C7 Carver 1920.

## Dispatch — round 19 (2026-11-17 22:12 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j26_heven` | jack | `scratch/ChainEvenHeven.lean` (= `ChainOddHodd2.lean` 1…4691 + **one theorem**) | `heven_kernel`: generic branch of `heven` — witness = the subfamily's kernel circle, `IsGCircleS` from `kernelCircle_isGCircleS`, children from `stepOdd_gen (k+1)`/`hodd_levelPoint` + `EptInf_child_eq_coe`, parent from `stepEven_gen (k+2)` + `EptInf_eq_coe`. Explicitly: `rowRelN`, `MN_mulVec`, `det_MN_*`, `stepEven_gen`, `stepOdd_gen`, `kernelCircle_*`, `children_eq_of_P3_zero`, `child_line_of_P3_zero` are already there and must not be restated. |

Collection: one-time `rem_642519dfa9aa478a960b27ab7f083445` at 2026-11-17 23:30 EST.

## Round 19: `heven_kernel` proved — the even step's generic branch (2026-11-17 23:35 EST)

j26_heven (jack, theorem at 22:19, ≈7 min of Lean work) delivered `scratch/ChainEvenHeven.lean` `041ceee2…a9431a`,
4,739 lines = `ChainOddHodd2.lean` 1…4691 byte-identical + 48 lines; my recompile rc=0, 54 s, 0 errors; 164 axiom lines
all standard; `heven_kernel` exactly `[propext, Classical.choice, Quot.sound]`; `gate.sh`/`Clifford/*` unchanged;
identical bytes on john (43 s).

**`heven_kernel`** (the generic branch, `hmid` + `hP0` + `hPi`): `Y` = the subfamily's kernel circle
(`kernelCircle_isGCircleS`), children from `stepOdd_gen (k+1)` + `EptInf_child_eq_coe`, parent from
`stepEven_gen (k+2)` + `EptInf_eq_coe`. ~30 lines, no new mathematics — the brief rule from r18 (one theorem, named
prefix lemmas, 15-minute checkpoint on the host) is what made it land on the first try.

**`heven` is now exactly two line branches**:

| branch | hypotheses | what is needed | numerics |
|---|---|---|---|
| (a) | `P₀(d) ≠ 0`, all children finite, parent at `∞` | the parent at `∞` forces the finite children onto **one line** (even analogue of r17's `child_line_of_P3_zero`) | 6e-42, n = 6, 8 — true, not impossible |
| (b) | `P₀(d) = 0`, `Q_{k+3}(d) ≠ 0`, parent finite | the parent lies on the children's `lineS` from `child_line_P0N` (`StepEven (k+2)` without its non-degeneracy hypothesis) | 1.9e-42 |

Verdicts: **C5 REDUCED, two named targets left**, C6 both sides all `n ≥ 1`, C7 Carver 1920.

## Dispatch — round 20 (2026-11-17 23:33 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j27_evenline` | jack | `scratch/ChainEvenLine.lean` (= `ChainEvenHeven.lean` 1…4739 + new section) | Target 1 `child_line_of_parent_mid_zero` (branch a, no `hall` needed — `∞` is on every `lineS`); Target 2 `parent_on_child_line` (branch b, as `oddCircleEq` at the parent level point); then, only if both compile, wire `heven_inf` + `heven_inf_all` + `cliffordChainS_of_inf''` = **C5 closed**. |

Collection: one-time `rem_c5e5ee4fb7fd41389dc052d0b01523f7` at 2026-11-18 00:45 EST.

## Round 20: second NULL — the two even branches are not rewiring (2026-11-18 00:46 EST)

j27_evenline (jack) was reaped at ≈30 min with nothing delivered (no `ChainEvenLine.lean`, a `#check` stub and ten
numeric scripts only), and its 10-minute checkpoint rule was ignored.

**Diagnosis — the round's value.** r19's `heven_kernel` took 7 minutes because it was rewiring. The two remaining
branches are not:

- **(b)** cannot come from `stepEven_gen`: with `P₀(d) = 0`, `oddCircleEq_of_P0_zero` makes `oddCircleEq` a constant
  in `z`, so `StepEven`'s conclusion says nothing about the parent's position. Needed: `stepEven_cleared_gen` (1336)
  translated into `child_line_P0N`'s (4076) real-linear equation at the parent level point.
- **(a)** is the general-`k` form of the n = 6 `heven_mid_line` (`layer0/r12_john/MidDegenerate.lean` 3055–3296,
  proved r12 with `KP6_mulVec_sparse` + `det3_of_affine`) — an r13→r15-style arc with `rowRelN`.

Verdicts: **C5 unchanged** (generic branch proved, two line branches open), C6 both sides all `n ≥ 1`, C7 Carver 1920.

## Dispatch — round 21 (2026-11-18 00:47 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j28_evenline2` | jack | `scratch/ChainEvenLine.lean` (= `ChainEvenHeven.lean` 1…4739 + **one theorem**) | branch (b) only: `parent_on_child_line`, stated exactly in the `child_line_P0N` real-linear shape at the parent level point. `stepEven_cleared_gen` named as the engine, `child_line_P0N` as the template; **numerics and Mathlib exploration forbidden**; prefix+`#check` checkpoint inside 12 min; 25-min time box with a residual-goal report. |

Collection: one-time `rem_49516561ab1d4c3e8fa433a205c9cbae` at 2026-11-18 01:55 EST. Branch (a) follows as its own
job; the three-way wiring to `heven_inf` / `heven_inf_all` / `cliffordChainS_of_inf''` is a fourth, mechanical job.

## Round 21: branch (b) **CLOSED** — `parent_on_child_line` in 8 minutes (2026-11-18 01:57 EST)

j28_evenline2 (jack) delivered `scratch/ChainEvenLine.lean`, **4906 lines**, sha
`52b2c94dba390d6b9e373d9877daf9bd4612ee5f04beb381039c12208c531392`, 7 minutes after the 00:47 launch, no numerics
and no Mathlib exploration. My verification: `lake env lean` **rc = 0, 55 s**, prefix `PREFIX_OK`, **0** forbidden
tokens in 4740–4906 (word-boundary grep), `parent_on_child_line` on exactly
`[propext, Classical.choice, Quot.sound]`, `Clifford/*.lean` + `gate.sh` hashes and mtimes unchanged; second-machine
receipt on john **rc = 0, 44 s**, same bytes, `PREFIX_OK_JOHN`. Collection: `layer0/COLLECT_2026-11-18_r21.md`.

**`parent_on_child_line`** (branch (b), `P₀(d) = 0`, parent finite): the parent level point satisfies the subfamily's
real-linear line equation from `child_line_P0N`. Route taken (not the brief's): the kernel vector of the subfamily
matrix at the parent level point (parent cross vector with column `Q₀ = k+3` moved to the last slot, sign flipped,
mirroring `child_det_MN`), each row reduced to the parent's own row relation using
`levelPointN` + `conj_levelPointN_even`, then `det_MN_expand` / `det_MN_D` / `det_MN_F` / `linear_combination`.
New helpers `kpe5_lo/6_lo/5_hi/6_hi` (closed forms of `kpe` below/above the split). `h` and `hQ0` are unused
(linter warnings) — kept to match the brief's statement. `stepEven_cleared_gen` was **not** needed.

**The even payload is now one branch + wiring away.** `heven_kernel` (generic) and `parent_on_child_line` (b) are in
the prefix; open: **(a)** `child_line_of_parent_mid_zero` — parent at `∞` forces the finite children onto one line.

Verdicts: **C5 one line branch left** ((a)) then the mechanical wiring; C6 both sides all `n ≥ 1`; C7 classical,
**Carver 1920, never ours**.

## Dispatch — round 22 (2026-11-18 01:58 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j29_parentmid` | jack | `scratch/ChainEvenParentMid.lean` (= `ChainEvenLine.lean` 1…4906 + **one theorem**) | branch (a) only: `child_line_of_parent_mid_zero` (r20 Target 1 verbatim, no `hall` — `∞` is on every `lineS`). Templates named: `child_line_of_P3_zero` (4612) structurally, the `n = 6` worked case `heven_mid_line`/`heven_mid_line_c6` (`MidDegenerate.lean` 3055–3296, staged at `scratch/j29/MidDegenerate_excerpt.lean`), `rowRelN` (3732) as the `k`-uniform engine; `parent_on_child_line` (4884) as the worked parent-level mirror. **Numerics and Mathlib exploration forbidden**; prefix+`#check` checkpoint inside 12 min; 25-min time box with a residual-goal report. |

After (a): the three-way wiring to `heven_inf` / `heven_inf_all` / `cliffordChainS_of_inf''` is a fourth, purely
mechanical job — (b) → the `lineS` of `child_line_P0N`; (a) → `lineS p u`; generic (`hmid ≠ 0`, `P₀(d) ≠ 0`, all
children finite) → `heven_kernel`; some child `P_{k+2} = 0` → children coincide (`children_eq_of_P3_zero`), any
circle through the parent and that point.

## Round 22: branch (a) is **degenerate-only** — partial, and that is the finding (2026-11-18 02:12 EST)

j29_parentmid (jack, 13.5 min measured) delivered `scratch/ChainEvenParentMid.lean` **5065 lines**, sha
`47d429a8…634b54`, prefix = the r21 file (`PREFIX_OK`), my verification rc = 0 / 56 s / 0 errors, both new theorems on
`[propext, Classical.choice, Quot.sound]`, 0 forbidden tokens, `Clifford/*` + `gate.sh` unchanged, john receipt
rc = 0 / 44 s. Collection: `layer0/COLLECT_2026-11-18_r22.md`.

**It did not prove the brief's statement.** `child_line_of_parent_mid_zero` was proved only with an extra
`hv : crossVec (KP (2k+6) c c̄) ≠ 0`, under which it is vacuous (`absurd`). What it did prove is the structural fact:

- **`parent_crossVec_zero_of_mid`** (5009): `GenPosN c → hmid = 0 → P₀(d) ≠ 0 →` the **whole parent cross vector
  vanishes**. (`parent_mid_ker_MNF` (4915): with `V₀ = V_{k+3} = 0`, the parent cross vector with columns `0, k+3`
  dropped and `V_{k+4}` moved to the front is a kernel vector of the subfamily's `MN` at the `F` columns; `det_MN_F`
  is `±P₀(d) ≠ 0`.)

So **branch (a) can only occur where the parent cross vector is degenerate (`V = 0`)**, and the brief's exact
collinearity statement is still open. The way through is the general-`k` form of the *verified* `n = 6` lemma
`subfamily_P0_zero`: `hmid = 0` + `V_last ≠ 0` ⇒ `P₀(d) = 0`, after which `child_line_P0N` gives the line through `∞`
and every finite child — no branch (a) needed at all.

Verdicts: **C5 unchanged in the strict sense** ((b) closed; (a) degenerate-only, exact shape open; wiring not
started), C6 both sides all `n ≥ 1`, C7 classical, **Carver 1920, never ours**.

## Dispatch — round 23 (2026-11-18 02:16 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j30_subp0` | jack | `scratch/ChainEvenSubP0.lean` (= `ChainEvenParentMid.lean` 1…5065 + **one theorem**) | `subfamily_P0_zero_gen` (hypothesis-free: `hmid = 0`, `V_last ≠ 0` ⇒ `P₀(d) = 0`), the general-`k` form of the verified `n = 6` `subfamily_P0_zero` (staged at `scratch/j30/MidDegenerate_excerpt.lean`), engine `rowRel2_gen` at `m = k+2` + `conj_crossVec_even`. No numerics, no Mathlib, 12-min checkpoint, 20-min box. Collection `rem_6bce90d7927b416997e237c9ffc682eb` 02:50 EST. |

**Residual corner for Josh (only if the wiring needs it):** `hmid = 0 ∧ V_last = 0 ∧ P₀(d) ≠ 0` forces `V = 0`; a
proof needs either a general-`k` rank statement (`GenPosN c → crossVec (KP (2k+6) c c̄) ≠ 0`; the `n = 4` analogue is
`crossVec_KP4_P2_ne_zero`) or a direct collinearity argument from `V = 0`.

## Round 23: `subfamily_P0_zero_gen` **CLOSED** — the `hmid = 0` branch falls (2026-11-18 02:52 EST)

j30_subp0 (jack, ≈1.8 min to the deliverable) delivered `scratch/ChainEvenSubP0.lean` **5093 lines**, sha
`cb2afb5e…845ac19`, prefix = the r22 file (`PREFIX_OK`); my verification rc = 0 / 55 s / 0 errors, `#check` exactly
the brief's hypothesis-free statement, `[propext, Classical.choice, Quot.sound]`, 0 forbidden tokens, `Clifford/*` +
`gate.sh` unchanged, john receipt rc = 0 / 44 s with `PREFIX_OK_JOHN`. Collection:
`layer0/COLLECT_2026-11-18_r23.md`.

**`subfamily_P0_zero_gen`** at general `k`: `hmid = 0 → V_last ≠ 0 → P₀(c ∘ i.succAbove) = 0`, the general-`k` form
of r12's `n = 6` lemma, 28 lines, no new mathematics (`conj_crossVec_even (k+2)` + `rowRel2_gen` at `m = k+2`).

**Consequence for the wiring:** with the parent at `∞`, `V_last ≠ 0` now forces `P₀(d) = 0`, so `child_line_P0N`
gives the line through `∞` and every finite child — **branch (a) is not needed for that half at all**. The only
case outside the line branch is the degenerate corner `hmid = 0 ∧ V_last = 0 ∧ P₀(d) ≠ 0` (where
`parent_crossVec_zero_of_mid` forces `V = 0`) — Josh's mathematics, not a Lean chore.

Verdicts: **C5 one step from closed** (branch (a) eliminated for the `V_last ≠ 0` half; `heven_inf` + the two
wrappers remain), C6 both sides all `n ≥ 1`, C7 classical, **Carver 1920, never ours**.

## Dispatch — round 24 (2026-11-18 02:52 EST, jack only)

| job | host | deliverable | purpose |
|---|---|---|---|
| `paperL/j31_eveninf` | jack | `scratch/ChainEvenInf.lean` (= `ChainEvenSubP0.lean` 1…5093 + `heven_inf` + `heven_inf_all` + `cliffordChainS_of_inf''`) | **the wiring**, branch skeleton spelled out in the brief: `hmid = 0` → (`V_last ≠ 0` → `subfamily_P0_zero_gen` → `P₀ = 0` → line branch via `child_line_P0N` + `collinear_of_reallin`; `V_last = 0` → residual corner, report only), `hmid ≠ 0` → (`P₀ = 0` → `parent_on_child_line` + children, `Q₀ = 0` via `QL_zero_of_P0_Q0`; `P₀ ≠ 0` all children finite → `heven_kernel`; some child `P_{k+2} = 0` → `children_eq_of_P3_zero`). Structural template `hodd_inf_P0_eq` (4281). 35-min box, **no silent extra hypotheses**, residual-goal report. Collection `rem_5dcd770b1b9e469eb32846e22534a4cb` 03:40 EST. **If all three compile, C5 is closed.** |

## Round 24 COLLECTED: even wiring done, **C5 not closed** — one named corner left (2026-11-18 03:46 EST)

j31_eveninf (jack, 4.8 min to the deliverable) delivered `scratch/ChainEvenInf.lean` **5288 lines**, sha
`7117c1e9…94ded`, prefix = the r23 file (`PREFIX_OK`); my verification rc = 0 / 56 s / 0 errors, 0 forbidden
tokens, six new declarations all on `[propext, Classical.choice, Quot.sound]`, `Clifford/*` + `gate.sh` unchanged,
john receipt same bytes / `PREFIX_OK_JOHN` / rc = 0 / 45 s. Collection: `layer0/COLLECT_2026-11-18_r24.md`.

**It did not deliver the brief's gate.** `heven_inf` was proved only as `heven_inf_of_corner` (explicit
`hcorner`), and the chain only as `cliffordChainS_of_corner (hC : EvenCorner)` — `cliffordChainS_of_inf''` was
not produced. What *did* land, hypothesis-free:

- **`heven_line_of_P0`** — the whole `P₀(d) = 0` branch, both `hmid` cases (`QL_zero_of_P0_Q0` kernel vector when
  `Q₀ = 0`; `collinear_of_reallin` + `parent_on_child_line` when `Q₀ ≠ 0`).
- packaging lemmas `heven_of_line` / `heven_of_common`, and `heven_inf_of_corner` as the complete four-way split:
  `P₀ = 0` → above; `hmid ≠ 0` + all children finite → `heven_kernel`; some child `P_{k+2} = 0` →
  `children_eq_of_P3_zero`; `hmid = 0` + all finite → `parent_crossVec_zero_of_mid` ⇒ `V = 0` ⇒ corner.
- **`def EvenCorner : Prop`** — the residual corner as a named, unproved proposition (a `def`, not an `axiom`).

**Verdicts:** **C5 NOT closed** (everything except the degenerate corner `hmid = 0 ∧ V_last = 0 ∧ P₀(d) ≠ 0`);
C6 both sides all `n ≥ 1`; C7 classical, **Carver 1920, never ours**.

**Open — Josh's maths, not a Lean chore:** in the corner (`V = 0`, `P₀(d) ≠ 0`, all grandchildren finite) prove the
grandchildren collinear: (i) general-`k` rank statement `GenPosN c → crossVec (KP (2k+6) c c̄) ≠ 0` (the `n = 4`
analogue `crossVec_KP4_P2_ne_zero`; makes the corner empty), or (ii) collinearity from `V = 0`. Only the `n = 6`
`heven_mid_line` instance is worked. **No round 25 dispatched**; the paper stage (layers 10–13, `SCOUT.md`
verdicts ready) stays blocked on that call.

## Round 25 — dispatch for `EvenCorner`, first attempt crashed, retry running (2026-11-18)

**Route chosen by Josh** ("use which one you think will work first"). Before dispatch I killed the rank route
numerically: `GenPosN` configurations at `k = 0` with `V = 0` exist (`layer0/r25_jack/RANK_ROUTE_COUNTEREXAMPLE.json`,
margins nondegenerate: `triP` 1e-2…0.14, `cycP` 1.3e-3…0.024, transversals ≥ 0.04, all `|c| ≥ 0.08`), and in them the
grandchildren **are** collinear to 1e-8. So the corner is nonempty and true — only a collinearity argument can close
C5 (ledger `paperL_r25_rank_route_REFUTED_20261118`).

**Dispatch:** jack `j32_corner`, one theorem `EvenCorner_proof : EvenCorner` on the r24 prefix (5288 lines,
`7117c1e9…`), 30-min box, residual report, no extra hypotheses, no numerics.
**First attempt died 07:53:17 EST (439 s) mid-stream, no output, no error, no OOM** — deliverable byte-identical to the
prefix, no `REPORT.md` (ledger `paperL_j32_corner_CRASH_20261118`, `gate_pass` false).
**Retry `j32b_corner` launched 08:23:46 EST** with an explicit context-discipline section (read only 5094–5288 and
named ranges, bound greps, compile only at the checkpoint and the end). Collection 08:58 EST
(`rem_0383762ed2cc41e0a19e4b3c40ac3e64`). If it dies the same way, the runner is the problem, not the maths.

## Round 25 COLLECTED: the corner is now **one scalar identity** (`EvenCornerQL`) (2026-11-18 09:05 EST)

Retry `j32b_corner` (launched 08:23:46 EST, exited itself 08:44, 21 min): `scratch/ChainEvenCorner.lean`
**5344 lines**, sha `0d1839e8…f55f`, prefix = the r24 file (`PREFIX_OK`); rc = 0 / 57 s jack, 68 s john (same
bytes, `PREFIX_OK_JOHN`), 0 forbidden tokens, standard axioms only, `Clifford/*` + `gate.sh` untouched.
Collection: `layer0/COLLECT_2026-11-18_r25.md`, report `layer0/r25_jack/REPORT_j32b.md`.

**The reduction (compiles):**

- **`evenCorner_of_QL`** — if the subfamily cross vector `w` has `w_last = 0` and `w₀ ≠ 0`, then `w ∘ castSucc` is a
  common nonzero kernel vector of every grandchild `KP (2k+4)` (`child_mulVec_of_parentN`), so **all finite
  grandchild level points coincide** (`levelPointN_of_ker`) — collinear with `u = 1`, `t = 0`.
- **`EvenCornerQL`** — the residual as a named `def : Prop`: in the corner `w_last = 0` (the subfamily's kernel
  circle has radius 0). **`evenCorner_of_cornerQL : EvenCornerQL → EvenCorner`.**

So C5 is **one scalar identity** away: `EvenCornerQL` → `EvenCorner` → (r24) `cliffordChainS_of_corner` → all `n ≥ 3`.

**Paper proof of the residual is complete** (`REPORT_j32b.md`): insert `0` into `w` at column `k+3` → a parent
kernel vector (rows `≠ i` by `mulVec_crossVec`; row `i` a Laplace/border expansion `= ±V_{k+3} = 0`); the kernel
conjugation symmetry gives `s_{k+3} = conj w₀ ≠ 0`; the resultant binary form of degree `2k+5` vanishes at the
`2k+6` pairwise non-proportional points `(c_r : c̄_r)` ⇒ identically zero; top coefficient `−conj w₀ · w_last`.
**Three lemmas are missing from the prefix** (row-`i` Laplace identity, kernel-vector conjugation symmetry, "binary
form with more zeros than its degree is zero" + top-coefficient extraction). Estimate **250–400 lines**.

**Numeric check (mine):** at a corner point with `|V| = 7e-15`, `|w_last|/|w₀| = 2e-10…7e-10` for every `i`
(`layer0/r25_jack/CORNER_EXACT_k0.json`) — the identity is true. What remains is formalisation of a written proof.

**Verdicts:** C5 = modulo `EvenCornerQL` only; C6 both sides `n ≥ 1`; C7 classical, **Carver 1920, never ours**.
**Next: one job with the three lemmas (45–60 min box) — needs Josh's go.** Paper stage (layers 10–13) still blocked.
