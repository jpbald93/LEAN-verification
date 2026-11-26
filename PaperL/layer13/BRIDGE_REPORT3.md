# Bridge report 3 — `scratch/BlindChain.lean`

## Final compile

Exact command required by the brief:

```
cd /home/jackagent/paperL_jack && env PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$HOME/paperL_jack lake env lean scratch/BlindChain.lean
```

Final output (exit code `0`; the first three warnings are the harmless `simpa` linter):

```
scratch/BlindChain.lean:83:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
scratch/BlindChain.lean:86:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
scratch/BlindChain.lean:89:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
scratch/BlindChain.lean:189:6: warning: declaration uses `sorry`
scratch/BlindChain.lean:223:8: warning: declaration uses `sorry`
EXIT=0
```

Prerequisite (not an edit to any frozen file): `scratch/BridgeBlind.olean` was absent, so it was
generated once with `lake env lean -o scratch/BridgeBlind.olean scratch/BridgeBlind.lean` before the
first import of `scratch.BridgeBlind`.

## Sorries

Count: **2**.

1. `scratch/BlindChain.lean:202` (`sorry` token), declaration starts at
   `scratch/BlindChain.lean:189` — `blindChain_four`, the mixed-degenerate level-4 branch
   (`hdeg`: at least one, but not all, triples have collinear second intersections).
2. `scratch/BlindChain.lean:240` (`sorry` token), declaration starts at
   `scratch/BlindChain.lean:223` — `blindN1_direct`, the case `n ≥ 5` (stage C).

No `axiom`, `admit`, `native_decide`, or `unsafe` was introduced. `scratch/BridgeBlind.lean`,
`Clifford/*.lean`, and `scratch/BlindCompareFull.lean` were not edited.

## Stage A — complete

Proved (file:line is the declaration start):

* `scratch/BlindChain.lean:58`
  ```lean
  lemma blindChain_three {c : Fin 3 → ℂ} (hc : BlindGenPos c) :
      ∃ Y : Set BlindS, BlindCliffordP false 3 c Y
  ```
  Construction: rewrite the three `BlindSecond`s to `Clifford.second` via `BlindSecond_eq`,
  use their pairwise distinctness from `hc.2`, apply
  `Clifford.exists_gcircle (Clifford.cospherical_or_collinear p01 p02 p12)`, and transport with
  `blindIsGCircle_of_isGCircle_of_two`. This covers the collinear (line + `∞`) branch as well.

Supporting algebra proved for stage B (also complete):

* `scratch/BlindChain.lean:22`
  ```lean
  lemma second_eq_of_collinear {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
      (hcol : Collinear ℝ ({a, b, c} : Set ℂ)) :
      Clifford.second a b = Clifford.second a c
  ```
  Proved by writing `c = a + t • (b - a)` with real `t`, then `field_simp`/`ring`.
* `scratch/BlindChain.lean:94`
  ```lean
  lemma noncollinear_centres_of_blind {a b c : ℂ}
      (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
      (hne : BlindSecond a b ≠ BlindSecond a c) :
      ¬ Collinear ℝ ({a, b, c} : Set ℂ)
  ```
  Consequently the `triP ≠ 0` part of `GenTriple` *does* follow from `BlindGenPos`; only
  `cycP ≠ 0` (non-collinear second points) remains the real gap, as the brief predicted.
* `scratch/BlindChain.lean:105`
  ```lean
  lemma genTriple_of_blind {a b c : ℂ}
      (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
      (hbc : Clifford.Transversal b c)
      (hne : BlindSecond a b ≠ BlindSecond a c)
      (hsec : ¬ Collinear ℝ ({Clifford.second a b, Clifford.second a c,
        Clifford.second b c} : Set ℂ)) :
      Clifford.GenTriple a b c
  ```

## Stage B — generic case complete; mixed degenerate case open

Proved:

* `scratch/BlindChain.lean:116`
  ```lean
  lemma genPosN_three_of_genPos4 {c : Fin 4 → ℂ} (hc : BlindGenPos c)
      (h : Clifford.GenPos4 (c 0) (c 1) (c 2) (c 3)) (i : Fin 4) :
      Clifford.GenPosN (c ∘ i.succAbove)
  ```
* `scratch/BlindChain.lean:133`
  ```lean
  lemma genPos4_of_blindGenPos {c : Fin 4 → ℂ} (hc : BlindGenPos c)
      (h012 : ¬ Collinear ℝ ({second (c 0) (c 1), second (c 0) (c 2), second (c 1) (c 2)}))
      (h013 : ¬ Collinear ℝ ({second (c 0) (c 1), second (c 0) (c 3), second (c 1) (c 3)}))
      (h023 : ¬ Collinear ℝ ({second (c 0) (c 2), second (c 0) (c 3), second (c 2) (c 3)}))
      (h123 : ¬ Collinear ℝ ({second (c 1) (c 2), second (c 1) (c 3), second (c 2) (c 3)})) :
      Clifford.GenPos4 (c 0) (c 1) (c 2) (c 3)
  ```
  (Set types abbreviated in this display; the file has the full types.)
* `scratch/BlindChain.lean:161`
  ```lean
  lemma blindChain_four_of_genPos4 {c : Fin 4 → ℂ} (hc : BlindGenPos c)
      (hpos : Clifford.GenPos4 (c 0) (c 1) (c 2) (c 3)) :
      ∃ p : BlindS, BlindCliffordP false 4 c {p}
  ```
  Uses `Clifford.chain4_ofS`, `blindCliffordP3_of_chainS`, and
  `genPosN_three_of_genPos4`.
* `scratch/BlindChain.lean:189` (partial)
  ```lean
  lemma blindChain_four {c : Fin 4 → ℂ} (hc : BlindGenPos c) :
      ∃ p : BlindS, BlindCliffordP false 4 c {p}
  ```
  The `¬hdeg` branch is fully proved by `genPos4_of_blindGenPos` +
  `blindChain_four_of_genPos4`. The `hdeg` branch is the labelled `sorry`.

Numerically checked (not in Lean) that the mixed degenerate case really occurs. Take
`a = 1+i`, `b = 2`, `c = 1-i`, `d = 1/2+2i`; the centres are pairwise transversal and all six
second intersections are distinct. With `sij = Clifford.second (centre_i) (centre_j)`:
`s01 = 2+2i`, `s02 = 2`, `s12 = 2-2i` are collinear, while the other three triples are not.
The common level-4 point is finite, approximately `q = 2 + 16/13 i = 2 + 1.230769i`: it lies
on the line through `s01,s02,s12` and on the circles through `s01,s03,s13`, `s02,s03,s23`,
`s12,s13,s23` (numerical residuals `≤ 2e-15`). So `∞` is **not** in general a level-4 point.

Useful structural fact found: `Clifford.second u v` is the foot of the perpendicular from `0`
to the line through `u` and `v`, and `Clifford.cross_second` /
`Clifford.cycP_ne_zero_iff` turn collinearity of `s01,s02,s12` into
`cycP a b c (conj a) (conj b) (conj c) = 0`, i.e. `0,a,b,c` concyclic. Equivalently, under
inversion `z ↦ 1/z` the problem is the Miquel theorem for the four lines `2*Re(a*z)=1`, ...,
`2*Re(d*z)=1`; the writer point is the inverse of that Miquel point. This route is not yet
formalized in Lean.

## Stage C — not reached

`blindN1_direct` (declaration at `scratch/BlindChain.lean:223`) is proved outright for `n = 1,2,3`
and for `n = 4` modulo the single stage-B `sorry`; `n ≥ 5` is the second labelled `sorry`.

## What the induction still needs (exact statements)

1. **Degenerate Clifford's first theorem** (closes the remaining stage-B `sorry`). All four
   triples are assumed to have distinct second points and no common nonzero point; one triple
   has collinear second points. Needed form:

   ```lean
   lemma chain4_common_of_collinear_seconds
       {a b c d : ℂ}
       (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
       (had : Clifford.Transversal a d) (hbc : Clifford.Transversal b c)
       (hbd : Clifford.Transversal b d) (hcd : Clifford.Transversal c d)
       (hno : ∀ {x y z}, x ∈ {a,b,c,d} → y ∈ {a,b,c,d} → z ∈ {a,b,c,d} →
            ¬ ∃ w : ℂ, w ≠ 0 ∧ w ∈ BlindCircle x ∧ w ∈ BlindCircle y ∧ w ∈ BlindCircle z)
       (hneq : Clifford.second a b ≠ Clifford.second a c ∧
               Clifford.second a b ≠ Clifford.second a d ∧
               Clifford.second a c ≠ Clifford.second b c)
       (hcol : Collinear ℝ ({Clifford.second a b, Clifford.second a c,
                              Clifford.second b c} : Set ℂ)) :
       ∃ q : ℂ,
         Collinear ℝ ({Clifford.second a b, Clifford.second a c,
                        Clifford.second b c, q} : Set ℂ) ∧
         (Cospherical ({Clifford.second a b, Clifford.second a d,
                        Clifford.second b d, q} : Set ℂ) ∨
          Collinear ℝ ({Clifford.second a b, Clifford.second a d,
                        Clifford.second b d, q} : Set ℂ)) ∧
         (Cospherical ({Clifford.second a c, Clifford.second a d,
                        Clifford.second c d, q} : Set ℂ) ∨
          Collinear ℝ ({Clifford.second a c, Clifford.second a d,
                        Clifford.second c d, q} : Set ℂ)) ∧
         (Cospherical ({Clifford.second b c, Clifford.second b d,
                        Clifford.second c d, q} : Set ℂ) ∨
          Collinear ℝ ({Clifford.second b c, Clifford.second b d,
                        Clifford.second c d, q} : Set ℂ))
   ```

   (In practice one also needs the analogous statements for the other three choices of the
   collinear triple, obtained by permuting the four centres. Given this lemma, the four
   writer-side level-3 objects are built by `exists_gcircle` applied to the four-point sets, so
   `q` is in each by construction; the level-4 blind object follows.)

   **Precise algebraic obstruction.** `Clifford.chain4_of` (`Clifford/Clean.lean:199`),
   `Clifford.clifford_one` (`Clifford/Basic.lean:601`) and `Clifford.gamma_cospherical`
   (`Clifford/Basic.lean:563`) all require `GenTriple` of the relevant triple, i.e. `cycP ≠ 0`.
   In the mixed case `mD (a b c d) (conj a) … = 0`, so `miquel = mN / mD = 0` by Lean's
   division-by-zero convention; it is junk, not the common point.

   The exact missing determinant identity is:
   ```lean
   lemma cD_second_of_cycP_zero {a b c d : ℂ}
       (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
       (had : Clifford.Transversal a d) (hbc : Clifford.Transversal b c)
       (hbd : Clifford.Transversal b d) (hcd : Clifford.Transversal c d)
       (hcyc : Clifford.cycP a b c (conj a) (conj b) (conj c) = 0) :
       Clifford.cD (second a c) (second a d) (second c d) (second a b) = 0 ∧
       Clifford.cD (second b c) (second b d) (second c d) (second a b) = 0
   ```
   plus the three permutations. `Clifford.cD_eq_zero_iff` then gives `Cospherical ∨ Collinear`
   for those four-point sets, and `Clifford.exists_gcircle` gives the writer objects, so the
   level-4 point follows. An attempted proof by rewriting `Clifford.second_eq_coords`, then
   `field_simp`/`ring_nf` against the unfolded `cycP` determinant, blew up and did not close;
   no such lemma exists in the repo. The closest existing results are
   `Clifford.chain4S_infty` (`Clifford/Mobius.lean:261`, only the forward implication
   `ChainS 4 {∞} → colD = 0`), `Clifford.chain4_cD` (`Clifford/General.lean:61`, also forward),
   and `levelPointN_four_div` / `EptInf` (`Clifford/MorleyKernel.lean:2674`, `:2549`), which
   send `mD = 0` to `0` or `∞` and have no incidence theorem outside `GenPosN`.

2. **Degenerate Clifford's second theorem** (needed at odd levels ≥ 5):

   ```lean
   lemma clifford_two_degenerate {n : ℕ} (c : Fin n → ℂ) (hc : BlindGenPos c) :
     ∀ k : ℕ, 5 ≤ 2 * k + 5 → 2 * k + 5 ≤ n →
       -- after restricting to any five entries, the five level-4 points lie on a generalized circle
       ∃ E : (m : ℕ) → (Fin m → ℂ) → OnePoint ℂ,
       True
   ```
   More usefully, mirroring `Clifford.clifford_two_clean` (`Clifford/Clean.lean:123`), the exact
   missing statement is:

   ```lean
   lemma clifford_two_clean_blind {a b c d e : ℂ}
       (hpair : ∀ x y ∈ ({a,b,c,d,e} : Set ℂ), x ≠ y → Clifford.Transversal x y)
       (hno : ∀ x y z ∈ ({a,b,c,d,e} : Set ℂ), x ≠ y → x ≠ z → y ≠ z →
         ¬ ∃ w, w ≠ 0 ∧ w ∈ BlindCircle x ∧ w ∈ BlindCircle y ∧ w ∈ BlindCircle z)
       (hne : ∀ x y z ∈ ({a,b,c,d,e} : Set ℂ), x ≠ y → x ≠ z → y ≠ z →
         BlindSecond x y ≠ BlindSecond x z) :
       ∃ (p : OnePoint ℂ) (Y : Set (OnePoint ℂ)),
         IsGCircleS Y ∧ p ∈ Y ∧ True   -- with p the level-4 point of each 4-subset and all five in Y
   ```
   (`clifford_two_clean` itself needs `GenPos5`, hence all ten `GenTriple`s; it cannot be applied
   when any triple has collinear second points.)

3. **Transport / induction.** Either prove the frozen `PaperLBlind.blindOfChainS`
   (`scratch/BridgeBlind.lean:331`) for `BlindGenPos`, or supply an `E` and the three incidence
   hypotheses of `Clifford.cliffordChainS_all_of` (`Clifford/Mobius.lean:330`) with
   `GenPosN` weakened to `BlindGenPos`:

   ```lean
   lemma chainS_all_of_blind
       (E : (n : ℕ) → (Fin n → ℂ) → OnePoint ℂ)
       (h4 : ∀ c : Fin 4 → ℂ, BlindGenPos c → ChainS 4 c {E 4 c})
       (hodd : ∀ (k : ℕ) (d : Fin (2*k+5) → ℂ), BlindGenPos d →
         ∃ Y, IsGCircleS Y ∧ ∀ i : Fin (2*k+5), E (2*k+4) (d ∘ i.succAbove) ∈ Y)
       (heven : ∀ (k : ℕ) (c : Fin (2*k+6) → ℂ), BlindGenPos c → ∀ i : Fin (2*k+6),
         ∃ Y, IsGCircleS Y ∧ E (2*k+6) c ∈ Y ∧
           ∀ j : Fin (2*k+5), E (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y)
       (n : ℕ) (hn : 3 ≤ n) : CliffordChainS n
   ```

   plus a writer-side transport from `ChainS n c X` to `BlindCliffordP false n c X` under
   `BlindGenPos`. The transport's known obstruction is the radius-zero sphere branch of
   `Clifford.IsGCircleS` (a singleton cannot be a writer `BlindIsGCircle`); under
   `BlindGenPos` it should be excluded at odd levels ≥ 3 by finding two distinct finite child
   points in the circle, which requires the finite-point results at even levels that
   `MorleyKernel` currently proves only under `GenPosN`.
