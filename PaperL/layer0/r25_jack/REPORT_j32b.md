# J32 — `EvenCorner`: status report

## Outcome
`EvenCorner_proof` is **not** closed within the 30-min box. What *is* done and compiles
(`lake env lean scratch/ChainEvenCorner.lean` → rc = 0, ~57 s, prefix lines 1–5288 untouched,
axioms `[propext, Classical.choice, Quot.sound]`):

* `evenCorner_of_QL` — if the subfamily cross vector `w := crossVec (KP (2k+5) d d̄)` (`d = c ∘ i.succAbove`)
  has `w (Fin.last _) = 0` and `w 0 ≠ 0`, then `w ∘ castSucc` is a common nonzero kernel vector of every
  grandchild `KP (2k+4)` (via `child_mulVec_of_parentN`), so **all** grandchild level points equal
  `-w_{2k+4}/w_{k+2}` (`levelPointN_of_ker`) ⇒ conclusion with `u = 1, t = 0`.
* `EvenCornerQL` (named Prop) and `evenCorner_of_cornerQL : EvenCornerQL → EvenCorner`.

So the whole corner reduces to **one scalar identity**:

```
residual goal (after intro k c h i hV hP0 hall):
  crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) (Fin.last _) = 0
```
i.e. in the corner the subfamily kernel circle has radius `|w_last / w_0| = 0`. (This is consistent
with fact 2: the grandchildren lie on the subfamily circle, by `stepOdd_gen`, *and* on a line; a
real circle meets a line in ≤ 2 points, so the circle must degenerate.)

## Proof of the residual (paper level, complete; not yet formalised)
Notation `m = k+2`, parent columns `P_0..P_{m+1}` (cols `0..k+3`), `Q_0..Q_m` (cols `k+4..2k+6`);
a vector is in `ker KP(2k+6)` iff at every point `(x,y)=(c_r, c̄_r)`:
`Pʰ(x,y) := Σ P_j (-x)^j y^{m+1-j} = Qʰ(x,y) := Σ Q_j (-x)^j y^{m-j}`.
`KP(2k+5)` = `KP(2k+6)` with column `k+3` deleted (entrywise, `kpe5_lo/hi` vs `kpe6_lo/hi`).

1. **`w' := w` with `0` inserted at column `k+3` lies in `ker KP(2k+6)`.** Rows `≠ i`: `mulVec_crossVec`.
   Row `i`: `row_i · w'` is the Laplace expansion (`det_border`, l. 727) of the `(2k+6)`-square matrix
   `KP(2k+6)` minus column `k+3`, rows permuted, `= ± V_{k+3} = 0` (only `hmid` is needed; sign irrelevant).
2. **`s := σ(w') ∈ ker KP(2k+6)`**, `σ(v): P'_j = conj P_{m+1-j}, Q'_j = -conj Q_{m-j}` (conjugate the row
   equation, `y = x̄`; this is the symmetry behind `conj_crossVec_even`). `s_{k+3} = conj w_0 ≠ 0`.
3. **Resultant.** `R(x,y) := Pʰ_{w'} Qʰ_s − Pʰ_s Qʰ_{w'}` is a binary form of degree `2m+1` vanishing at the
   `2m+2` points `(c_r : c̄_r)`, pairwise non-proportional (`Transversal` from `GenPosN`), `c̄_r ≠ 0`
   ⇒ `R ≡ 0`. Its `(-x)^{2m+1}` coefficient is `P_{m+1}(w') Q_m(s) − P_{m+1}(s) Q_m(w') = 0 − conj w_0 · w_last`.
   Hence `w_last = 0`. (`hall` is not even needed.)

## Lemmas wanted and not available in the prefix
* (step 1) `row_i · w' = ± crossVec (KP (2k+6) c c̄) ⟨k+3⟩` — a Laplace/border identity for `KP(2k+6)` with
  column `k+3` removed and row `i` moved to the top (`det_border` + `det_permute`).
* (step 2) an explicit kernel involution lemma: `KP n c c̄ *ᵥ v = 0 → KP n c c̄ *ᵥ σ v = 0` (only the
  crossVec-level statement `conj_crossVec_even` exists).
* (step 3) "binary form of degree `2m+1` with `2m+2` non-proportional zeros is `0`" in coordinates
  (dehomogenise `t = -c/c̄`, then `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`), plus the
  top-coefficient extraction of the convolution `R`.

Resisting sub-case: none mathematically — the only open branch is `EvenCornerQL` itself; steps 1–3 are
pure bookkeeping, estimated 250–400 lines, larger than the time box.
