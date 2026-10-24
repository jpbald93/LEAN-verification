# REPORT_EXT — Paper F extension, Task 2 (quadrangle_ext)

Repo: `john:~/lean/quadrangle_ext`, a copy of `~/lean/quadrangle`; the original is untouched.
* **New file:** `QuadMiquel/QuadrangleSym.lean` (123 lines).
* `QuadMiquel.lean`: one line appended, `import QuadMiquel.QuadrangleSym`.
* `gate.sh`: only line 15 (`REQUIRED=`) changed, checked by diffing.
* No existing `.lean` file was edited. `poncelet_on_pedal_c` is untouched. There is no sorry, admit, axiom, set_option, macro or notation.

## Result
* **Gate:** `PASS (106 declarations, standard axioms only)` (94 old + 12 new). Log: `scratch/ext_gate.log`.
* **Tamper:** `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, wrap, falsehyp). Log: `scratch/ext_tamper.log`.
* **Targets:** S1 and S2 are fully proved.

## Main theorems (`QuadMiquel/QuadrangleSym.lean`)
**S1**
* `:46` `ponDen_swap_cd (a b c d : ℂ) : ponDen a b d c = -ponDen a b c d`. Unconditional.
* `:50` `ponDen_cd_ne_iff (a b c d) : ponDen a b d c ≠ 0 ↔ ponDen a b c d ≠ 0`
* `:54` `QGen.swap_cd (h : QGen a b c d) : QGen a b d c`
* `:60` **`ortho_swap_iff (h : QGen a b c d) : d = ortho a b c ↔ c = ortho a b d`**. Orthocentricity is symmetric. The proof goes through `ponDen_eq_zero_iff` on both sides together with `ponDen_swap_cd`.
* `:64` `poncelet_swap_cd_of_ne (hD : ponDen a b c d ≠ 0) : poncelet a b d c = poncelet a b c d`
* `:75` **`poncelet_swap_cd (h : QGen a b c d) (ho : d ≠ ortho a b c) : poncelet a b d c = poncelet a b c d`**
* `:82` `poncelet_swap_cd_orthocentric : poncelet 0 4 (1+3/2·I) (1+2·I) ≠ poncelet 0 4 (1+2·I) (1+3/2·I)`. This is the finding below.
* Algebraic core, all closed by `ring` / `field_simp`:
  * `:19` `pD_cd : pD (x−z) (X−Z) (y−z) (Y−Z) (−z) (−Z) = −pD x X y Y z Z`
  * `:23` `pN_cd : pN (…) = 2·z·pD x X y Y z Z − pN x X y Y z Z`
  * `:27` `pP_cd`

**S2**
* `:96` **`poncelet_S4 (h : QGen a b c d) (ho : d ≠ ortho a b c)`**. It proves that `poncelet a b c d` equals each of:
  * `poncelet a c b d` — transposition (b c)
  * `poncelet b c a d` — 3-cycle (a b c)
  * `poncelet a b d c` — transposition (c d)
  * `poncelet d b c a` — transposition (a d)
  * `poncelet a d c b` — transposition (b d)
  * `poncelet b c d a` — 4-cycle

  (b c), (a b c) and (c d) generate S₄. The other three are derived inside the proof from the generators.
* `:115` **`poncelet_on_pedal_c' (h : QGen a b c d) (ho : d ≠ ortho a b c) (hc : ¬Cospherical {a,b,c,d}) : Cospherical {foot c (lineThrough a b), foot c (lineThrough b d), foot c (lineThrough d a), poncelet a b c d}`**
  * This is the same statement as `poncelet_on_pedal_c`. The proof is `rw [← poncelet_swap_cd h ho]; exact poncelet_on_pedal_d h.swap_cd (fun e => ho ((ortho_swap_iff h).2 e)) (by rwa [Set.pair_comm d c])`.
  * That is three short terms rather than literally one line: `poncelet_on_pedal_d`'s hypotheses have to be transported along c ↔ d (`QGen.swap_cd`, `ortho_swap_iff`, and a set reorder).

## Hypotheses and findings
1. **Finding: the non-orthocentric hypothesis is needed.** `poncelet a b d c = poncelet a b c d` is **false** without `d ≠ ortho a b c`.
   * Counterexample: a = 0, b = 4, c = 1+2i, d = 1+3i/2 = H(a,b,c).
   * Both denominators are 0. Lean's `x/0 = 0` makes the left side c and the right side d, so the two sides are 1+2i and 1+3i/2.
   * This is proved as `poncelet_swap_cd_orthocentric`.
   * Corrected hypothesis: `QGen a b c d ∧ d ≠ ortho a b c`. By `ortho_swap_iff`, this is the same as the non-orthocentric hypothesis of the swapped quadrangle, so a single hypothesis covers both sides.
2. **The denominator condition is symmetric.** `ponDen a b d c = −ponDen a b c d` holds as an exact identity, with no hypotheses. So the two denominators are nonzero together (`ponDen_cd_ne_iff`).
3. **The c ↔ d identity holds under ponDen ≠ 0 alone.** `poncelet_swap_cd_of_ne` needs nothing more; `QGen` is used only to translate the condition into `d ≠ ortho a b c`.

## Numerics / symbolic checks (`scratch/s1.py`, `scratch/num.py`)
* SymPy, exact over ℚ with the conjugates as independent atoms:
  * `pD_cd + pD = 0`
  * `pN_cd − (2z·pD − pN) = 0`
  * the cross-multiplied c ↔ d identity is 0
  * the a ↔ d analogue is also exactly 0
* mpmath at 50 digits, 300 random quadrangles × all 24 permutations:
  * max |P(σ) − P| = 1.3e-48
  * relative change of |ponDen| = 2.3e-49
  * |ponDen(abdc) + ponDen(abcd)| = 2.8e-48
* 100 random triangles: d = H(abc) ⇒ |c − H(abd)| ≤ 2.5e-48.
* Orthocentric example: both |ponDen| are about 5e-50, i.e. 0 in exact arithmetic. With Lean's x/0 = 0 semantics the two sides differ, as the finding above says.
* Near-orthocentric, d = H + ε(1+i):
  * ε = 1e-10: the swap discrepancy is 6e-42.
  * ε = 1e-20: the swap discrepancy is 3e-32.
  * The identity keeps holding as the denominators shrink; the loss of accuracy is only floating-point cancellation.

## REQUIRED names added (12, all `QuadMiquel.`-qualified)
pD_cd pN_cd pP_cd ponDen_swap_cd ponDen_cd_ne_iff QGen.swap_cd ortho_swap_iff poncelet_swap_cd_of_ne poncelet_swap_cd poncelet_swap_cd_orthocentric poncelet_S4 poncelet_on_pedal_c'

## Hashes (sha256). Pre-existing library files: identical before and after
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  QuadMiquel/Algebra.lean
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  QuadMiquel/Basic.lean
fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa  QuadMiquel/Bridge.lean
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  QuadMiquel/Frame.lean
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  QuadMiquel/Miquel.lean
ea33070625a616859d0ac8e145c1fe6224af0f2c9bbc28a84f1e4505f9d49e5f  QuadMiquel/Parallel.lean
4116bc5913cb0e4daede8a6d18d079344619a6e2e4d88d53c403bc5991d0d639  QuadMiquel/Quadrangle.lean
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  QuadMiquel/Simson.lean
5da507d51bdc4b18c7f4e11a3d25fd967b0fcb57bd972f9fcd3ca481bef32751  tests/tamper.sh
7241a353c784648d4845a08f094acb5899de8f9d92d8a53652db83ba4bcc1903  lakefile.toml
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
01cd99b1415c15f68b71234930a2ef89077b1a45f44f1c171b6347316fe291d2  lake-manifest.json
```
Changed, as permitted:
* QuadMiquel.lean `d65fd8aa…` → `e7e20c5ea5d30b00994157194e966fa021b88c2419fdb8c13f82910d23f2ceaf`
* gate.sh `dc269b44…` → `ff54d84da2958597b897d92345641c9aad55b9217309cd494b06eb2a1d6d91ae`

New file:
* QuadrangleSym.lean `471cf9b35bf444ef94004a254bbdb7f9a17811337785af4251b8d35428d4a171`

Original `~/lean/quadrangle`: rehashed after the work and identical to before.
