# REPORT — Paper F part 2: the complete quadrangle and the Poncelet point

Repo: `john:~/lean/quadrangle`. New file: `QuadMiquel/Quadrangle.lean` (about 1130 lines). The root file `QuadMiquel.lean` got one line appended, `import QuadMiquel.Quadrangle`. In `gate.sh` only the `REQUIRED=` line changed. No existing `.lean` file was edited.

## Result
* **Gate:** `PASS (94 declarations, standard axioms only)` (62 old + 32 new REQUIRED names)
* **Tamper:** `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, wrap, falsehyp)
* **Targets:** D1, D2 (concurrence and uniqueness), D3, D4 (all four vertices) and D5 (stretch) are all proved, with no sorry. D6 was skipped as permitted.

## Definitions (QuadMiquel/Quadrangle.lean)
* `:18` `structure QGen (a b c d : ℂ) : Prop` has four fields: `abc : cr (b-a) (c-a) ≠ 0`, `abd`, `acd`, `bcd` (no three of the points collinear). No other condition was added to `QGen`; each extra hypothesis is stated on the theorem that needs it (see Findings).
* `:27/:31` `pD`, `pN` are polynomials in x, X, y, Y, z, Z (the conjugates are separate atoms):
  `pD = X²Yz − X²Zy − XY²z + XZ²y + Y²Zx − YZ²x`,
  `pN = X²Yz² − X²Zy² − XY²z² + XZ²y² + Y²Zx² − YZ²x²`.
* `:36` `ponDen a b c d = pD (a−d) (conj(a−d)) (b−d) … (c−d) …`
* `:40` **`poncelet a b c d = d + pN(…)/(2·ponDen a b c d)`**. Derived in SymPy from the rectangular hyperbola Re(αz² + βz) + γ = 0 through the four points, P = −β/(2α), then translated so that d is the origin.
* `:44` `npc x y z = (x+y+z − circ x y z)/2`, the nine-point centre (midpoint of O and H).
* `:897` `lineThrough p q : Line := ⟨p, q−p⟩`; `:958` `diagPt p q r s = meet (lineThrough p q) (lineThrough r s)`; `:670` `tri h : Affine.Triangle ℝ ℂ` builds Mathlib's triangle on three non-collinear points.

## Bridges to Mathlib
* `:55` `npc_eq_ninePointCircle_center (h : ¬Collinear ℝ {a,b,c}) : npc a b c = (⟨![a,b,c],_⟩ : Affine.Triangle ℝ ℂ).ninePointCircle.center`. Mathlib does have `Affine.Simplex.ninePointCircle`, so this bridges to it directly.
* `:64` `ninePointCircle_radius_eq : (…).ninePointCircle.radius = dist ((a+b)/2) (npc a b c)`
* `:673` `mem_ninePointCircle_iff : w ∈ (tri h).ninePointCircle ↔ dist w (npc a b c) = dist ((a+b)/2) (npc a b c)`
* `:642` `npc_mid`: the other two side midpoints are at the same distance from `npc`.
* `:756` `cospherical_of_crossC`: if p, q, r are not collinear and the cross-ratio polynomial vanishes, then `EuclideanGeometry.Cospherical {p,q,r,w}`.

## Main theorems
* **D1** `:626` `poncelet_on_ninepoint (h : QGen a b c d) (ho : d ≠ ortho a b c)`: a conjunction of four statements `dist P (npc Δ) = dist (midpoint of a side of Δ) (npc Δ)`, for Δ = abc, abd, acd, bcd.
* **D2** `:679` `ninepoint_concur (h) (ho)`: `poncelet a b c d ∈ (tri h.ncol_abc).ninePointCircle ∧ … abd ∧ … acd ∧ … bcd` (Mathlib spheres).
  `:692` `ninepoint_unique (h) (ho) (h1 : w ∈ …abc…) (h2 : w ∈ …abd…) (h3 : w ∈ …acd…) : w = poncelet a b c d`. This is stronger than asked: three of the four circles already have P as their only common point.
* **D3** `:571` `ponDen_eq_zero_iff (h : QGen a b c d) : ponDen a b c d = 0 ↔ d = ortho a b c`.
  `:718` `orthocentric_npc_eq (h) (ho : d = ortho a b c)`: all four nine-point centres are equal.
  `:1114` `orthocentric_ninePointCircle_eq`: all four Mathlib `ninePointCircle`s are equal, centres and radii.
  `:598` `orthocentric_example`: `QGen 0 4 (1+2i) (1+3i/2)`, `1+3i/2 = ortho 0 4 (1+2i)`, and `ponDen … = 0`.
* **D4** `:906/:917/:928/:942` `poncelet_on_pedal_d / _c / _b / _a (h) (ho) (hc : ¬Cospherical {a,b,c,d})`. Each gives `Cospherical {foot v (lineThrough ..), foot v (..), foot v (..), poncelet a b c d}` for the pedal triangle of v with respect to the other three points. For d it is proved in the frame centred at d; for c it uses a separate frame lemma (`pedal_frame_z`); for b and a it relabels using the proved symmetries `poncelet_swap` and `poncelet_cyc` (permutations of a, b, c, `:≈880`).
* **D5** `:1041` `poncelet_on_diagonal_circle (h) (ho) (p1 : ¬ line[ℝ,a,b] ∥ line[ℝ,c,d]) (p2 : ¬ ac ∥ bd) (p3 : ¬ ad ∥ bc)`: `Cospherical {diagPt a b c d, diagPt a c b d, diagPt a d b c, poncelet a b c d}`. The parallelism hypotheses use `AffineSubspace.Parallel`.

## Findings
1. **Where the formula breaks down (proved, D3).** Under `QGen`, `ponDen = 0` holds exactly when the quadrangle is orthocentric (d = H(a,b,c), equivalently each point is the orthocentre of the other three). Algebraic certificate: `pD = Y(Z−X)·g₁ + X(Z−Y)·g₂`, where g₁, g₂ are the altitude conditions. In the other direction, `(Xy−xY)(Xz−xZ)(Yz−yZ) = xy·pD − XY·conj(pD) + (Xy+Yx)·det`. Explicit example: a = 0, b = 4, c = 1+2i, d = 1+3i/2. There the four nine-point circles coincide (proved), so every point of that circle is common to all four, and uniqueness genuinely needs `d ≠ ortho a b c`.
2. **Which theorem needs which hypothesis.**
   * D1, D2 and D3: `QGen` + `d ≠ ortho a b c`.
   * D4: also needs `¬Cospherical {a,b,c,d}`. If the four points are concyclic, the three feet are collinear (the Simson line), so the "pedal circle" is degenerate and Cospherical is false or meaningless. Numerically, in that case P lies on the Simson line (sin of the angle ≤ 3e-39 over 50 cases). In the frame the collinearity determinant of the feet is `K²·cross(a,b,c,d)/(4·…)`.
   * D5: needs the three pairs of opposite sides non-parallel (the diagonal points must exist), plus `QGen` and `d ≠ ortho`. The non-degeneracy of the diagonal triangle follows from `QGen` and is proved (`diagK`); the denominator check (`KDiag`) shows the diagonal triangle is never degenerate under `QGen`.
3. **Concyclic quadrangles are fine for P.** Over 200 concyclic quadrangles × 300 points each, the normalised |pD| had a minimum of 1.0 (`concyc2.py`). P stays well defined there; only the pedal statement degenerates.
4. **The sign trap I hit.** My first transcription of the third diagonal point D₃ = ad ∩ bc had the wrong sign, and the identity was false. The symbolic check caught it before any Lean was written; the corrected formula is in `diagC`/`diagK`.

## Numeric and symbolic checks (repo `scratch/`)
* `derive.py`: SymPy derivation of P from the 5×5 conic determinant (rectangular hyperbola).
* `num.py`: mpmath at 50 digits, 300 random quadrangles. Max residuals: nine-point circles ≤ 5.5e-48, pedal circles ≤ 1.9e-48, diagonal circle ≤ 7.7e-47. Symmetry of the formula under all permutations of a, b, c, d ≤ 1.7e-48; translation covariance 5e-51; the Mathlib nine-point centre formula agrees exactly. Orthocentric: |den| ≤ 1e-44 and the nine-point centres' spread is ≤ 5e-48.
* `size2.py`, `alg.py`, `ped.py`, `diag.py`, `dsz.py`, `gen*.py`, `targets.py`, `certs2.py`, `conv.py`, `lift.py`: exact polynomial identities over ℚ with the conjugates as independent variables. All of these are zero: the four nine-point identities, the four pedal identities, the diagonal identity, the radical-axis determinant (= −pD·conj pD/(4·…)), the differences of nine-point centres, and the orthocentric ideal certificates.
* `denzero.py`: root search on the zero set of pD with a, b fixed. The only roots besides the degenerate z ∈ {0, a, b} were z = the orthocentre.
* `concyc2.py`, `simson.py`: the concyclic-case findings above.

## Proof method
Every theorem translates so that d is the origin (`shift_ex`, `frame_of_QGen` → `Frame x y z`). The algebraic cores (`nineC`, `nine0`, `midC`, `midC2`, `pedC`, `pedC'`, `diagC`, `radC`, `ndiffC`, `pedK`, `pedK'`, `diagK`, `pD_zero_iff`) are identities in independent atoms x, X, y, Y, z, Z. They are closed by `field_simp; ring`. Where `field_simp` blew up, the denominators were abstracted with `set`, or a generic fraction lemma (`crossC_div`, `kfrac`, `lin_frac`) reduced the goal to one polynomial `ring`. Conjugation is then reattached with the `conj_pD`/`conj_pN`/`conj_pP`/`conj_npcC` lemmas.

## Not reached / caveats
* D6 was skipped.
* Full symmetry of `poncelet` under moving d (for example `poncelet a b c d = poncelet d b c a`) is not proved in Lean; it was only checked numerically. Only permutations of a, b, c are proved. D4 for vertex c therefore has its own frame proof, and D4 for b and a is obtained by relabelling a, b, c only.
* D1 is stated with one side midpoint per triangle; `npc_mid` supplies the other two. D2 uniqueness is stated for the circles of abc, abd and acd (which implies uniqueness for all four).

## REQUIRED names added (32)
poncelet_on_ninepoint ninepoint_concur ninepoint_unique ponDen_eq_zero_iff orthocentric_example orthocentric_npc_eq orthocentric_ninePointCircle_eq poncelet_on_pedal_d poncelet_on_pedal_c poncelet_on_pedal_b poncelet_on_pedal_a poncelet_on_diagonal_circle npc_eq_ninePointCircle_center ninePointCircle_radius_eq mem_ninePointCircle_iff npc_mid cospherical_of_crossC frame_of_QGen pD_zero_iff nineC nine0 pedC pedC' diagC radC ndiffC pedK pedK' diagK poncelet_swap poncelet_cyc ponDen_ne (all `QuadMiquel.`-qualified)

## Hashes (sha256)
The seven pre-existing library files are **identical before and after**:
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  Algebra.lean
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  Basic.lean
fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa  Bridge.lean
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  Frame.lean
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  Miquel.lean
ea33070625a616859d0ac8e145c1fe6224af0f2c9bbc28a84f1e4505f9d49e5f  Parallel.lean
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  Simson.lean
```
Also unchanged: tests/tamper.sh `5da507d5…`, lakefile.toml `7241a353…`, lake-manifest.json `01cd99b1…`, lean-toolchain `3aac669c…`.

Changed, as permitted:
* QuadMiquel.lean `40e264fd…` → `d65fd8aa7230fd531ac5bd48c048595d10492e811447a67c301e16bad57cd39b` (one import line)
* gate.sh `321aa825…` → `dc269b4499a5e6300acf234068b51439f8a470d55e56e81b0f3eb813d123b714` (REQUIRED line only; verified against the original copy)

New: QuadMiquel/Quadrangle.lean `4116bc5913cb0e4daede8a6d18d079344619a6e2e4d88d53c403bc5991d0d639`.
Full lists: `scratch/hashes_before.txt` and `scratch/hashes_after.txt`.
