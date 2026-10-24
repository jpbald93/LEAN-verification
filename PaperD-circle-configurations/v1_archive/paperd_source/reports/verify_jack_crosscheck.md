**Summary:** all three Clifford results and Sawayama–Thébault re-check cleanly on jack (x86-64 Linux, Lean v4.33.1, Mathlib pin `0df444a3…`): both builds pass, only the three standard axioms appear, every tamper case is rejected, and the numerics hold at 60 digits. The defects are about scope, not soundness: `clifford_two` alone is weakened, and the "chain" covers only n=4 and n=5.

**`clifford_j` n=4: VERIFIED**
- **Statement:** `clifford_one {a b c d : ℂ} (h : GenPos4 a b c d) : OnCircle3 (second a b) (second a c) (second b c) (miquel a b c d) ∧ …` for all four triples. `OnCircle3 z₁ z₂ z₃ z := Cospherical {z₁,z₂,z₃,z}`.
- **Setup:** `M = 0`, which loses nothing (translate). `miquel` is an explicit ratio of two determinants, and its denominator is proven nonzero (`mD_ne_zero`).
- **Hypotheses (`GenPos4`):**
  - Pairwise `Transversal`: `conj c·d ≠ c·conj d`, i.e. M and the two centres are not collinear. This excludes tangent circles and equal centres.
  - Each triple satisfies `triP ≠ 0` (centres not collinear) and `cycP ≠ 0`.
  - `cycP ≠ 0` means M is not on the circle through the three centres. By Simson's theorem that is the same as the three second intersection points not being collinear, so each circle Γ is unique.
  - These are standard genericity conditions. The only cases left out are those where some Γ degenerates into a line.
- **Numerics (mpmath, 60 digits, 1500 four-circle sets):**
  - Lean's `second` matches the geometric reflection of M to 1.7e-60.
  - Lean's `miquel` matches the geometric Γ∩Γ point to 2e-54.
  - The point lies on all four Γ to 2.4e-55.
  - Negative control (centroid of the six P points): violated 1500/1500.

**`clifford_j` n=5: VERIFIED as `clifford_two_clean`; `clifford_two` on its own is WEAKENED**
- `clifford_two (h : GenPos5 …) (hk : CliffordNondeg a b c d e) : Cospherical {five miquel points}`.
  - `hk` says `k3 ≠ 0`, a polynomial coefficient condition with no geometric meaning, and it removes real configurations.
  - My script found a `GenPos5` configuration where the five Miquel points are distinct (minimum spacing 0.042) and collinear to 5e-60. In that case "on a circle" is false and `hk` fails.
- `clifford_two_clean (h : GenPos5 a b c d e) : Cospherical S ∨ Collinear ℝ S` has no extra hypothesis. **This "circle or line" form is the honest one.**
  - The k1=0 branch reaches `Cospherical` with radius 0, because all five points coincide there. This is allowed, not a defect.
  - The `cleanand` tamper case confirms that changing ∨ to ∧ breaks the build.
- **Numerics (300 random configurations):** concyclic to a relative residual of 3.2e-55. Negative control (one point replaced by a P point): violated 300/300.

**`clifford_j` chain: VERIFIED for the base cases only (n=4, n=5)**
- `cliffordChain_four : CliffordChain 4` and `cliffordChain_five : CliffordChain 5`. `CliffordChain n := ∀ c, GenPosN c → ∃ X, Chain n c X`.
- The general `CliffordChain n` is defined but not proved.
- `Chain` is existential. In general position each level is unique, so this is faithful there.

**`thebault3_j`: VERIFIED**
- **Statement:** `sawayama_thebault (A B C D P Q : Pt) (h : AffineIndependent ℝ ![A,B,C]) (hD : Sbtw ℝ B D C) (hP : IsThebaultCircle A B C D B P h) (hQ : IsThebaultCircle A B C D C Q h) : Collinear ℝ {P, Q, (tri A B C h).incenter}`.
- **`IsThebaultCircle`** says there is an `r > 0` with:
  - `infDist P (line AD) = r` and `infDist P (line BC) = r`;
  - `dist P O = R − r` (internal tangency);
  - `SSameSide` of AD with X, and `SSameSide` of BC with A.
  - The two side conditions together are exactly the open angle ∠ADX, which is the "one on each side of AD" condition.
- **Fidelity:**
  - Triangle non-degenerate; D strictly inside segment BC. That is the classical setting.
  - The theorem assumes P and Q satisfy the condition rather than asserting they exist. That is harmless.
  - The conclusion uses Mathlib's `incenter`, and `tri_incenter_spec` proves it is equidistant from the three lines and on the inner side of each.
  - Nothing is added or dropped.
- **Numerics (500 random rotated triangles):**
  - I computed the circles independently by bisection along the angle bisector. The Lean hypotheses hold on them to 4e-60.
  - Collinearity holds to 3.7e-59.
  - Negative controls, each violated 500/500: centroid instead of incentre; an externally tangent circle; a circle in the opposite angle across BC.

**Harness and soundness (both repos)**
- `gate.sh`: Clifford PASS with 14 declarations, Thébault PASS with 12, each only `[propext, Classical.choice, Quot.sound]`.
- `tests/tamper.sh`: Clifford 7/7 rejected (sorry, ax2line, evalfake, macro, wrap, falsehyp, cleanand). Thébault 6/6 rejected (same minus cleanand).
- A grep of all source `.lean` files (`.lake` excluded) finds none of: `sorry`, `admit`, `axiom`, `native_decide`, `#eval`, `run_cmd`, `set_option`, `macro`, `elab`, `syntax`, `notation`, infix/prefix/postfix, `import Lean`, `initialize`, `unsafe`, `implemented_by`, `extern`.

**Prior art: none found for Clifford n≥4 or Sawayama–Thébault.** The only formal proofs I found are the known 3-circle Miquel base cases:
- AFP Miquel (complete, 3 circles only): https://www.isa-afp.org/entries/Miquel.html
- Rocq HighSchoolGeometry `applications_cocyclicite.v` (complete, 3 circles only): https://github.com/rocq-community/HighSchoolGeometry

These came up empty (repo greps or downloads, since web search was down): Mathlib master and its PRs/issues, the full AFP mirror, GeoCoq, HOL Light, HOL4, Metamath, ProofAtlas, and GitHub Lean/Coq code search. I did not check the pin `0df444a3` separately; master was clean.

Coverage gaps:
- Lean Zulip could not be searched (needs a login).
- Mizar was only partly covered (39 geometry articles).
- The GitHub Isabelle search for "Sawayama" hit a rate limit.

The only other machine proof I know of (Chou's Wu-method proof of Thébault III, 1988) is from memory and was not machine-checked by a proof assistant.

**DEFECTS:**
1. `clifford_two` needs `CliffordNondeg` (`k3 ≠ 0`), which excludes real general-position cases where the five points are collinear. Calling it "Clifford's second theorem" alone overstates it. Cite `clifford_two_clean` (circle ∨ line) as the n=5 result.
2. "Chain" means only the n=4 and n=5 base cases. The general `CliffordChain n` is not proved.
3. Minor: `GenPos4/5` exclude configurations where some Γ through three P points is a line (`cycP = 0`). This is standard genericity, but it is not the full inversive-plane statement.

My scripts are in `/tmp/vjack_num/` (`cliff.py`, `theb.py`) on this machine.
