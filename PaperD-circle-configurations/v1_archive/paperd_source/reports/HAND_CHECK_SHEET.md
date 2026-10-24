# Paper D — hand check sheet (for Josh)

**What to do:** for each row, read the paper's theorem (left) and the Lean statement (right). Tick ✅ if the Lean says the same thing as the paper — same objects, every hypothesis in the paper appears in the Lean and vice versa, same conclusion. Write a note if anything looks different, even slightly. You do not need to read any proofs.

Each Lean statement links to the exact line on GitHub at the published commit.

Tips: `¬ Collinear ℝ {a,b,c}` = "a, b, c are not on one line". `Cospherical S` = "the points of S lie on one circle". `secondInter c₁ c₂` = P₁₂, the second intersection point. `≠` = "is not equal to". `∃ p, …` = "there is a point p such that …".

---

## CLIFF4 — paper says

Let four circles pass through a common point $M$, with centres $c_1,\dots,c_4$. Suppose every
second intersection point $P_{ij}$ ($i<j$) differs from $M$, and for each triple $\{i,j,k\}$ the
three points $P_{ij},P_{ik},P_{jk}$ are not collinear. Then the four circles
$\Gamma_{123},\Gamma_{124},\Gamma_{134},\Gamma_{234}$ have a common point.

### Lean: `clifford_one` — [Clifford/Basic.lean:381](https://github.com/jpbald93/clifford/blob/209abaa5e638f37aee8ec374e29b74341297cc46/Clifford/Basic.lean#L381)

```lean
theorem clifford_one (c₁ c₂ c₃ c₄ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ)) :
    ∃ P : ℂ, P ∈ gam c₁ c₂ c₃ ∧ P ∈ gam c₁ c₂ c₄ ∧ P ∈ gam c₁ c₃ c₄ ∧ P ∈ gam c₂ c₃ c₄ := …
```

- [ ] matches the paper      Note: ________________________

---

## CLIFF5 — paper says

Let five circles pass through $M$, with every $P_{ij}\neq M$ and no triple $P_{ij},P_{ik},P_{jk}$
collinear. For each $k$, let $P_k=\mathrm{cp}$ of the four circles other than circle $k$. Then each
$P_k$ lies on the four circles $\Gamma$ of those four, and the five points $P_1,\dots,P_5$ lie on one
circle or on one line.

### Lean: `clifford_two` — [Clifford/Third.lean:543](https://github.com/jpbald93/clifford/blob/209abaa5e638f37aee8ec374e29b74341297cc46/Clifford/Third.lean#L543)

```lean
theorem clifford_two (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)) :
    ∃ P₁ P₂ P₃ P₄ P₅ : ℂ,
      (P₁ ∈ gam c₂ c₃ c₄ ∧ P₁ ∈ gam c₂ c₃ c₅ ∧ P₁ ∈ gam c₂ c₄ c₅ ∧ P₁ ∈ gam c₃ c₄ c₅) ∧
      (P₂ ∈ gam c₁ c₃ c₄ ∧ P₂ ∈ gam c₁ c₃ c₅ ∧ P₂ ∈ gam c₁ c₄ c₅ ∧ P₂ ∈ gam c₃ c₄ c₅) ∧
      (P₃ ∈ gam c₁ c₂ c₄ ∧ P₃ ∈ gam c₁ c₂ c₅ ∧ P₃ ∈ gam c₁ c₄ c₅ ∧ P₃ ∈ gam c₂ c₄ c₅) ∧
      (P₄ ∈ gam c₁ c₂ c₃ ∧ P₄ ∈ gam c₁ c₂ c₅ ∧ P₄ ∈ gam c₁ c₃ c₅ ∧ P₄ ∈ gam c₂ c₃ c₅) ∧
      (P₅ ∈ gam c₁ c₂ c₃ ∧ P₅ ∈ gam c₁ c₂ c₄ ∧ P₅ ∈ gam c₁ c₃ c₄ ∧ P₅ ∈ gam c₂ c₃ c₄) ∧
      (Cospherical ({P₁, P₂, P₃, P₄, P₅} : Set ℂ) ∨ Collinear ℝ ({P₁, P₂, P₃, P₄, P₅} : Set ℂ)) := …
```

- [ ] matches the paper      Note: ________________________

### Lean: `clifford_two_explicit` — [Clifford/Third.lean:457](https://github.com/jpbald93/clifford/blob/209abaa5e638f37aee8ec374e29b74341297cc46/Clifford/Third.lean#L457)

```lean
theorem clifford_two_explicit (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)) :
    Cospherical ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄} : Set ℂ) ∨
      Collinear ℝ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄} : Set ℂ) := …
```

- [ ] matches the paper      Note: ________________________

---

## CLIFF6 — paper says

Let six circles pass through $M$, with every $P_{ij}\neq M$ and no triple $P_{ij},P_{ik},P_{jk}$
collinear. For each five-element subset $S$ of the six, let $P^S_T=\mathrm{cp}(c_T)$ for the five
four-element subsets $T\subset S$, and let $C_S$ be the circle through three designated ones of them
(for $S=\{1,\dots,5\}$: those of $\{1,2,3,4\}$, $\{1,2,3,5\}$, $\{1,2,4,5\}$; the six choices are listed
in the Lean statement). Suppose those three points are not collinear, for each $S$. Then all five
points $P^S_T$ lie on $C_S$, for each $S$, and the six circles $C_S$ have a common point.

### Lean: `clifford_three` — [Clifford/Third.lean:780](https://github.com/jpbald93/clifford/blob/209abaa5e638f37aee8ec374e29b74341297cc46/Clifford/Third.lean#L780)

```lean
theorem clifford_three (c₁ c₂ c₃ c₄ c₅ c₆ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h16 : secondInter c₁ c₆ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0)
    (h24 : secondInter c₂ c₄ ≠ 0) (h25 : secondInter c₂ c₅ ≠ 0) (h26 : secondInter c₂ c₆ ≠ 0)
    (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0) (h36 : secondInter c₃ c₆ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0) (h46 : secondInter c₄ c₆ ≠ 0) (h56 : secondInter c₅ c₆ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n126 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₆, secondInter c₂ c₆} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n136 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₆, secondInter c₃ c₆} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n146 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₆, secondInter c₄ c₆} : Set ℂ))
    (n156 : ¬ Collinear ℝ ({secondInter c₁ c₅, secondInter c₁ c₆, secondInter c₅ c₆} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n236 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₆, secondInter c₃ c₆} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n246 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₆, secondInter c₄ c₆} : Set ℂ))
    (n256 : ¬ Collinear ℝ ({secondInter c₂ c₅, secondInter c₂ c₆, secondInter c₅ c₆} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))
    (n346 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₆, secondInter c₄ c₆} : Set ℂ))
    (n356 : ¬ Collinear ℝ ({secondInter c₃ c₅, secondInter c₃ c₆, secondInter c₅ c₆} : Set ℂ))
    (n456 : ¬ Collinear ℝ ({secondInter c₄ c₅, secondInter c₄ c₆, secondInter c₅ c₆} : Set ℂ))
    (m6 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ))
    (m5 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₄ c₆} : Set ℂ))
    (m4 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₅ c₆} : Set ℂ))
    (m3 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₆, cliffordPoint c₁ c₂ c₅ c₆} : Set ℂ))
    (m2 : ¬ Collinear ℝ ({cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₆, cliffordPoint c₁ c₃ c₅ c₆} : Set ℂ))
    (m1 : ¬ Collinear ℝ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₆, cliffordPoint c₂ c₃ c₅ c₆} : Set ℂ)) :
    ∃ Q : ℂ,
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₅} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₄ c₆, cliffordPoint c₁ c₃ c₄ c₆, cliffordPoint c₂ c₃ c₄ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₄ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₄ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₅ c₆, cliffordPoint c₁ c₃ c₅ c₆, cliffordPoint c₂ c₃ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₆, cliffordPoint c₁ c₂ c₅ c₆, cliffordPoint c₁ c₄ c₅ c₆, cliffordPoint c₂ c₄ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₄ c₅) (cliffordPoint c₁ c₂ c₄ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₄ c₅) (cliffordPoint c₁ c₂ c₄ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₆, cliffordPoint c₁ c₃ c₅ c₆, cliffordPoint c₁ c₄ c₅ c₆, cliffordPoint c₃ c₄ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₃ c₄ c₅) (cliffordPoint c₁ c₃ c₄ c₆) (cliffordPoint c₁ c₃ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₃ c₄ c₅) (cliffordPoint c₁ c₃ c₄ c₆) (cliffordPoint c₁ c₃ c₅ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₆, cliffordPoint c₂ c₃ c₅ c₆, cliffordPoint c₂ c₄ c₅ c₆, cliffordPoint c₃ c₄ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₂ c₃ c₄ c₅) (cliffordPoint c₂ c₃ c₄ c₆) (cliffordPoint c₂ c₃ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₂ c₃ c₄ c₅) (cliffordPoint c₂ c₃ c₄ c₆) (cliffordPoint c₂ c₃ c₅ c₆)) := …
```

- [ ] matches the paper      Note: ________________________

---

## CHAIN — paper says

$\mathrm{CliffordChain}(4)$ and $\mathrm{CliffordChain}(5)$ hold.

### Lean: `cliffordChain_four` — [Clifford/Clean.lean:226](https://github.com/jpbald93/cliffordchain/blob/df7d65c85915a1da9ffd1ab8fa362f42609af8c1/Clifford/Clean.lean#L226)

```lean
theorem cliffordChain_four : CliffordChain 4 := …
```

- [ ] matches the paper      Note: ________________________

### Lean: `cliffordChain_five` — [Clifford/Clean.lean:245](https://github.com/jpbald93/cliffordchain/blob/df7d65c85915a1da9ffd1ab8fa362f42609af8c1/Clifford/Clean.lean#L245)

```lean
theorem cliffordChain_five : CliffordChain 5 := …
```

- [ ] matches the paper      Note: ________________________

---

## CHAINFAIL — paper says

For the six centres
\[
 c=(3-6i,\;6-3i,\;1+2i,\;-2-i,\;-4i,\;4)
\]
the circles through $M=0$ are in general position in the sense of $\mathrm{CliffordChain}$, but no
level-$6$ object exists. Consequently $\mathrm{CliffordChain}(n)$ fails for every $n\ge6$, and
$\mathrm{CliffordChain}(n)$ holds if and only if $n\le5$.

### Lean: `not_cliffordChain_six` — [Clifford/Counter6.lean:227](https://github.com/jpbald93/cliffordchain/blob/df7d65c85915a1da9ffd1ab8fa362f42609af8c1/Clifford/Counter6.lean#L227)

```lean
theorem not_cliffordChain_six : ¬ CliffordChain 6 := …
```

- [ ] matches the paper      Note: ________________________

### Lean: `cliffordChain_iff` — [Clifford/Classify.lean:227](https://github.com/jpbald93/cliffordchain/blob/df7d65c85915a1da9ffd1ab8fa362f42609af8c1/Clifford/Classify.lean#L227)

```lean
theorem cliffordChain_iff (n : ℕ) : CliffordChain n ↔ n ≤ 5 := …
```

- [ ] matches the paper      Note: ________________________

---

## FIVE — paper says

Let $A,T,M:\{0,\dots,4\}\toℂ$ be injective, with no point of one family equal to a point of
another (so the fifteen labelled points are pairwise distinct). Suppose that for each $i$ (indices mod 5) the points $A_{i-1},A_i,T_{i+1},T_{i-1}$ are
collinear and the points $A_{i-1},A_i,T_i,M_{i-1},M_i$ are concyclic. Then $M_0,\dots,M_4$ lie on one
circle or on one line.

### Lean: `fivecircles` — [Fivecircles/Basic.lean:383](https://github.com/jpbald93/fivecircles/blob/f1fd9b7b2bd9f6b1e881425019f86fc49adba927/Fivecircles/Basic.lean#L383)

```lean
theorem fivecircles (A T M : Fin 5 → ℂ) (hA : Function.Injective A) (hT : Function.Injective T)
    (hM : Function.Injective M) (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j)
    (hTM : ∀ i j, T i ≠ M j)
    (hL : ∀ i, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hC : ∀ i, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)) :
    Concyclic (Set.range M) ∨ Collinear ℝ (Set.range M) := …
```

- [ ] matches the paper      Note: ________________________

---

## LESTER — paper says

Let $ABC$ be a scalene triangle in the plane. Let $F_1$ be its first Fermat point, the common point of
the three lines joining each vertex to the apex of the equilateral triangle erected outwards on the
opposite side, and $F_2$ its second Fermat point (the same with the equilateral triangles erected
inwards). Then the circumcentre, the nine-point centre, $F_1$ and $F_2$ are concyclic.

### Lean: `lester` — [Lester/Basic.lean:56](https://github.com/jpbald93/lester/blob/9f94754987cbb9ddb8bf14bef295f2bfedb077df/Lester/Basic.lean#L56)

```lean
theorem lester (t : Affine.Triangle ℝ ℂ)
    (h01 : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2))
    (h12 : dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0))
    (h20 : dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (F₁ F₂ : ℂ)
    (h₁ : IsFermatOuter (t.points 0) (t.points 1) (t.points 2) F₁)
    (h₂ : IsFermatInner (t.points 0) (t.points 1) (t.points 2) F₂) :
    Concyclic ({ninePointCenter t, t.circumcenter, F₁, F₂} : Set ℂ) := …
```

- [ ] matches the paper      Note: ________________________

---

## THEBAULT — paper says

Let $ABC$ be a triangle and $D$ a point strictly between $B$ and $C$. Let $P$ be the centre of a
circle tangent to the lines $AD$ and $BC$, internally tangent to the circumcircle of $ABC$, and lying in
the angle $\angle ADB$; let $Q$ be the centre of such a circle lying in the angle $\angle ADC$. Then
$P$, $Q$ and the incentre of $ABC$ are collinear.

### Lean: `sawayama_thebault` — [Thebault3/Basic.lean:514](https://github.com/jpbald93/thebault/blob/c37f92e53c9ed790a2c90afdef95a7a35e6a7842/Thebault3/Basic.lean#L514)

```lean
theorem sawayama_thebault (A B C D P Q : Pt) (h : AffineIndependent ℝ ![A, B, C])
    (hD : Sbtw ℝ B D C) (hP : IsThebaultCircle A B C D B P h)
    (hQ : IsThebaultCircle A B C D C Q h) :
    Collinear ℝ {P, Q, (tri A B C h).incenter} := …
```

- [ ] matches the paper      Note: ________________________

---

## KOSNITA — paper says

Let $ABC$ be a triangle with circumcentre $O$, and let $O_a,O_b,O_c$ be the circumcentres of the
triangles $OBC$, $OCA$, $OAB$. Suppose that no two of $A,B,C$ are diametrically opposite (so that
$OBC$, $OCA$, $OAB$ are triangles) and that $AB^2+BC^2+CA^2\neq 5R^2$, where $R$ is the circumradius.
Then the lines $AO_a$, $BO_b$, $CO_c$ are concurrent.

### Lean: `kosnita` — [Kosnita/Basic.lean:180](https://github.com/jpbald93/kosnita/blob/702f0263a70136830aee7a9fd38ec7f4fc7d304d/Kosnita/Basic.lean#L180)

```lean
theorem kosnita (A B C O Oa Ob Oc : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hOA : dist O A = dist O B) (hOC : dist O A = dist O C)
    (hOBC : ¬ Collinear ℝ ({O, B, C} : Set Plane))
    (hOCA : ¬ Collinear ℝ ({O, C, A} : Set Plane))
    (hOAB : ¬ Collinear ℝ ({O, A, B} : Set Plane))
    (hOa1 : dist Oa O = dist Oa B) (hOa2 : dist Oa O = dist Oa C)
    (hOb1 : dist Ob O = dist Ob C) (hOb2 : dist Ob O = dist Ob A)
    (hOc1 : dist Oc O = dist Oc A) (hOc2 : dist Oc O = dist Oc B)
    (hS : dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2 ≠ 5 * dist O A ^ 2) :
    ∃ P : Plane, Collinear ℝ ({A, Oa, P} : Set Plane) ∧ Collinear ℝ ({B, Ob, P} : Set Plane) ∧
      Collinear ℝ ({C, Oc, P} : Set Plane) := …
```

- [ ] matches the paper      Note: ________________________

---

## BLUNDON — paper says

For a triangle in a real inner product space with circumradius $R$, inradius $r$ and semiperimeter $s$,
\[
2R^2+10Rr-r^2-2(R-2r)\sqrt{R^2-2Rr}\;\le\; s^2\;\le\;2R^2+10Rr-r^2+2(R-2r)\sqrt{R^2-2Rr}.
\]

### Lean: `blundon` — [Blundon/Basic.lean:147](https://github.com/jpbald93/blundon/blob/118b4c9f3afd6d4120ea2c2d2e60c1e70d7dc8b8/Blundon/Basic.lean#L147)

```lean
theorem blundon (t : Affine.Triangle ℝ P) :
    2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 -
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) ≤
      semiperimeter t ^ 2 ∧
    semiperimeter t ^ 2 ≤
      2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 +
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) := …
```

- [ ] matches the paper      Note: ________________________

---

## STEINER — paper says

In a non-degenerate triangle $ABC$, let $E$ on segment $AC$ and $F$ on segment $AB$ be the feet of
the internal bisectors from $B$ and $C$. If $BE=CF$ then $AB=AC$.

### Lean: `steiner_lehmus` — [SteinerLehmus/Basic.lean:112](https://github.com/jpbald93/steinerlehmus/blob/a3a3d26bee6c68eae6d564228355524c46fe546d/SteinerLehmus/Basic.lean#L112)

```lean
theorem steiner_lehmus {A B C E F : P} (hABC : ¬Collinear ℝ ({A, B, C} : Set P))
    (hE : Wbtw ℝ A E C) (hbisB : ∠ A B E = ∠ E B C)
    (hF : Wbtw ℝ A F B) (hbisC : ∠ A C F = ∠ F C B)
    (heq : dist B E = dist C F) : dist A B = dist A C := …
```

- [ ] matches the paper      Note: ________________________
Hand check completed by Josh Bald, 2026-10-14 15:53 EDT: all rows agree (reported in chat).
