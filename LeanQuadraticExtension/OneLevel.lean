import Mathlib

/-!
# One-level quadratic extension `F(√d)` — the order, built syntactically

Mirrors the *bottom* of the Verus `dts_nonneg` construction, for a single quadratic
extension `F(√d)` rather than the full dynamic tower.

Point of interest: we define "`a + b√d ≥ 0`" **without `√d` ever existing as an
element**. `F` is an arbitrary linearly ordered field; `√d` need not live in it. So
`Nonneg` is a purely *syntactic* sign-case predicate, exactly as in Verus
(`dyn_tower.rs`, the `Ext` branch of `dts_nonneg_fuel`):

* `a ≥ 0 ∧ b ≥ 0`                (C1: obviously nonneg)
* `a ≥ 0 ∧ b < 0 ∧ d·b² ≤ a²`   (C2: `a ≥ |b|√d ⟺ a² ≥ d b²`)
* `a < 0 ∧ b > 0 ∧ a² ≤ d·b²`   (C3: `b√d ≥ |a| ⟺ d b² ≥ a²`)

`nonneg_add` proves the positive cone is closed under `+`. In Verus this is
`lemma_dts_nonneg_add_closed_fuel` + the ~470-line `lemma_dts_nonneg_add_remaining`,
hand-driving Z3 through a 6-way dispatch. Here: `rcases` into 9 cases + `nlinarith`.
-/

namespace QuadExt

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Syntactic "`a + b√d ≥ 0`", `√d` taken as the nonnegative root.
Meaningful when `0 ≤ d` (carried at use sites; cf. Verus `dts_nonneg_radicands`). -/
def Nonneg (d a b : F) : Prop :=
  (0 ≤ a ∧ 0 ≤ b) ∨
  (0 ≤ a ∧ b < 0 ∧ d * b ^ 2 ≤ a ^ 2) ∨
  (a < 0 ∧ 0 < b ∧ a ^ 2 ≤ d * b ^ 2)

/-- Cross-term lemma powering the mixed cases. From two norm bounds we get
`(d b₁ b₂)² ≤ (a₁ a₂)²`, via the identity
`(a₁a₂)² − (d b₁b₂)² = a₁²·(a₂²−d b₂²) + d b₂²·(a₁²−d b₁²)` — a sum of nonneg
products. This is the Lean counterpart of Verus' "cancellation-by-B²". -/
theorem norm_cross_sq {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (h1 : d * b₁ ^ 2 ≤ a₁ ^ 2) (h2 : d * b₂ ^ 2 ≤ a₂ ^ 2) :
    (d * b₁ * b₂) ^ 2 ≤ (a₁ * a₂) ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg a₁) (sub_nonneg.mpr h2),
             mul_nonneg (mul_nonneg hd (sq_nonneg b₂)) (sub_nonneg.mpr h1),
             mul_nonneg hd (sq_nonneg b₁), sq_nonneg b₁, sq_nonneg b₂]

/-- Sign-resolved cross bound: when `a₁a₂` and `d b₁b₂` are both nonnegative, the
squared bound upgrades to the linear `d b₁ b₂ ≤ a₁ a₂`. -/
theorem norm_cross {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (h1 : d * b₁ ^ 2 ≤ a₁ ^ 2) (h2 : d * b₂ ^ 2 ≤ a₂ ^ 2)
    (hbb : 0 ≤ d * b₁ * b₂) (haa : 0 ≤ a₁ * a₂) :
    d * b₁ * b₂ ≤ a₁ * a₂ := by
  have hsq := norm_cross_sq hd h1 h2
  nlinarith [hsq, hbb, haa]

/-- Reverse cross-term: from `a² ≤ d b²` bounds (the C3 direction) get
`(a₁ a₂)² ≤ (d b₁ b₂)²`, via
`(d b₁b₂)² − (a₁a₂)² = d b₁²·(d b₂²−a₂²) + a₂²·(d b₁²−a₁²)`. -/
theorem norm_cross_sq' {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (h1 : a₁ ^ 2 ≤ d * b₁ ^ 2) (h2 : a₂ ^ 2 ≤ d * b₂ ^ 2) :
    (a₁ * a₂) ^ 2 ≤ (d * b₁ * b₂) ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg hd (sq_nonneg b₁)) (sub_nonneg.mpr h2),
             mul_nonneg (sq_nonneg a₂) (sub_nonneg.mpr h1),
             mul_nonneg hd (sq_nonneg b₁), sq_nonneg a₂]

/-- Sign-resolved reverse cross bound: `a₁ a₂ ≤ d b₁ b₂`. -/
theorem norm_cross' {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (h1 : a₁ ^ 2 ≤ d * b₁ ^ 2) (h2 : a₂ ^ 2 ≤ d * b₂ ^ 2)
    (hbb : 0 ≤ d * b₁ * b₂) (haa : 0 ≤ a₁ * a₂) :
    a₁ * a₂ ≤ d * b₁ * b₂ := by
  have hsq := norm_cross_sq' hd h1 h2
  nlinarith [hsq, hbb, haa]

/-- Cross inequality `a₂ b₁ ≤ a₁ b₂` for a C2 factor `(a₁,b₁)` and C3 factor
`(a₂,b₂)`, from `(a₁b₂)² − (a₂b₁)² = b₂²(a₁²−db₁²) + b₁²(db₂²−a₂²)`. -/
theorem cross_c2c3 {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (ha1 : 0 ≤ a₁) (hb1 : b₁ < 0) (hn1 : d * b₁ ^ 2 ≤ a₁ ^ 2)
    (ha2 : a₂ < 0) (hb2 : 0 < b₂) (hn2 : a₂ ^ 2 ≤ d * b₂ ^ 2) :
    a₂ * b₁ ≤ a₁ * b₂ := by
  nlinarith [mul_nonneg (sq_nonneg b₂) (sub_nonneg.mpr hn1),
             mul_nonneg (sq_nonneg b₁) (sub_nonneg.mpr hn2),
             mul_nonneg ha1 hb2.le, mul_pos_of_neg_of_neg ha2 hb1]

set_option maxHeartbeats 1000000 in
/-- **The hard case**: C2 + C3 closure. Verus needed four sub-lemmas here
(`c2c3_norm_bound`, `c2c3_neg_norm_bound`, `case4_contradiction`,
`iszero_sum_im_implies_nonneg_sum_re`); we mirror that with a 4-way sign split
on `A := a₁+a₂`, `B := b₁+b₂`, each closed by the hand-derived `b²·G` identity. -/
theorem nonneg_add_c2c3 {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (ha1 : 0 ≤ a₁) (hb1 : b₁ < 0) (hn1 : d * b₁ ^ 2 ≤ a₁ ^ 2)
    (ha2 : a₂ < 0) (hb2 : 0 < b₂) (hn2 : a₂ ^ 2 ≤ d * b₂ ^ 2) :
    Nonneg d (a₁ + a₂) (b₁ + b₂) := by
  have hcross := cross_c2c3 hd ha1 hb1 hn1 ha2 hb2 hn2
  have hb1sq : 0 < b₁ * b₁ := mul_pos_of_neg_of_neg hb1 hb1
  have hb2sq : 0 < b₂ * b₂ := mul_pos hb2 hb2
  have hd' : 0 < d := by nlinarith [hn2, hb2sq, mul_pos_of_neg_of_neg ha2 ha2]
  rcases le_or_gt 0 (a₁ + a₂) with hA | hA
  · rcases le_or_gt 0 (b₁ + b₂) with hB | hB
    · exact Or.inl ⟨hA, hB⟩                                  -- L
    · -- M :  d B² ≤ A².   b₁²·G = (a₁²−db₁²)B² + (a₁b₂−a₂b₁)(−b₁A − a₁B)
      refine Or.inr (Or.inl ⟨hA, hB, ?_⟩)
      have hfac : 0 ≤ -b₁ * (a₁ + a₂) - a₁ * (b₁ + b₂) := by
        nlinarith [mul_nonneg (show (0:F) ≤ -b₁ by linarith) hA,
                   mul_nonneg ha1 (show (0:F) ≤ -(b₁ + b₂) by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (b₁ + b₂)),
                 mul_nonneg (sub_nonneg.mpr hcross) hfac, hb1sq]
  · -- A < 0  ⟹  0 < B,  then  A² ≤ d B².
    have hBpos : 0 < b₁ + b₂ := by
      have ha_sq : a₁ ^ 2 < a₂ ^ 2 := by
        nlinarith [mul_pos (show (0:F) < -a₂ - a₁ by linarith)
                           (show (0:F) < -a₂ + a₁ by linarith)]
      have hbb_sq : b₁ ^ 2 < b₂ ^ 2 := by nlinarith [hn1, hn2, ha_sq, hd']
      rcases le_or_gt (b₁ + b₂) 0 with h | h
      · exfalso
        nlinarith [hbb_sq, mul_nonneg (show (0:F) ≤ -b₁ - b₂ by linarith)
                                      (show (0:F) ≤ -b₁ + b₂ by linarith)]
      · exact h
    refine Or.inr (Or.inr ⟨hA, hBpos, ?_⟩)
    -- R :  A² ≤ d B².   b₂²·G' = (db₂²−a₂²)B² + (a₁b₂−a₂b₁)(−a₂B − b₂A)
    have hfac' : 0 ≤ -a₂ * (b₁ + b₂) - b₂ * (a₁ + a₂) := by
      nlinarith [mul_nonneg (show (0:F) ≤ -a₂ by linarith) hBpos.le,
                 mul_nonneg hb2.le (show (0:F) ≤ -(a₁ + a₂) by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg (b₁ + b₂)),
               mul_nonneg (sub_nonneg.mpr hcross) hfac', hb2sq]

set_option maxHeartbeats 1000000 in
/-- **The positive cone is closed under addition.**
Verus: `lemma_dts_nonneg_add_closed_fuel` (+ `_remaining`, ~470 lines).
The 9 cases share one declaration's heartbeat budget, so we lift the default. -/
theorem nonneg_add {d a₁ b₁ a₂ b₂ : F} (hd : 0 ≤ d)
    (hx : Nonneg d a₁ b₁) (hy : Nonneg d a₂ b₂) :
    Nonneg d (a₁ + a₂) (b₁ + b₂) := by
  unfold Nonneg at *
  rcases hx with ⟨ha1, hb1⟩ | ⟨ha1, hb1, hn1⟩ | ⟨ha1, hb1, hn1⟩ <;>
  rcases hy with ⟨ha2, hb2⟩ | ⟨ha2, hb2, hn2⟩ | ⟨ha2, hb2, hn2⟩
  · -- C1 + C1
    exact Or.inl ⟨by linarith, by linarith⟩
  · -- C1 + C2
    rcases le_or_gt 0 (b₁ + b₂) with hB | hB
    · exact Or.inl ⟨by linarith, hB⟩
    · refine Or.inr (Or.inl ⟨by linarith, hB, ?_⟩)
      -- b₁+2b₂ < 0, b₁ ≥ 0  ⟹  d·b₁·(-(b₁+2b₂)) ≥ 0
      have hkey : 0 ≤ d * b₁ * (-(b₁ + 2 * b₂)) :=
        mul_nonneg (mul_nonneg hd hb1) (by linarith)
      nlinarith [hn2, mul_nonneg ha1 ha2, hkey, sq_nonneg a₁]
  · -- C1 + C3
    rcases le_or_gt 0 (a₁ + a₂) with hA | hA
    · exact Or.inl ⟨hA, by linarith⟩
    · refine Or.inr (Or.inr ⟨hA, by linarith, ?_⟩)
      -- a₁+2a₂ < 0, a₁ ≥ 0  ⟹  a₁·(-(a₁+2a₂)) ≥ 0
      have hkey : 0 ≤ a₁ * (-(a₁ + 2 * a₂)) := mul_nonneg ha1 (by linarith)
      have hb1b2 : 0 ≤ d * b₁ * b₂ := mul_nonneg (mul_nonneg hd hb1) (le_of_lt hb2)
      nlinarith [hn2, hkey, hb1b2, mul_nonneg hd (sq_nonneg b₁)]
  · -- C2 + C1  (mirror of C1 + C2)
    rcases le_or_gt 0 (b₁ + b₂) with hB | hB
    · exact Or.inl ⟨by linarith, hB⟩
    · refine Or.inr (Or.inl ⟨by linarith, hB, ?_⟩)
      have hkey : 0 ≤ d * b₂ * (-(b₂ + 2 * b₁)) :=
        mul_nonneg (mul_nonneg hd hb2) (by linarith)
      nlinarith [hn1, mul_nonneg ha1 ha2, hkey, sq_nonneg a₂]
  · -- C2 + C2
    refine Or.inr (Or.inl ⟨by linarith, by linarith, ?_⟩)
    have hbb : 0 ≤ d * b₁ * b₂ := by
      have h := mul_pos_of_neg_of_neg hb1 hb2
      nlinarith [mul_nonneg hd h.le]
    have hc := norm_cross hd hn1 hn2 hbb (mul_nonneg ha1 ha2)
    nlinarith [hn1, hn2, hc]
  · -- C2 + C3  *** the hard case (Verus: lemma_dts_c2c3_*) ***
    exact nonneg_add_c2c3 hd ha1 hb1 hn1 ha2 hb2 hn2
  · -- C3 + C1  (mirror of C1 + C3)
    rcases le_or_gt 0 (a₁ + a₂) with hA | hA
    · exact Or.inl ⟨hA, by linarith⟩
    · refine Or.inr (Or.inr ⟨hA, by linarith, ?_⟩)
      have hkey : 0 ≤ a₂ * (-(a₂ + 2 * a₁)) := mul_nonneg ha2 (by linarith)
      have hb1b2 : 0 ≤ d * b₁ * b₂ := mul_nonneg (mul_nonneg hd (le_of_lt hb1)) hb2
      nlinarith [hn1, hkey, hb1b2, mul_nonneg hd (sq_nonneg b₂)]
  · -- C3 + C2  (mirror of C2 + C3): swap factors, reuse via commutativity
    have h := nonneg_add_c2c3 hd ha2 hb2 hn2 ha1 hb1 hn1
    rwa [add_comm a₂ a₁, add_comm b₂ b₁] at h
  · -- C3 + C3
    refine Or.inr (Or.inr ⟨by linarith, by linarith, ?_⟩)
    have hbb : 0 ≤ d * b₁ * b₂ := mul_nonneg (mul_nonneg hd (le_of_lt hb1)) (le_of_lt hb2)
    have hc := norm_cross' hd hn1 hn2 hbb (le_of_lt (mul_pos_of_neg_of_neg ha1 ha2))
    nlinarith [hn1, hn2, hc]

end QuadExt
