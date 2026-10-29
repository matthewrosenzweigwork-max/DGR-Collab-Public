import SharpSymmetricLSI.Paper.UpperBound
import FullLabeledLSI.Paper.Sec3RecoveryJensen

/-!
# Section 3 recovery: entropy convergence for the regularization

Abstract statement: if `ρ_j = (v_j² + t_j)/(m_j + t_j)` with `v_j² ≤ moll (n j) ρ`, then
`H(ρ_j | haar) → H(ρ | haar)`.
-/

noncomputable section
open SharpLSI MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### Part A stubs -/

/-! ### Elementary real-variable facts -/

/-- Positive part of `x log x`. -/
def entPos (x : ℝ) : ℝ := max 0 (x * Real.log x)

/-- Negative part of `x log x`. -/
def entNeg (x : ℝ) : ℝ := max 0 (-(x * Real.log x))

theorem continuous_entPos : Continuous entPos :=
  continuous_const.max Real.continuous_mul_log

theorem continuous_entNeg : Continuous entNeg :=
  continuous_const.max Real.continuous_mul_log.neg

theorem entPos_nonneg (x : ℝ) : 0 ≤ entPos x := le_max_left _ _

theorem entNeg_nonneg (x : ℝ) : 0 ≤ entNeg x := le_max_left _ _

theorem entPos_one : entPos 1 = 0 := by simp [entPos]

theorem entPos_zero : entPos 0 = 0 := by simp [entPos]

theorem entNeg_le_one {x : ℝ} (hx : 0 ≤ x) : entNeg x ≤ 1 := by
  unfold entNeg
  refine max_le zero_le_one ?_
  rcases hx.eq_or_lt with h | h
  · rw [← h]; simp
  · have := Real.one_sub_inv_le_log_of_pos h
    have h2 : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left this hx
    have h3 : x * (1 - x⁻¹) = x - 1 := by field_simp
    linarith

theorem klFun_add_entNeg (x : ℝ) :
    klFun x + entNeg x + x = entPos x + 1 := by
  unfold klFun entNeg entPos
  rcases le_total 0 (x * Real.log x) with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonpos.2 h)]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonneg.2 h)]; ring

theorem convexOn_entPos : ConvexOn ℝ (Set.Ici (0 : ℝ)) entPos :=
  (convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))).sup Real.convexOn_mul_log

theorem entPos_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : entPos x ≤ entPos y := by
  unfold entPos
  refine max_le (le_max_left _ _) ?_
  rcases le_total (x * Real.log x) 0 with h | h
  · exact h.trans (le_max_left _ _)
  · rcases hx.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · refine le_trans ?_ (le_max_right _ _)
      have hl : Real.log x ≤ Real.log y := Real.log_le_log h0 hxy
      have hl0 : 0 ≤ Real.log x := by
        by_contra hneg
        have := mul_neg_of_pos_of_neg h0 (not_le.1 hneg)
        linarith
      calc x * Real.log x ≤ y * Real.log x := mul_le_mul_of_nonneg_right hxy hl0
        _ ≤ y * Real.log y := mul_le_mul_of_nonneg_left hl (h0.le.trans hxy)

theorem entPos_mul_le {s y : ℝ} (hs : 1 ≤ s) (hy : 0 ≤ y) :
    entPos (s * y) ≤ s * entPos y + s * y * Real.log s := by
  have hs0 : 0 < s := by linarith
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs
  have hP := entPos_nonneg y
  have hsy : 0 ≤ s * y * Real.log s := mul_nonneg (mul_nonneg hs0.le hy) hls
  unfold entPos at *
  refine max_le (by positivity) ?_
  rcases hy.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [Real.log_mul hs0.ne' h.ne']
    have : y * Real.log y ≤ max 0 (y * Real.log y) := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left this hs0.le]

/-- Pointwise bound used for the limsup. -/
theorem entPos_reg_le {a g m t : ℝ} (ha : 0 ≤ a) (hag : a ≤ g) (hm0 : 0 < m) (hm1 : m ≤ 1)
    (ht : 0 < t) :
    entPos ((a + t) / (m + t)) ≤ (entPos g + g * (-Real.log m)) / (m + t) := by
  have hc : 0 < m + t := by linarith
  have hg : 0 ≤ g := ha.trans hag
  have hsplit : (a + t) / (m + t) = (m / (m + t)) • (a / m) + (t / (m + t)) • (1 : ℝ) := by
    simp only [smul_eq_mul]; field_simp
  have h1 := convexOn_entPos.2 (show a / m ∈ Set.Ici (0:ℝ) from div_nonneg ha hm0.le)
    (show (1:ℝ) ∈ Set.Ici (0:ℝ) by simp) (show 0 ≤ m / (m + t) by positivity)
    (show 0 ≤ t / (m + t) by positivity) (by field_simp)
  rw [← hsplit] at h1
  simp only [smul_eq_mul, entPos_one, mul_zero, add_zero] at h1
  have h2 : entPos (a / m) ≤ entPos (m⁻¹ * g) := by
    refine entPos_mono (div_nonneg ha hm0.le) ?_
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hag (inv_nonneg.2 hm0.le)
  have h3 := entPos_mul_le (s := m⁻¹) (y := g) (by rw [le_inv_comm₀ one_pos hm0]; simpa using hm1) hg
  rw [Real.log_inv] at h3
  have h4 : m / (m + t) * entPos (a / m) ≤ (entPos g + g * (-Real.log m)) / (m + t) := by
    calc m / (m + t) * entPos (a / m) ≤ m / (m + t) * (m⁻¹ * entPos g + m⁻¹ * g * -Real.log m) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      _ = (entPos g + g * (-Real.log m)) / (m + t) := by field_simp
  exact h1.trans h4


theorem lintegral_klFun_add {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρm : Measurable ρ)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂haar d + ∫⁻ x, ENNReal.ofReal (entNeg (ρ x)) ∂haar d + 1
      = ∫⁻ x, ENNReal.ofReal (entPos (ρ x)) ∂haar d + 1 := by
  have hρi := integrable_of_integral_eq_one' hρ1
  have h1 : ∫⁻ x, ENNReal.ofReal (ρ x) ∂haar d = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1]; simp
  have mk : Measurable fun x => ENNReal.ofReal (klFun (ρ x)) :=
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp hρm)
  have mn : Measurable fun x => ENNReal.ofReal (entNeg (ρ x)) :=
    ENNReal.measurable_ofReal.comp (continuous_entNeg.measurable.comp hρm)
  calc _ = ∫⁻ x, (ENNReal.ofReal (klFun (ρ x)) + ENNReal.ofReal (entNeg (ρ x))
            + ENNReal.ofReal (ρ x)) ∂haar d := by
        rw [lintegral_add_left (f := fun x => ENNReal.ofReal (klFun (ρ x)) + ENNReal.ofReal (entNeg (ρ x)))
          (mk.add mn), lintegral_add_left mk, h1]
    _ = ∫⁻ x, (ENNReal.ofReal (entPos (ρ x)) + 1) ∂haar d := by
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_add (klFun_nonneg (hρ0 x)) (entNeg_nonneg _),
          ← ENNReal.ofReal_add (add_nonneg (klFun_nonneg (hρ0 x)) (entNeg_nonneg _)) (hρ0 x),
          klFun_add_entNeg, ENNReal.ofReal_add (entPos_nonneg _) zero_le_one, ENNReal.ofReal_one]
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]; simp

theorem tendsto_klDiv_regularization {d : ℕ} {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρm : Measurable ρ) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hρH : klDiv (densMeasure ρ) (haar d) ≠ ⊤)
    (v : ℕ → Torus d → ℝ) (hvm : ∀ j, Measurable (v j)) (hvc : ∀ j, Continuous (v j))
    (n : ℕ → ℕ) (t m : ℕ → ℝ)
    (ht0 : ∀ j, 0 < t j) (htl : Tendsto t atTop (𝓝 0))
    (hm : ∀ j, ∫ x, v j x ^ 2 ∂haar d = m j) (hm1 : ∀ j, 1/2 ≤ m j ∧ m j ≤ 1)
    (hml : Tendsto m atTop (𝓝 1))
    (hdom : ∀ j y, v j y ^ 2 ≤ moll (n j) ρ y)
    (hae : ∀ᵐ x ∂haar d,
      Tendsto (fun j => (v j x ^ 2 + t j) / (m j + t j)) atTop (𝓝 (ρ x))) :
    Tendsto (fun j => klDiv (densMeasure (fun x => (v j x ^ 2 + t j) / (m j + t j))) (haar d))
      atTop (𝓝 (klDiv (densMeasure ρ) (haar d))) := by
  have hρi := integrable_of_integral_eq_one' hρ1
  have hm0 : ∀ j, 0 < m j := fun j => by linarith [(hm1 j).1]
  have hc0 : ∀ j, 0 < m j + t j := fun j => by linarith [hm0 j, ht0 j]
  set ρs : ℕ → Torus d → ℝ := fun j x => (v j x ^ 2 + t j) / (m j + t j) with hρs
  have hvi : ∀ j, Integrable (fun x => v j x ^ 2) (haar d) := by
    intro j
    by_contra h
    have := hm j
    rw [integral_undef h] at this
    linarith [hm0 j]
  have hρs0 : ∀ j x, 0 ≤ ρs j x := fun j x =>
    div_nonneg (add_nonneg (sq_nonneg _) (ht0 j).le) (hc0 j).le
  have hρs1 : ∀ j, ∫ x, ρs j x ∂haar d = 1 := by
    intro j
    simp only [hρs]
    rw [integral_div, integral_add (hvi j) (integrable_const _), hm j]
    have : ∫ _x : Torus d, t j ∂haar d = t j := by simp
    rw [this]
    exact div_self (hc0 j).ne'
  have hρsm : ∀ j, Measurable (ρs j) := fun j =>
    (((hvm j).pow_const 2).add_const _).div_const _
  have hklD : ∀ j, klDiv (densMeasure (ρs j)) (haar d)
      = ∫⁻ x, ENNReal.ofReal (klFun (ρs j x)) ∂haar d :=
    fun j => klDiv_densMeasure' (hρs0 j) (hρs1 j)
  -- liminf
  have hinf := klDiv_le_liminf hρ0 hρ1 hρs0 hρs1 hρsm hae
  -- limsup
  set a : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂haar d with ha
  set nn : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (entNeg (ρ x)) ∂haar d with hnn
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (entPos (ρ x)) ∂haar d with hB
  have haeq : klDiv (densMeasure ρ) (haar d) = a := klDiv_densMeasure' hρ0 hρ1
  have haT : a ≠ ⊤ := haeq ▸ hρH
  have hnle : nn ≤ 1 := by
    calc nn ≤ ∫⁻ _x, 1 ∂haar d :=
          lintegral_mono fun x => by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (entNeg_le_one (hρ0 x))
      _ = 1 := by simp
  have hnT : nn ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hnle
  have hBeq : B = a + nn := by
    have := lintegral_klFun_add hρ0 hρm hρ1
    exact ((ENNReal.add_left_inj ENNReal.one_ne_top).1 this).symm
  have hBT : B ≠ ⊤ := by
    rw [hBeq]; exact ENNReal.add_ne_top.2 ⟨haT, hnT⟩
  have hρmeasN : ∀ j, Measurable fun x => ENNReal.ofReal (entNeg (ρs j x)) := fun j =>
    ENNReal.measurable_ofReal.comp (continuous_entNeg.measurable.comp (hρsm j))
  -- the bound
  have hbound : ∀ j, ∫⁻ x, ENNReal.ofReal (entPos (ρs j x)) ∂haar d
      ≤ ENNReal.ofReal (1 / (m j + t j)) * (B + ENNReal.ofReal (-Real.log (m j))) := by
    intro j
    set g := moll (n j) ρ with hg
    have hgm : Measurable g := measurable_moll _ hρi
    have hg0 : ∀ y, 0 ≤ g y := moll_nonneg (n j) hρ0
    have hgint : ∫ y, g y ∂haar d = 1 := by rw [hg, integral_moll _ hρi, hρ1]
    have hgi : Integrable g (haar d) := integrable_of_integral_eq_one' hgint
    have hg1 : ∫⁻ y, ENNReal.ofReal (g y) ∂haar d = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0), hgint]; simp
    have hL0 : 0 ≤ -Real.log (m j) := neg_nonneg.2 (Real.log_nonpos (hm0 j).le (hm1 j).2)
    have hmP : Measurable fun y => ENNReal.ofReal (entPos (g y)) :=
      ENNReal.measurable_ofReal.comp (continuous_entPos.measurable.comp hgm)
    have hJ := lintegral_convex_moll_le (n j) convexOn_entPos continuous_entPos
      (fun x _ => entPos_nonneg x) hρ0 hρm hρi
    calc ∫⁻ x, ENNReal.ofReal (entPos (ρs j x)) ∂haar d
        ≤ ∫⁻ x, ENNReal.ofReal (1 / (m j + t j)) *
            (ENNReal.ofReal (entPos (g x)) +
              ENNReal.ofReal (-Real.log (m j)) * ENNReal.ofReal (g x)) ∂haar d := by
          refine lintegral_mono fun x => ?_
          have key := entPos_reg_le (a := v j x ^ 2) (g := g x) (m := m j) (t := t j)
            (sq_nonneg _) (hdom j x) (hm0 j) (hm1 j).2 (ht0 j)
          have hc := hc0 j
          calc ENNReal.ofReal (entPos (ρs j x))
              ≤ ENNReal.ofReal (1 / (m j + t j) *
                  (entPos (g x) + g x * (-Real.log (m j)))) := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [one_div, inv_mul_eq_div]; exact key
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity),
                  ENNReal.ofReal_add (entPos_nonneg _) (mul_nonneg (hg0 x) hL0),
                  ENNReal.ofReal_mul (hg0 x), mul_comm (ENNReal.ofReal (g x))]
      _ = ENNReal.ofReal (1 / (m j + t j)) * (∫⁻ x, ENNReal.ofReal (entPos (g x)) ∂haar d +
            ENNReal.ofReal (-Real.log (m j)) * ∫⁻ x, ENNReal.ofReal (g x) ∂haar d) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmP,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          rw [hg1, mul_one]
          gcongr
  -- limit of the bound
  have hc_t : Tendsto (fun j => m j + t j) atTop (𝓝 1) := by
    simpa using hml.add htl
  have hL_t : Tendsto (fun j => -Real.log (m j)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp hml).neg
    simpa using this
  have hB_t : Tendsto (fun j => ENNReal.ofReal (1 / (m j + t j)) *
      (B + ENNReal.ofReal (-Real.log (m j)))) atTop (𝓝 B) := by
    have h1 : Tendsto (fun j => ENNReal.ofReal (1 / (m j + t j))) atTop (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (tendsto_const_nhds.div hc_t one_ne_zero (a := (1:ℝ)))
      simpa using this
    have h2 : Tendsto (fun j => B + ENNReal.ofReal (-Real.log (m j))) atTop (𝓝 B) := by
      have := ENNReal.tendsto_ofReal hL_t
      simpa using tendsto_const_nhds.add this (a := B)
    have := ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero) h2 (Or.inr ENNReal.one_ne_top)
    simpa using this
  -- convergence of the negative parts
  have hn_t : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (entNeg (ρs j x)) ∂haar d) atTop (𝓝 nn) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hρmeasN
      (fun j => Eventually.of_forall fun x => ?_) (by simp) ?_
    · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (entNeg_le_one (hρs0 j x))
    · filter_upwards [hae] with x hx
      exact (ENNReal.continuous_ofReal.comp continuous_entNeg).tendsto _ |>.comp hx
  -- upper bound on a_j
  have hle : ∀ j, klDiv (densMeasure (ρs j)) (haar d) ≤
      ENNReal.ofReal (1 / (m j + t j)) * (B + ENNReal.ofReal (-Real.log (m j))) -
        ∫⁻ x, ENNReal.ofReal (entNeg (ρs j x)) ∂haar d := by
    intro j
    rw [hklD j]
    have hnjT : ∫⁻ x, ENNReal.ofReal (entNeg (ρs j x)) ∂haar d ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _x, (1 : ℝ≥0∞) ∂haar d) (by simp) (lintegral_mono fun x => ?_)
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (entNeg_le_one (hρs0 j x))
    refine ENNReal.le_sub_of_add_le_right hnjT ?_
    have h := lintegral_klFun_add (hρs0 j) (hρsm j) (hρs1 j)
    have h2 : ∫⁻ x, ENNReal.ofReal (klFun (ρs j x)) ∂haar d +
        ∫⁻ x, ENNReal.ofReal (entNeg (ρs j x)) ∂haar d + 1 ≤
        (ENNReal.ofReal (1 / (m j + t j)) * (B + ENNReal.ofReal (-Real.log (m j)))) + 1 := by
      rw [h]; exact add_le_add_left (hbound j) 1
    exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h2
  have hsub_t := ENNReal.Tendsto.sub hB_t hn_t (Or.inl hBT)
  have hBa : B - nn = a := by rw [hBeq]; exact ENNReal.add_sub_cancel_right hnT
  rw [hBa] at hsub_t
  have hsup : limsup (fun j => klDiv (densMeasure (ρs j)) (haar d)) atTop ≤ a := by
    calc _ ≤ limsup (fun j => ENNReal.ofReal (1 / (m j + t j)) * (B + ENNReal.ofReal (-Real.log (m j))) -
        ∫⁻ x, ENNReal.ofReal (entNeg (ρs j x)) ∂haar d) atTop := limsup_le_limsup (Eventually.of_forall hle)
      _ = a := hsub_t.limsup_eq
  rw [haeq]
  rw [haeq] at hinf
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup

end SharpLSI.FL
