import SharpSymmetricLSI.Paper.AppAPos8

/-!
# Positivity (9): `ρ_t ≥ 0`

For a linear mild solution with `|N| ≤ A|ρ|` and `ρ₀ ≥ 0`, `ρ_t ≥ 0` a.e. for every `t ≥ 0`
(`LinMild.ae_nonneg`): the energy inequality with `G(r) = (r⁻)⁴` gives, as `ε → 0`,
`∫ G(ρ_t) ≤ 3|ι|A² ∫₀ᵗ ∫ G(ρ_u)`, and Grönwall.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

theorem negPow_two_mul_sq (r : ℝ) : negPow 2 r * r ^ 2 = negPow 4 r := by
  unfold negPow
  rcases le_total r 0 with hr | hr
  · rw [min_eq_left hr]; ring
  · rw [min_eq_right hr]; ring

theorem negPow_four_nonneg (r : ℝ) : 0 ≤ negPow 4 r := by unfold negPow; positivity

theorem negPow_two_nonneg (r : ℝ) : 0 ≤ negPow 2 r := by unfold negPow; positivity

theorem negPow_four_le {r K : ℝ} (hr : |r| ≤ K) : negPow 4 r ≤ K ^ 4 := by
  unfold negPow
  have h1 : |min r 0| ≤ K := by
    rcases le_total r 0 with h | h
    · rw [min_eq_left h]; exact hr
    · rw [min_eq_right h, abs_zero]; exact (abs_nonneg _).trans hr
  calc min r 0 ^ 4 = |min r 0| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ K ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h1 4

theorem nonneg_of_negPow_four_eq_zero {r : ℝ} (h : negPow 4 r = 0) : 0 ≤ r := by
  unfold negPow at h
  have := pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h
  by_contra hr
  push_neg at hr
  rw [min_eq_left hr.le] at this
  linarith

theorem hasDerivAt_G4 (r : ℝ) : HasDerivAt (negPow 4) (4 * negPow 3 r) r := by
  have := hasDerivAt_negPow (n := 4) (by norm_num) r
  simpa using this

theorem hasDerivAt_G4' (r : ℝ) :
    HasDerivAt (fun r => 4 * negPow 3 r) (12 * negPow 2 r) r := by
  have := (hasDerivAt_negPow (n := 3) (by norm_num) r).const_mul 4
  convert this using 1; push_cast; ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The quadratic estimate behind the flux limit. -/
theorem abs_P_S_sub_le {L K a : ℝ} (ha : 0 ≤ a) (hL : ∀ x y, |x| ≤ K → |y| ≤ K →
      |12 * negPow 2 x - 12 * negPow 2 y| ≤ L * |x - y|) (hL0 : 0 ≤ L) (hK : 0 ≤ K)
    {x y : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) {b c : ι → ℝ} (hb : ∀ j, |b j| ≤ a) (hc : ∀ j, |c j| ≤ a) :
    |12 * negPow 2 x * (∑ j, b j ^ 2) / 4 - 12 * negPow 2 y * (∑ j, c j ^ 2) / 4| ≤
      (L * |x - y| * (Fintype.card ι * a ^ 2) + 12 * K ^ 2 * ∑ j, 2 * a * |b j - c j|) / 4 := by
  have hSb : |∑ j, b j ^ 2| ≤ Fintype.card ι * a ^ 2 := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    calc ∑ j, b j ^ 2 ≤ ∑ _j : ι, a ^ 2 := Finset.sum_le_sum fun j _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb j) 2
      _ = _ := by simp
  have hPy : |12 * negPow 2 y| ≤ 12 * K ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12), abs_of_nonneg (negPow_two_nonneg y)]
    gcongr
    unfold negPow
    have h1 : |min y 0| ≤ K := by
      rcases le_total y 0 with h | h
      · rw [min_eq_left h]; exact hy
      · rw [min_eq_right h, abs_zero]; exact hK
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hSbc : |∑ j, b j ^ 2 - ∑ j, c j ^ 2| ≤ ∑ j, 2 * a * |b j - c j| := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [show b j ^ 2 - c j ^ 2 = (b j - c j) * (b j + c j) by ring, abs_mul, mul_comm]
    gcongr
    calc |b j + c j| ≤ |b j| + |c j| := abs_add_le _ _
      _ ≤ a + a := add_le_add (hb j) (hc j)
      _ = 2 * a := by ring
  have e : 12 * negPow 2 x * (∑ j, b j ^ 2) / 4 - 12 * negPow 2 y * (∑ j, c j ^ 2) / 4 =
      ((12 * negPow 2 x - 12 * negPow 2 y) * (∑ j, b j ^ 2) +
        12 * negPow 2 y * (∑ j, b j ^ 2 - ∑ j, c j ^ 2)) / 4 := by ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  gcongr
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul (hL x y hx hy) hSb (abs_nonneg _) (mul_nonneg hL0 (abs_nonneg _))
  · rw [abs_mul]
    exact mul_le_mul hPy hSbc (abs_nonneg _) (by positivity)

theorem abs_P_S_le {K a x : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) (hx : |x| ≤ K) {b : ι → ℝ}
    (hb : ∀ j, |b j| ≤ a) :
    |12 * negPow 2 x * (∑ j, b j ^ 2) / 4| ≤ 12 * K ^ 2 * (Fintype.card ι * a ^ 2) / 4 := by
  have hS0 : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSb : ∑ j, b j ^ 2 ≤ Fintype.card ι * a ^ 2 := by
    calc ∑ j, b j ^ 2 ≤ ∑ _j : ι, a ^ 2 := Finset.sum_le_sum fun j _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb j) 2
      _ = _ := by simp
  have hP : negPow 2 x ≤ K ^ 2 := by
    unfold negPow
    have h1 : |min x 0| ≤ K := by
      rcases le_total x 0 with h | h
      · rw [min_eq_left h]; exact hx
      · rw [min_eq_right h, abs_zero]; exact hK
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [abs_of_nonneg (by have := negPow_two_nonneg x; positivity)]
  gcongr

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- The flux term converges as `ε → 0`. -/
theorem tendsto_flux_term {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    Tendsto (fun m : ℕ => ∫ x, 12 * negPow 2 (heatT (1 / ((m : ℝ) + 1)) (ρ u) x) *
        (∑ j, (heatT (1 / ((m : ℝ) + 1)) (fun z => N u z j) x) ^ 2) / 4) atTop
      (𝓝 (∫ x, 12 * negPow 2 (ρ u x) * (∑ j, (N u x j) ^ 2) / 4)) := by
  set ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hε
  have hεp : ∀ m, 0 < ε m := fun m => by simp only [hε]; positivity
  have hP : ∀ r, HasDerivAt (fun r => 12 * negPow 2 r) (12 * (2 * negPow 1 r)) r := fun r => by
    have := (hasDerivAt_negPow (n := 2) le_rfl r).const_mul 12
    simpa using this
  obtain ⟨L, hL0, hL⟩ := exists_lip_on hP (by unfold negPow; fun_prop) K
  set a := A * K
  have ha : 0 ≤ a := mul_nonneg h.A_nonneg hK0
  have hρm := h.measurable_section u
  have hNm := fun j => h.measurable_sectionN u j
  have hρb := hK u hu
  have hNb : ∀ z j, |N u z j| ≤ a := fun z j => h.abs_N_le hK hu z j
  set φ : ℕ → UnitAddTorus ι → ℝ := fun m => heatT (ε m) (ρ u)
  set ψ : ℕ → ι → UnitAddTorus ι → ℝ := fun m j => heatT (ε m) (fun z => N u z j)
  have hφm : ∀ m, Measurable (φ m) := fun m => (measurable_heatT_joint hρm).comp measurable_prodMk_left
  have hψm : ∀ m j, Measurable (ψ m j) := fun m j =>
    (measurable_heatT_joint (hNm j)).comp measurable_prodMk_left
  have hφb : ∀ m x, |φ m x| ≤ K := fun m x =>
    abs_heatT_le (hεp m) hρm.aestronglyMeasurable (Eventually.of_forall hρb) x
  have hψb : ∀ m j x, |ψ m j x| ≤ a := fun m j x =>
    abs_heatT_le (hεp m) (hNm j).aestronglyMeasurable (Eventually.of_forall fun z => hNb z j) x
  have hc1 : Tendsto (fun m => ∫ x, |φ m x - ρ u x|) atTop (𝓝 0) :=
    tendsto_integral_abs_heatT_sub hρm hρb
  have hc2 : ∀ j, Tendsto (fun m => ∫ x, |ψ m j x - N u x j|) atTop (𝓝 0) := fun j =>
    tendsto_integral_abs_heatT_sub (hNm j) fun z => hNb z j
  set F : ℕ → UnitAddTorus ι → ℝ := fun m x => 12 * negPow 2 (φ m x) * (∑ j, (ψ m j x) ^ 2) / 4
  set F₀ : UnitAddTorus ι → ℝ := fun x => 12 * negPow 2 (ρ u x) * (∑ j, (N u x j) ^ 2) / 4
  have hPc : Continuous fun r => 12 * negPow 2 r := by unfold negPow; fun_prop
  have hFm : ∀ m, Measurable (F m) := fun m =>
    ((hPc.measurable.comp (hφm m)).mul (Finset.measurable_sum _ fun j _ => (hψm m j).pow_const 2)).div_const 4
  have hF₀m : Measurable F₀ :=
    ((hPc.measurable.comp hρm).mul (Finset.measurable_sum _ fun j _ => (hNm j).pow_const 2)).div_const 4
  have hpt : ∀ m x, |F m x - F₀ x| ≤
      (L * |φ m x - ρ u x| * (Fintype.card ι * a ^ 2) + 12 * K ^ 2 * ∑ j, 2 * a * |ψ m j x - N u x j|) / 4 :=
    fun m x => abs_P_S_sub_le (b := fun j => ψ m j x) (c := fun j => N u x j) ha hL hL0 hK0
      (hφb m x) (hρb x) (fun j => hψb m j x) (fun j => hNb x j)
  have hi1 : ∀ m, Integrable fun x => |φ m x - ρ u x| := fun m =>
    (appA_integrable_of_abs_le' ((hφm m).sub hρm) fun x => (abs_sub _ _).trans
      (add_le_add (hφb m x) (hρb x))).abs
  have hi2 : ∀ m j, Integrable fun x => |ψ m j x - N u x j| := fun m j =>
    (appA_integrable_of_abs_le' ((hψm m j).sub (hNm j)) fun x => (abs_sub _ _).trans
      (add_le_add (hψb m j x) (hNb x j))).abs
  have hbound : ∀ m, ∫ x, (L * |φ m x - ρ u x| * (Fintype.card ι * a ^ 2) +
      12 * K ^ 2 * ∑ j, 2 * a * |ψ m j x - N u x j|) / 4 =
      ((L * (Fintype.card ι * a ^ 2) * ∫ x, |φ m x - ρ u x|) +
        12 * K ^ 2 * ∑ j, 2 * a * ∫ x, |ψ m j x - N u x j|) / 4 := fun m => by
    have ia : Integrable fun x => L * |φ m x - ρ u x| * (Fintype.card ι * a ^ 2) :=
      ((hi1 m).const_mul L).mul_const _
    have ib : Integrable fun x => 12 * K ^ 2 * ∑ j, 2 * a * |ψ m j x - N u x j| :=
      (integrable_finsetSum _ fun j _ => ((hi2 m j).const_mul (2 * a))).const_mul _
    rw [integral_div, integral_add ia ib, integral_mul_const, integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun j _ => ((hi2 m j).const_mul (2 * a))]
    simp_rw [integral_const_mul]
    ring
  have hz : Tendsto (fun m => ((L * (Fintype.card ι * a ^ 2) * ∫ x, |φ m x - ρ u x|) +
      12 * K ^ 2 * ∑ j, 2 * a * ∫ x, |ψ m j x - N u x j|) / 4) atTop (𝓝 0) := by
    have := ((hc1.const_mul (L * (Fintype.card ι * a ^ 2))).add
      ((tendsto_finsetSum (Finset.univ : Finset ι) fun j _ => (hc2 j).const_mul (2 * a)).const_mul
        (12 * K ^ 2))).div_const 4
    simpa using this
  have hFi : ∀ m, Integrable (F m) := fun m =>
    appA_integrable_of_abs_le' (hFm m) fun x => abs_P_S_le hK0 ha (hφb m x) fun j => hψb m j x
  have hF₀i : Integrable F₀ :=
    appA_integrable_of_abs_le' hF₀m fun x => abs_P_S_le hK0 ha (hρb x) fun j => hNb x j
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hz
  rw [← hbound m, ← integral_sub (hFi m) hF₀i, Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) ?_ (Eventually.of_forall fun x => hpt m x))
  have ia : Integrable fun x => L * |φ m x - ρ u x| * (Fintype.card ι * a ^ 2) :=
    ((hi1 m).const_mul L).mul_const _
  have ib : Integrable fun x => 12 * K ^ 2 * ∑ j, 2 * a * |ψ m j x - N u x j| :=
    (integrable_finsetSum _ fun j _ => ((hi2 m j).const_mul (2 * a))).const_mul _
  exact (ia.add ib).div_const 4

/-- **Positivity of linear mild solutions.** -/
theorem ae_nonneg (hρ₀ : ∀ x, 0 ≤ ρ₀ x) {t : ℝ} (ht : 0 ≤ t) : ∀ᵐ x, 0 ≤ ρ t x := by
  obtain ⟨K, hK0, hK⟩ := h.bdd t
  set T := t with hTdef
  set ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hε
  have hεp : ∀ m, 0 < ε m := fun m => by simp only [hε]; positivity
  set E : ℝ → ℝ := fun u => ∫ x, negPow 4 (ρ u x) with hE
  have hEm : Measurable E :=
    ((continuous_negPow 4).measurable.comp h.meas).stronglyMeasurable.integral_prod_right'.measurable
  have hE0 : ∀ u, 0 ≤ E u := fun u => integral_nonneg fun x => negPow_four_nonneg _
  have hEM : ∀ u ∈ Icc 0 T, E u ≤ K ^ 4 := fun u hu => by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => negPow_four_nonneg _)
      (integrable_const (K ^ 4)) (Eventually.of_forall fun x => negPow_four_le (hK u hu x))).trans ?_
    simp
  set c : ℝ := 3 * Fintype.card ι * A ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set a := A * K
  have ha : 0 ≤ a := mul_nonneg h.A_nonneg hK0
  set B0 : ℝ := 12 * K ^ 2 * (Fintype.card ι * a ^ 2) / 4
  have hPc : Continuous fun r => 12 * negPow 2 r := by unfold negPow; fun_prop
  -- the flux integrand, jointly measurable
  have hJm : ∀ m, Measurable fun p : ℝ × UnitAddTorus ι =>
      12 * negPow 2 (heatT (ε m) (ρ p.1) p.2) * (∑ j, (heatT (ε m) (fun z => N p.1 z j) p.2) ^ 2) / 4 :=
    fun m => ((hPc.measurable.comp (measurable_heatT_family h.meas)).mul
      (Finset.measurable_sum _ fun j _ => (measurable_heatT_family (ρ := fun u z => N u z j)
        (h.measN j)).pow_const 2)).div_const 4
  have hJ0m : Measurable fun p : ℝ × UnitAddTorus ι =>
      12 * negPow 2 (ρ p.1 p.2) * (∑ j, (N p.1 p.2 j) ^ 2) / 4 :=
    ((hPc.measurable.comp h.meas).mul (Finset.measurable_sum _ fun j _ =>
      (h.measN j).pow_const 2)).div_const 4
  have key : ∀ s ∈ Icc 0 T, E s ≤ c * ∫ u in Ioc 0 s, E u := by
    intro s hs
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) s)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    set Em : ℕ → ℝ := fun m => ∫ x, negPow 4 (heatT (ε m) (ρ s) x)
    set Im : ℕ → ℝ := fun m => ∫ u in Ioc 0 s, ∫ x, 12 * negPow 2 (heatT (ε m) (ρ u) x) *
      (∑ j, (heatT (ε m) (fun z => N u z j) x) ^ 2) / 4
    have hineq : ∀ m, Em m ≤ Im m := fun m => by
      have := h.energy_ineq (G := negPow 4) (Gp := fun r => 4 * negPow 3 r)
        (Gpp := fun r => 12 * negPow 2 r) hasDerivAt_G4 hasDerivAt_G4' hPc
        (fun r => by have := negPow_two_nonneg r; positivity) (hεp m) hK0 hK hs
      have h0 : ∫ x, negPow 4 (heatT (ε m) ρ₀ x) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
        refine negPow_eq_zero_of_nonneg (by norm_num) ?_
        rw [heatT_eq (hεp m) h.meas0.aestronglyMeasurable]
        exact integral_nonneg fun z => mul_nonneg (heatP_pos (hεp m) z).le (hρ₀ _)
      rw [h0, zero_add] at this
      exact this
    have hlim1 : Tendsto Em atTop (𝓝 (E s)) := by
      have hG3 : Continuous fun r => 4 * negPow 3 r := by unfold negPow; fun_prop
      obtain ⟨L, -, hL⟩ := exists_lip_on hasDerivAt_G4 hG3 K
      exact tendsto_integral_comp_of_L1 (continuous_negPow 4) hL
        (fun m => (measurable_heatT_joint (h.measurable_section s)).comp measurable_prodMk_left)
        (h.measurable_section s)
        (fun m x => abs_heatT_le (hεp m) (h.measurable_section s).aestronglyMeasurable
          (Eventually.of_forall (hK s hs)) x) (hK s hs)
        (tendsto_integral_abs_heatT_sub (h.measurable_section s) (hK s hs))
    have hlim2 : Tendsto Im atTop (𝓝 (∫ u in Ioc 0 s,
        ∫ x, 12 * negPow 2 (ρ u x) * (∑ j, (N u x j) ^ 2) / 4)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => B0)
        (fun m => (hJm m).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
        (integrable_const B0) (fun m => (ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun u hu => ?_)) ((ae_restrict_iff' measurableSet_Ioc).2
            (Eventually.of_forall fun u hu => ?_))
      · have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const B0) (Eventually.of_forall fun x => ?_)).trans (by simp)
        exact abs_P_S_le hK0 ha (abs_heatT_le (hεp m) (h.measurable_section u).aestronglyMeasurable
          (Eventually.of_forall (hK u hu')) x) fun j => abs_heatT_le (hεp m)
            (h.measurable_sectionN u j).aestronglyMeasurable
            (Eventually.of_forall fun z => h.abs_N_le hK hu' z j) x
      · exact h.tendsto_flux_term hK0 hK ⟨hu.1.le, hu.2.trans hs.2⟩
    have hEle := le_of_tendsto_of_tendsto' hlim1 hlim2 hineq
    refine hEle.trans ?_
    rw [← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun u hu => ?_
    · refine (integrable_const B0).mono' hJ0m.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
      have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
      rw [Real.norm_eq_abs]
      refine (abs_integral_le_integral_abs).trans ?_
      refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_const B0) (Eventually.of_forall fun x => ?_)).trans (by simp)
      exact abs_P_S_le hK0 ha (hK u hu' x) fun j => h.abs_N_le hK hu' x j
    · exact ((integrable_const (K ^ 4)).mono' hEm.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hE0 u)]
          exact hEM u ⟨hu.1.le, hu.2.trans hs.2⟩))).const_mul c
    · have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
      rw [← integral_const_mul]
      refine integral_mono (appA_integrable_of_abs_le' (hJ0m.comp measurable_prodMk_left)
        fun x => abs_P_S_le hK0 ha (hK u hu' x) fun j => h.abs_N_le hK hu' x j)
        ((appA_integrable_of_abs_le' ((continuous_negPow 4).measurable.comp (h.measurable_section u))
          (C := K ^ 4) fun x => by
            show |negPow 4 (ρ u x)| ≤ K ^ 4
            rw [abs_of_nonneg (negPow_four_nonneg _)]; exact negPow_four_le (hK u hu' x)).const_mul c)
        fun x => ?_
      have hN2 : ∑ j, (N u x j) ^ 2 ≤ Fintype.card ι * (A ^ 2 * (ρ u x) ^ 2) := by
        calc ∑ j, (N u x j) ^ 2 ≤ ∑ _j : ι, A ^ 2 * (ρ u x) ^ 2 := Finset.sum_le_sum fun j _ => by
              calc N u x j ^ 2 = |N u x j| ^ 2 := (sq_abs _).symm
                _ ≤ (A * |ρ u x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h.flux u hu'.1 x j) 2
                _ = A ^ 2 * ρ u x ^ 2 := by rw [mul_pow, sq_abs]
          _ = _ := by simp
      show 12 * negPow 2 (ρ u x) * (∑ j, (N u x j) ^ 2) / 4 ≤ c * negPow 4 (ρ u x)
      rw [← negPow_two_mul_sq]
      have hP0 := negPow_two_nonneg (ρ u x)
      calc 12 * negPow 2 (ρ u x) * (∑ j, (N u x j) ^ 2) / 4
          ≤ 12 * negPow 2 (ρ u x) * (Fintype.card ι * (A ^ 2 * (ρ u x) ^ 2)) / 4 := by gcongr
        _ = c * (negPow 2 (ρ u x) * ρ u x ^ 2) := by simp only [hc]; ring
  have hzero := gronwall_zero hc0 hEm (fun u _ => hE0 u) hEM key t ⟨ht, le_rfl⟩
  have hint : Integrable fun x => negPow 4 (ρ t x) :=
    appA_integrable_of_abs_le' ((continuous_negPow 4).measurable.comp (h.measurable_section t))
      (C := K ^ 4) fun x => by
        show |negPow 4 (ρ t x)| ≤ K ^ 4
        rw [abs_of_nonneg (negPow_four_nonneg _)]; exact negPow_four_le (hK t ⟨ht, le_rfl⟩ x)
  have := (integral_eq_zero_iff_of_nonneg (fun x => negPow_four_nonneg _) hint).1 hzero
  filter_upwards [this] with x hx
  exact nonneg_of_negPow_four_eq_zero hx

end LinMild

end SharpLSI
