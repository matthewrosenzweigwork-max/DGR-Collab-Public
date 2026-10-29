import DGPS.FiniteN.Tools.VonMises
import DGPS.Analysis.OneDimensionalHardy
import DGPS.Circle.AngularNormalization
import DGPS.Analysis.LSITensorization
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.Foundations.PeriodicSmoothing
import DGPS.FiniteN.Tools.BoundedComparison

open MeasureTheory Real Set Topology
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.Tools.UniformVonMises

/-- The open interval `(-π, π)` carrying the von Mises law. -/
def vmI : Set ℝ := Ioo (-π) π

lemma vmI_ordConnected : vmI.OrdConnected := ordConnected_Ioo
lemma vmI_open : IsOpen vmI := isOpen_Ioo

lemma vm_cont (r : ℝ) : Continuous (vonMisesDensity r) := by
  unfold vonMisesDensity; fun_prop

lemma vm_pos (r θ : ℝ) : 0 < vonMisesDensity r θ :=
  div_pos (exp_pos _) (vonMisesZ_pos r)

lemma vm_even (r θ : ℝ) : vonMisesDensity r (-θ) = vonMisesDensity r θ := by
  simp [vonMisesDensity]

lemma vm_integral_one (r : ℝ) : ∫ t in (-π)..π, vonMisesDensity r t = 1 := by
  unfold vonMisesDensity
  rw [intervalIntegral.integral_div]
  exact div_self (vonMisesZ_pos r).ne'

/-- the von Mises law on `(-π, π)` -/
noncomputable abbrev vmMeasure (r : ℝ) : Measure ℝ := densityMeasure vmI (vonMisesDensity r)

lemma vmMeasure_apply (r : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    vmMeasure r s = ∫⁻ x in s ∩ vmI, ENNReal.ofReal (vonMisesDensity r x) := by
  rw [vmMeasure, densityMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

lemma vm_Ici (r : ℝ) {x : ℝ} (hx : -π ≤ x) (hxπ : x ≤ π) :
    vmMeasure r (Ici x) = ENNReal.ofReal (∫ t in x..π, vonMisesDensity r t) := by
  rw [vmMeasure_apply r measurableSet_Ici]
  have hset : Ici x ∩ vmI = Ico x π \ {-π} := by
    ext y; simp only [vmI, mem_inter_iff, mem_Ici, mem_Ioo, mem_Ico, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, by intro h; linarith⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, lt_of_le_of_ne (hx.trans h1) (Ne.symm h2), h3⟩
  have hae : Ici x ∩ vmI =ᵐ[volume] Ioo x π := by
    rw [hset]
    exact (sdiff_null_ae_eq_self (by simp)).trans Ioo_ae_eq_Ico.symm
  rw [setLIntegral_congr hae]
  have hint : IntegrableOn (vonMisesDensity r) (Ioo x π) volume :=
    ((vm_cont r).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint, intervalIntegral.integral_of_le hxπ,
    integral_Ioc_eq_integral_Ioo]
  exact (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t _ => (vm_pos r t).le)

lemma vm_Iic (r : ℝ) {x : ℝ} (hx : -π ≤ x) (hxπ : x ≤ π) :
    vmMeasure r (Iic x) = ENNReal.ofReal (∫ t in (-π)..x, vonMisesDensity r t) := by
  rw [vmMeasure_apply r measurableSet_Iic]
  have hset : Iic x ∩ vmI = Ioc (-π) x \ {π} := by
    ext y; simp only [vmI, mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h1⟩, by intro h; linarith⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩; exact ⟨h1, h2, lt_of_le_of_ne (h1.trans hxπ) h3⟩
  have hae : Iic x ∩ vmI =ᵐ[volume] Ioo (-π) x := by
    rw [hset]
    exact (sdiff_null_ae_eq_self (by simp)).trans Ioo_ae_eq_Ioc.symm
  rw [setLIntegral_congr hae]
  have hint : IntegrableOn (vonMisesDensity r) (Ioo (-π) x) volume :=
    ((vm_cont r).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint, intervalIntegral.integral_of_le hx,
    integral_Ioc_eq_integral_Ioo]
  exact (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t _ => (vm_pos r t).le)

lemma vm_univ (r : ℝ) : vmMeasure r univ = 1 := by
  have h := vm_Ici r (x := -π) le_rfl (by linarith [pi_pos])
  have : vmMeasure r (Ici (-π)) = vmMeasure r univ := by
    rw [vmMeasure_apply r measurableSet_Ici, vmMeasure_apply r MeasurableSet.univ]
    congr 2
    ext y; simp only [vmI, mem_inter_iff, mem_Ici, mem_univ, mem_Ioo, true_and]
    constructor
    · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨h2.le, h2, h3⟩
  rw [← this, h, vm_integral_one]; simp

instance vmMeasure_prob (r : ℝ) : IsProbabilityMeasure (vmMeasure r) := ⟨vm_univ r⟩


lemma vm_half (r : ℝ) : ∫ t in (-π)..0, vonMisesDensity r t = 1 / 2 ∧
    ∫ t in (0 : ℝ)..π, vonMisesDensity r t = 1 / 2 := by
  have hc := vm_cont r
  have h1 : ∫ t in (-π)..0, vonMisesDensity r t = ∫ t in (0 : ℝ)..π, vonMisesDensity r t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) (vonMisesDensity r)
    simp only [vm_even, neg_zero] at this
    exact this.symm
  have h2 := intervalIntegral.integral_add_adjacent_intervals (a := -π) (b := 0) (c := π)
    (f := vonMisesDensity r) (hc.intervalIntegrable (μ := volume) _ _)
    (hc.intervalIntegrable (μ := volume) _ _)
  rw [vm_integral_one] at h2
  constructor <;> linarith

lemma vm_toReal_Ici (r : ℝ) {x : ℝ} (hx : -π ≤ x) (hxπ : x ≤ π) :
    (vmMeasure r (Ici x)).toReal = vonMisesTail r x := by
  rw [vm_Ici r hx hxπ, ENNReal.toReal_ofReal]
  · rfl
  · exact intervalIntegral.integral_nonneg hxπ fun t _ => (vm_pos r t).le

lemma vm_toReal_Iic (r : ℝ) {x : ℝ} (hx : -π ≤ x) (hxπ : x ≤ π) :
    (vmMeasure r (Iic x)).toReal = vonMisesTail r (-x) := by
  rw [vm_Iic r hx hxπ, ENNReal.toReal_ofReal]
  · unfold vonMisesTail
    have := intervalIntegral.integral_comp_neg (a := -π) (b := x) (vonMisesDensity r)
    simp only [vm_even, neg_neg] at this
    exact this
  · exact intervalIntegral.integral_nonneg hx fun t _ => (vm_pos r t).le

lemma vm_med_Iic (r : ℝ) : 1 / 2 ≤ (vmMeasure r (Iic 0)).toReal := by
  rw [vm_Iic r (by linarith [pi_pos]) pi_pos.le, ENNReal.toReal_ofReal]
  · exact (vm_half r).1.ge
  · exact intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun t _ => (vm_pos r t).le

lemma vm_med_Ici (r : ℝ) : 1 / 2 ≤ (vmMeasure r (Ici 0)).toReal := by
  rw [vm_toReal_Ici r (by linarith [pi_pos]) pi_pos.le]
  exact (vm_half r).2.ge

lemma tailLogWeight_le_two_mul {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    tailLogWeight t ≤ 2 * (t * Real.log (1 / t)) := by
  unfold tailLogWeight
  have hu : 2 ≤ 1 / t := by
    rw [le_div_iff₀ ht0]; linarith
  have h1 : Real.log (1 + 1 / t) ≤ 2 * Real.log (1 / t) := by
    have : 2 * Real.log (1 / t) = Real.log ((1 / t) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [this]
    apply Real.log_le_log (by positivity)
    nlinarith
  nlinarith

lemma tailLogWeight_le_one {t : ℝ} (ht0 : 0 < t) : tailLogWeight t ≤ 1 := by
  unfold tailLogWeight
  have h := Real.log_le_sub_one_of_pos (x := 1 + 1 / t) (by positivity)
  have : t * Real.log (1 + 1 / t) ≤ t * (1 / t) := by
    apply mul_le_mul_of_nonneg_left _ ht0.le
    linarith
  rwa [mul_one_div_cancel ht0.ne'] at this

lemma vm_inv_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (t : ℝ) :
    (vonMisesDensity r t)⁻¹ ≤ 2 * π * exp 2 := by
  unfold vonMisesDensity
  rw [inv_div]
  have hZ := vonMisesZ_le hr
  have h1 : (exp (r * cos t))⁻¹ ≤ exp 1 := by
    rw [← exp_neg]
    apply exp_le_exp.2
    nlinarith [neg_one_le_cos t, cos_le_one t]
  have h2 : exp r ≤ exp 1 := exp_le_exp.2 hr1
  have h3 : exp 1 * exp 1 = exp 2 := by rw [← exp_add]; norm_num
  have hE := exp_pos (r * cos t)
  rw [div_eq_mul_inv]
  calc vonMisesZ r * (exp (r * cos t))⁻¹ ≤ (2 * π * exp 1) * exp 1 := by
        apply mul_le_mul (hZ.trans (by gcongr)) h1 (by positivity) (by positivity)
    _ = 2 * π * exp 2 := by rw [mul_assoc, h3]

lemma vm_right_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : ℝ, 0 < x → x < π →
      tailLogWeight (vonMisesTail r x) * ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ ≤ B := by
  obtain ⟨C, hC, hCb⟩ := von_mises_half_circle_resistance_estimates
  have hp := pi_pos
  refine ⟨2 * C + 2 * π ^ 2 * exp 2, by positivity, fun r hr x hx0 hxπ => ?_⟩
  have hT0 : 0 < vonMisesTail r x := by
    unfold vonMisesTail
    exact intervalIntegral.intervalIntegral_pos_of_pos ((vm_cont r).intervalIntegrable _ _)
      (vm_pos r) hxπ
  have hW0 : 0 ≤ ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ :=
    intervalIntegral.integral_nonneg hx0.le fun t _ => (inv_pos.2 (vm_pos r t)).le
  have hTle : vonMisesTail r x ≤ 1 / 2 := by
    rw [← vm_toReal_Ici r (by linarith) hxπ.le]
    exact toReal_Ici_le_half (P := vmMeasure r) hx0 (vm_med_Iic r)
  rcases le_or_gt 1 r with h1 | h1
  · have hb := (hCb r h1).2 x hx0 hxπ
    have hinv : ∫ u in (0 : ℝ)..x, 1 / vonMisesDensity r u =
        ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ := by simp
    rw [hinv] at hb
    have := tailLogWeight_le_two_mul hT0 hTle
    calc _ ≤ 2 * (vonMisesTail r x * Real.log (1 / vonMisesTail r x)) *
          ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ := mul_le_mul_of_nonneg_right this hW0
      _ ≤ 2 * C := by nlinarith
      _ ≤ _ := by nlinarith [mul_pos (mul_pos two_pos (pow_pos hp 2)) (exp_pos 2)]
  · have hW : ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ ≤ π * (2 * π * exp 2) := by
      calc _ ≤ ∫ t in (0 : ℝ)..x, (2 * π * exp 2) :=
            intervalIntegral.integral_mono_on hx0.le
              (((vm_cont r).inv₀ fun t => (vm_pos r t).ne').intervalIntegrable _ _)
              intervalIntegrable_const fun t _ => vm_inv_le hr h1.le t
        _ = x * (2 * π * exp 2) := by simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        _ ≤ _ := by gcongr
    have h1' := tailLogWeight_le_one hT0
    calc _ ≤ 1 * ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ :=
          mul_le_mul_of_nonneg_right h1' hW0
      _ ≤ _ := by nlinarith [mul_pos hC (exp_pos 2), mul_pos (pow_pos hp 2) (exp_pos 2)]


lemma vm_left_eq {r x : ℝ} (hx : -π ≤ x) (hx0 : x ≤ 0) :
    tailLogWeight (vmMeasure r (Iic x)).toReal * ∫ t in x..0, (vonMisesDensity r t)⁻¹ =
      tailLogWeight (vonMisesTail r (-x)) * ∫ t in (0 : ℝ)..(-x), (vonMisesDensity r t)⁻¹ := by
  rw [vm_toReal_Iic r hx (hx0.trans pi_pos.le)]
  congr 1
  have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -x) (fun t => (vonMisesDensity r t)⁻¹)
  simp only [vm_even, neg_neg, neg_zero] at this
  exact this.symm

lemma vm_logres_bounds : ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 ≤ r →
    BddAbove ((fun x => tailLogWeight (vmMeasure r (Ici x)).toReal *
      ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹) '' (vmI ∩ Ioi 0)) ∧
    BddAbove ((fun x => tailLogWeight (vmMeasure r (Iic x)).toReal *
      ∫ t in x..0, (vonMisesDensity r t)⁻¹) '' (vmI ∩ Iio 0)) ∧
    max (rightLogResistanceConstant vmI (vonMisesDensity r) 0)
      (leftLogResistanceConstant vmI (vonMisesDensity r) 0) ≤ B := by
  obtain ⟨B, hB, hb⟩ := vm_right_bound
  refine ⟨B, hB, fun r hr => ?_⟩
  have hR : ∀ x ∈ vmI ∩ Ioi (0 : ℝ), tailLogWeight (vmMeasure r (Ici x)).toReal *
      ∫ t in (0 : ℝ)..x, (vonMisesDensity r t)⁻¹ ≤ B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    rw [vm_toReal_Ici r h1.le h2.le]
    exact hb r hr x h3 h2
  have hL : ∀ x ∈ vmI ∩ Iio (0 : ℝ), tailLogWeight (vmMeasure r (Iic x)).toReal *
      ∫ t in x..0, (vonMisesDensity r t)⁻¹ ≤ B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    rw [vm_left_eq h1.le h3.le]
    have h4 := mem_Iio.1 h3
    exact hb r hr (-x) (by linarith) (by linarith)
  refine ⟨⟨B, ?_⟩, ⟨B, ?_⟩, max_le ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hR x hx
  · rintro _ ⟨x, hx, rfl⟩; exact hL x hx
  · exact Real.sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hR x hx) hB.le
  · exact Real.sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hL x hx) hB.le

/-- Interval version of the uniform von Mises log-Sobolev inequality. -/
theorem vm_interval_lsi : ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 ≤ r → ∀ F F' : ℝ → ℝ,
    (∀ x ∈ vmI, ∀ y ∈ vmI, F y - F x = ∫ t in x..y, F' t) →
    LocallyIntegrableOn F' vmI volume →
    Integrable (fun x => F' x ^ 2) (vmMeasure r) →
    homogeneousEntropy (vmMeasure r) (fun x => F x ^ 2) ≤
      ENNReal.ofReal (K * ∫ x, F' x ^ 2 ∂(vmMeasure r)) := by
  obtain ⟨B, hB, hb⟩ := vm_logres_bounds
  refine ⟨200 * B, by positivity, fun r hr F F' hF hF' hE => ?_⟩
  obtain ⟨hBp, hBm, hmax⟩ := hb r hr
  have hmem : (0 : ℝ) ∈ vmI := ⟨by linarith [pi_pos], pi_pos⟩
  have : IsProbabilityMeasure (densityMeasure vmI (vonMisesDensity r)) := vmMeasure_prob r
  have := median_logarithmic_hardy_lsi_criterion (I := vmI) (p := vonMisesDensity r) (m := 0)
    (f := F) (f' := F') vmI_open vmI_ordConnected hmem (vm_cont r).continuousOn
    (fun x _ => vm_pos r x) (vm_med_Iic r) (vm_med_Ici r) hBp hBm hF hF' hE
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have hE0 : 0 ≤ ∫ x, F' x ^ 2 ∂(densityMeasure vmI (vonMisesDensity r)) :=
    integral_nonneg fun x => sq_nonneg _
  have h := mul_le_mul_of_nonneg_right hmax hE0
  change 200 * _ * _ ≤ 200 * B * _
  nlinarith


/-! ### Angular von Mises law -/

open DGPS.Circle.AngularNormalization

/-- The phase `w · (cos θ, sin θ)` on the angular circle. -/
noncomputable def vmPhase (w : EuclideanSpace ℝ (Fin 2)) (θ : AngCircle) : ℝ :=
  w 0 * ((AddCircle.toCircle θ : Circle) : ℂ).re + w 1 * ((AddCircle.toCircle θ : Circle) : ℂ).im

lemma vmPhase_coe (w : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    vmPhase w (t : AngCircle) = w 0 * cos t + w 1 * sin t := by
  have h : ((AddCircle.toCircle (t : AngCircle) : Circle) : ℂ) = Complex.exp (t * Complex.I) := by
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 2
    field_simp
  unfold vmPhase
  rw [h, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

lemma continuous_vmPhase (w : EuclideanSpace ℝ (Fin 2)) : Continuous (vmPhase w) := by
  unfold vmPhase
  have := AddCircle.continuous_toCircle (T := 2 * π)
  fun_prop

/-- The complex number `w₀ + i w₁`. -/
noncomputable def vmCplx (w : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨w 0, w 1⟩

/-- The modulus of `w`. -/
noncomputable def vmRadius (w : EuclideanSpace ℝ (Fin 2)) : ℝ := ‖vmCplx w‖

/-- The argument of `w`. -/
noncomputable def vmAngle (w : EuclideanSpace ℝ (Fin 2)) : ℝ := Complex.arg (vmCplx w)

lemma vmRadius_nonneg (w : EuclideanSpace ℝ (Fin 2)) : 0 ≤ vmRadius w := norm_nonneg _

lemma vmPhase_rot (w : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    vmPhase w ((vmAngle w + s : ℝ) : AngCircle) = vmRadius w * cos s := by
  rw [vmPhase_coe]
  have h0 : vmRadius w * cos (vmAngle w) = w 0 := Complex.norm_mul_cos_arg (vmCplx w)
  have h1 : vmRadius w * sin (vmAngle w) = w 1 := Complex.norm_mul_sin_arg (vmCplx w)
  rw [← h0, ← h1]
  have : cos s = cos (vmAngle w + s - vmAngle w) := by ring_nf
  rw [this, cos_sub]
  ring

/-- The normalizing constant `∫ e^{w·(cos θ, sin θ)} dθ/(2π)`. -/
noncomputable def vmNorm (w : EuclideanSpace ℝ (Fin 2)) : ℝ := ∫ θ, exp (vmPhase w θ) ∂angHaar

/-- The von Mises law `q_w(dθ) ∝ exp(w·(cos θ, sin θ)) dθ/(2π)` on the angular circle. -/
noncomputable def vmLaw (w : EuclideanSpace ℝ (Fin 2)) : Measure AngCircle :=
  angHaar.withDensity fun θ => ENNReal.ofReal (exp (vmPhase w θ) / vmNorm w)

lemma lintegral_angHaar_rot (φ : ℝ) (h : AngCircle → ENNReal) :
    ∫⁻ θ, h θ ∂angHaar = (ENNReal.ofReal (2 * π))⁻¹ * ∫⁻ s in Ioc (-π) π, h ((φ + s : ℝ) : AngCircle) := by
  have h1 := AddCircle.lintegral_preimage (T := 2 * π) (φ - π) h
  have h2 : ∫⁻ b : AngCircle, h b = ENNReal.ofReal (2 * π) * ∫⁻ θ, h θ ∂angHaar := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure]
    rfl
  have h3 : ∫⁻ a in Ioc (φ - π) (φ - π + 2 * π), h (a : AngCircle) =
      ∫⁻ s in Ioc (-π) π, h ((φ + s : ℝ) : AngCircle) := by
    have hm := (measurePreserving_add_left volume φ).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addLeft φ) (fun a : ℝ => h (a : AngCircle)) (Ioc (φ - π) (φ - π + 2 * π))
    rw [preimage_const_add_Ioc] at hm
    have e1 : φ - π - φ = -π := by ring
    have e2 : φ - π + 2 * π - φ = π := by ring
    rw [e1, e2] at hm
    exact hm.symm
  rw [h3, h2] at h1
  have hne : ENNReal.ofReal (2 * π) ≠ 0 := by simp [pi_pos]
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]


lemma periodic_deriv_aux {g : ℝ → ℝ} {c : ℝ} (h : Function.Periodic g c) :
    Function.Periodic (deriv g) c := by
  intro x
  have h1 : (fun y => g (y + c)) = g := funext h
  have := deriv_comp_add_const (f := g) (a := c) (x := x)
  rw [h1] at this
  exact this.symm

lemma angSec_coe (t : ℝ) : ∃ n : ℤ, angSec (t : AngCircle) = t + n * (2 * π) := by
  have h : ((angSec (t : AngCircle) : ℝ) : AngCircle) = (t : AngCircle) := by
    unfold angSec
    exact AddCircle.coe_equivIoc
  have h2 : ((angSec (t : AngCircle) - t : ℝ) : AngCircle) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h2
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn
  linarith

lemma angDeriv_coe {ψ : AngCircle → ℝ} (t : ℝ) :
    angDeriv ψ (t : AngCircle) = deriv (fun s : ℝ => ψ (s : AngCircle)) t := by
  obtain ⟨n, hn⟩ := angSec_coe t
  unfold angDeriv
  rw [hn]
  have hp : Function.Periodic (fun s : ℝ => ψ (s : AngCircle)) (2 * π) := by
    intro x
    simp only
    rw [AddCircle.coe_add_period]
  exact (periodic_deriv_aux hp).int_mul n t

lemma vmNorm_eq (w : EuclideanSpace ℝ (Fin 2)) :
    vmNorm w = vonMisesZ (vmRadius w) / (2 * π) := by
  have hcont : Continuous fun θ => exp (vmPhase w θ) := (Real.continuous_exp.comp (continuous_vmPhase w))
  have hl : ∫⁻ θ, ENNReal.ofReal (exp (vmPhase w θ)) ∂angHaar =
      (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (vonMisesZ (vmRadius w)) := by
    rw [lintegral_angHaar_rot (vmAngle w)]
    congr 1
    have hc : Continuous fun s : ℝ => exp (vmRadius w * cos s) := by fun_prop
    have hint : IntegrableOn (fun s : ℝ => exp (vmRadius w * cos s)) (Ioc (-π) π) volume :=
      (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    simp_rw [vmPhase_rot]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s => (exp_pos _).le),
      vonMisesZ, intervalIntegral.integral_of_le (by linarith [pi_pos])]
  unfold vmNorm
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun θ => (exp_pos _).le)
    hcont.aestronglyMeasurable, hl, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (vonMisesZ_pos _).le]
  ring

lemma vmNorm_pos (w : EuclideanSpace ℝ (Fin 2)) : 0 < vmNorm w := by
  rw [vmNorm_eq]; exact div_pos (vonMisesZ_pos _) (by positivity)

lemma vmNorm_mul (w : EuclideanSpace ℝ (Fin 2)) : 2 * π * vmNorm w = vonMisesZ (vmRadius w) := by
  rw [vmNorm_eq]; field_simp

/-- The rotation `s ↦ [arg w + s]`. -/
noncomputable def vmRot (w : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : AngCircle :=
  ((vmAngle w + s : ℝ) : AngCircle)

lemma continuous_vmRot (w : EuclideanSpace ℝ (Fin 2)) : Continuous (vmRot w) := by
  unfold vmRot; fun_prop

lemma vmMeasurePreserving (w : EuclideanSpace ℝ (Fin 2)) :
    MeasurePreserving (vmRot w) (vmMeasure (vmRadius w)) (vmLaw w) := by
  refine ⟨(continuous_vmRot w).measurable, ?_⟩
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (continuous_vmRot w).measurable hA]
  have hmeas : MeasurableSet (vmRot w ⁻¹' A) := (continuous_vmRot w).measurable hA
  have hρ : Measurable fun θ : AngCircle => ENNReal.ofReal (exp (vmPhase w θ) / vmNorm w) :=
    ((Real.continuous_exp.comp (continuous_vmPhase w)).div_const _).measurable.ennreal_ofReal
  rw [vmLaw, withDensity_apply _ hA, ← lintegral_indicator hA,
    lintegral_angHaar_rot (vmAngle w), vmMeasure_apply _ hmeas]
  have h1 : ∀ s : ℝ, A.indicator (fun θ : AngCircle => ENNReal.ofReal (exp (vmPhase w θ) / vmNorm w))
      ((vmAngle w + s : ℝ) : AngCircle) =
      (vmRot w ⁻¹' A).indicator (fun s : ℝ => ENNReal.ofReal (exp (vmRadius w * cos s) / vmNorm w)) s := by
    intro s
    by_cases hs : vmRot w s ∈ A
    · rw [indicator_of_mem (show ((vmAngle w + s : ℝ) : AngCircle) ∈ A from hs),
        indicator_of_mem (show s ∈ vmRot w ⁻¹' A from hs), vmPhase_rot]
    · rw [indicator_of_notMem (show ((vmAngle w + s : ℝ) : AngCircle) ∉ A from hs),
        indicator_of_notMem (show s ∉ vmRot w ⁻¹' A from hs)]
  simp_rw [h1]
  rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
  have hae : vmRot w ⁻¹' A ∩ Ioc (-π) π =ᵐ[volume] vmRot w ⁻¹' A ∩ vmI :=
    ae_eq_set_inter (ae_eq_refl _) Ioo_ae_eq_Ioc.symm
  rw [setLIntegral_congr hae, ← lintegral_const_mul' _ _ (by simp [pi_pos])]
  refine lintegral_congr fun s => ?_
  have hpi : 0 < 2 * π := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hpi, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have := vmNorm_mul w
  have hn := vmNorm_pos w
  have hz := vonMisesZ_pos (vmRadius w)
  unfold vonMisesDensity
  rw [← this]
  field_simp


instance vmLaw_prob (w : EuclideanSpace ℝ (Fin 2)) : IsProbabilityMeasure (vmLaw w) := by
  rw [← (vmMeasurePreserving w).map_eq]
  exact (Measure.isProbabilityMeasure_map_iff (continuous_vmRot w).measurable.aemeasurable).2 inferInstance

lemma measurable_angSec : Measurable angSec := by
  have := (AddCircle.measurableEquivIoc (2 * π) 0).measurable
  exact measurable_subtype_coe.comp this

lemma measurable_angDeriv (ψ : AngCircle → ℝ) : Measurable (angDeriv ψ) := by
  unfold angDeriv
  have hd : Measurable (deriv fun s : ℝ => ψ (s : AngCircle)) := measurable_deriv _
  exact hd.comp measurable_angSec

lemma integral_vmRot (w : EuclideanSpace ℝ (Fin 2)) {v : AngCircle → ℝ}
    (hv : AEStronglyMeasurable v (vmLaw w)) :
    ∫ s, v (vmRot w s) ∂(vmMeasure (vmRadius w)) = ∫ θ, v θ ∂(vmLaw w) := by
  have hv' : AEStronglyMeasurable v (Measure.map (vmRot w) (vmMeasure (vmRadius w))) := by
    rw [(vmMeasurePreserving w).map_eq]; exact hv
  rw [← integral_map (continuous_vmRot w).measurable.aemeasurable hv',
    (vmMeasurePreserving w).map_eq]

lemma vmMeasure_le (r : ℝ) (hr : 0 ≤ r) :
    vmMeasure r ≤ ENNReal.ofReal (exp r / vonMisesZ r) • volume.restrict vmI := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [vmMeasure_apply r hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  calc ∫⁻ x in s ∩ vmI, ENNReal.ofReal (vonMisesDensity r x)
      ≤ ∫⁻ x in s ∩ vmI, ENNReal.ofReal (exp r / vonMisesZ r) := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        unfold vonMisesDensity
        exact div_le_div_of_nonneg_right (exp_le_exp.2 (by nlinarith [cos_le_one x])) (vonMisesZ_pos r).le
    _ = _ := by rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]

lemma vm_smooth_lsi : ∃ K : ℝ, 0 < K ∧ ∀ (w : EuclideanSpace ℝ (Fin 2)) (ψ : AngCircle → ℝ),
    IsSmoothAngular ψ →
    homogeneousEntropy (vmLaw w) (fun θ => ψ θ ^ 2) ≤
      ENNReal.ofReal (K * ∫ θ, angDeriv ψ θ ^ 2 ∂(vmLaw w)) := by
  obtain ⟨K, hK, h⟩ := vm_interval_lsi
  refine ⟨K, hK, fun w ψ hψ => ?_⟩
  set F : ℝ → ℝ := fun s => ψ (vmRot w s) with hFdef
  set F' : ℝ → ℝ := fun s => angDeriv ψ (vmRot w s) with hF'def
  have hFsm : ContDiff ℝ ∞ F := by
    have : F = (fun t : ℝ => ψ (t : AngCircle)) ∘ (fun s : ℝ => vmAngle w + s) := rfl
    rw [this]; exact hψ.comp (contDiff_const.add contDiff_id)
  have hder : ∀ s, HasDerivAt F (F' s) s := by
    intro s
    have h1 : DifferentiableAt ℝ (fun t : ℝ => ψ (t : AngCircle)) (vmAngle w + s) :=
      (hψ.differentiable (by simp)).differentiableAt
    have h2 := h1.hasDerivAt.comp_const_add (vmAngle w) s
    have h3 : F' s = deriv (fun t : ℝ => ψ (t : AngCircle)) (vmAngle w + s) := angDeriv_coe _
    rw [h3]; exact h2
  have hF'eq : F' = deriv F := funext fun s => (hder s).deriv.symm
  have hF'c : Continuous F' := by
    rw [hF'eq]; exact hFsm.continuous_deriv (by simp)
  have hFFTC : ∀ x ∈ vmI, ∀ y ∈ vmI, F y - F x = ∫ t in x..y, F' t := fun x _ y _ =>
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      (hF'c.intervalIntegrable _ _)).symm
  have hr : 0 ≤ vmRadius w := vmRadius_nonneg w
  have hE : Integrable (fun x => F' x ^ 2) (vmMeasure (vmRadius w)) := by
    have h1 : IntegrableOn (fun x => F' x ^ 2) vmI volume :=
      ((hF'c.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    exact (h1.smul_measure (by simp)).mono_measure (vmMeasure_le _ hr)
  have key := h (vmRadius w) hr F F' hFFTC (hF'c.locallyIntegrable.locallyIntegrableOn _) hE
  have hmP : AEStronglyMeasurable (fun θ => ψ θ ^ 2) (vmLaw w) := by
    have : Measurable ψ := by
      have h1 : ψ = (fun s : ℝ => ψ (s : AngCircle)) ∘ angSec := by
        funext θ; simp only [Function.comp]; unfold angSec; rw [AddCircle.coe_equivIoc]
      rw [h1]; exact hψ.continuous.measurable.comp measurable_angSec
    exact (this.pow_const 2).aestronglyMeasurable
  rw [← integral_vmRot w (v := fun θ => angDeriv ψ θ ^ 2)
    ((measurable_angDeriv ψ).pow_const 2).aestronglyMeasurable]
  rw [← DGPS.Analysis.homogeneousEntropy_comp_measurePreserving (vmMeasurePreserving w) hmP]
  exact key


lemma vmPhase_le (w : EuclideanSpace ℝ (Fin 2)) (θ : AngCircle) : vmPhase w θ ≤ vmRadius w := by
  have h := vmPhase_rot w (angSec θ - vmAngle w)
  rw [add_sub_cancel] at h
  have hθ : ((angSec θ : ℝ) : AngCircle) = θ := by unfold angSec; exact AddCircle.coe_equivIoc
  rw [hθ] at h
  rw [h]
  exact mul_le_of_le_one_right (vmRadius_nonneg w) (cos_le_one _)

lemma vmLaw_le (w : EuclideanSpace ℝ (Fin 2)) :
    vmLaw w ≤ ENNReal.ofReal (exp (vmRadius w) / vmNorm w) • angHaar := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [vmLaw, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ θ in s, ENNReal.ofReal (exp (vmPhase w θ) / vmNorm w) ∂angHaar
      ≤ ∫⁻ θ in s, ENNReal.ofReal (exp (vmRadius w) / vmNorm w) ∂angHaar :=
        lintegral_mono fun θ => ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (exp_le_exp.2 (vmPhase_le w θ)) (vmNorm_pos w).le)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

lemma eLpNorm_vm_le (w : EuclideanSpace ℝ (Fin 2)) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ h : AngCircle → ℝ, AEStronglyMeasurable h angHaar →
      eLpNorm h 2 (vmLaw w) ≤ c * eLpNorm h 2 angHaar := by
  refine ⟨ENNReal.ofReal (exp (vmRadius w) / vmNorm w) ^ (1 / (2 : ℝ≥0∞)).toReal,
    ENNReal.rpow_ne_top_of_nonneg (by simp) ENNReal.ofReal_ne_top, fun h hh => ?_⟩
  refine (eLpNorm_mono_measure h (vmLaw_le w)).trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by simp) h _ hh, smul_eq_mul]

lemma smooth_isWeakDeriv {ψ : AngCircle → ℝ} (hψ : IsSmoothAngular ψ) :
    IsAngularWeakDeriv ψ (angDeriv ψ) := by
  rw [isWeakGradient_comp_iff]
  have h := ((isSmoothPeriodic_comp_iff ψ).2 hψ).isWeakGradient
  have : smoothGrad (ψ ∘ angEquiv) = physGrad (angDeriv ψ) := by
    funext x; ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [smoothGrad_apply, physGrad_apply, coordPartial_comp_angEquiv hψ]
  rwa [this] at h

lemma vm_h1_lsi : ∃ K : ℝ, 0 < K ∧ ∀ (w : EuclideanSpace ℝ (Fin 2)) (f g : AngCircle → ℝ),
    IsAngularWeakDeriv f g →
    homogeneousEntropy (vmLaw w) (fun θ => f θ ^ 2) ≤
      ENNReal.ofReal (K * ∫ θ, g θ ^ 2 ∂(vmLaw w)) := by
  obtain ⟨K, hK, hs⟩ := vm_smooth_lsi
  refine ⟨K, hK, fun w f g hg => ?_⟩
  obtain ⟨c, hc, hcle⟩ := eLpNorm_vm_le w
  have hgr := (isWeakGradient_comp_iff f g).1 hg
  obtain ⟨v, hvs, -, hv1, hv2⟩ := exists_smooth_tendsto_H1 hgr
  set ψ : ℕ → AngCircle → ℝ := fun n => v n ∘ angEquiv.symm with hψdef
  have hψc : ∀ n, ψ n ∘ angEquiv = v n := fun n => by funext x; simp [hψdef]
  have hψs : ∀ n, IsSmoothAngular (ψ n) := fun n => by
    rw [← isSmoothPeriodic_comp_iff, hψc]; exact hvs n
  have hψw := fun n => smooth_isWeakDeriv (hψs n)
  have hc1 : Filter.Tendsto (fun n => eLpNorm (ψ n - f) 2 angHaar) Filter.atTop (𝓝 0) := by
    have : ∀ n, eLpNorm (ψ n - f) 2 angHaar =
        eLpNorm (fun x => v n x - (f ∘ angEquiv) x) 2 (haar 1) := by
      intro n
      rw [← eLpNorm_comp_measurePreserving ((hψw n).memLp.sub hg.memLp).aestronglyMeasurable
        measurePreserving_angEquiv]
      congr 1
      funext x
      have := congrFun (hψc n) x
      simp only [Function.comp_apply, Pi.sub_apply] at this ⊢
      rw [this]
    simp_rw [this]
    exact hv1
  have hc2 : Filter.Tendsto (fun n => eLpNorm (angDeriv (ψ n) - g) 2 angHaar) Filter.atTop (𝓝 0) := by
    have : ∀ n, eLpNorm (angDeriv (ψ n) - g) 2 angHaar =
        ‖(2 * π)⁻¹‖ₑ * eLpNorm (fun x => smoothGrad (v n) x 0 - physGrad g x 0) 2 (haar 1) := by
      intro n
      rw [← eLpNorm_comp_measurePreserving
        ((hψw n).memLp_deriv.sub hg.memLp_deriv).aestronglyMeasurable measurePreserving_angEquiv,
        ← eLpNorm_const_smul]
      congr 1
      funext x
      have e := coordPartial_comp_angEquiv (hψs n) x
      rw [hψc n] at e
      simp only [Function.comp_apply, Pi.sub_apply, smoothGrad_apply, physGrad_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [e]
      field_simp
    simp_rw [this]
    have := ENNReal.Tendsto.const_mul (hv2 0) (Or.inr (enorm_ne_top : ‖(2 * π)⁻¹‖ₑ ≠ ⊤))
    simpa using this
  have trans : ∀ (u : ℕ → AngCircle → ℝ) (h : AngCircle → ℝ),
      (∀ n, AEStronglyMeasurable (u n) angHaar) → AEStronglyMeasurable h angHaar →
      Filter.Tendsto (fun n => eLpNorm (u n - h) 2 angHaar) Filter.atTop (𝓝 0) →
      Filter.Tendsto (fun n => eLpNorm (u n - h) 2 (vmLaw w)) Filter.atTop (𝓝 0) := by
    intro u h hu hh ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
      (fun n => hcle _ ((hu n).sub hh))
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr hc)
  have memP : ∀ h : AngCircle → ℝ, MemLp h 2 angHaar → MemLp h 2 (vmLaw w) := fun h hh =>
    (hcle h hh.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top hc.lt_top hh)
  have hmP := fun n => memP _ (hψw n).memLp
  have hdmP := fun n => memP _ (hψw n).memLp_deriv
  have hfP := memP _ hg.memLp
  have hgP := memP _ hg.memLp_deriv
  have t1 := trans ψ f (fun n => (hψw n).memLp.aestronglyMeasurable)
    hg.memLp.aestronglyMeasurable hc1
  have t2 := trans (fun n => angDeriv (ψ n)) g (fun n => (hψw n).memLp_deriv.aestronglyMeasurable)
    hg.memLp_deriv.aestronglyMeasurable hc2
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero t1).exists_seq_tendsto_ae
  refine DGPS.FiniteN.Tools.WeightedSobolev.homogeneousEntropy_le_of_tendsto
    (v := fun k y => ψ (ns k) y ^ 2)
    (b := fun k => ENNReal.ofReal (K * ∫ θ, angDeriv (ψ (ns k)) θ ^ 2 ∂(vmLaw w)))
    (B := ENNReal.ofReal (K * ∫ θ, g θ ^ 2 ∂(vmLaw w)))
    (fun k => ((hmP (ns k)).aestronglyMeasurable.aemeasurable.pow_const 2)) ?_ ?_
    (integral_nonneg fun y => sq_nonneg _) ?_ (fun k => hs w _ (hψs _))
  · filter_upwards [hae] with y hy using hy.pow 2
  · exact (DGPS.FiniteN.Tools.WeightedSobolev.tendsto_integral_sq_of_tendsto_eLpNorm hmP hfP
      t1).comp hns.tendsto_atTop
  · have := (DGPS.FiniteN.Tools.WeightedSobolev.tendsto_integral_sq_of_tendsto_eLpNorm hdmP hgP
      t2).comp hns.tendsto_atTop
    exact (ENNReal.continuous_ofReal.tendsto _).comp (this.const_mul K)


/-- `L²(angHaar)` functions are `L²` for the von Mises law. -/
lemma memLp_vmLaw (w : EuclideanSpace ℝ (Fin 2)) {g : AngCircle → ℝ} (hg : MemLp g 2 angHaar) :
    MemLp g 2 (vmLaw w) := by
  obtain ⟨c, hc, hle⟩ := eLpNorm_vm_le w
  exact lt_of_le_of_lt (hle g hg.aestronglyMeasurable) (ENNReal.mul_lt_top hc.lt_top hg)

open Classical in
/-- A chosen weak angular derivative of an `H¹` function (and `0` otherwise). -/
noncomputable def vmGrad (f : AngCircle → ℝ) : AngCircle → ℝ :=
  if h : AngularH1 f then Classical.choose h else 0

/-- The carre-du-champ `θ ↦ |f′(θ)|²` along the chosen weak derivative. -/
noncomputable def vmGamma (f : AngCircle → ℝ) (θ : AngCircle) : ℝ≥0∞ :=
  ENNReal.ofReal (vmGrad f θ ^ 2)

lemma vmGrad_spec {f : AngCircle → ℝ} (hf : AngularH1 f) : IsAngularWeakDeriv f (vmGrad f) := by
  unfold vmGrad
  simp only [hf, dite_true]
  exact Classical.choose_spec hf

lemma lintegral_vmGamma (w : EuclideanSpace ℝ (Fin 2)) {f : AngCircle → ℝ} (hf : AngularH1 f) :
    ∫⁻ θ, vmGamma f θ ∂vmLaw w = ENNReal.ofReal (∫ θ, vmGrad f θ ^ 2 ∂vmLaw w) := by
  have hm := memLp_vmLaw w (vmGrad_spec hf).memLp_deriv
  rw [ofReal_integral_eq_lintegral_ofReal hm.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
  rfl

lemma logSobolevAt_vmLaw {K : ℝ} (hK : 0 < K)
    (h : ∀ (w : EuclideanSpace ℝ (Fin 2)) (f g : AngCircle → ℝ), IsAngularWeakDeriv f g →
      homogeneousEntropy (vmLaw w) (fun θ => f θ ^ 2) ≤
        ENNReal.ofReal (K * ∫ θ, g θ ^ 2 ∂(vmLaw w)))
    (w : EuclideanSpace ℝ (Fin 2)) :
    DGPS.FiniteN.Tools.BoundedComparison.LogSobolevAt (vmLaw w) AngularH1 vmGamma K := by
  intro f hf
  refine (h w f _ (vmGrad_spec hf)).trans ?_
  rw [lintegral_vmGamma w hf, ENNReal.ofReal_mul hK.le]

end DGPS.FiniteN.Tools.UniformVonMises

namespace DGPS.FiniteN

open MeasureTheory
open DGPS.Circle.AngularNormalization
open DGPS.FiniteN.Tools.UniformVonMises
open DGPS.FiniteN.Tools.BoundedComparison

/-- FIN009: uniform one-site von Mises log-Sobolev inequality, with the same constant `2/γ` for
every field `w` and every tensor power (angular coordinates). -/
theorem uniform_one_site_von_mises_lsi :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ (w : EuclideanSpace ℝ (Fin 2)) (f g : AngCircle → ℝ), IsAngularWeakDeriv f g →
        homogeneousEntropy (vmLaw w) (fun θ => f θ ^ 2) ≤
          ENNReal.ofReal (2 / γ * ∫ θ, g θ ^ 2 ∂(vmLaw w))) ∧
      (∀ (n : ℕ) (w : Fin n → EuclideanSpace ℝ (Fin 2)) (F : (Fin n → AngCircle) → ℝ),
        TP AngularH1 vmGamma (fun i => vmLaw (w i)) F →
        homogeneousEntropy (Measure.pi fun i => vmLaw (w i)) (fun x => F x ^ 2) ≤
          ENNReal.ofReal (2 / γ) *
            ∫⁻ x, ∑ i, vmGamma (slice i F x) (x i) ∂Measure.pi fun i => vmLaw (w i)) := by
  obtain ⟨K, hK, h⟩ := vm_h1_lsi
  have hγ : 2 / (2 / K) = K := by field_simp
  refine ⟨2 / K, by positivity, ?_, ?_⟩
  · intro w f g hfg
    rw [hγ]
    exact h w f g hfg
  · intro n w F hF
    rw [hγ]
    exact logSobolev_tensorization (fun i => vmLaw (w i))
      (fun i => logSobolevAt_vmLaw hK h (w i)) F hF

end DGPS.FiniteN
