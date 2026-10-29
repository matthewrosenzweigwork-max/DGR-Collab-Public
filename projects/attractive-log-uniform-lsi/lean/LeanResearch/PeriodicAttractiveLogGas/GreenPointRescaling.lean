import LeanResearch.PeriodicAttractiveLogGas.PointWeightDensity
import LeanResearch.PeriodicAttractiveLogGas.RectangleDilation
import LeanResearch.PeriodicAttractiveLogGas.KernelLemma

/-! Actual Green rescaling and normalized point weights in reference coordinates.
The later mesh proof supplies the compatible source lifts and the far-field
oscillation. Kernel bounds here are the earlier kernel lemma's conclusions. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.GreenPointRescaling

open PointWeightDensity SingularRectangleMoments

variable {ι : Type*} [Fintype ι]

def chart (a : PlanarSpace) (J : ℝ) (Z : PlanarSpace) : Torus :=
  torusQuotient (RectangleDilation.affine a J Z)

theorem chart_sub (a Z Y : PlanarSpace) (J : ℝ) :
    chart a J Z - chart a J Y = torusQuotient (J⁻¹ • (Z - Y)) := by
  rw [chart, chart, ← torusQuotient_sub]
  congr 1
  simp only [RectangleDilation.affine, smul_sub]
  abel

def logRemainder (J : ℝ) (Y Z : PlanarSpace) : ℝ :=
  regularGreenRepresentative (torusQuotient (J⁻¹ • (Z - Y))) - Real.log J + Real.log ‖Z - Y‖

theorem measurable_logRemainder (J : ℝ) (Y : PlanarSpace) : Measurable (logRemainder J Y) := by
  unfold logRemainder
  apply Measurable.add
  · apply Measurable.sub _ measurable_const
    apply regularGreenRepresentative_measurable.comp
    have hq : Continuous torusQuotient := by unfold torusQuotient; fun_prop
    exact hq.measurable.comp (show Continuous (fun Z : PlanarSpace ↦ J⁻¹ • (Z - Y)) by fun_prop).measurable
  · exact ((continuous_id.sub continuous_const).norm.measurable).log

/-- Exact logarithmic rescaling off the pole in the half-period Euclidean chart. -/
theorem abs_logRemainder_le {C₀ J D : ℝ} (hJ : 0 < J) (hDJ : D < J / 2)
    (hb : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    {Y Z : PlanarSpace} (hne : Z ≠ Y) (hd : ‖Z - Y‖ ≤ D) :
    |logRemainder J Y Z| ≤ C₀ := by
  have hn0 : 0 < ‖Z - Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hn : ‖J⁻¹ • (Z - Y)‖ = ‖Z - Y‖ / J := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJ), div_eq_mul_inv, mul_comm]
  have hsmall : ‖J⁻¹ • (Z - Y)‖ < (1 / 2 : ℝ) := by
    rw [hn]
    apply (div_lt_iff₀ hJ).mpr
    linarith
  have hrad := torusEuclideanNorm_quotient_eq_of_norm_lt_half hsmall
  rw [hn] at hrad
  have hq : torusQuotient (J⁻¹ • (Z - Y)) ≠ 0 := by
    intro he
    have hz : torusEuclideanNorm (torusQuotient (J⁻¹ • (Z - Y))) = 0 := by
      rw [he, torusEuclideanNorm_zero]
    rw [hrad] at hz
    exact (div_pos hn0 hJ).ne' hz
  have hlog : Real.log (torusEuclideanNorm (torusQuotient (J⁻¹ • (Z - Y)))) =
      Real.log ‖Z - Y‖ - Real.log J := by
    rw [hrad, Real.log_div hn0.ne' hJ.ne']
  have h := hb _ hq
  rw [hlog] at h
  convert h using 1
  congr 1
  simp only [logRemainder]
  ring

def perturbation (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (F : PlanarSpace → ℝ) (Z₀ Z : PlanarSpace) : ℝ :=
  F Z - F Z₀ + ∑ i, w i * logRemainder J (Y i) Z

def greenWeight (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (F : PlanarSpace → ℝ) (Z : PlanarSpace) : ℝ :=
  Real.exp (F Z + ∑ i, w i * regularGreenRepresentative (chart a J Z - chart a J (Y i)))

theorem measurable_perturbation (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    {F : PlanarSpace → ℝ} (hF : Measurable F) (Z₀ : PlanarSpace) :
    Measurable (perturbation J Y w F Z₀) := by
  apply (hF.sub measurable_const).add
  exact Finset.measurable_sum _ fun i _ ↦ (measurable_logRemainder J (Y i)).const_mul (w i)

theorem perturbation_bound {μ : Measure PlanarSpace} (hμ : μ ≪ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {C₀ J D ω : ℝ} (hJ : 0 < J) (hDJ : D < J / 2)
    (hb : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D) {F : PlanarSpace → ℝ} (Z₀ : PlanarSpace)
    (hF : ∀ᵐ Z ∂μ, |F Z - F Z₀| ≤ ω) :
    ∀ᵐ Z ∂μ, |perturbation J Y w F Z₀ Z| ≤ ω + (∑ i, w i) * C₀ := by
  filter_upwards [hd, hF, ae_avoid_poles hμ Y] with Z hZ hFZ hne
  calc
    _ ≤ |F Z - F Z₀| + |∑ i, w i * logRemainder J (Y i) Z| := abs_add_le _ _
    _ ≤ ω + ∑ i, |w i * logRemainder J (Y i) Z| :=
      add_le_add hFZ (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ω + ∑ i, w i * C₀ := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (abs_logRemainder_le hJ hDJ hb (hne i) (hZ i)) (hw i)
    _ = _ := by rw [Finset.sum_mul]

/-- The original Green exponential differs from the singular product by a
positive constant. The equality is intentionally asserted only off the poles. -/
theorem greenWeight_factor (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (F : PlanarSpace → ℝ) (Z₀ Z : PlanarSpace) (hne : ∀ i, Z ≠ Y i) :
    greenWeight a J Y w F Z = Real.exp ((∑ i, w i) * Real.log J + F Z₀) *
      perturbedWeight Y w (perturbation J Y w F Z₀) Z := by
  have hp : poleProduct Y w Z = Real.exp (∑ i, (-w i) * Real.log ‖Z - Y i‖) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [inverseDistancePower, Real.rpow_def_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne i)))]
    congr 1
    ring
  rw [perturbedWeight, hp, ← Real.exp_add, ← Real.exp_add]
  unfold greenWeight perturbation logRemainder
  simp only [chart_sub]
  congr 1
  simp only [Finset.sum_mul, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Normalization for the actual Green weight, once the source's geometric
distance and far-field oscillation bounds have been established. -/
theorem greenWeight_normalized_bounds {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (a : PlanarSpace) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i ≤ 1 / 4)
    {C₀ J D ω : ℝ} (hC₀ : 0 ≤ C₀) (hJ : 0 < J) (hD : 1 ≤ D) (hDJ : D < J / 2)
    (hb : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D)
    {F : PlanarSpace → ℝ} (hFm : Measurable F) (Z₀ : PlanarSpace)
    (hF : ∀ᵐ Z ∂μ, |F Z - F Z₀| ≤ ω) :
    Integrable (greenWeight a J Y w F) μ ∧
      0 < (∫ Z, greenWeight a J Y w F Z ∂μ) ∧
      IsProbabilityMeasure (μ.withDensity (fun Z ↦
        ENNReal.ofReal (normalizedDensity μ (greenWeight a J Y w F) Z))) ∧
      MemLp (normalizedDensity μ (greenWeight a J Y w F)) 4 μ ∧
      (∀ᵐ Z ∂μ, sourceLowerConstant D ω C₀ ≤ normalizedDensity μ (greenWeight a J Y w F) Z) ∧
      lpNorm (normalizedDensity μ (greenWeight a J Y w F)) 4 μ ≤ sourceNormConstant D ω C₀ := by
  have hH := perturbation_bound hμ.absolutelyContinuous Y w hw hJ hDJ hb hd Z₀ hF
  have h := source_normalized_bounds hμ Y w hw hκ (measurable_perturbation J Y w hFm Z₀)
    hC₀ hH hD hd
  let c := Real.exp ((∑ i, w i) * Real.log J + F Z₀)
  have hc : 0 < c := Real.exp_pos _
  have he : greenWeight a J Y w F =ᵐ[μ]
      (fun Z ↦ c * perturbedWeight Y w (perturbation J Y w F Z₀) Z) := by
    filter_upwards [ae_avoid_poles hμ.absolutelyContinuous Y] with Z hZ
    exact greenWeight_factor a J Y w F Z₀ Z hZ
  have hG : Integrable (perturbedWeight Y w (perturbation J Y w F Z₀)) μ :=
    (weight_bounds hμ Y w hw hκ (measurable_perturbation J Y w hFm Z₀)
      hH hD hd).1.integrable (by norm_num)
  have hi : Integrable (greenWeight a J Y w F) μ := (hG.const_mul c).congr he.symm
  have hz : 0 < ∫ Z, greenWeight a J Y w F Z ∂μ := by
    rw [integral_congr_ae he, integral_const_mul]
    exact mul_pos hc h.1
  have he' := normalizedDensity_congr_ae he
  rw [normalizedDensity_const_mul μ _ hc.ne'] at he'
  refine ⟨hi, hz, normalizedDensity_probability hi (fun Z ↦ (Real.exp_pos _).le) hz,
    (memLp_congr_ae he').mpr h.2.2.1, ?_, ?_⟩
  · filter_upwards [h.2.2.2.1, he'] with Z hZ hEq
    simpa only [hEq] using hZ
  · change (eLpNorm _ 4 μ).toReal ≤ _
    rw [eLpNorm_congr_ae he']
    exact h.2.2.2.2

end PeriodicAttractiveLogGas.GreenPointRescaling
