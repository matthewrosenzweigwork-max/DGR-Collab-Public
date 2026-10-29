import LeanResearch.PeriodicAttractiveLogGas.ResolutionCutoffs
import LeanResearch.PeriodicAttractiveLogGas.CrudeEntropyIntegrated
import LeanResearch.PeriodicAttractiveLogGas.GlobalPoincare

/-! Physical energy estimates for the successive cutoffs in Theorem 7.5.
The preceding-mesh heavy estimate pays for the next cutoff. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.ResolutionEnergy
open ResolutionCutoffs SquaredLocalization HeavyLocalization HeavyScales
  HeavyCoercivityConstants SeparatedRadius ConditionalLawEstimates SmoothOccupations

/-- The unscaled physical energy, as an integral of the actual gradient. -/
def energy {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ)) : ℝ :=
  ∫ X, ‖descendedLiftGradient f X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β

def squareIntegral {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ)) : ℝ :=
  ∫ X, f X ^ 2 ∂gibbsMeasure greenRealRepresentative N β

theorem energy_nonneg {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ)) : 0 ≤ energy β f :=
  integral_nonneg fun X => sq_nonneg _
theorem squareIntegral_nonneg {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ)) : 0 ≤ squareIntegral β f :=
  integral_nonneg fun X => sq_nonneg _

def cost {N : ℕ} (β : ℝ) (f θ : C(Configuration N, ℝ)) : ℝ :=
  ∫ X, f X ^ 2 * ‖descendedLiftGradient θ X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β

theorem integrable_cost {N : ℕ} (β : ℝ) (f θ : C(Configuration N, ℝ))
    {L : ℝ≥0} (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    Integrable (fun X => f X ^ 2 * ‖descendedLiftGradient θ X‖ ^ 2)
      (gibbsMeasure greenRealRepresentative N β) := by
  apply (integrable_sq_norm_descendedLiftGradient _ θ hθ).bdd_mul
    (f.continuous.measurable.pow_const 2).aestronglyMeasurable
  filter_upwards [] with X
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm X) 2

theorem cost_nonneg {N : ℕ} (β : ℝ) (f θ : C(Configuration N, ℝ)) : 0 ≤ cost β f θ :=
  integral_nonneg fun X => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem cost_angle_le (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (β : ℝ) (f : C(Configuration N, ℝ)) :
    cost β f (angle N J (by omega) t) ≤
      angleConstant t * (J : ℝ) ^ 2 / N * squareIntegral β f := by
  unfold cost squareIntegral
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_cost β f _ (angle_lipschitz N J hN hJ ht))
    ((integrable_continuous_sq _ f).const_mul _)
  filter_upwards [ae_angle_gradient_sq_bound N J hN hJ ht β] with X hX
  have hb : ‖descendedLiftGradient (angle N J (by omega) t) X‖ ^ 2 ≤
      angleConstant t * (J : ℝ) ^ 2 / N := by
    apply hX.trans
    by_cases hs : X ∈ OccupationMassCutoff.transitionRegion N J (by omega) (t / 4) (t / 2)
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      exact div_nonneg (mul_nonneg (angleConstant_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
  simpa only [mul_comm (f X ^ 2)] using mul_le_mul_of_nonneg_left hb (sq_nonneg (f X))

theorem energy_split (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (β : ℝ) (f : C(Configuration N, ℝ))
    {K : ℝ≥0} (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    energy β (lightPiece N J (by omega) t f m) +
      energy β (remainder N J (by omega) t f (m + 1)) =
      energy β (remainder N J (by omega) t f m) +
        cost β (remainder N J (by omega) t f m) (refinementAngle N J (by omega) t m) := by
  obtain ⟨L, hL⟩ := remainder_lipschitz N J hN hJ ht f hf m
  exact squared_localization_integral (gibbsMeasure greenRealRepresentative N β)
    (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
    (remainder N J (by omega) t f m) (refinementAngle N J (by omega) t m) hL
    (angle_lipschitz N (mesh J m) hN (mesh_three hJ m) ht)

theorem energy_eq_physical {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ))
    {K : ℝ≥0} (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) :
    energy β f = ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X
      ∂gibbsMeasure greenRealRepresentative N β := by
  rw [GlobalPoincare.physical_energy f hf β, configurationLipschitzAmbient_energy_eq_integral]
  rfl

section Heavy
variable {N J : ℕ} {β β₀ t : ℝ}
  (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t) (ht1 : t / 4 < 1)
  (hres : sourceResolution β₀ (t / 4) ≤ J)
  (hlarge : particleThreshold β₀ (t / 4) ≤ N)
  (hβ : 0 ≤ β) (hβle : β ≤ β₀)

include hβ₀ hsub ht ht1 hres hlarge hβ hβle

theorem resolution_heavy (m : ℕ) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y)))
    (hs : ∀ X, maximumOccupation N (mesh J m)
      (mesh_pos (source_mesh_pos hres) m) X ≤ t / 4 → F X = 0) :
    squareIntegral β F ≤ coercivityConstant β₀ (t / 4) / ((mesh J m : ℝ) ^ 2 * N) * energy β F := by
  have hr : sourceResolution β₀ (t / 4) ≤ (mesh J m : ℝ) :=
    hres.trans (by exact_mod_cast base_le_mesh J m)
  have hh := HeavyCoercivity.heavy_coercivity hβ₀ hsub (by linarith : 0 < t / 4)
    ht1 hr hlarge hβ hβle F hF hs
  rw [configurationLipschitzAmbient_energy_eq_integral] at hh
  exact hh

theorem remainder_heavy (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    squareIntegral β (remainder N J (source_mesh_pos hres) t f (m + 1)) ≤
      coercivityConstant β₀ (t / 4) / ((mesh J m : ℝ) ^ 2 * N) *
        energy β (remainder N J (source_mesh_pos hres) t f (m + 1)) := by
  have hN := threshold_positive (by linarith : 0 < t / 4) hlarge
  obtain ⟨L, hL⟩ := remainder_lipschitz N J hN (source_mesh_ge_three hres) ht f hf (m + 1)
  exact resolution_heavy hβ₀ hsub ht ht1 hres hlarge hβ hβle m _ hL
    (fun X hX => remainder_succ_zero_low N J (source_mesh_pos hres) ht f m hX)

theorem lightPiece_heavy (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    squareIntegral β (lightPiece N J (source_mesh_pos hres) t f (m + 1)) ≤
      coercivityConstant β₀ (t / 4) / ((mesh J m : ℝ) ^ 2 * N) *
        energy β (lightPiece N J (source_mesh_pos hres) t f (m + 1)) := by
  have hN := threshold_positive (by linarith : 0 < t / 4) hlarge
  obtain ⟨L, hL⟩ := lightPiece_lipschitz N J hN (source_mesh_ge_three hres) ht f hf (m + 1)
  exact resolution_heavy hβ₀ hsub ht ht1 hres hlarge hβ hβle m _ hL
    (fun X hX => lightPiece_succ_zero_low N J (source_mesh_pos hres) ht f m hX)

def relativeCost (N J : ℕ) (β₀ t : ℝ) : ℝ :=
  angleConstant t * coercivityConstant β₀ (t / 4) * (J : ℝ) ^ 2 / (N : ℝ) ^ 2

theorem successive_cost_le (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    cost β (remainder N J (source_mesh_pos hres) t f (m + 1))
      (refinementAngle N J (source_mesh_pos hres) t (m + 1)) ≤
      relativeCost N J β₀ t * energy β (remainder N J (source_mesh_pos hres) t f (m + 1)) := by
  have hN := threshold_positive (by linarith : 0 < t / 4) hlarge
  have hJ := source_mesh_pos hres
  have ha := cost_angle_le N (mesh J (m + 1)) hN
    (mesh_three (source_mesh_ge_three hres) (m + 1)) ht β
    (remainder N J hJ t f (m + 1))
  have hb := remainder_heavy hβ₀ hsub ht ht1 hres hlarge hβ hβle f hf m
  have hc : 0 ≤ angleConstant t * (mesh J (m + 1) : ℝ) ^ 2 / N :=
    div_nonneg (mul_nonneg (angleConstant_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
  refine ha.trans ((mul_le_mul_of_nonneg_left hb hc).trans_eq ?_)
  rw [← mul_assoc]
  congr 1
  unfold relativeCost
  rw [mesh_succ, Nat.cast_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (mesh J m : ℝ) ≠ 0 := by exact_mod_cast (mesh_pos hJ m).ne'
  field_simp [hn, hm]
  <;> ring

def initialBound {N : ℕ} (J : ℕ) (t β : ℝ) (f : C(Configuration N, ℝ)) : ℝ :=
  energy β f + angleConstant t * (J : ℝ) ^ 2 / N * squareIntegral β f

theorem initialBound_nonneg {N : ℕ} (J : ℕ) (t β : ℝ) (f : C(Configuration N, ℝ)) :
    0 ≤ initialBound J t β f :=
  add_nonneg (energy_nonneg _ _) (mul_nonneg
    (div_nonneg (mul_nonneg (angleConstant_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
    (squareIntegral_nonneg _ _))

theorem energy_pair_le (hbudget : relativeCost N J β₀ t ≤ 1)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    energy β (lightPiece N J (source_mesh_pos hres) t f m) +
      energy β (remainder N J (source_mesh_pos hres) t f (m + 1)) ≤
        (2 : ℝ) ^ m * initialBound J t β f := by
  have hN := threshold_positive (by linarith : 0 < t / 4) hlarge
  have hJ3 := source_mesh_ge_three hres
  induction m with
  | zero =>
    rw [energy_split N J hN hJ3 ht β f hf 0]
    have hc := cost_angle_le N J hN hJ3 ht β f
    simpa only [remainder_zero, refinementAngle, mesh_zero, pow_zero, one_mul, initialBound]
      using add_le_add (le_refl (energy β f)) hc
  | succ m ih =>
    rw [energy_split N J hN hJ3 ht β f hf (m + 1)]
    have hc := successive_cost_le hβ₀ hsub ht ht1 hres hlarge hβ hβle f hf m
    have he := energy_nonneg β (remainder N J (source_mesh_pos hres) t f (m + 1))
    have hl := energy_nonneg β (lightPiece N J (source_mesh_pos hres) t f m)
    have hb := mul_le_mul_of_nonneg_right hbudget he
    rw [one_mul] at hb
    rw [pow_succ]
    nlinarith only [ih, hc, hb, hl]

theorem lightPiece_energy_le (hbudget : relativeCost N J β₀ t ≤ 1)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    energy β (lightPiece N J (source_mesh_pos hres) t f m) ≤
      (2 : ℝ) ^ m * initialBound J t β f := by
  have hh := energy_pair_le hβ₀ hsub ht ht1 hres hlarge hβ hβle hbudget f hf m
  have hn := energy_nonneg β (remainder N J (source_mesh_pos hres) t f (m + 1))
  linarith only [hh, hn]

/-- The source ceiling threshold supplies the same relative-cost bound at
all refinement levels. -/
theorem relativeCost_le_one (hceil : ⌈(J : ℝ) *
    Real.sqrt (angleConstant t * coercivityConstant β₀ (t / 4))⌉₊ ≤ N) :
    relativeCost N J β₀ t ≤ 1 := by
  have hN := threshold_positive (by linarith : 0 < t / 4) hlarge
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 ≤ angleConstant t * coercivityConstant β₀ (t / 4) :=
    mul_nonneg (angleConstant_nonneg _) (coercivityConstant_pos hsub (by linarith)).le
  have hc := Nat.ceil_le.mp hceil
  have hs : ((J : ℝ) * Real.sqrt (angleConstant t * coercivityConstant β₀ (t / 4))) ^ 2 ≤
      (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
  rw [mul_pow, Real.sq_sqrt hp] at hs
  unfold relativeCost
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith only [hs]

end Heavy
end PeriodicAttractiveLogGas.ResolutionEnergy
