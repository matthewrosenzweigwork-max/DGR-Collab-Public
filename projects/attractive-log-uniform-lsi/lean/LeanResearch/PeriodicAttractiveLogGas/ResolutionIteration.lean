import LeanResearch.PeriodicAttractiveLogGas.ResolutionEnergy
import LeanResearch.PeriodicAttractiveLogGas.ResolutionRemainder
import LeanResearch.PeriodicAttractiveLogGas.ResolutionCoefficients

/-! Entropy comparison with the light region, manuscript Theorem 7.5.
The cutoff functions, physical energies, entropy remainder and coefficient
series are those constructed in the preceding modules. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.ResolutionIteration
open ResolutionCutoffs ResolutionEnergy ResolutionRemainder ResolutionCoefficients
  SquaredLocalization HeavyScales HeavyCoercivityConstants SeparatedRadius
  ConditionalLawEstimates SmoothOccupations CrudeEntropyIntegrated

/-- The real expression is used only after identifying it with actual entropy. -/
theorem continuous_entropy_eq {N : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) :
    entropy μ (fun X => f X ^ 2) = (Rothaus.squareEntropy μ f : EReal) :=
  Rothaus.entropy_sq_eq f.continuous.measurable
    (fun X => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm X)

theorem real_entropy_split {N : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (F θ : C(Configuration N, ℝ)) :
    Rothaus.squareEntropy μ F ≤ Rothaus.squareEntropy μ (cosMap θ * F) +
      Rothaus.squareEntropy μ (sinMap θ * F) := by
  have hh := entropy_square_split μ F θ
  rw [continuous_entropy_eq μ F, continuous_entropy_eq μ (cosMap θ * F),
    continuous_entropy_eq μ (sinMap θ * F), ← EReal.coe_add] at hh
  exact EReal.coe_le_coe_iff.mp hh

theorem finite_entropy_decomposition {N J : ℕ} (hJ : 0 < J) (t : ℝ)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (f : C(Configuration N, ℝ)) (M : ℕ) :
    Rothaus.squareEntropy μ f ≤
      (∑ m ∈ Finset.range M, Rothaus.squareEntropy μ (lightPiece N J hJ t f m)) +
        Rothaus.squareEntropy μ (remainder N J hJ t f M) := by
  induction M with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, remainder_zero, le_refl]
  | succ M ih =>
    have hh := real_entropy_split μ (remainder N J hJ t f M) (refinementAngle N J hJ t M)
    change Rothaus.squareEntropy μ (remainder N J hJ t f M) ≤
      Rothaus.squareEntropy μ (lightPiece N J hJ t f M) +
        Rothaus.squareEntropy μ (remainder N J hJ t f (M + 1)) at hh
    rw [Finset.sum_range_succ]
    linarith only [ih, hh]


theorem threshold_ge_two {N J : ℕ} {β₀ t : ℝ} (ht : 0 < t) (ht1 : t / 4 < 1)
    (hlarge : ResolutionCoefficients.threshold J β₀ t ≤ N) : 2 ≤ N := by
  have hDP : particleThreshold β₀ (t / 4) ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hsmall : (2 : ℝ) ≤ 8 / (t / 4) := by
    apply (le_div_iff₀ (by linarith : 0 < t / 4)).mpr
    linarith only [ht1]
  exact_mod_cast hsmall.trans (threshold_eight hDP)

/-- The base cutoff has exactly the support, pointwise square bound and
physical energy cost used in the source conclusion. -/
theorem first_cutoff_properties {N J : ℕ} (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (β : ℝ) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) :
    (∀ X, t / 2 ≤ maximumOccupation N J (by omega) X →
      lightPiece N J (by omega) t f 0 X = 0) ∧
    (∀ X, lightPiece N J (by omega) t f 0 X ^ 2 ≤ f X ^ 2) ∧
    energy β (lightPiece N J (by omega) t f 0) ≤ initialBound J t β f := by
  refine ⟨fun X hX => lightPiece_zero_high N J (by omega) ht f 0
    (by simpa only [mesh_zero] using hX), ?_, ?_⟩
  · intro X
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (abs_lightPiece_le N J (by omega) t f 0 X) 2
  · have hs := energy_split N J hN hJ ht β f hf 0
    have hc := cost_angle_le N J hN hJ ht β f
    have hn := energy_nonneg β (remainder N J (by omega) t f 1)
    simp only [remainder_zero, refinementAngle, mesh_zero] at hs
    unfold initialBound
    linarith only [hs, hc, hn]

section Source
variable {N J : ℕ} {β β₀ t C₂ : ℝ}
    (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (hres : sourceResolution β₀ (t / 4) ≤ J)
    (hlarge : ResolutionCoefficients.threshold J β₀ t ≤ N)

include hβ hβle hsub ht htδ hmesh hC hk hscale hsmall hres hlarge

/-- The crude N-dependent entropy defect is paid by the heavy estimate at
exactly the preceding mesh. The conclusion has no N-dependent coefficient. -/
theorem lightPiece_entropy_le_kappa (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    Rothaus.squareEntropy (gibbsMeasure greenRealRepresentative N β)
      (lightPiece N J (source_mesh_pos hres) t f (m + 1)) ≤
        kappa J β₀ t C₂ (m + 1) *
          energy β (lightPiece N J (source_mesh_pos hres) t f (m + 1)) := by
  have hβ₀ := hβ.trans hβle
  have hδ := (chosen_parameters β₀ hβ₀).2.1
  have ht1 : t / 4 < 1 := by linarith
  have hN := threshold_ge_two ht ht1 hlarge
  have hJ := source_mesh_pos hres
  have hmass : OccupationMassCutoff.halfMassThreshold β₀ (t / 4) (t / 2) ≤ N :=
    (le_max_left _ _).trans hlarge
  have hDP : particleThreshold β₀ (t / 4) ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  obtain ⟨L, hL⟩ := lightPiece_lipschitz N J (by omega) (source_mesh_ge_three hres) ht f hf (m + 1)
  have hmesh' : 8 * (radius β₀ + 4) ≤ mesh J (m + 1) := hmesh.trans (base_le_mesh J (m + 1))
  have hscale' : 2 ≤ (mesh J (m + 1) : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t) :=
    hscale.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast base_le_mesh J (m + 1))
      (Real.sqrt_nonneg _))
  have hres' : sourceResolution β₀ (t / 4) ≤ (mesh J (m + 1) : ℝ) :=
    hres.trans (by exact_mod_cast base_le_mesh J (m + 1))
  have hh := crude_light_entropy_uniform (mesh_pos hJ (m + 1)) hN hβ hβle hsub ht htδ
    hmesh' hC hk hscale' hsmall hres' hmass
    (configurationEuclideanLipschitzWith_iff_lift.mpr hL)
    (fun X hX => lightPiece_zero_high N J hJ ht f (m + 1) hX)
  rw [continuous_entropy_eq] at hh
  have he := EReal.coe_le_coe_iff.mp hh
  rw [← energy_eq_physical β _ hL] at he
  have hheavy := lightPiece_heavy hβ₀ hsub ht ht1 hres hDP hβ hβle f hf m
  have hdef : 0 ≤ (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
      N * (1 + Real.log (mesh J (m + 1) : ℝ)) := by
    have hd := crude_coefficient_nonneg hβ₀ ht.le hC
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ mesh J (m + 1) by
      exact_mod_cast mesh_pos hJ (m + 1))
    positivity
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  calc
    _ ≤ (2 * entropyBound β₀ / (mesh J (m + 1) : ℝ) ^ 2) *
        energy β (lightPiece N J hJ t f (m + 1)) +
        (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) * N *
          (1 + Real.log (mesh J (m + 1) : ℝ)) *
            squareIntegral β (lightPiece N J hJ t f (m + 1)) := he
    _ ≤ (2 * entropyBound β₀ / (mesh J (m + 1) : ℝ) ^ 2) *
        energy β (lightPiece N J hJ t f (m + 1)) +
        (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) * N *
          (1 + Real.log (mesh J (m + 1) : ℝ)) *
            (coercivityConstant β₀ (t / 4) / ((mesh J m : ℝ) ^ 2 * N) *
              energy β (lightPiece N J hJ t f (m + 1))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hheavy hdef)
    _ = _ := by
      rw [kappa_succ_mesh]
      field_simp [hn]


/-- Source Theorem 7.5. All refinement levels use the same particle threshold.
There is no assumed entropy estimate, tail limit, or monotonicity of the
smoothed occupations in the hypotheses. -/
theorem entropy_resolution_iteration (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X => f X ^ 2) ≤
      entropy (gibbsMeasure greenRealRepresentative N β)
        (fun X => lightPiece N J (source_mesh_pos hres) t f 0 X ^ 2) +
      ((ResolutionCoefficients.entropyConstant J β₀ t C₂ * initialBound J t β f : ℝ) : EReal) := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let B := initialBound J t β f
  have hβ₀ := hβ.trans hβle
  have hδ := (chosen_parameters β₀ hβ₀).2.1
  have ht1 : t / 4 < 1 := by linarith
  have hJ := source_mesh_pos hres
  have hJ3 := source_mesh_ge_three hres
  have hDP : particleThreshold β₀ (t / 4) ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hceil : ⌈(J : ℝ) * Real.sqrt (angleConstant t * coercivityConstant β₀ (t / 4))⌉₊ ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hbudget := relativeCost_le_one hβ₀ hsub ht ht1 hres hDP hβ hβle hceil
  have hB : 0 ≤ B := by
    have he := energy_nonneg β f
    have hs := squareIntegral_nonneg β f
    have hθ := angleConstant_nonneg t
    dsimp only [B, initialBound]
    positivity
  have hpiece (m : ℕ) : Rothaus.squareEntropy μ (lightPiece N J hJ t f (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) * kappa J β₀ t C₂ (m + 1)) * B := by
    calc
      _ ≤ kappa J β₀ t C₂ (m + 1) * energy β (lightPiece N J hJ t f (m + 1)) :=
        lightPiece_entropy_le_kappa hβ hβle hsub ht htδ hmesh hC hk hscale hsmall hres hlarge f hf m
      _ ≤ kappa J β₀ t C₂ (m + 1) * ((2 : ℝ) ^ (m + 1) * B) :=
        mul_le_mul_of_nonneg_left
          (lightPiece_energy_le hβ₀ hsub ht ht1 hres hDP hβ hβle hbudget f hf (m + 1))
          (kappa_nonneg hJ hβ₀ hsub ht hC (m + 1))
      _ = _ := by ring
  have hsplit (m : ℕ) : Rothaus.squareEntropy μ (remainder N J hJ t f m) ≤
      Rothaus.squareEntropy μ (lightPiece N J hJ t f m) +
        Rothaus.squareEntropy μ (remainder N J hJ t f (m + 1)) :=
    real_entropy_split μ (remainder N J hJ t f m) (refinementAngle N J hJ t m)
  have hfinite (M : ℕ) : Rothaus.squareEntropy μ f ≤
      Rothaus.squareEntropy μ (lightPiece N J hJ t f 0) +
        (∑ m ∈ Finset.range M, (2 : ℝ) ^ (m + 1) * kappa J β₀ t C₂ (m + 1)) * B +
          Rothaus.squareEntropy μ (remainder N J hJ t f (M + 1)) := by
    induction M with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty, zero_mul, add_zero, remainder_zero]
        using hsplit 0
    | succ M ih =>
      rw [Finset.sum_range_succ, add_mul]
      have hs := hsplit (M + 1)
      have hp := hpiece M
      linarith only [ih, hs, hp]
  have hsum (M : ℕ) :
      (∑ m ∈ Finset.range M, (2 : ℝ) ^ (m + 1) * kappa J β₀ t C₂ (m + 1)) ≤
        ResolutionCoefficients.entropyConstant J β₀ t C₂ :=
    Summable.sum_le_tsum (Finset.range M)
      (fun m _ => mul_nonneg (by positivity) (kappa_nonneg hJ hβ₀ hsub ht hC (m + 1)))
      (weighted_kappa_summable hJ3 β₀ t C₂)
  have hbound (M : ℕ) : Rothaus.squareEntropy μ f ≤
      Rothaus.squareEntropy μ (lightPiece N J hJ t f 0) +
        ResolutionCoefficients.entropyConstant J β₀ t C₂ * B +
          Rothaus.squareEntropy μ (remainder N J hJ t f (M + 1)) := by
    have hh := hfinite M
    have hc := mul_le_mul_of_nonneg_right (hsum M) hB
    linarith only [hh, hc]
  have hr := remainder_entropy_tendsto_zero hJ3 ht (single_particle_le_inner ht hDP) β f
  have hlimit : Tendsto (fun M => Rothaus.squareEntropy μ (lightPiece N J hJ t f 0) +
      ResolutionCoefficients.entropyConstant J β₀ t C₂ * B +
        Rothaus.squareEntropy μ (remainder N J hJ t f (M + 1))) atTop
      (𝓝 (Rothaus.squareEntropy μ (lightPiece N J hJ t f 0) +
        ResolutionCoefficients.entropyConstant J β₀ t C₂ * B)) := by
    have htail := hr.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, add_zero] using tendsto_const_nhds.add htail
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit (Eventually.of_forall hbound)
  rw [continuous_entropy_eq _ f, continuous_entropy_eq _ _, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr hh

end Source
end PeriodicAttractiveLogGas.ResolutionIteration
