import DGRHS.Attractive.SignedFeatureLinearization

/-! Properness and positivity of the actual positive Wick factor on the
Gaussian AE set, before applying the real logarithm. No particle moment is
needed for the one-body Wick integrand, whose Gaussian expectation is one. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma stronglyMeasurable_positiveFeatureWick (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ)
    (hg : StronglyMeasurable g) (N : ℕ) :
    StronglyMeasurable (positiveFeatureWick β k g N) := by
  unfold positiveFeatureWick
  exact Real.continuous_exp.comp_stronglyMeasurable ((hg.const_mul _).sub
    (((hk.comp_measurable measurable_fst).norm.pow 2).const_mul _))

lemma ae_positiveFeatureWick_gaussian_integral
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) :
    ∀ᵐ x ∂μ, Integrable (fun ω => positiveFeatureWick β k g N (x,ω))
      IsonormalProcess.iidStdGaussian ∧
      (∫ ω, positiveFeatureWick β k g N (x,ω) ∂IsonormalProcess.iidStdGaussian) = 1 := by
  filter_upwards [hW] with x hx
  let c := Real.exp (-β/(2*(N:ℝ))*‖k x‖^2)
  have he : (fun ω => positiveFeatureWick β k g N (x,ω))
      =ᵐ[IsonormalProcess.iidStdGaussian] fun ω => c*Real.exp
        (Real.sqrt (β/(N:ℝ))*indexedGaussianIsometry b f hf (k x) ω) := by
    filter_upwards [hx] with ω hω
    unfold positiveFeatureWick
    rw [hω]
    dsimp [c]
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨hi, hv⟩ := indexedGaussian_exp_integrable_and_integral b f hf
    (k x) (Real.sqrt (β/(N:ℝ)))
  refine ⟨(hi.const_mul c).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const_mul, hv]
  dsimp [c]
  rw [← Real.exp_add, Real.sq_sqrt (div_nonneg hβ (Nat.cast_nonneg N))]
  have hz : -β/(2*(N:ℝ))*‖k x‖^2+(β/(N:ℝ))*‖k x‖^2/2=0 := by ring
  rw [hz, Real.exp_zero]

lemma integrable_positiveFeatureWick
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) :
    Integrable (positiveFeatureWick β k g N) (μ.prod IsonormalProcess.iidStdGaussian) := by
  apply (integrable_prod_iff
    (stronglyMeasurable_positiveFeatureWick β k hk g hg N).aestronglyMeasurable).2
  have ha := ae_positiveFeatureWick_gaussian_integral b f hf β hβ k g hW N
  refine ⟨ha.mono (fun x hx => hx.1), (integrable_const (1:ℝ)).congr ?_⟩
  filter_upwards [ha] with x hx
  rw [← hx.2]
  apply integral_congr_ae
  filter_upwards [] with ω
  unfold positiveFeatureWick
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Actual proper spatial sections, strictly positive factor, proper factor
and exact first Gaussian moment. These statements precede any logarithm. -/
theorem positiveFeatureFactor_proper_positive_mean
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) :
    (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      Integrable (fun x => positiveFeatureWick β k g N (x,ω)) μ ∧
        0 < positiveFeatureFactor μ β k g N ω) ∧
    Integrable (positiveFeatureFactor μ β k g N) IsonormalProcess.iidStdGaussian ∧
    (∫ ω, positiveFeatureFactor μ β k g N ω ∂IsonormalProcess.iidStdGaussian) = 1 := by
  have hi := integrable_positiveFeatureWick b f hf β hβ k hk g hg hW N
  refine ⟨?_, hi.integral_prod_right, ?_⟩
  · filter_upwards [hi.prod_left_ae] with ω hω
    refine ⟨hω, ?_⟩
    exact integral_exp_pos hω
  · change (∫ ω, ∫ x, positiveFeatureWick β k g N (x,ω) ∂μ
      ∂IsonormalProcess.iidStdGaussian) = 1
    rw [← integral_prod_symm _ hi, integral_prod _ hi]
    have he : (fun x => ∫ ω, positiveFeatureWick β k g N (x,ω)
        ∂IsonormalProcess.iidStdGaussian) =ᵐ[μ] fun _ => (1:ℝ) :=
      (ae_positiveFeatureWick_gaussian_integral b f hf β hβ k g hW N).mono
        (fun x hx => hx.2)
    rw [integral_congr_ae he]
    simp

end DGRHS.Attractive
#check DGRHS.Attractive.positiveFeatureFactor_proper_positive_mean
#print axioms DGRHS.Attractive.positiveFeatureFactor_proper_positive_mean
