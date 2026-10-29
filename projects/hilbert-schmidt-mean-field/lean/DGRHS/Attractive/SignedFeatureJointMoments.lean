import DGRHS.Attractive.SignedGaussianMoments

/-! Joint weighted Gaussian moments from a genuine diagonal exponential
moment. Gaussian laws of the actual sections are used before Fubini. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

lemma joint_gaussian_weighted_even_moment
    (D : X → ℝ) (hDm : StronglyMeasurable D) (hD : ∀ x, 0 ≤ D x)
    (g : X × Ω → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ, HasLaw (fun ω => g (x,ω)) (gaussianReal 0 (Real.toNNReal (D x))) P)
    (a : ℝ) (ha : 0 < a) (hM : Integrable (fun x => Real.exp (a*D x)) μ)
    (s : ℝ) (hs : 0 ≤ s) (hsa : s^2 ≤ a/2) (l r : ℕ) :
    Integrable (fun p => D p.1^l * |g p|^(2*r) * Real.exp (s*|g p|)) (μ.prod P) ∧
    (∫ p, D p.1^l * |g p|^(2*r) * Real.exp (s*|g p|) ∂μ.prod P) ≤
      (2*((2*r).factorial:ℝ)*Real.exp 1*((l+r).factorial:ℝ)/(a/2)^(l+r)) *
        ∫ x, Real.exp (a*D x) ∂μ := by
  let C := 2*((2*r).factorial:ℝ)*Real.exp 1*((l+r).factorial:ℝ)/(a/2)^(l+r)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let F : X × Ω → ℝ := fun p => D p.1^l * |g p|^(2*r) * Real.exp (s*|g p|)
  have hm : StronglyMeasurable F := by
    dsimp [F]
    exact (((hDm.comp_measurable measurable_fst).pow l).mul (hg.norm.pow (2*r))).mul
      (Real.continuous_exp.comp_stronglyMeasurable (hg.norm.const_mul s))
  have hF0 : ∀ p, 0 ≤ F p := by
    intro p
    dsimp [F]
    exact mul_nonneg (mul_nonneg (pow_nonneg (hD _) l)
      (pow_nonneg (abs_nonneg _) (2*r))) (Real.exp_pos _).le
  have hb (x : X) :
      (D x)^l * (2*((2*r).factorial:ℝ)*(D x)^r*Real.exp ((D x)*s^2+1)) ≤
        C*Real.exp (a*D x) := by
    have hp := nonnegative_power_le_exponential (a/2) (D x) (by linarith) (hD x) (l+r)
    have hx := mul_le_mul_of_nonneg_left hsa (hD x)
    have he : Real.exp (D x*s^2)≤Real.exp ((a/2)*D x) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using hx
    calc
      _ = 2*((2*r).factorial:ℝ)*Real.exp 1*(D x)^(l+r)*Real.exp ((D x)*s^2) := by
        rw [Real.exp_add, pow_add]
        ring
      _ ≤ 2*((2*r).factorial:ℝ)*Real.exp 1*
          (((l+r).factorial:ℝ)/(a/2)^(l+r)*Real.exp ((a/2)*D x))*Real.exp ((a/2)*D x) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) he
          (Real.exp_pos _).le (by positivity)
      _ = C*(Real.exp ((a/2)*D x)*Real.exp ((a/2)*D x)) := by
        dsimp [C]
        ring
      _ = C*Real.exp (a*D x) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
  have hsections : ∀ᵐ x ∂μ, Integrable (fun ω => F (x,ω)) P ∧
      (∫ ω, F (x,ω) ∂P) ≤ C*Real.exp (a*D x) := by
    filter_upwards [hLaw] with x hx
    obtain ⟨hi,he⟩ := gaussian_weighted_even_moment (D x) (hD x) hx s hs r
    refine ⟨by simpa [F, mul_assoc] using hi.const_mul ((D x)^l), ?_⟩
    have heq : (∫ ω,F (x,ω) ∂P) = (D x)^l*
        (∫ ω,|g (x,ω)|^(2*r)*Real.exp (s*|g (x,ω)|) ∂P) := by
      dsimp [F]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    rw [heq]
    exact (mul_le_mul_of_nonneg_left he (pow_nonneg (hD x) l)).trans (hb x)
  have hi : Integrable F (μ.prod P) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    refine ⟨hsections.mono (fun x hx => hx.1), ?_⟩
    apply (hM.const_mul C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hsections] with x hx
    have hn : (∫ ω, ‖F (x,ω)‖ ∂P) = ∫ ω, F (x,ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact Real.norm_of_nonneg (hF0 _)
    rw [hn, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ω => hF0 _))]
    exact hx.2
  refine ⟨hi, ?_⟩
  change (∫ p, F p ∂μ.prod P) ≤ C*(∫ x, Real.exp (a*D x) ∂μ)
  rw [integral_prod _ hi, ← integral_const_mul]
  exact integral_mono_ae hi.integral_prod_left (hM.const_mul C) (hsections.mono (fun x hx => hx.2))

lemma ae_feature_gaussian_law {ι H : Type*} [Countable ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      DGRHS.Gaussian.indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω))
      (gaussianReal 0 (Real.toNNReal (‖k x‖^2))) IsonormalProcess.iidStdGaussian := by
  filter_upwards [hW] with x hx
  have hl : HasLaw (DGRHS.Gaussian.indexedGaussianIsometry b f hf (k x) : (ℕ → ℝ) → ℝ)
      (gaussianReal 0 (Real.toNNReal (‖k x‖^2))) IsonormalProcess.iidStdGaussian :=
    ⟨(Lp.aestronglyMeasurable _).aemeasurable,
      DGRHS.Gaussian.map_indexedGaussianIsometry_eq_gaussianReal b f hf (k x)⟩
  exact hl.congr hx

end DGRHS.Attractive
#check DGRHS.Attractive.joint_gaussian_weighted_even_moment
#print axioms DGRHS.Attractive.joint_gaussian_weighted_even_moment
