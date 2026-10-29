import DGRHS.Gaussian.FeatureRateParticleLaplace

/-!
Positive-sign Gaussian linearization for source positiveSignFeatureLaplace.
The real Gaussian MGF replaces the existing imaginary-phase transform. Joint
properness is proved from actual particle-weight properness and proper Gaussian
sections, before Fubini. This module does not assume a Gaussian factor identity.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma indexedGaussian_exp_integrable_and_integral
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (v : H) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * indexedGaussianIsometry b f hf v ω))
      IsonormalProcess.iidStdGaussian ∧
    (∫ ω, Real.exp (t * indexedGaussianIsometry b f hf v ω)
      ∂IsonormalProcess.iidStdGaussian) = Real.exp (t^2 * ‖v‖^2 / 2) := by
  have hLaw : HasLaw (indexedGaussianIsometry b f hf v : (ℕ → ℝ) → ℝ)
      (gaussianReal 0 (Real.toNNReal (‖v‖ ^ 2))) IsonormalProcess.iidStdGaussian :=
    ⟨(Lp.aestronglyMeasurable _).aemeasurable,
      map_indexedGaussianIsometry_eq_gaussianReal b f hf v⟩
  have he : mgf (indexedGaussianIsometry b f hf v : (ℕ → ℝ) → ℝ)
      IsonormalProcess.iidStdGaussian t = Real.exp (t^2 * ‖v‖^2 / 2) := by
    rw [mgf_gaussianReal hLaw]
    simp only [zero_mul, zero_add, Real.toNNReal_of_nonneg (sq_nonneg ‖v‖), NNReal.coe_mk]
    congr 1
    ring
  exact ⟨mgf_pos_iff.mp (he.symm ▸ Real.exp_pos _), he⟩

def positiveFeatureWick (β : ℝ) (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (N : ℕ) (p : X × (ℕ → ℝ)) : ℝ :=
  Real.exp (Real.sqrt (β / (N : ℝ)) * g p - β / (2 * (N : ℝ)) * ‖k p.1‖^2)

def positiveFeatureFactor (μ : Measure X) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∫ x, positiveFeatureWick β k g N (x,ω) ∂μ

def positiveFeatureProduct (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : (Fin N → X) × (ℕ → ℝ)) : ℝ :=
  ∏ i : Fin N, positiveFeatureWick β k g N (p.1 i,p.2)

def positiveFeatureParticleExp (β : ℝ) (k : X → H) (N : ℕ) (x : Fin N → X) : ℝ :=
  Real.exp (β / (2 * (N : ℝ)) *
    (‖∑ i : Fin N, k (x i)‖^2 - ∑ i : Fin N, ‖k (x i)‖^2))

lemma positiveFeatureProduct_eq_exp (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : (Fin N → X) × (ℕ → ℝ)) :
    positiveFeatureProduct β k g N p = Real.exp
      (Real.sqrt (β / (N : ℝ)) * ∑ i : Fin N, g (p.1 i,p.2) -
        β / (2 * (N : ℝ)) * ∑ i : Fin N, ‖k (p.1 i)‖^2) := by
  unfold positiveFeatureProduct positiveFeatureWick
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

lemma stronglyMeasurable_positiveFeatureProduct (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (N : ℕ) : StronglyMeasurable (positiveFeatureProduct β k g N) := by
  unfold positiveFeatureProduct
  apply Finset.stronglyMeasurable_fun_prod
  intro i hi
  have hw : StronglyMeasurable (positiveFeatureWick β k g N) := by
    unfold positiveFeatureWick
    exact Real.continuous_exp.comp_stronglyMeasurable ((hg.const_mul _).sub
      (((hk.comp_measurable measurable_fst).norm.pow 2).const_mul _))
  exact hw.comp_measurable
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)

lemma ae_positiveFeatureProduct_gaussian_integral
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      Integrable (fun ω => positiveFeatureProduct β k g N (x,ω))
        IsonormalProcess.iidStdGaussian ∧
      (∫ ω, positiveFeatureProduct β k g N (x,ω) ∂IsonormalProcess.iidStdGaussian) =
        positiveFeatureParticleExp β k N x := by
  filter_upwards [ae_feature_particle_sum_eq_same_process b f hf k g hW N] with x hx
  let c := Real.exp (-β / (2 * (N : ℝ)) * ∑ i : Fin N, ‖k (x i)‖^2)
  have he : (fun ω => positiveFeatureProduct β k g N (x,ω))
      =ᵐ[IsonormalProcess.iidStdGaussian] fun ω =>
        c * Real.exp (Real.sqrt (β / (N : ℝ)) *
          indexedGaussianIsometry b f hf (∑ i : Fin N, k (x i)) ω) := by
    filter_upwards [hx] with ω hω
    rw [positiveFeatureProduct_eq_exp, hω]
    dsimp [c]
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨hi, hv⟩ := indexedGaussian_exp_integrable_and_integral b f hf
    (∑ i : Fin N, k (x i)) (Real.sqrt (β / (N : ℝ)))
  refine ⟨(hi.const_mul c).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const_mul, hv]
  dsimp [c, positiveFeatureParticleExp]
  rw [← Real.exp_add, Real.sq_sqrt (div_nonneg hβ (Nat.cast_nonneg N))]
  congr 1
  ring

lemma integrable_positiveFeatureProduct
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ)
    (hp : Integrable (positiveFeatureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ))) :
    Integrable (positiveFeatureProduct β k g N)
      ((Measure.pi (fun _ : Fin N => μ)).prod IsonormalProcess.iidStdGaussian) := by
  apply (integrable_prod_iff
    (stronglyMeasurable_positiveFeatureProduct β k hk g hg N).aestronglyMeasurable).2
  have ha := ae_positiveFeatureProduct_gaussian_integral b f hf β hβ k g hW N
  refine ⟨ha.mono (fun x hx => hx.1), hp.congr ?_⟩
  filter_upwards [ha] with x hx
  rw [← hx.2]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  unfold positiveFeatureProduct positiveFeatureWick
  exact Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le

lemma integral_positiveFeatureProduct_section (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    (∫ x, positiveFeatureProduct β k g N (x,ω) ∂Measure.pi (fun _ : Fin N => μ)) =
      positiveFeatureFactor μ β k g N ω ^ N := by
  simpa only [positiveFeatureProduct, positiveFeatureFactor, Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ)
      (fun x => positiveFeatureWick β k g N (x,ω)))

/-- Actual positive-sign Hubbard--Stratonovich identity, with properness of
both the joint integrand and the Gaussian power derived before rearrangement. -/
theorem positiveFeature_linearization
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ)
    (hp : Integrable (positiveFeatureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ))) :
    Integrable (fun ω => positiveFeatureFactor μ β k g N ω ^ N)
      IsonormalProcess.iidStdGaussian ∧
    (∫ x, positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ)) =
      ∫ ω, positiveFeatureFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian := by
  have hi := integrable_positiveFeatureProduct b f hf β hβ k hk g hg hW N hp
  have hsec := integral_positiveFeatureProduct_section (μ := μ) β k g N
  refine ⟨hi.integral_prod_right.congr (Filter.Eventually.of_forall hsec), ?_⟩
  calc
    _ = ∫ x, ∫ ω, positiveFeatureProduct β k g N (x,ω)
          ∂IsonormalProcess.iidStdGaussian ∂Measure.pi (fun _ : Fin N => μ) := by
      apply integral_congr_ae
      exact (ae_positiveFeatureProduct_gaussian_integral b f hf β hβ k g hW N).mono
        (fun x hx => hx.2.symm)
    _ = ∫ p, positiveFeatureProduct β k g N p
          ∂((Measure.pi (fun _ : Fin N => μ)).prod IsonormalProcess.iidStdGaussian) :=
      (integral_prod _ hi).symm
    _ = _ := by
      rw [integral_prod_symm _ hi]
      exact integral_congr_ae (Filter.Eventually.of_forall hsec)

lemma stronglyMeasurable_positiveFeatureParticleExp (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (N : ℕ) :
    StronglyMeasurable (positiveFeatureParticleExp β k N) := by
  have hsum : StronglyMeasurable (fun x : Fin N → X => ∑ i : Fin N, k (x i)) :=
    by
      apply Finset.stronglyMeasurable_fun_sum
      intro i hi
      exact hk.comp_measurable (measurable_pi_apply i)
  have hdiag : StronglyMeasurable (fun x : Fin N → X => ∑ i : Fin N, ‖k (x i)‖^2) :=
    by
      apply Finset.stronglyMeasurable_fun_sum
      intro i hi
      exact ((hk.comp_measurable (measurable_pi_apply i)).norm.pow 2)
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((hsum.norm.pow 2).sub hdiag).const_mul _)

/-- The source's doubled positive moment supplies the properness needed by
linearization at half the exponent, including negative particle statistics. -/
lemma integrable_positiveFeatureParticleExp_of_doubled (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (N : ℕ)
    (hp : Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ))) :
    Integrable (positiveFeatureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ)) := by
  apply ((integrable_const (1 : ℝ)).add hp).mono'
    (stronglyMeasurable_positiveFeatureParticleExp β k hk N).aestronglyMeasurable
  filter_upwards [] with x
  let a := β / (2*(N:ℝ)) * (‖∑ i : Fin N, k (x i)‖^2 - ∑ i : Fin N, ‖k (x i)‖^2)
  have he : positiveFeatureParticleExp β k N x = Real.exp a := rfl
  have hd : positiveFeatureParticleExp (2*β) k N x = Real.exp (2*a) := by
    unfold positiveFeatureParticleExp a
    congr 1
    ring
  rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  change Real.exp a ≤ 1+positiveFeatureParticleExp (2*β) k N x
  rw [hd]
  by_cases ha : 0 ≤ a
  · have hh := Real.exp_le_exp.mpr (show a ≤ 2*a by linarith)
    linarith
  · have hh := Real.exp_le_exp.mpr (show a ≤ 0 by linarith)
    rw [Real.exp_zero] at hh
    linarith [Real.exp_pos (2*a)]

lemma positiveFeatureFactor_double (μ : Measure X) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) :
    positiveFeatureFactor μ (2*β) k g (2*N) = positiveFeatureFactor μ β k g N := by
  funext ω
  unfold positiveFeatureFactor positiveFeatureWick
  congr 1
  funext x
  congr 1
  have hratio : (2*β) / ((2*N:ℕ):ℝ) = β / (N:ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
    ring
  have hratio' : (2*β) / (2*((2*N:ℕ):ℝ)) = β / (2*(N:ℝ)) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hratio, hratio']

/-- The actual second Gaussian power equals the source doubled particle
weight. Its properness is obtained from that particle weight, not assumed. -/
theorem positiveFeature_doubled_linearization
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ)
    (hp : Integrable (positiveFeatureParticleExp (2*β) k (2*N))
      (Measure.pi (fun _ : Fin (2*N) => μ))) :
    Integrable (fun ω => positiveFeatureFactor μ β k g N ω ^ (2*N))
      IsonormalProcess.iidStdGaussian ∧
    (∫ ω, positiveFeatureFactor μ β k g N ω ^ (2*N) ∂IsonormalProcess.iidStdGaussian) =
      ∫ x, positiveFeatureParticleExp (2*β) k (2*N) x
        ∂Measure.pi (fun _ : Fin (2*N) => μ) := by
  obtain ⟨hi, he⟩ := positiveFeature_linearization b f hf (2*β) (by positivity)
    k hk g hg hW (2*N) hp
  rw [positiveFeatureFactor_double] at hi he
  exact ⟨hi, he.symm⟩

end DGRHS.Attractive
#check DGRHS.Attractive.indexedGaussian_exp_integrable_and_integral
#print axioms DGRHS.Attractive.indexedGaussian_exp_integrable_and_integral
#check DGRHS.Attractive.ae_positiveFeatureProduct_gaussian_integral
#print axioms DGRHS.Attractive.ae_positiveFeatureProduct_gaussian_integral
#check DGRHS.Attractive.integrable_positiveFeatureProduct
#print axioms DGRHS.Attractive.integrable_positiveFeatureProduct
#check DGRHS.Attractive.positiveFeature_linearization
#print axioms DGRHS.Attractive.positiveFeature_linearization

#check DGRHS.Attractive.integrable_positiveFeatureParticleExp_of_doubled
#print axioms DGRHS.Attractive.integrable_positiveFeatureParticleExp_of_doubled
#check DGRHS.Attractive.positiveFeature_doubled_linearization
#print axioms DGRHS.Attractive.positiveFeature_doubled_linearization
