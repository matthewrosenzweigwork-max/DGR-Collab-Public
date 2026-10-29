import DGRHS.Commutator.SourceLogGaussianShortKernel
import DGRHS.Commutator.SourceLogTransportBound
import DGRHS.Gaussian.RieszGaussianFullScale

/-! Positive derivative order yields a full Gaussian mass and therefore a
short transport bound uniform in the positive cutoff. The complement estimate
is for the actual difference of the two collision-zero kernels; identifying
that difference with derivatives of the source long profile is a later step.
No properness, boundedness, or source estimate is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance sourceLogGaussianPositiveOrderNative1 (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance sourceLogGaussianPositiveOrderNative2 (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance sourceLogGaussianPositiveOrderNative3 (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance sourceLogGaussianPositiveOrderNative4 (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance sourceLogGaussianPositiveOrderNative5 (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance sourceLogGaussianPositiveOrderNative6 (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance sourceLogGaussianPositiveOrderNative7 (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance sourceLogGaussianPositiveOrderNative8 (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


def sourceLogGaussianPositiveOrderConstant (n : ℕ) : ℝ :=
  sourceRieszGaussianDerivativeConstant n * (8:ℝ)^((n:ℝ)/2) *
    (1/2) * Real.Gamma ((n:ℝ)/2)

lemma sourceLogGaussianPositiveOrderConstant_pos (n : ℕ) (hn : 0<n) :
    0<sourceLogGaussianPositiveOrderConstant n := by
  have hnreal : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
  have hn' : (0:ℝ)<(n:ℝ)/2 := by positivity
  have hG := Real.Gamma_pos_of_pos hn'
  have hC := sourceRieszGaussianDerivativeConstant_pos n
  unfold sourceLogGaussianPositiveOrderConstant
  positivity

lemma sourceLogGaussianPositiveOrder_full_mass (n : ℕ) (hn : 0<n) (r : ℝ) (hr : 0<r) :
    r^n * (∫ t in Ioi 0,t^(-(n:ℝ)-1)*Real.exp (-r^2/(8*t^2))) =
      (8:ℝ)^((n:ℝ)/2)*(1/2)*Real.Gamma ((n:ℝ)/2) := by
  have hn' : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
  have he : (fun t : ℝ=>t^(-(n:ℝ)-1)*Real.exp (-r^2/(8*t^2))) =
      (fun t : ℝ=>t^(-(n:ℝ)-1)*Real.exp (-(r^2/8)/t^2)) := by
    funext t
    congr 2
    ring
  have hp : (r^2/8)^(-(n:ℝ)/2) = r^(-(n:ℝ))*(8:ℝ)^((n:ℝ)/2) := by
    rw [Real.div_rpow (sq_nonneg r) (by norm_num),←Real.rpow_two,
      ←Real.rpow_mul hr.le,show (2:ℝ)*(-(n:ℝ)/2)=-(n:ℝ) by ring,
      show -(n:ℝ)/2=-((n:ℝ)/2) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤8)]
    simp only [div_inv_eq_mul]
  rw [he,DGRHS.Gaussian.integral_gaussianRiesz_full_scale (n:ℝ) (r^2/8)
    hn' (by positivity),hp,Real.rpow_neg hr.le,Real.rpow_natCast]
  have hpow : r^n≠0 := pow_ne_zero n hr.ne'
  calc
    _ = (r^n*(r^n)⁻¹)*((8:ℝ)^((n:ℝ)/2)*(1/2)*Real.Gamma ((n:ℝ)/2)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hpow,one_mul]

lemma sourceLogGaussian_scale_transport_positive_order (n : ℕ) (t : ℝ) (ht : 0<t)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (x y : E) :
    |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)) (fun _=>v x-v y)| ≤
      sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*‖x-y‖^n*
        (t^(-(n:ℝ)-1)*Real.exp (-‖x-y‖^2/(8*t^2))) := by
  have hw : ‖v x-v y‖≤(K:ℝ)*‖x-y‖ := by simpa only [dist_eq_norm] using hv.dist_le_mul x y
  have h := (iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)).le_opNorm (fun _=>v x-v y)
  simp only [Real.norm_eq_abs,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  have hscale : t⁻¹*(t⁻¹)^n=t^(-(n:ℝ)-1) := by
    rw [show -(n:ℝ)-1=-((n+1:ℕ):ℝ) by push_cast;ring,
      Real.rpow_neg ht.le,Real.rpow_natCast,pow_succ,mul_inv_rev]
    rw [←inv_pow]
  simp only [smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr ht.le)]
  calc
    _ ≤ t⁻¹*(‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)‖*‖v x-v y‖^n) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ht.le)
    _ ≤ t⁻¹*((t⁻¹)^n*sourceRieszGaussianDerivativeConstant n*
      Real.exp (-‖x-y‖^2/(8*t^2))*((K:ℝ)*‖x-y‖)^n) := by
      have hd := sourceRieszGaussian_iteratedFDeriv_unweighted_bound n t ht (x-y)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hd (pow_le_pow_left₀ (norm_nonneg _) hw n)
          (pow_nonneg (norm_nonneg _) n) ((norm_nonneg _).trans hd))
        (inv_nonneg.mpr ht.le)
    _ = (t⁻¹*(t⁻¹)^n)*sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*‖x-y‖^n*
      Real.exp (-‖x-y‖^2/(8*t^2)) := by rw [mul_pow];ring
    _ = _ := by rw [hscale];ring

lemma sourceLogGaussianShortTransportKernel_uniform_bound (n : ℕ) (hn : 0<n)
    (η : ℝ) (hη : 0<η) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (p : E×E) :
    |sourceLogGaussianShortTransportKernel n η v p|≤
      sourceLogGaussianPositiveOrderConstant n*(K:ℝ)^n := by
  classical
  by_cases hp : p.1=p.2
  · simp only [sourceLogGaussianShortTransportKernel,if_pos hp,abs_zero]
    exact mul_nonneg (sourceLogGaussianPositiveOrderConstant_pos n hn).le (by positivity)
  have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp
  have hr : 0<‖p.1-p.2‖ := norm_pos_iff.mpr hz
  have hn' : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
  let f : ℝ→ℝ := fun t=>t^(-(n:ℝ)-1)*Real.exp (-‖p.1-p.2‖^2/(8*t^2))
  have hf : IntegrableOn f (Ioi 0) := by
    have h := DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (n:ℝ)
      (‖p.1-p.2‖^2/8) hn' (by positivity)
    convert h using 1
    ext t
    dsimp [f]
    congr 2
    ring
  have hfshort := hf.mono_set (s:=Ioc 0 η) Ioc_subset_Ioi_self
  have hmono : (∫ t in Ioc 0 η,f t)≤∫ t in Ioi 0,f t := by
    apply setIntegral_mono_set hf
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall (fun t ht=>ht.1)
  have hi := integrable_sourceLogGaussian_derivative_scale n η hη hz
  have hEval : Integrable (fun t : ℝ=>
      (t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (p.1-p.2))
        (fun _=>v p.1-v p.2)) (volume.restrict (Ioc 0 η)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n=>E) ℝ (fun _=>v p.1-v p.2)).integrable_comp hi
  have hAbs : Integrable (fun t : ℝ=>
      |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (p.1-p.2))
        (fun _=>v p.1-v p.2)|) (volume.restrict (Ioc 0 η)) := by
    simpa only [Real.norm_eq_abs] using hEval.norm
  have hB : (∫ t in Ioc 0 η,
      |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (p.1-p.2))
        (fun _=>v p.1-v p.2)|)≤
      sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*‖p.1-p.2‖^n*
        (∫ t in Ioc 0 η,f t) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hAbs (hfshort.const_mul _)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact sourceLogGaussian_scale_transport_positive_order n t ht.1 hv p.1 p.2
  simp only [sourceLogGaussianShortTransportKernel,if_neg hp]
  rw [sourceLogShortRange_iteratedFDeriv_formula n η hη hz,
    ContinuousMultilinearMap.integral_apply hi]
  calc
    _ ≤ ∫ t in Ioc 0 η,
        |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (p.1-p.2))
          (fun _=>v p.1-v p.2)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t : ℝ=>(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (p.1-p.2))
          (fun _=>v p.1-v p.2))
    _ ≤ sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*‖p.1-p.2‖^n*
        (∫ t in Ioc 0 η,f t) := hB
    _ ≤ sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*‖p.1-p.2‖^n*
        (∫ t in Ioi 0,f t) := mul_le_mul_of_nonneg_left hmono
          (mul_nonneg (mul_nonneg (sourceRieszGaussianDerivativeConstant_pos n).le
            (pow_nonneg K.coe_nonneg n)) (pow_nonneg (norm_nonneg _) n))
    _ = sourceLogGaussianPositiveOrderConstant n*(K:ℝ)^n := by
      have hm := sourceLogGaussianPositiveOrder_full_mass n hn ‖p.1-p.2‖ hr
      change ‖p.1-p.2‖^n*(∫ t in Ioi 0,f t)=_ at hm
      calc
        _ = sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*
            (‖p.1-p.2‖^n*(∫ t in Ioi 0,f t)) := by ring
        _ = _ := by rw [hm];unfold sourceLogGaussianPositiveOrderConstant;ring

lemma exists_sourceLogGaussianComplementTransportKernel_uniform_bound
    (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ,0<C ∧ ∀ (η : ℝ),0<η → ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      ∀ p : E×E,|sourceLogTransportKernel n v p-sourceLogGaussianShortTransportKernel n η v p|≤C*(K:ℝ)^n := by
  have hPhysical : ∃ C : ℝ,0≤C ∧ ∀ {K : ℝ≥0} {v : E→E},LipschitzWith K v →
      ∀ p : E×E,|sourceLogTransportKernel n v p|≤C*(K:ℝ)^n :=
    exists_sourceLogTransportKernel_bound n hn
  obtain ⟨C,hC,hBound⟩ := hPhysical
  refine ⟨C+sourceLogGaussianPositiveOrderConstant n+1,by
    have hPos:=sourceLogGaussianPositiveOrderConstant_pos n hn;linarith,?_⟩
  intro η hη K v hv p
  calc
    _ ≤ |sourceLogTransportKernel n v p|+|sourceLogGaussianShortTransportKernel n η v p| := abs_sub _ _
    _ ≤ C*(K:ℝ)^n+sourceLogGaussianPositiveOrderConstant n*(K:ℝ)^n :=
      add_le_add (hBound hv p) (sourceLogGaussianShortTransportKernel_uniform_bound n hn η hη hv p)
    _ ≤ (C+sourceLogGaussianPositiveOrderConstant n+1)*(K:ℝ)^n := by
      have hpow : (0:ℝ)≤(K:ℝ)^n := by positivity
      nlinarith

end DGRHS.Commutator
