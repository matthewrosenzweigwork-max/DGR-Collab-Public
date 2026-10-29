import LeanResearch.PeriodicAttractiveLogGas.LabelRatioTransport
import LeanResearch.PeriodicAttractiveLogGas.ConditionalVarianceIntegral
import LeanResearch.PeriodicAttractiveLogGas.CoordinateConditionalKernels
import LeanResearch.PeriodicAttractiveLogGas.DensityMoments
import Mathlib.Probability.Moments.Covariance

/-! Source Proposition 3.12, lines 920--946: the exact edge covariance,
conditional covariance decomposition, and boundary-splitting inequality.
This bounded unit stops before quantitative Proposition 3.11 substitution
or summing label edges. SOURCE_ONLY: central Lean checking is pending.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.BoundaryCovarianceSplitting

open CoordinateOscillation ConditionalKernelL2 ConditionalL2Projections
  ConditionalVarianceIntegral MeshCells MeshAdjacentCells CellRestrictions
  OneCoordinateConditionals ConditionalLawEstimates LabelOccupations GreenPointWeights

section ScalarAnalysis

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy--Schwarz for actual integrable products and squared norms. -/
theorem integral_mul_squared_le {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hh := integral_mul_norm_le_Lp_mul_Lq hconj hf' hg'
  have hn : |∫ x, f x * g x ∂μ| ≤ lpNorm f 2 μ * lpNorm g 2 μ := by
    calc
      _ ≤ ∫ x, ‖f x * g x‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x ↦ f x * g x)
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
      _ ≤ _ := by
        rw [DensityMoments.lpNorm_two_eq hf.aestronglyMeasurable,
          DensityMoments.lpNorm_two_eq hg.aestronglyMeasurable]
        simpa only [Real.rpow_two] using hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) hn 2
  simpa only [sq_abs, mul_pow, DensityMoments.lpNorm_two_sq hf,
    DensityMoments.lpNorm_two_sq hg, Real.norm_eq_abs] using hs

theorem covariance_squared_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    covariance f g μ ^ 2 ≤ variance f μ * variance g μ := by
  have hfc : MemLp (fun x ↦ f x - ∫ y, f y ∂μ) 2 μ := hf.sub (memLp_const _)
  have hgc : MemLp (fun x ↦ g x - ∫ y, g y ∂μ) 2 μ := hg.sub (memLp_const _)
  rw [covariance, variance_eq_integral hf.aemeasurable, variance_eq_integral hg.aemeasurable]
  exact integral_mul_squared_le hfc hgc

omit [MeasurableSpace Ω] in
theorem indicator_bound (s : Set Ω) (x : Ω) : |s.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
  classical
  by_cases hx : x ∈ s <;> simp [hx]

omit [MeasurableSpace Ω] in
theorem indicator_squared (s : Set Ω) (x : Ω) :
    (s.indicator (fun _ ↦ (1 : ℝ)) x) ^ 2 = s.indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx]

theorem bernoulli_variance [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : MemLp g 2 μ) (hsq : ∀ x, g x ^ 2 = g x) :
    variance g μ = (∫ x, g x ∂μ) * (1 - ∫ x, g x ∂μ) := by
  rw [variance_eq_sub hg]
  have he : (∫ x, g x ^ 2 ∂μ) = ∫ x, g x ∂μ :=
    integral_congr_ae (Eventually.of_forall hsq)
  change (∫ x, g x ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 = _
  rw [he]
  ring

end ScalarAnalysis

section Mixtures

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ νa νb : Measure Ω} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure νa] [IsProbabilityMeasure νb]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure νa] [IsProbabilityMeasure νb] in
theorem integral_two_label_mixture {c : ℝ≥0∞} (hc : c ≤ 1)
    (hmix : μ = c • νa + (1 - c) • νb) {f : Ω → ℝ}
    (ha : Integrable f νa) (hb : Integrable f νb) :
    (∫ x, f x ∂μ) = c.toReal * (∫ x, f x ∂νa) +
      (1 - c.toReal) * (∫ x, f x ∂νb) := by
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc
  have hd : 1 - c ≠ ⊤ := by finiteness
  rw [hmix, integral_add_measure (ha.smul_measure hct) (hb.smul_measure hd),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_sub_of_le hc (by simp), ENNReal.toReal_one, smul_eq_mul, smul_eq_mul]

/-- The indicator covariance is computed from a genuine mixture supported
on the two disjoint label events. All three needed integrals are finite. -/
theorem two_label_indicator_covariance {c : ℝ≥0∞} (hc : c ≤ 1)
    (hmix : μ = c • νa + (1 - c) • νb)
    (s : Set Ω) (hs : MeasurableSet s)
    (ha : ∀ᵐ x ∂νa, x ∈ s) (hb : ∀ᵐ x ∂νb, x ∉ s)
    {f : Ω → ℝ} {B : ℝ} (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ B) :
    (∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) = c.toReal ∧
      covariance f (s.indicator (fun _ ↦ (1 : ℝ))) μ =
        c.toReal * (1 - c.toReal) * ((∫ x, f x ∂νa) - ∫ x, f x ∂νb) := by
  let I := s.indicator (fun _ ↦ (1 : ℝ))
  have hIm : Measurable I := measurable_const.indicator hs
  have hf2 (ν : Measure Ω) [IsProbabilityMeasure ν] : MemLp f 2 ν :=
    DensityMoments.memLp_of_bounded hfm ⟨B, hfb⟩ 2
  have hI2 (ν : Measure Ω) [IsProbabilityMeasure ν] : MemLp I 2 ν :=
    DensityMoments.memLp_of_bounded hIm ⟨1, indicator_bound s⟩ 2
  have hIa : (∫ x, I x ∂νa) = 1 := by
    calc
      _ = ∫ _ : Ω, (1 : ℝ) ∂νa := integral_congr_ae (ha.mono fun x hx ↦ by simp [I, hx])
      _ = 1 := by simp
  have hIb : (∫ x, I x ∂νb) = 0 := by
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂νb := integral_congr_ae (hb.mono fun x hx ↦ by simp [I, hx])
      _ = 0 := by simp
  have hmean : (∫ x, I x ∂μ) = c.toReal := by
    rw [integral_two_label_mixture hc hmix ((hI2 νa).integrable (by norm_num))
      ((hI2 νb).integrable (by norm_num)), hIa, hIb]
    ring
  have hfa : (∫ x, f x * I x ∂νa) = ∫ x, f x ∂νa :=
    integral_congr_ae (ha.mono fun x hx ↦ by simp [I, hx])
  have hfb' : (∫ x, f x * I x ∂νb) = 0 := by
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂νb :=
        integral_congr_ae (hb.mono fun x hx ↦ by simp [I, hx])
      _ = 0 := by simp
  have hprod : (∫ x, f x * I x ∂μ) = c.toReal * ∫ x, f x ∂νa := by
    change (∫ x, (f * I) x ∂μ) = _
    rw [integral_two_label_mixture hc hmix ((hf2 νa).integrable_mul (hI2 νa))
      ((hf2 νb).integrable_mul (hI2 νb))]
    simp only [Pi.mul_apply, hfa, hfb']
    ring
  refine ⟨hmean, ?_⟩
  change covariance f I μ = _
  rw [covariance_eq_sub (hf2 μ) (hI2 μ)]
  simp only [Pi.mul_apply]
  rw [hprod, hmean,
    integral_two_label_mixture hc hmix ((hf2 νa).integrable (by norm_num))
      ((hf2 νb).integrable (by norm_num))]
  ring

end Mixtures

section ConditionalSplitting

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)]
variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]
variable (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ]

def kernelCovariance (f g : (∀ k, E k) → ℝ) (i : ι) (x : ∀ k, E k) : ℝ :=
  covariance (fun z ↦ f (Function.update x i z))
    (fun z ↦ g (Function.update x i z)) (κ i x)

theorem section_memLp_of_bounded {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ B) (i : ι) (x : ∀ k, E k) :
    MemLp (fun z ↦ f (Function.update x i z)) 2 (κ i x) :=
  DensityMoments.memLp_of_bounded (hm.comp (measurable_update x))
    ⟨B, fun _ ↦ hb _⟩ 2

theorem siteAverage_memLp_of_bounded {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ B) (i : ι) :
    MemLp (siteAverage κ f i) 2 μ :=
  DensityMoments.memLp_of_bounded (measurable_siteAverage κ hm i)
    ⟨B, siteAverage_bound κ hb i⟩ 2

theorem kernelCovariance_eq {f g : (∀ k, E k) → ℝ} {B D : ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ B)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ D) (i : ι) (x : ∀ k, E k) :
    kernelCovariance κ f g i x = siteAverage κ (fun y ↦ f y * g y) i x -
      siteAverage κ f i x * siteAverage κ g i x := by
  exact covariance_eq_sub (section_memLp_of_bounded κ hfm hfb i x)
    (section_memLp_of_bounded κ hgm hgb i x)

theorem integrable_kernelCovariance (hstat : PreservesLaw κ μ)
    {f g : (∀ k, E k) → ℝ} {B D : ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ B)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ D) (i : ι) :
    Integrable (kernelCovariance κ f g i) μ := by
  have hf2 := DensityMoments.memLp_of_bounded (μ := μ) hfm ⟨B, hfb⟩ 2
  have hg2 := DensityMoments.memLp_of_bounded (μ := μ) hgm ⟨D, hgb⟩ 2
  have hprod := hf2.integrable_mul hg2
  have havg := ConditionalVarianceIntegral.integrable_siteAverage κ μ hstat
    (hfm.mul hgm) hprod i
  have hmul := (siteAverage_memLp_of_bounded κ μ hfm hfb i).integrable_mul
    (siteAverage_memLp_of_bounded κ μ hgm hgb i)
  exact (havg.sub hmul).congr (Eventually.of_forall fun x ↦
    (kernelCovariance_eq κ hfm hfb hgm hgb i x).symm)

/-- Total covariance is derived from actual stationary resampling and
finite products. It is not a constructor hypothesis. -/
theorem covariance_decomposition (hstat : PreservesLaw κ μ)
    {f g : (∀ k, E k) → ℝ} {B D : ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ B)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ D) (i : ι) :
    covariance f g μ = (∫ x, kernelCovariance κ f g i x ∂μ) +
      covariance (siteAverage κ f i) (siteAverage κ g i) μ := by
  have hf2 := DensityMoments.memLp_of_bounded (μ := μ) hfm ⟨B, hfb⟩ 2
  have hg2 := DensityMoments.memLp_of_bounded (μ := μ) hgm ⟨D, hgb⟩ 2
  have ha2 := siteAverage_memLp_of_bounded κ μ hfm hfb i
  have hq2 := siteAverage_memLp_of_bounded κ μ hgm hgb i
  have hmeanf := ConditionalVarianceIntegral.integral_siteAverage κ μ hstat hfm
    (hf2.integrable (by norm_num)) i
  have hmeang := ConditionalVarianceIntegral.integral_siteAverage κ μ hstat hgm
    (hg2.integrable (by norm_num)) i
  have hprod := hf2.integrable_mul hg2
  have hmeanprod := ConditionalVarianceIntegral.integral_siteAverage κ μ hstat
    (hfm.mul hgm) hprod i
  have hcond : (∫ x, kernelCovariance κ f g i x ∂μ) =
      (∫ x, f x * g x ∂μ) - ∫ x, siteAverage κ f i x * siteAverage κ g i x ∂μ := by
    rw [integral_congr_ae (Eventually.of_forall (kernelCovariance_eq κ hfm hfb hgm hgb i))]
    change (∫ x, siteAverage κ (f * g) i x - (siteAverage κ f i * siteAverage κ g i) x ∂μ) = _
    rw [integral_sub (ConditionalVarianceIntegral.integrable_siteAverage κ μ hstat
        (hfm.mul hgm) hprod i) (ha2.integrable_mul hq2), hmeanprod]
    rfl
  rw [covariance_eq_sub hf2 hg2, covariance_eq_sub ha2 hq2, hmeanf, hmeang, hcond]
  simp only [Pi.mul_apply]
  ring

/-- The two conditional Cauchy--Schwarz applications can be performed
together on the actual resampling product measure. Fubini is used only
after the residuals and their products have genuine finite moments. -/
theorem integral_kernelCovariance_squared_le
    {f g : (∀ k, E k) → ℝ} {B D : ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ B)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ D) (i : ι) :
    (∫ x, kernelCovariance κ f g i x ∂μ) ^ 2 ≤
      (∫ x, kernelVariance κ f i x ∂μ) * (∫ x, kernelVariance κ g i x ∂μ) := by
  let U : (∀ k, E k) × E i → ℝ := fun p ↦
    f (Function.update p.1 i p.2) - siteAverage κ f i p.1
  let V : (∀ k, E k) × E i → ℝ := fun p ↦
    g (Function.update p.1 i p.2) - siteAverage κ g i p.1
  have hUm : Measurable U := (hfm.comp measurable_update').sub
    ((measurable_siteAverage κ hfm i).comp measurable_fst)
  have hVm : Measurable V := (hgm.comp measurable_update').sub
    ((measurable_siteAverage κ hgm i).comp measurable_fst)
  have hUb (p : (∀ k, E k) × E i) : |U p| ≤ B + B :=
    (abs_sub _ _).trans (add_le_add (hfb _) (siteAverage_bound κ hfb i _))
  have hVb (p : (∀ k, E k) × E i) : |V p| ≤ D + D :=
    (abs_sub _ _).trans (add_le_add (hgb _) (siteAverage_bound κ hgb i _))
  have hU : MemLp U 2 (μ ⊗ₘ κ i) := DensityMoments.memLp_of_bounded hUm ⟨B + B, hUb⟩ 2
  have hV : MemLp V 2 (μ ⊗ₘ κ i) := DensityMoments.memLp_of_bounded hVm ⟨D + D, hVb⟩ 2
  have hC : (∫ p, U p * V p ∂(μ ⊗ₘ κ i)) = ∫ x, kernelCovariance κ f g i x ∂μ := by
    change (∫ p, (U * V) p ∂(μ ⊗ₘ κ i)) = _
    rw [Measure.integral_compProd (hU.integrable_mul hV)]
    rfl
  have hF : (∫ p, U p ^ 2 ∂(μ ⊗ₘ κ i)) = ∫ x, kernelVariance κ f i x ∂μ := by
    rw [Measure.integral_compProd hU.integrable_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦
      (variance_eq_integral (hfm.comp (measurable_update x)).aemeasurable).symm
  have hG : (∫ p, V p ^ 2 ∂(μ ⊗ₘ κ i)) = ∫ x, kernelVariance κ g i x ∂μ := by
    rw [Measure.integral_compProd hV.integrable_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦
      (variance_eq_integral (hgm.comp (measurable_update x)).aemeasurable).symm
  simpa only [hC, hF, hG] using integral_mul_squared_le hU hV

theorem integral_kernelVariance_le_variance (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) {g : (∀ k, E k) → ℝ} (hg : MemLp g 2 μ) (i : ι) :
    (∫ x, kernelVariance κ g i x ∂μ) ≤ variance g μ := by
  have hh := integral_condVar_add_variance_condExp (outsideSigma_le E i) hg
  rw [← ConditionalVarianceIntegral.integral_kernelVariance κ μ hind hstat hg i] at hh
  linarith [variance_nonneg (μ[g | outsideSigma E i]) μ]

theorem covariance_splitting_squared (hind : IndependentSite κ) (hstat : PreservesLaw κ μ)
    {f g : (∀ k, E k) → ℝ} {B D : ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ B)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ D) (i : ι) :
    covariance f g μ ^ 2 ≤
      2 * (∫ x, kernelVariance κ f i x ∂μ) * variance g μ +
        2 * variance (siteAverage κ f i) μ * variance (siteAverage κ g i) μ := by
  have hg2 := DensityMoments.memLp_of_bounded (μ := μ) hgm ⟨D, hgb⟩ 2
  have hfirst := (integral_kernelCovariance_squared_le κ μ hfm hfb hgm hgb i).trans
    (mul_le_mul_of_nonneg_left (integral_kernelVariance_le_variance κ μ hind hstat hg2 i)
      (integral_nonneg fun x ↦ variance_nonneg _ _))
  have hsecond := covariance_squared_le (siteAverage_memLp_of_bounded κ μ hfm hfb i)
    (siteAverage_memLp_of_bounded κ μ hgm hgb i)
  rw [covariance_decomposition κ μ hstat hfm hfb hgm hgb i]
  nlinarith [sq_nonneg ((∫ x, kernelCovariance κ f g i x ∂μ) -
    covariance (siteAverage κ f i) (siteAverage κ g i) μ)]

/-- The conditional Bernoulli variance is exactly q(1-q), before its
integral is compared with the actual global Bernoulli variance. -/
theorem kernelVariance_indicator (s : Set (∀ k, E k)) (hs : MeasurableSet s)
    (i : ι) (x : ∀ k, E k) :
    kernelVariance κ (s.indicator (fun _ ↦ (1 : ℝ))) i x =
      siteAverage κ (s.indicator (fun _ ↦ (1 : ℝ))) i x *
        (1 - siteAverage κ (s.indicator (fun _ ↦ (1 : ℝ))) i x) :=
  bernoulli_variance
    (section_memLp_of_bounded κ (measurable_const.indicator hs) (indicator_bound s) i x)
    (fun _ ↦ indicator_squared s _)

end ConditionalSplitting

section ActualAdjacentLaw

variable {n J : ℕ}

/-- The source indicator retains the distinguished particle label. -/
def leftEvent (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J) :
    Set (Configuration (n + 1)) := {X | X i ∈ meshCell J hJ a}

def leftIndicator (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J) :
    Configuration (n + 1) → ℝ := (leftEvent hJ i a).indicator (fun _ ↦ 1)

theorem measurable_leftIndicator (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J) :
    Measurable (leftIndicator hJ i a) :=
  measurable_const.indicator ((measurableSet_meshCell J hJ a).preimage (measurable_pi_apply i))

def adjacentKernels (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (β : ℝ) :
    Fin (n + 1) → Kernel (Configuration (n + 1)) Torus :=
  CoordinateConditionalKernels.gibbsKernel
    (fun k ↦ patchMeasure J hJ (Function.update η i a k) (adjacentShapes i d k)) β

instance isMarkovKernel_adjacentKernels (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (β : ℝ) (k : Fin (n + 1)) :
    IsMarkovKernel (adjacentKernels hJ η i a d β k) := by
  unfold adjacentKernels
  infer_instance

theorem independentSite_adjacentKernels (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (β : ℝ) :
    IndependentSite (adjacentKernels hJ η i a d β) :=
  CoordinateConditionalKernels.independentSite_gibbsKernel _ _

/-- This is proved from the existing Gibbs disintegration with the actual
outside marginal, for every resampled coordinate. -/
theorem preservesLaw_adjacentKernels (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    PreservesLaw (adjacentKernels hJ η i a d β)
      (twoCellGibbsMeasure hJ η i a (nextCell J hJ a d) β) := by
  let :=  isProbabilityMeasure_twoCellGibbsMeasure hJ hn η i
    (Ne.symm (nextCell_ne J hJ hJ2 a d)) hβ hsub
  apply CoordinateConditionalKernels.preservesLaw_finLift
  intro k F hF
  exact lintegral_twoCell_conditionals hJ hJ2 hn η i k a d hβ hsub hF

theorem adjacentKernels_self (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (β : ℝ)
    (X : Configuration (n + 1)) :
    adjacentKernels hJ η i a d β i X =
      conditionalKernel (edgeCellMeasure J hJ a d) i β (removeSite i X) := by
  change conditionalKernel
    (patchMeasure J hJ (Function.update η i a i) (adjacentShapes i d i))
      i β (removeSite i X) = _
  simp only [adjacent_measure_self]

/-- The conditional mean, crossing probability, and variance all use the
actual union-of-two-cells conditional kernel from Proposition 3.4. -/
def conditionalAverage (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J)
    (d : Fin 2) (β : ℝ) (f : Configuration (n + 1) → ℝ)
    (X : Configuration (n + 1)) : ℝ :=
  ∫ z, f (insertSite i z (removeSite i X))
    ∂conditionalKernel (edgeCellMeasure J hJ a d) i β (removeSite i X)

def crossingProbability (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J)
    (d : Fin 2) (β : ℝ) (X : Configuration (n + 1)) : ℝ :=
  (conditionalKernel (edgeCellMeasure J hJ a d) i β (removeSite i X)).real (meshCell J hJ a)

def conditionalVariance (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J)
    (d : Fin 2) (β : ℝ) (f : Configuration (n + 1) → ℝ)
    (X : Configuration (n + 1)) : ℝ :=
  variance (fun z ↦ f (insertSite i z (removeSite i X)))
    (conditionalKernel (edgeCellMeasure J hJ a d) i β (removeSite i X))

def conditionalIndicatorCovariance (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J)
    (d : Fin 2) (β : ℝ) (f : Configuration (n + 1) → ℝ)
    (X : Configuration (n + 1)) : ℝ :=
  covariance (fun z ↦ f (insertSite i z (removeSite i X)))
    ((meshCell J hJ a).indicator (fun _ ↦ (1 : ℝ)))
    (conditionalKernel (edgeCellMeasure J hJ a d) i β (removeSite i X))

theorem siteAverage_eq_conditionalAverage (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (β : ℝ)
    (f : Configuration (n + 1) → ℝ) :
    siteAverage (adjacentKernels hJ η i a d β) f i = conditionalAverage hJ i a d β f := by
  funext X
  simp only [siteAverage, conditionalAverage, adjacentKernels_self,
    CoordinateConditionalKernels.insertSite_eq_update]

theorem leftIndicator_update (hJ : 0 < J) (i : Fin (n + 1)) (a : MeshIndex J)
    (X : Configuration (n + 1)) (z : Torus) :
    leftIndicator hJ i a (Function.update X i z) =
      (meshCell J hJ a).indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  by_cases hz : z ∈ meshCell J hJ a <;>
    simp only [mem_meshCell] at hz <;> simp [leftIndicator, leftEvent, hz]

theorem siteAverage_indicator_eq_crossingProbability (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J)
    (d : Fin 2) (β : ℝ) :
    siteAverage (adjacentKernels hJ η i a d β) (leftIndicator hJ i a) i =
      crossingProbability hJ i a d β := by
  funext X
  simp only [siteAverage, adjacentKernels_self, leftIndicator_update, crossingProbability]
  exact integral_indicator_one (measurableSet_meshCell J hJ a)

theorem kernelVariance_eq_conditionalVariance (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (β : ℝ)
    (f : Configuration (n + 1) → ℝ) :
    kernelVariance (adjacentKernels hJ η i a d β) f i = conditionalVariance hJ i a d β f := by
  funext X
  simp only [kernelVariance, conditionalVariance, adjacentKernels_self,
    CoordinateConditionalKernels.insertSite_eq_update]

theorem kernelCovariance_eq_conditionalIndicatorCovariance (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J)
    (d : Fin 2) (β : ℝ) (f : Configuration (n + 1) → ℝ) :
    kernelCovariance (adjacentKernels hJ η i a d β) f (leftIndicator hJ i a) i =
      conditionalIndicatorCovariance hJ i a d β f := by
  funext X
  simp only [kernelCovariance, conditionalIndicatorCovariance, adjacentKernels_self,
    CoordinateConditionalKernels.insertSite_eq_update, leftIndicator_update]

/-- Exact edge covariance, with the coefficient defined from the actual
specified-label event masses. No permutation symmetry is used. -/
theorem twoCell_indicator_covariance (hJ : 0 < J) (hn : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration (n + 1) → ℝ} {B : ℝ}
    (hfm : Measurable f) (hfb : ∀ X, |f X| ≤ B) :
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    (∫ X, leftIndicator hJ i a X ∂P) = p ∧
      covariance f (leftIndicator hJ i a) P = p * (1 - p) *
        ((∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i a) β) -
          ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i b) β) := by
  let :=  isProbabilityMeasure_twoCellGibbsMeasure hJ hn η i hab hβ hsub
  let :=  isProbabilityMeasure_labelGibbsMeasure hJ hn (Function.update η i a) hβ hsub
  let :=  isProbabilityMeasure_labelGibbsMeasure hJ hn (Function.update η i b) hβ hsub
  have hs : MeasurableSet (leftEvent hJ i a) :=
    (measurableSet_meshCell J hJ a).preimage (measurable_pi_apply i)
  have hsupport (c : MeshIndex J) :
      ∀ᵐ X ∂labelGibbsMeasure hJ (Function.update η i c) β,
        X ∈ labelFiber hJ (Function.update η i c) := by
    let :=  isProbabilityMeasure_labelGibbsMeasure hJ hn (Function.update η i c) hβ hsub
    apply (ae_mem_iff_measure_eq (measurableSet_labelFiber hJ _).nullMeasurableSet).mpr
    simpa only [measure_univ] using labelGibbsMeasure_labelFiber hJ hn (Function.update η i c) hβ hsub
  apply two_label_indicator_covariance (twoCellMixingWeight_le_one hJ hn η i a b hβ hsub)
    (twoCellGibbsMeasure_eq_mixture hJ hn η i hab hβ hsub) (leftEvent hJ i a) hs
    _ _ hfm hfb
  · exact (hsupport a).mono fun X hX ↦ ((mem_labelFiber_update hJ η i a X).mp hX).1
  · filter_upwards [hsupport b] with X hX
    have hXb := ((mem_labelFiber_update hJ η i b X).mp hX).1
    intro hXa
    exact hab (((mem_meshCell J hJ a (X i)).mp hXa).symm.trans
      ((mem_meshCell J hJ b (X i)).mp hXb))

theorem adjacent_covariance_decomposition (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration (n + 1) → ℝ} {B : ℝ}
    (hfm : Measurable f) (hfb : ∀ X, |f X| ≤ B) :
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a d) β
    Integrable (conditionalIndicatorCovariance hJ i a d β f) P ∧
      covariance f (leftIndicator hJ i a) P =
        (∫ X, conditionalIndicatorCovariance hJ i a d β f X ∂P) +
          covariance (conditionalAverage hJ i a d β f) (crossingProbability hJ i a d β) P := by
  let :=  isProbabilityMeasure_twoCellGibbsMeasure hJ hn η i
    (Ne.symm (nextCell_ne J hJ hJ2 a d)) hβ hsub
  have hstat := preservesLaw_adjacentKernels hJ hJ2 hn η i a d hβ hsub
  have hm := measurable_leftIndicator hJ i a
  have hb := indicator_bound (leftEvent hJ i a)
  have hi := integrable_kernelCovariance (adjacentKernels hJ η i a d β) _ hstat hfm hfb hm hb i
  have he := covariance_decomposition (adjacentKernels hJ η i a d β) _ hstat hfm hfb hm hb i
  rw [kernelCovariance_eq_conditionalIndicatorCovariance] at hi he
  rw [siteAverage_indicator_eq_crossingProbability, siteAverage_eq_conditionalAverage] at he
  exact ⟨hi, he⟩

/-- The actual conditional mean and crossing probability are square
integrable. The conditional variance and Bernoulli variance are integrable,
and the latter has exactly the source bound p(1-p). -/
theorem adjacent_integrability_and_crossing (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration (n + 1) → ℝ} {B : ℝ}
    (hfm : Measurable f) (hfb : ∀ X, |f X| ≤ B) :
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a d) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a d) β).toReal
    let A := conditionalAverage hJ i a d β f
    let q := crossingProbability hJ i a d β
    MemLp A 2 P ∧ MemLp q 2 P ∧
      Integrable (conditionalVariance hJ i a d β f) P ∧
      (∫ X, q X ∂P) = p ∧
      Integrable (fun X ↦ q X * (1 - q X)) P ∧
      (∫ X, q X * (1 - q X) ∂P) ≤ p * (1 - p) := by
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a d) β
  let κ := adjacentKernels hJ η i a d β
  let I := leftIndicator hJ i a
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hn η i
    (Ne.symm (nextCell_ne J hJ hJ2 a d)) hβ hsub
  have hind := independentSite_adjacentKernels hJ η i a d β
  have hstat := preservesLaw_adjacentKernels hJ hJ2 hn η i a d hβ hsub
  have hIm := measurable_leftIndicator hJ i a
  have hIb := indicator_bound (leftEvent hJ i a)
  have hf2 : MemLp f 2 P := DensityMoments.memLp_of_bounded hfm ⟨B, hfb⟩ 2
  have hI2 : MemLp I 2 P := DensityMoments.memLp_of_bounded hIm ⟨1, hIb⟩ 2
  have hA := siteAverage_memLp_of_bounded κ P hfm hfb i
  have hq := siteAverage_memLp_of_bounded κ P hIm hIb i
  have hV := ConditionalVarianceIntegral.integrable_kernelVariance κ P hind hstat hf2 i
  have hVI := ConditionalVarianceIntegral.integrable_kernelVariance κ P hind hstat hI2 i
  have hmean := ConditionalVarianceIntegral.integral_siteAverage κ P hstat hIm
    (hI2.integrable (by norm_num)) i
  have hedge := twoCell_indicator_covariance hJ hn η i
    (Ne.symm (nextCell_ne J hJ hJ2 a d)) hβ hsub hfm hfb
  have hvar : variance I P =
      (twoCellMixingWeight hJ η i a (nextCell J hJ a d) β).toReal *
        (1 - (twoCellMixingWeight hJ η i a (nextCell J hJ a d) β).toReal) := by
    rw [bernoulli_variance hI2 (indicator_squared (leftEvent hJ i a)), hedge.1]
  have hVIeq : kernelVariance κ I i = fun X ↦ crossingProbability hJ i a d β X *
      (1 - crossingProbability hJ i a d β X) := by
    funext X
    change kernelVariance (adjacentKernels hJ η i a d β)
      ((leftEvent hJ i a).indicator (fun _ ↦ (1 : ℝ))) i X = _
    rw [kernelVariance_indicator (adjacentKernels hJ η i a d β) (leftEvent hJ i a)
      ((measurableSet_meshCell J hJ a).preimage (measurable_pi_apply i))]
    change siteAverage (adjacentKernels hJ η i a d β) (leftIndicator hJ i a) i X *
      (1 - siteAverage (adjacentKernels hJ η i a d β) (leftIndicator hJ i a) i X) = _
    rw [siteAverage_indicator_eq_crossingProbability]
  have hbound := integral_kernelVariance_le_variance κ P hind hstat hI2 i
  rw [hVIeq, hvar] at hbound
  rw [hVIeq] at hVI
  change MemLp (siteAverage (adjacentKernels hJ η i a d β) f i) 2 P at hA
  change MemLp (siteAverage (adjacentKernels hJ η i a d β) (leftIndicator hJ i a) i) 2 P at hq
  change Integrable (kernelVariance (adjacentKernels hJ η i a d β) f i) P at hV
  change (∫ X, siteAverage (adjacentKernels hJ η i a d β) (leftIndicator hJ i a) i X ∂P) = _ at hmean
  rw [siteAverage_eq_conditionalAverage] at hA
  rw [siteAverage_indicator_eq_crossingProbability] at hq hmean
  rw [kernelVariance_eq_conditionalVariance] at hV
  rw [hedge.1] at hmean
  exact ⟨hA, hq, hV, hmean, hVI, hbound⟩

/-- The source boundary split for a bounded measurable observable. Its
mixing factor is computed from actual label masses; both cap hypotheses
discharge the source mixing-range theorem and hence the positive divisor.
No covariance identity or desired inequality is an input. -/
theorem adjacent_boundary_splitting_bounded (hn : 2 ≤ n + 1)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    {f : Configuration (n + 1) → ℝ} {B : ℝ}
    (hfm : Measurable f) (hfb : ∀ X, |f X| ≤ B) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a d
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let Φa := ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i a) β
    let Φb := ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i b) β
    let A := conditionalAverage hJ i a d β f
    let q := crossingProbability hJ i a d β
    0 < p ∧ p < 1 ∧
      p * (1 - p) * (Φa - Φb) ^ 2 ≤
        2 * (∫ X, conditionalVariance hJ i a d β f X ∂P) +
          2 * variance A P * variance q P / (p * (1 - p)) := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a d
  let P := twoCellGibbsMeasure hJ η i a b β
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  let κ := adjacentKernels hJ η i a d β
  have hab : a ≠ b := Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a d)
  let : IsProbabilityMeasure P :=
    isProbabilityMeasure_twoCellGibbsMeasure hJ hn η i hab hβ (hβ₀.trans_lt hsub)
  have hr := LabelRatioTransport.adjacent_mixing_range hn hβ hβ₀ hsub hδ₀ hδ hmesh η i a d hadm
  change lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 at hr
  have hp0 : 0 < p := by linarith [lowerBound_pos β₀, hr.1]
  have hp1 : p < 1 := lt_of_le_of_lt hr.2 (by linarith [lowerBound_pos β₀])
  have hd : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hm := measurable_leftIndicator hJ i a
  have hb := indicator_bound (leftEvent hJ i a)
  have hI2 : MemLp (leftIndicator hJ i a) 2 P :=
    DensityMoments.memLp_of_bounded hm ⟨1, hb⟩ 2
  have hedge := twoCell_indicator_covariance hJ hn η i hab hβ (hβ₀.trans_lt hsub) hfm hfb
  have hvar : variance (leftIndicator hJ i a) P = p * (1 - p) := by
    rw [bernoulli_variance hI2 (indicator_squared (leftEvent hJ i a)), hedge.1]
  have hs := covariance_splitting_squared κ P
    (independentSite_adjacentKernels hJ η i a d β)
    (preservesLaw_adjacentKernels hJ (mesh_two_le hmesh) hn η i a d hβ (hβ₀.trans_lt hsub))
    hfm hfb hm hb i
  change covariance f (leftIndicator hJ i a) P ^ 2 ≤
    2 * (∫ X, kernelVariance (adjacentKernels hJ η i a d β) f i X ∂P) *
      variance (leftIndicator hJ i a) P +
      2 * variance (siteAverage (adjacentKernels hJ η i a d β) f i) P *
        variance (siteAverage (adjacentKernels hJ η i a d β) (leftIndicator hJ i a) i) P at hs
  rw [kernelVariance_eq_conditionalVariance, siteAverage_indicator_eq_crossingProbability,
    siteAverage_eq_conditionalAverage, hvar] at hs
  refine ⟨hp0, hp1, ?_⟩
  change p * (1 - p) * ((∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i a) β) -
    ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i b) β) ^ 2 ≤
      2 * (∫ X, conditionalVariance hJ i a d β f X ∂P) +
        2 * variance (conditionalAverage hJ i a d β f) P *
          variance (crossingProbability hJ i a d β) P / (p * (1 - p))
  calc
    _ = covariance f (leftIndicator hJ i a) P ^ 2 / (p * (1 - p)) := by
      have he : covariance f (leftIndicator hJ i a) P = p * (1 - p) *
          ((∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i a) β) -
            ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i b) β) := hedge.2
      rw [he]
      apply (eq_div_iff hd.ne').mpr
      ring
    _ ≤ (2 * (∫ X, conditionalVariance hJ i a d β f X ∂P) * (p * (1 - p)) +
        2 * variance (conditionalAverage hJ i a d β f) P *
          variance (crossingProbability hJ i a d β) P) / (p * (1 - p)) :=
      div_le_div_of_nonneg_right hs hd.le
    _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hd.ne']

/-- Source endpoint for continuous observables on the compact ambient
configuration torus, in particular for each source smooth observable.
Boundedness and measurability are proved here, with no symmetry premise. -/
theorem adjacent_boundary_splitting (hn : 2 ≤ n + 1)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    {f : Configuration (n + 1) → ℝ} (hf : Continuous f) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a d
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let Φa := ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i a) β
    let Φb := ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i b) β
    let A := conditionalAverage hJ i a d β f
    let q := crossingProbability hJ i a d β
    0 < p ∧ p < 1 ∧
      p * (1 - p) * (Φa - Φb) ^ 2 ≤
        2 * (∫ X, conditionalVariance hJ i a d β f X ∂P) +
          2 * variance A P * variance q P / (p * (1 - p)) := by
  obtain ⟨B, _hB, hb⟩ := (isCompact_univ.image_of_continuousOn hf.continuousOn).isBounded.exists_pos_norm_le
  apply adjacent_boundary_splitting_bounded hn hβ hβ₀ hsub hδ₀ hδ hmesh η i a d hadm hf.measurable
  intro X
  exact hb _ (mem_image_of_mem f (mem_univ X))

end ActualAdjacentLaw

end PeriodicAttractiveLogGas.BoundaryCovarianceSplitting
