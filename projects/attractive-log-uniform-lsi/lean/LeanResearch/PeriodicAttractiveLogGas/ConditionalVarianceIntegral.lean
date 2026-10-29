import LeanResearch.PeriodicAttractiveLogGas.DobrushinVariance

/-! Literal resampling variances for arbitrary square-integrable functions.
Stationarity supplies all joint and sectional integrability; no pointwise
bounded representative or conditional-expectation identity is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace PeriodicAttractiveLogGas.ConditionalVarianceIntegral

open CoordinateOscillation ConditionalKernelL2 ConditionalL2Projections

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)]
variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]
variable (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ]

omit [∀ i, IsMarkovKernel (κ i)] [IsProbabilityMeasure μ] in
theorem measurePreserving_resample (hstat : PreservesLaw κ μ) (i : ι) :
    MeasurePreserving (fun p : (∀ k, E k) × E i ↦ Function.update p.1 i p.2)
      (μ ⊗ₘ κ i) μ := ⟨measurable_update', hstat i⟩

omit [∀ i, IsMarkovKernel (κ i)] [IsProbabilityMeasure μ] in
theorem integrable_resample (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} (hf : Integrable f μ) (i : ι) :
    Integrable (fun p : (∀ k, E k) × E i ↦ f (Function.update p.1 i p.2)) (μ ⊗ₘ κ i) :=
  (measurePreserving_resample κ μ hstat i).integrable_comp_of_integrable hf

theorem integrable_siteAverage (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} (hm : Measurable f) (hf : Integrable f μ) (i : ι) :
    Integrable (siteAverage κ f i) μ := by
  have hi := integrable_resample κ μ hstat hf i
  have hn := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).2
  apply hn.mono' (measurable_siteAverage κ hm i).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ norm_integral_le_integral_norm _

theorem integral_siteAverage (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} (hm : Measurable f) (hf : Integrable f μ) (i : ι) :
    (∫ x, siteAverage κ f i x ∂μ) = ∫ x, f x ∂μ := by
  calc
    _ = ∫ p : (∀ k, E k) × E i, f (Function.update p.1 i p.2) ∂(μ ⊗ₘ κ i) :=
      (Measure.integral_compProd (integrable_resample κ μ hstat hf i)).symm
    _ = ∫ x, f x ∂Measure.map (fun p : (∀ k, E k) × E i ↦ Function.update p.1 i p.2)
        (μ ⊗ₘ κ i) :=
      (integral_map_of_stronglyMeasurable measurable_update' hm.stronglyMeasurable).symm
    _ = _ := by rw [hstat i]

theorem setIntegral_siteAverage (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} (hm : Measurable f) (hf : Integrable f μ) (i : ι)
    {s : Set (∀ k, E k)} (hs : MeasurableSet[outsideSigma E i] s) :
    (∫ x in s, siteAverage κ f i x ∂μ) = ∫ x in s, f x ∂μ := by
  have hs₀ : MeasurableSet s := outsideSigma_le E i s hs
  rw [← integral_indicator hs₀, ← integral_indicator hs₀,
    ← ConditionalKernelL2.siteAverage_indicator κ i hs f]
  exact integral_siteAverage κ μ hstat (hm.indicator hs₀) (hf.indicator hs₀) i

theorem siteAverage_ae_eq_condExp (hind : IndependentSite κ) (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} (hm : Measurable f) (hf : Integrable f μ) (i : ι) :
    siteAverage κ f i =ᵐ[μ] μ[f | outsideSigma E i] := by
  let := nonempty_of_isProbabilityMeasure μ
  have hi := integrable_siteAverage κ μ hstat hm hf i
  apply ae_eq_condExp_of_forall_setIntegral_eq (outsideSigma_le E i) hf
    (fun _ _ _ ↦ hi.integrableOn)
    (fun s hs _ ↦ setIntegral_siteAverage κ μ hstat hm hf i hs)
  exact (measurable_outside_siteAverage κ hind hm i).stronglyMeasurable.aestronglyMeasurable

theorem ae_section_memLp (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} (hm : Measurable f) (hf : MemLp f 2 μ) (i : ι) :
    ∀ᵐ x ∂μ, MemLp (fun z ↦ f (Function.update x i z)) 2 (κ i x) := by
  have hi := integrable_resample κ μ hstat hf.integrable_sq i
  have hs := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).1
  filter_upwards [hs] with x hx
  exact (memLp_two_iff_integrable_sq
    (hm.comp (measurable_update x)).aestronglyMeasurable).mpr hx

def kernelVariance (f : (∀ k, E k) → ℝ) (i : ι) (x : ∀ k, E k) : ℝ :=
  ProbabilityTheory.variance (fun z ↦ f (Function.update x i z)) (κ i x)

theorem kernelVariance_ae_eq_condVar_of_measurable (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) {f : (∀ k, E k) → ℝ}
    (hm : Measurable f) (hf : MemLp f 2 μ) (i : ι) :
    kernelVariance κ f i =ᵐ[μ] ProbabilityTheory.condVar (outsideSigma E i) f μ := by
  have hm₂ : Measurable (fun x ↦ f x ^ 2) := hm.pow_const 2
  have hs := siteAverage_ae_eq_condExp κ μ hind hstat hm₂ hf.integrable_sq i
  have ha := siteAverage_ae_eq_condExp κ μ hind hstat hm (hf.integrable (by norm_num)) i
  have hv := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp (outsideSigma_le E i) hf
  filter_upwards [ae_section_memLp κ μ hstat hm hf i, hs, ha, hv] with x hx hsx hax hvx
  rw [kernelVariance, ProbabilityTheory.variance_eq_sub hx]
  change siteAverage κ (fun x ↦ f x ^ 2) i x - (siteAverage κ f i x) ^ 2 = _
  rw [hsx, hax]
  exact hvx.symm

theorem ae_sections_congr (hstat : PreservesLaw κ μ)
    {f g : (∀ k, E k) → ℝ} (hfg : f =ᵐ[μ] g) (i : ι) :
    ∀ᵐ x ∂μ, (fun z ↦ f (Function.update x i z)) =ᵐ[κ i x]
      (fun z ↦ g (Function.update x i z)) :=
  Measure.ae_ae_of_ae_compProd
    ((measurePreserving_resample κ μ hstat i).quasiMeasurePreserving.ae hfg)

theorem kernelVariance_congr_ae (hstat : PreservesLaw κ μ)
    {f g : (∀ k, E k) → ℝ} (hfg : f =ᵐ[μ] g) (i : ι) :
    kernelVariance κ f i =ᵐ[μ] kernelVariance κ g i := by
  filter_upwards [ae_sections_congr κ μ hstat hfg i] with x hx
  exact ProbabilityTheory.variance_congr hx

/-- All L2 representatives, with the actual conditional law at each point.
The necessary measurable representative is used only inside the proof. -/
theorem kernelVariance_ae_eq_condVar (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) {f : (∀ k, E k) → ℝ} (hf : MemLp f 2 μ) (i : ι) :
    kernelVariance κ f i =ᵐ[μ] ProbabilityTheory.condVar (outsideSigma E i) f μ := by
  let g := hf.aestronglyMeasurable.mk f
  have hm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  exact (kernelVariance_congr_ae κ μ hstat hfg i).trans
    ((kernelVariance_ae_eq_condVar_of_measurable κ μ hind hstat hm ((memLp_congr_ae hfg).mp hf) i).trans
      (ProbabilityTheory.condVar_congr_ae hfg).symm)

theorem integrable_kernelVariance (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) {f : (∀ k, E k) → ℝ} (hf : MemLp f 2 μ) (i : ι) :
    Integrable (kernelVariance κ f i) μ :=
  ProbabilityTheory.integrable_condVar.congr (kernelVariance_ae_eq_condVar κ μ hind hstat hf i).symm

theorem integral_kernelVariance (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) {f : (∀ k, E k) → ℝ} (hf : MemLp f 2 μ) (i : ι) :
    (∫ x, kernelVariance κ f i x ∂μ) =
      ∫ x, ProbabilityTheory.condVar (outsideSigma E i) f μ x ∂μ :=
  integral_congr_ae (kernelVariance_ae_eq_condVar κ μ hind hstat hf i)

variable [Fintype ι] [Nonempty ι]

theorem variance_le_kernel_variances (hind : IndependentSite κ) (hstat : PreservesLaw κ μ)
    (hα : maxColumnSum κ < 1) {f : (∀ k, E k) → ℝ} (hf : MemLp f 2 μ) :
    ProbabilityTheory.variance f μ ≤ (1 - maxColumnSum κ)⁻¹ *
      ∑ i, ∫ x, kernelVariance κ f i x ∂μ := by
  have h := DobrushinVariance.approximate_tensorization_memLp μ κ hind hstat hα hf
  simpa only [integral_kernelVariance κ μ hind hstat hf] using h

theorem variance_le_twice_kernel_variances (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) (hα : maxColumnSum κ ≤ 1 / 2)
    {f : (∀ k, E k) → ℝ} (hf : MemLp f 2 μ) :
    ProbabilityTheory.variance f μ ≤ 2 * ∑ i, ∫ x, kernelVariance κ f i x ∂μ := by
  have hlt : maxColumnSum κ < 1 := by linarith
  have hc : (1 - maxColumnSum κ)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - maxColumnSum κ)]
    linarith
  have hs : 0 ≤ ∑ i, ∫ x, kernelVariance κ f i x ∂μ :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ ProbabilityTheory.variance_nonneg _ _
  exact (variance_le_kernel_variances κ μ hind hstat hlt hf).trans
    (mul_le_mul_of_nonneg_right hc hs)

end PeriodicAttractiveLogGas.ConditionalVarianceIntegral
