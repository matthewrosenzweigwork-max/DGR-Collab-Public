import DGRHS.Concentration.SourceD

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Concentration

lemma ae_absolute_le_essSup_toReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f ∞ μ) :
    ∀ᵐ x ∂μ, |f x| ≤ (eLpNormEssSup f μ).toReal := by
  have hh : eLpNormEssSup f μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hf.eLpNorm_ne_top
  filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
  simpa only [toReal_enorm,Real.norm_eq_abs] using ENNReal.toReal_mono hh hx

/-- Empty matrices have A=0. This is the maximum of the genuine joint essential norms. -/
def kernelSourceA {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ) : ℝ :=
  ↑(Finset.univ.sup fun ij : Fin n × Fin q ↦ (eLpNormEssSup (h ij.1 ij.2) ((μ ij.1).prod (ν ij.2))).toNNReal)

def kernelRowEnergy {Ω Ψ : Type*} [MeasurableSpace Ψ] {n q : ℕ}
    (ν : Fin q → Measure Ψ) (h : Fin n → Fin q → Ω × Ψ → ℝ) (i : Fin n) (x : Ω) : ℝ :=
  ∑ j, ∫ y, (h i j (x,y))^2 ∂ν j

/-- Both marginal energy norms are essential norms. No pointwise supremum occurs. -/
def kernelSourceB {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ) : ℝ :=
  Real.sqrt (max
    (↑(Finset.univ.sup fun i : Fin n ↦ (eLpNormEssSup (kernelRowEnergy ν h i) (μ i)).toNNReal) : ℝ)
    (↑(Finset.univ.sup fun j : Fin q ↦ (eLpNormEssSup (kernelColumnEnergy μ h j) (ν j)).toNNReal) : ℝ))

def kernelSourceC {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j))

lemma kernelSourceA_bound {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ)
    (hh : ∀ i j, MemLp (h i j) ∞ ((μ i).prod (ν j))) :
    ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ kernelSourceA μ ν h := by
  intro i j
  filter_upwards [ae_absolute_le_essSup_toReal ((μ i).prod (ν j)) (h i j) (hh i j)] with p hp
  apply hp.trans
  exact_mod_cast (Finset.le_sup (f := fun ij : Fin n × Fin q ↦
    (eLpNormEssSup (h ij.1 ij.2) ((μ ij.1).prod (ν ij.2))).toNNReal) (Finset.mem_univ (i,j)))

lemma bounded_section_square_integral {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    ∀ᵐ x ∂μ, (∫ y, (h (x,y))^2 ∂ν) ≤ A^2 := by
  filter_upwards [bounded_kernel_sections_memLp μ ν h A hAES hBound,
    Measure.ae_ae_of_ae_prod hBound] with x hx hb
  have hi := (memLp_two_iff_integrable_sq hx.aestronglyMeasurable).mp hx
  have ht := integral_mono_ae hi (integrable_const (A^2))
    (hb.mono fun y hy ↦ by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hy 2)
  simpa using ht

lemma kernelRowEnergy_memLp_top {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) :
    ∀ i, MemLp (kernelRowEnergy ν h i) ∞ (μ i) := by
  intro i
  have hi : ∀ j, Integrable (fun p ↦ (h i j p)^2) ((μ i).prod (ν j)) := fun j ↦ by
    simpa only [sq_abs] using bounded_kernel_abs_moment_integrable (μ i) (ν j) (h i j)
      A (hAES i j) (hBound i j) 2
  have ha : AEStronglyMeasurable (kernelRowEnergy ν h i) (μ i) := by
    change AEStronglyMeasurable (fun x ↦ ∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) (μ i)
    simpa only [Finset.sum_apply] using
      (integrable_finsetSum Finset.univ (fun j _ ↦ (hi j).integral_prod_left)).aestronglyMeasurable
  apply bounded_real_memLp ha
  have hs : ∀ᵐ x ∂μ i, ∀ j, (∫ y, (h i j (x,y))^2 ∂ν j) ≤ A^2 :=
    ae_all_iff.mpr fun j ↦ bounded_section_square_integral (μ i) (ν j) (h i j) A (hAES i j) (hBound i j)
  filter_upwards [hs] with x hx
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun y ↦ sq_nonneg _)]
  exact Finset.sum_le_sum fun j _ ↦ hx j

lemma kernelColumnEnergy_memLp_top {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) :
    ∀ j, MemLp (kernelColumnEnergy μ h j) ∞ (ν j) := by
  intro j
  have ht := kernelRowEnergy_memLp_top ν μ (fun j i p ↦ h i j p.swap) A
    (fun j i ↦ (hAES i j).comp_quasiMeasurePreserving (Measure.measurePreserving_swap (μ := ν j) (ν := μ i)).quasiMeasurePreserving)
    (fun j i ↦ (Measure.measurePreserving_swap (μ := ν j) (ν := μ i)).quasiMeasurePreserving.ae (hBound i j)) j
  exact ht

/-- Actual A/B/C definition bridges, including all energy measurability and boundedness. -/
theorem kernelSourceABC_controls {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ)
    (hh : ∀ i j, MemLp (h i j) ∞ ((μ i).prod (ν j))) :
    0 ≤ kernelSourceA μ ν h ∧ 0 ≤ kernelSourceB μ ν h ∧ 0 ≤ kernelSourceC μ ν h ∧
    (∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ kernelSourceA μ ν h) ∧
    (∀ i, ∀ᵐ x ∂μ i, kernelRowEnergy ν h i x ≤ (kernelSourceB μ ν h)^2) ∧
    (∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ (kernelSourceB μ ν h)^2) ∧
    (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) = (kernelSourceC μ ν h)^2 := by
  have ha : 0 ≤ kernelSourceA μ ν h := NNReal.coe_nonneg _
  have hb := kernelSourceA_bound μ ν h hh
  have hAES := fun i j ↦ (hh i j).aestronglyMeasurable
  have hr := kernelRowEnergy_memLp_top μ ν h (kernelSourceA μ ν h) hAES hb
  have hc := kernelColumnEnergy_memLp_top μ ν h (kernelSourceA μ ν h) hAES hb
  have hBsq : (kernelSourceB μ ν h)^2 = max
      (↑(Finset.univ.sup fun i : Fin n ↦ (eLpNormEssSup (kernelRowEnergy ν h i) (μ i)).toNNReal) : ℝ)
      (↑(Finset.univ.sup fun j : Fin q ↦ (eLpNormEssSup (kernelColumnEnergy μ h j) (ν j)).toNNReal) : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  refine ⟨ha,Real.sqrt_nonneg _,Real.sqrt_nonneg _,hb,?_,?_,?_⟩
  · intro i
    filter_upwards [ae_absolute_le_essSup_toReal (μ i) (kernelRowEnergy ν h i) (hr i)] with x hx
    rw [hBsq]
    apply (le_abs_self _).trans (hx.trans ((show
      (eLpNormEssSup (kernelRowEnergy ν h i) (μ i)).toReal ≤
      ↑(Finset.univ.sup fun i : Fin n ↦ (eLpNormEssSup (kernelRowEnergy ν h i) (μ i)).toNNReal) from by
        exact_mod_cast Finset.le_sup (f := fun i : Fin n ↦
          (eLpNormEssSup (kernelRowEnergy ν h i) (μ i)).toNNReal) (Finset.mem_univ i)).trans (le_max_left _ _)))
  · intro j
    filter_upwards [ae_absolute_le_essSup_toReal (ν j) (kernelColumnEnergy μ h j) (hc j)] with y hy
    rw [hBsq]
    apply (le_abs_self _).trans (hy.trans ((show
      (eLpNormEssSup (kernelColumnEnergy μ h j) (ν j)).toReal ≤
      ↑(Finset.univ.sup fun j : Fin q ↦ (eLpNormEssSup (kernelColumnEnergy μ h j) (ν j)).toNNReal) from by
        exact_mod_cast Finset.le_sup (f := fun j : Fin q ↦
          (eLpNormEssSup (kernelColumnEnergy μ h j) (ν j)).toNNReal) (Finset.mem_univ j)).trans (le_max_right _ _)))
  · exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      integral_nonneg fun p ↦ sq_nonneg _)).symm

theorem kernel_real_four_scale_actual {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ)
    (hh : ∀ i j, MemLp (h i j) ∞ ((μ i).prod (ν j)))
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ ω, |kernelDecoupledSum h ω|^p ∂(Measure.pi μ).prod (Measure.pi ν))^(1/p) ≤
      13824*glzRealScale p (kernelSourceA μ ν h) (kernelSourceB μ ν h) (kernelSourceC μ ν h) (kernelSourceD μ ν h) := by
  obtain ⟨ha,hb,hc,hbound,hrow,hcol,htrace⟩ := kernelSourceABC_controls μ ν h hh
  have hd := kernelSourceD_controls μ ν h (kernelSourceA μ ν h) ha
    (fun i j ↦ (hh i j).aestronglyMeasurable) hbound
  exact kernel_real_four_scale μ ν h (kernelSourceA μ ν h) (kernelSourceB μ ν h)
    (kernelSourceC μ ν h) (kernelSourceD μ ν h) ha hb hc hd.1
    (fun i j ↦ (hh i j).aestronglyMeasurable) hbound hMeanRight hMeanLeft
    hrow hcol htrace.le hd.2 p hp

#print axioms DGRHS.Concentration.kernel_real_four_scale_actual
#check @DGRHS.Concentration.kernel_real_four_scale_actual

theorem kernel_even_four_scale_power_actual {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ)
    (hh : ∀ i j, MemLp (h i j) ∞ ((μ i).prod (ν j)))
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ p, |kernelDecoupledSum h p|^(2*k) ∂(Measure.pi μ).prod (Measure.pi ν)) ≤
      (864*glzScale (2*k) (kernelSourceA μ ν h) (kernelSourceB μ ν h) (kernelSourceC μ ν h) (kernelSourceD μ ν h))^(2*k) := by
  obtain ⟨ha,hb,hc,hbound,hrow,hcol,htrace⟩ := kernelSourceABC_controls μ ν h hh
  have hd := kernelSourceD_controls μ ν h (kernelSourceA μ ν h) ha
    (fun i j ↦ (hh i j).aestronglyMeasurable) hbound
  exact kernel_even_four_scale_power μ ν h (kernelSourceA μ ν h) (kernelSourceB μ ν h)
    (kernelSourceC μ ν h) (kernelSourceD μ ν h) ha hb hc hd.1
    (fun i j ↦ (hh i j).aestronglyMeasurable) hbound hMeanRight hMeanLeft
    hrow hcol htrace.le hd.2 k hk

#print axioms DGRHS.Concentration.kernel_even_four_scale_power_actual
#check @DGRHS.Concentration.kernel_even_four_scale_power_actual

#print axioms DGRHS.Concentration.kernelSourceA_bound
#print axioms DGRHS.Concentration.kernelRowEnergy_memLp_top
#print axioms DGRHS.Concentration.kernelSourceABC_controls
#check @DGRHS.Concentration.kernelSourceABC_controls
end DGRHS.Concentration
