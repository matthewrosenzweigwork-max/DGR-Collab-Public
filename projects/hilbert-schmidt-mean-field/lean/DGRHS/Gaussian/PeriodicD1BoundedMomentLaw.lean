import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-! RECORDS-ONLY UNCOMPILED DRAFT. Actual equality of bounded probability laws
from all natural moments, using exact native MGF series and analytic uniqueness.
This is not analytic continuation from integer arguments. All natural moments
are coefficients of the local MGF series; eventual equality is proved first.
The concrete Good/Beta matching and bounds remain separate downstream premises
to discharge, rather than an assumed Dyson identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace DGRHS.Periodic
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}

lemma periodicD1_integrableExpSet_of_bounded [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) {a b : ℝ} (hb : ∀ᵐ ω ∂μ,X ω∈Icc a b) :
    integrableExpSet X μ=univ := by
  ext t
  constructor
  · intro _;trivial
  · intro _
    exact integrable_exp_mul_of_mem_Icc hX hb

lemma periodicD1_bounded_moments_mgf [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    {a b c d : ℝ} (hbX : ∀ᵐ ω ∂μ,X ω∈Icc a b) (hbY : ∀ᵐ ω ∂ν,Y ω∈Icc c d)
    (hMom : ∀ n : ℕ,(∫ ω,(X ω)^n ∂μ)=(∫ ω,(Y ω)^n ∂ν)) :
    mgf X μ=mgf Y ν := by
  have hSX := periodicD1_integrableExpSet_of_bounded hX hbX
  have hSY := periodicD1_integrableExpSet_of_bounded hY hbY
  have h0X : (0:ℝ)∈interior (integrableExpSet X μ) := by simp [hSX]
  have h0Y : (0:ℝ)∈interior (integrableExpSet Y ν) := by simp [hSY]
  have hpX := hasFPowerSeriesAt_mgf h0X
  have hpY := hasFPowerSeriesAt_mgf h0Y
  simp only [zero_mul,Real.exp_zero,mul_one] at hpX hpY
  have hc : (fun n : ℕ => (∫ ω,(X ω)^n ∂μ)/(n.factorial:ℝ))=
      fun n : ℕ => (∫ ω,(Y ω)^n ∂ν)/(n.factorial:ℝ) := by
    funext n
    rw [hMom n]
  rw [hc] at hpX
  have hlocal : mgf X μ=ᶠ[𝓝 (0:ℝ)]mgf Y ν := by
    filter_upwards [hpX.eventually_hasSum_sub,hpY.eventually_hasSum_sub] with t htX htY
    exact htX.unique htY
  have hanX : AnalyticOnNhd ℝ (mgf X μ) univ := by
    simpa only [hSX,interior_univ] using (analyticOnNhd_mgf (X:=X) (μ:=μ))
  have hanY : AnalyticOnNhd ℝ (mgf Y ν) univ := by
    simpa only [hSY,interior_univ] using (analyticOnNhd_mgf (X:=Y) (μ:=ν))
  exact hanX.eq_of_eventuallyEq hanY hlocal

/-- Equal literal bounded moments determine the actual pushforward laws. -/
theorem periodicD1_bounded_moments_law [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    {a b c d : ℝ} (hbX : ∀ᵐ ω ∂μ,X ω∈Icc a b) (hbY : ∀ᵐ ω ∂ν,Y ω∈Icc c d)
    (hMom : ∀ n : ℕ,(∫ ω,(X ω)^n ∂μ)=(∫ ω,(Y ω)^n ∂ν)) :
    Measure.map X μ=Measure.map Y ν := by
  have hmgf := periodicD1_bounded_moments_mgf hX hY hbX hbY hMom
  have he := eqOn_complexMGF_of_mgf hmgf
  have hSX := periodicD1_integrableExpSet_of_bounded hX hbX
  apply Measure.ext_of_complexMGF_eq hX hY
  funext z
  apply he
  simp [hSX]

/-- Proper integration is transported through the proved laws, never inferred
from a possibly totalized Bochner identity. This applies to negative real powers. -/
theorem periodicD1_bounded_moments_proper_transfer
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    {a b c d : ℝ} (hbX : ∀ᵐ ω ∂μ,X ω∈Icc a b) (hbY : ∀ᵐ ω ∂ν,Y ω∈Icc c d)
    (hMom : ∀ n : ℕ,(∫ ω,(X ω)^n ∂μ)=(∫ ω,(Y ω)^n ∂ν))
    (F : ℝ → ℝ) (hF : Measurable F) (hi : Integrable (fun ω => F (Y ω)) ν) :
    Integrable (fun ω => F (X ω)) μ ∧
      (∫ ω,F (X ω) ∂μ)=(∫ ω,F (Y ω) ∂ν) := by
  have he := periodicD1_bounded_moments_law hX hY hbX hbY hMom
  have himap : Integrable F (Measure.map Y ν) :=
    (integrable_map_measure hF.aestronglyMeasurable hY).2 hi
  have hip : Integrable F (Measure.map X μ) := by rw [he];exact himap
  refine ⟨(integrable_map_measure hF.aestronglyMeasurable hX).1 hip,?_⟩
  rw [←integral_map hX hF.aestronglyMeasurable,
    ←integral_map hY hF.aestronglyMeasurable,he]

end DGRHS.Periodic
