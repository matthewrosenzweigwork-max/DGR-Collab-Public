import DGRHS.Dynamics.SourceLogAdjointIntervalRemainder

/-! Measurability of the actual logarithmic classical remainder, requiring
joint input measurability only on the closed source horizon. Auxiliary
extensions preserve every sample's actual time integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem measurable_sourceLog_adjoint_interval_remainder
    {Ω : Type*} [MeasurableSpace Ω] (T : ℝ) (hT : 0≤T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2))
    (q : ℝ→E→ℝ)
    (hgrad : Continuous (fun p : Icc (0:ℝ) T×E=>gradient (q p.1) p.2))
    (N : ℕ) (hN : 0<N) (X : ℝ→Ω→Fin N→E)
    (hXm : Measurable (fun p : Icc (0:ℝ) T×Ω=>X p.1 p.2)) :
    Measurable (fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 T,
      sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (gradient (q r))) N (X r ω)))) := by
  let ρe := fun r=>ρ (projIcc 0 T hT r)
  let ve := fun r=>gradient (q (projIcc 0 T hT r))
  let Xe := fun r=>X (projIcc 0 T hT r)
  have hρeq (r : ℝ) (hr : r∈Icc 0 T) : ρe r=ρ r := by
    dsimp only [ρe];rw [projIcc_of_mem hT hr]
  have hveq (r : ℝ) (hr : r∈Icc 0 T) : ve r=gradient (q r) := by
    dsimp only [ve];rw [projIcc_of_mem hT hr]
  have hXeq (r : ℝ) (hr : r∈Icc 0 T) : Xe r=X r := by
    dsimp only [Xe];rw [projIcc_of_mem hT hr]
  have hp : Measurable (fun p : ℝ×E=>(projIcc 0 T hT p.1,p.2)) :=
    ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd).measurable
  have hρem : Measurable (Function.uncurry ρe) := hρm.comp hp
  have hvem : Measurable (Function.uncurry ve) := hgrad.measurable.comp hp
  have hXem : Measurable (Function.uncurry Xe) := hXm.comp
    (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  let κ := sourceDensityKernel volume ρe
  letI := sourceDensityKernel_sfinite volume ρe
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρe r) :=
    sourceDensityKernel_apply volume ρe hρem r
  let Ae := fun r ω=>sourceTransportEnergy (κ r) (sourceLogTransportKernel 1 (ve r)) N (Xe r ω)
  have hAm : Measurable (Function.uncurry Ae) :=
    measurable_sourceLogTransportEnergy_time κ ve hvem N hN (Function.uncurry Xe) hXem
  let η := volume.restrict (Ioc 0 T)
  have hint (ω : Ω) : (∫ r,Ae r ω ∂η)=∫ r in Ioc 0 T,
      sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (gradient (q r))) N (X r ω) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    dsimp only [Ae]
    rw [hκ r,hρeq r hr',hveq r hr',hXeq r hr']
  have hh := ((hAm.stronglyMeasurable.integral_prod_left' (μ:=η)).measurable.const_mul
    (Real.sqrt N/2)).neg
  change Measurable (fun ω=>-((Real.sqrt N/2)*(∫ r,Ae r ω ∂η))) at hh
  simpa only [hint] using hh

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.measurable_sourceLog_adjoint_interval_remainder
#print axioms DGRHS.Dynamics.measurable_sourceLog_adjoint_interval_remainder
