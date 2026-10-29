import DGRHS.Gaussian.GaussianRieszAdaptiveBounds

/-! Concrete master data for the actual centered Gaussian-profile Riesz
cutoff. Every M1/M2/M3 field and the finite size supremum is derived; no
exponential moment, concentration, or event comparison is supplied. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

noncomputable def gaussianRieszMasterCutoffData (s η δ β A u₀ : ℝ)
    (hs : 0 < s) (hη : 0 < η) (hηδ : η ≤ δ) (hδ : 0 < δ) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (hAcontrol : 4*β*gaussianRieszShortConstant s M ι ≤ A)
    (hu₀ : 1 ≤ u₀) (hlow : 8*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) ≤ u₀)
    (hrow : 16*(2*β)^2*gaussianRieszBandRowControl s δ M ι ≤ 1/glzUniversalTailConstant)
    (hop : 4*|2*β| *Real.sqrt (gaussianRieszBandRowControl s δ M ι) ≤ 1/glzUniversalTailConstant) :
    MasterCutoffData (gaussianRieszDensityMeasure ρ) n
      (fun ω => β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszTruncatedPair s η)) ω) u₀ := by
  let μ := gaussianRieszDensityMeasure ρ
  let α := fun u => max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η
  have hα (u : ℝ) (hu : u₀ ≤ u) :=
    gaussianRieszAdaptiveBand_parameters (ι := ι) δ A u s η n hδ hA (hu₀.trans hu) hn hηδ
  have hb (u : ℝ) (hu : u₀ ≤ u) := gaussianRieszAdaptiveBand_cap_ess_bounds s η δ β A hs hηδ hδ hβ hA ha ρ M hM hρ n hn u (hu₀.trans hu)
  have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsize := masterCutoffSize_le_adaptive_power μ (fun u => gaussianRieszAdaptiveBand s η δ β A n u ρ)
    (fun u => gaussianRieszAdaptiveCap s η δ β A n u ι) (n : ℝ) u₀
    (s/((Fintype.card ι : ℝ)-s)) (gaussianRieszAdaptiveC0 s δ β) (gaussianRieszAdaptiveC1 s β A ι)
    hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
    (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)
  refine { kernel := fun u => gaussianRieszAdaptiveBand s η δ β A n u ρ
           cap := fun u => gaussianRieszAdaptiveCap s η δ β A n u ι
           measurable := ?_
           memLp := ?_
           symmetric := ?_
           canonical := ?_
           cap_pos := fun u hu => (hb u hu).2.2.1
           compare := ?_
           capped := ?_
           row := ?_
           joint := ?_
           operator := ?_
           size_finite := hsize.1 }
  · intro u hu
    exact measurable_gaussianRieszMasterBand s (α u) δ (2*β) hs (hα u hu).1 (hα u hu).2 ρ
  · intro u hu
    exact memLp_infty_gaussianRieszMasterBand s (α u) δ (2*β) hs (hα u hu).1 (hα u hu).2 ha ρ M hM hρ
  · intro u hu x y
    exact gaussianRieszMasterBand_symmetric s (α u) δ (2*β) ρ x y
  · intro u hu
    exact gaussianRieszMasterBand_canonical s (α u) δ (2*β) hs (hα u hu).1 (hα u hu).2 ha ρ M hM hρ
  · intro u hu
    exact ae_gaussianRieszParticle_adaptive_comparison s η δ β A u₀ u hs hη hηδ hδ hβ ha ρ M hM hρ n hn hA hAcontrol hu₀ hlow hu
  · intro u hu
    apply Filter.Eventually.of_forall
    intro ω
    have hc := gaussianRieszMasterBand_particle_cap s (α u) δ (2*β) hs (hα u hu).1 (hα u hu).2 ha
      (by linarith : 0 ≤ 2*β) ρ M hM hρ n hn ω
    change iidNegativeStatistic n (gaussianRieszMasterBand s (α u) δ (2*β) ρ) ω ≤
      1+4*β*(gaussianRieszSourceCoefficient s/s*(α u)^(-s))
    nlinarith only [hc]
  · intro u hu
    exact (gaussianRieszMasterBand_norm_fields s (α u) δ β hs (hα u hu).1 (hα u hu).2 ha ρ M hM hρ hrow hop).1
  · intro u hu
    exact (gaussianRieszMasterBand_norm_fields s (α u) δ β hs (hα u hu).1 (hα u hu).2 ha ρ M hM hρ hrow hop).2.1
  · intro u hu
    exact (gaussianRieszMasterBand_norm_fields s (α u) δ β hs (hα u hu).1 (hα u hu).2 ha ρ M hM hρ hrow hop).2.2

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszMasterCutoffData
#print axioms DGRHS.Gaussian.gaussianRieszMasterCutoffData
