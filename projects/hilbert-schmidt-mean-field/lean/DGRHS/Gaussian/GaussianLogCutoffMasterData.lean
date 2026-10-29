import DGRHS.Gaussian.GaussianLogCutoffAdaptive
import DGRHS.Gaussian.GaussianLogCutoffBounds

/-! Supporting development: concrete cutoff source-exponent master data: every
comparison, cap, norm and size field is derived from the actual physical band. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianLogCutoffSourceMasterData (η δ T β A u₀ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n)
    (hA : 0 < A) (hAC : 8*gaussianLogShortConstant M ι ≤ A)
    (hu₀ : 1 ≤ u₀) (hlow : 4*gaussianLogSourceLowConstant δ β M ι ≤ u₀)
    (hrow : 16*(2*β)^2*gaussianLogBandRowControl δ M ι ≤ 1/glzUniversalTailConstant)
    (hop : 4*|2*β| *Real.sqrt (gaussianLogBandRowControl δ M ι) ≤ 1/glzUniversalTailConstant) :
    MasterCutoffData (gaussianRieszDensityMeasure ρ) n
      (gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η T n) u₀ := by
  let μ := gaussianRieszDensityMeasure ρ
  let α := fun u => gaussianLogAdaptiveScale δ A β (n : ℝ) u (Fintype.card ι : ℝ)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hα (u : ℝ) (hu : u₀ ≤ u) := gaussianLogAdaptiveScale_pos_le δ A β (n : ℝ) u
    (Fintype.card ι : ℝ) hδ hA hβ (Nat.cast_nonneg n) (by linarith)
  have hℓ (u : ℝ) (hu : u₀ ≤ u) : 0 < max η (α u) ∧ max η (α u) ≤ δ :=
    ⟨hη.trans_le (le_max_left _ _),max_le hηδ (hα u hu).2⟩
  have hmass (u : ℝ) (hu : u₀ ≤ u) : 0 ≤ Real.log (δ/max η (α u)) := Real.log_nonneg (by
    rw [le_div_iff₀ (hℓ u hu).1]
    simpa using (hℓ u hu).2)
  have hsize := gaussianLogCutoffAdaptive_actual_size_bound η δ A β (n : ℝ) u₀ hη hηδ hδ hδ1 hA hβ hn' hu₀ hd μ
  refine {kernel := fun u => gaussianLogMasterBand (max η (α u)) δ (2*β) μ
          cap := fun u => 1+4*β*Real.log (δ/max η (α u))
          measurable := ?_
          memLp := ?_
          symmetric := ?_
          canonical := ?_
          cap_pos := ?_
          compare := ?_
          capped := ?_
          row := ?_
          joint := ?_
          operator := ?_
          size_finite := hsize.1}
  · intro u hu
    exact measurable_gaussianLogMasterBand (max η (α u)) δ (2*β) (hℓ u hu).1 μ
  · intro u hu
    exact memLp_infty_gaussianLogMasterBand (max η (α u)) δ (2*β) (hℓ u hu).1 (hℓ u hu).2 μ
  · intro u hu x y
    exact gaussianLogMasterBand_symmetric (max η (α u)) δ (2*β) μ x y
  · intro u hu
    exact gaussianLogMasterBand_canonical (max η (α u)) δ (2*β) (hℓ u hu).1 (hℓ u hu).2 μ
  · intro u hu
    have hm := mul_nonneg (by positivity : 0 ≤ 4*β) (hmass u hu)
    linarith
  · intro u hu
    exact ae_gaussianLogCutoff_adaptive_comparison η δ T β A u₀ u hη hηδ hδ hδ1 hT hβ hd ρ M hM hρ n hn hA hAC hu₀ hlow hu
  · intro u hu
    apply Filter.Eventually.of_forall
    intro ω
    have hc := gaussianLogMasterBand_particle_cap (max η (α u)) δ (2*β) (hℓ u hu).1 (hℓ u hu).2
      (by positivity : 0 ≤ 2*β) μ n hn ω
    nlinarith only [hc]
  · intro u hu
    exact (gaussianLogMasterBand_norm_fields (max η (α u)) δ β (hℓ u hu).1 (hℓ u hu).2 hd ρ M hM hρ hrow hop).1
  · intro u hu
    exact (gaussianLogMasterBand_norm_fields (max η (α u)) δ β (hℓ u hu).1 (hℓ u hu).2 hd ρ M hM hρ hrow hop).2.1
  · intro u hu
    exact (gaussianLogMasterBand_norm_fields (max η (α u)) δ β (hℓ u hu).1 (hℓ u hu).2 hd ρ M hM hρ hrow hop).2.2

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogCutoffSourceMasterData
#print axioms DGRHS.Gaussian.gaussianLogCutoffSourceMasterData
