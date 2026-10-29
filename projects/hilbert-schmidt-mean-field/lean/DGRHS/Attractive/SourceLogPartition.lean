/- Literal extended singular attractive partition, source612–641/2490–2595.
Uniform estimate follows from original singular L1, uniform row moments and
one-body exponential properness; no desired partition/moment conclusion is
assumed. -/
import DGRHS.Attractive.SourceLogWeight
import DGRHS.Attractive.SourceMomentThreshold
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def attractiveLogPartition (μ : Measure E) (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x,attractiveLogSingularWeight μ β N x ∂Measure.pi (fun _ : Fin N => μ)

def attractiveUniformConstant (μ : Measure E) (C β : ℝ) : ℝ :=
  Real.exp (β*|DGRHS.interactionEnergy μ attractiveLogInteraction|)*
    Real.sqrt (2/(1-(β*(attractiveMomentConstant*C))^2))*
    Real.sqrt (∫ x,Real.exp (2*β*DGRHS.potential μ attractiveLogInteraction x) ∂μ)

theorem attractiveLogPartition_uniform (μ : Measure E) [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p,DGRHS.Gaussian.singularAbsLog p ∂μ.prod μ)<∞)
    (C β : ℝ) (hC : 0≤C)
    (hrow : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal
        (|DGRHS.centeredKernel μ attractiveLogInteraction x y|^p) ∂μ) ≤
          ENNReal.ofReal (C^p*(p.factorial : ℝ)))
    (hβ : 0≤β) (hsmall : β*(attractiveMomentConstant*C)<1)
    (htail : Integrable
      (fun x => Real.exp (2*β*DGRHS.potential μ attractiveLogInteraction x)) μ) :
    ∀ N : ℕ,0<N →
      attractiveLogPartition μ β N ≤ ENNReal.ofReal (attractiveUniformConstant μ C β) ∧
      attractiveLogPartition μ β N < ∞ := by
  intro N hN
  obtain ⟨hi,hb⟩ := attractiveLog_source_uniform μ hpair C β hC hrow hβ hsmall htail N hN
  have he : attractiveLogPartition μ β N = ENNReal.ofReal
      (∫ x : Fin N → E,Real.exp (-β*(N : ℝ)*
        DGRHS.CLT.sourceCanonicalModulatedEnergy
          (fun p => DGRHS.centeredKernel μ attractiveLogInteraction p.1 p.2)
          (DGRHS.potential μ attractiveLogInteraction)
          (DGRHS.interactionEnergy μ attractiveLogInteraction) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) := by
    unfold attractiveLogPartition
    rw [lintegral_congr_ae (attractiveLogSingularWeight_ae μ hpair β N)]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm
  rw [he]
  exact ⟨ENNReal.ofReal_le_ofReal hb,ENNReal.ofReal_lt_top⟩

theorem attractiveLogPartition_uniform_threshold (μ : Measure E) [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p,DGRHS.Gaussian.singularAbsLog p ∂μ.prod μ)<∞)
    (C β : ℝ) (hC : 0<C)
    (hrow : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal
        (|DGRHS.centeredKernel μ attractiveLogInteraction x y|^p) ∂μ) ≤
          ENNReal.ofReal (C^p*(p.factorial : ℝ)))
    (hβ : 0≤β) (hsmall : β<attractiveBetaThreshold C)
    (htail : Integrable
      (fun x => Real.exp (2*β*DGRHS.potential μ attractiveLogInteraction x)) μ) :
    0<attractiveBetaThreshold C ∧ ∀ N : ℕ,0<N →
      attractiveLogPartition μ β N ≤ ENNReal.ofReal (attractiveUniformConstant μ C β) ∧
      attractiveLogPartition μ β N < ∞ := by
  exact ⟨attractiveBetaThreshold_pos hC,attractiveLogPartition_uniform μ hpair C β hC.le
    hrow hβ ((attractiveBetaThreshold_lt_iff hC).mp hsmall) htail⟩

end DGRHS.Attractive
#check @DGRHS.Attractive.attractiveLogPartition_uniform
#print axioms DGRHS.Attractive.attractiveLogPartition_uniform
#check @DGRHS.Attractive.attractiveLogPartition_uniform_threshold
#print axioms DGRHS.Attractive.attractiveLogPartition_uniform_threshold
