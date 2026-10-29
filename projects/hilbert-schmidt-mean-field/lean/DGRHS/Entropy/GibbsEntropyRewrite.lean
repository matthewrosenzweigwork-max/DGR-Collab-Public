/- Source eq:intro-entropy-rewrite and eq:expDV, on the explicitly proper
finite-entropy/finite-energy domain. Reuses the pinned native likelihood-ratio
identities and KL divergence. The extended-valued all-law variational domain
remains a separate obligation; this supporting theorem does not totalize it. -/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Tactic
noncomputable section
open MeasureTheory InformationTheory
namespace DGRHS.Entropy

lemma gibbsEntropy_rewrite {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hν : ν ≪ μ) (hu : Integrable u ν)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ)
    (hllr : Integrable (llr ν μ) ν) :
    Integrable (llr ν (μ.tilted u)) ν ∧
      (klDiv ν (μ.tilted u)).toReal=
        (klDiv ν μ).toReal-(∫ x,u x ∂ν)+Real.log (∫ x,Real.exp (u x) ∂μ) := by
  letI := isProbabilityMeasure_tilted hexp
  have hνQ : ν ≪ μ.tilted u := hν.trans (absolutelyContinuous_tilted hexp)
  have hQ := integrable_llr_tilted_right hν hu hllr hexp
  refine ⟨hQ,?_⟩
  have h := integral_llr_tilted_right hν hu hexp hllr
  simpa [toReal_klDiv hνQ hQ,toReal_klDiv hν hllr] using h

lemma gibbsEntropy_variational_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hν : ν ≪ μ) (hu : Integrable u ν)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ)
    (hllr : Integrable (llr ν μ) ν) :
    (∫ x,u x ∂ν)≤(klDiv ν μ).toReal+Real.log (∫ x,Real.exp (u x) ∂μ) := by
  have h := (gibbsEntropy_rewrite μ ν u hν hu hexp hllr).2
  have hn := ENNReal.toReal_nonneg (a:=klDiv ν (μ.tilted u))
  linarith

end DGRHS.Entropy
#check @DGRHS.Entropy.gibbsEntropy_rewrite
#check @DGRHS.Entropy.gibbsEntropy_variational_lower
#print axioms DGRHS.Entropy.gibbsEntropy_rewrite
#print axioms DGRHS.Entropy.gibbsEntropy_variational_lower
