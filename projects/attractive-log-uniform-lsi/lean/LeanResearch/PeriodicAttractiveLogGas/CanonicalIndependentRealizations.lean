import LeanResearch.PeriodicAttractiveLogGas.CanonicalPairs
import Mathlib.Algebra.Order.Floor.Semiring

/-! Independent-realization transport of the source canonical pair theorem,
and real-exponent decoupling derived from its natural factorial moments.
Joint laws and integrability are conclusions, not extra input assumptions. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace PeriodicAttractiveLogGas.CanonicalIndependentRealizations
open CanonicalPairs CanonicalDecoupling CanonicalRowHolder

variable {m : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
  (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
  (h : ∀ i j, α i → α j → ℝ)

/-- Natural moments above q supply the real-exponent MemLp input on a probability law. -/
theorem pairwise_memLp_real_of_source {q : ℝ} (hq : 1 ≤ q)
    (hf : ∀ i j, i < j → Measurable (Function.uncurry (h i j))) {L : ℝ}
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j, i < j →
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    ∀ i j, MemLp (Function.uncurry (upperKernel h i j)) (ENNReal.ofReal q) ((ν i).prod (ν j)) := by
  have hn : 1 ≤ Nat.ceil q := Nat.one_le_ceil_iff.mpr (by linarith)
  have hm := pairwise_memLp_of_essSup_sum ν (upperKernel h) hn
    (measurable_upperKernel h hf) (upperKernel_factorial ν h hsource _ hn)
  intro i j
  exact (hm i j).mono_exponent (ENNReal.ofReal_le_natCast.mpr (Nat.le_ceil q))

/-- All real q at least one in the supplied decoupling step, with actual
integrability derived from the original source inputs. -/
theorem real_q_decoupling {q : ℝ} (hq : 1 ≤ q)
    (hf : ∀ i j, i < j → Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, i < j → ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, i < j → ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ}
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j, i < j →
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    Integrable (fun Y => |canonicalSum h Y| ^ q) (Measure.pi ν) ∧
      Integrable (fun Z => |decoupledSum (upperKernel h) Z| ^ q)
        ((Measure.pi ν).prod (Measure.pi ν)) ∧
      (∫ Y, |canonicalSum h Y| ^ q ∂Measure.pi ν) ≤
        (4 : ℝ) ^ q * ∫ Z, |decoupledSum (upperKernel h) Z| ^ q
          ∂(Measure.pi ν).prod (Measure.pi ν) := by
  have hm := pairwise_memLp_real_of_source ν h hq hf hsource
  have hq0 : 0 ≤ q := by linarith
  exact ⟨integrable_abs_rpow_pairSum ν (upperKernel h) hq0 (upperKernel_triangular h) hm,
    integrable_abs_rpow_decoupledSum ν (upperKernel h) hq0 hm,
    integral_abs_rpow_pairSum_le ν (upperKernel h) (upperKernel_triangular h)
      (measurable_upperKernel h hf) (upperKernel_left ν h hleft)
      (upperKernel_right ν h hright) hq hm⟩

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : ∀ i, Ω → α i)

/-- The actual vector of random coordinates on the original probability space. -/
def independentVector (ω : Ω) : ∀ i, α i := fun i => X i ω

/-- The original source pair sum on its ambient independent realization. -/
def ambientSum (ω : Ω) : ℝ := canonicalSum h (independentVector X ω)

/-- The decoupled sum on the explicit independent product copy of the ambient space. -/
def ambientDecoupledSum (ω : Ω × Ω) : ℝ :=
  decoupledSum (upperKernel h) (independentVector X ω.1, independentVector X ω.2)

omit [∀ i, IsProbabilityMeasure (ν i)] [IsProbabilityMeasure μ] in
/-- Independence and the marginal laws prove the joint product law. -/
theorem measurePreserving_independentVector
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hLaw : ∀ i, μ.map (X i) = ν i) :
    MeasurePreserving (independentVector X) μ (Measure.pi ν) := by
  refine ⟨Measurable.of_eval hX, ?_⟩
  change μ.map (fun ω i => X i ω) = Measure.pi ν
  rw [hInd.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
  congr 1
  funext i
  exact hLaw i

omit [∀ i, MeasurableSpace (α i)] [MeasurableSpace Ω] in
theorem ambientSum_eq_upper_sum (ω : Ω) :
    ambientSum h X ω = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h i j (X i ω) (X j ω) :=
  canonicalSum_eq_upper_sum h (independentVector X ω)

/-- The real-q decoupling inequality transported to actual independent variables
and the explicit independent copy, with neither joint law assumed. -/
theorem real_q_decoupling_independent {q : ℝ} (hq : 1 ≤ q)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν i)
    (hf : ∀ i j, i < j → Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, i < j → ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, i < j → ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ}
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j, i < j →
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    Integrable (fun ω => |ambientSum h X ω| ^ q) μ ∧
      Integrable (fun ω => |ambientDecoupledSum h X ω| ^ q) (μ.prod μ) ∧
      (∫ ω, |ambientSum h X ω| ^ q ∂μ) ≤
        (4 : ℝ) ^ q * ∫ ω, |ambientDecoupledSum h X ω| ^ q ∂μ.prod μ := by
  obtain ⟨hI, hJ, hb⟩ := real_q_decoupling ν h hq hf hleft hright hsource
  have hT := measurePreserving_independentVector ν μ X hX hInd hLaw
  have hTT := hT.prod hT
  have hA : Integrable (fun ω => |ambientSum h X ω| ^ q) μ :=
    hT.integrable_comp_of_integrable hI
  have hD : Integrable (fun ω => |ambientDecoupledSum h X ω| ^ q) (μ.prod μ) :=
    hTT.integrable_comp_of_integrable hJ
  refine ⟨hA, hD, ?_⟩
  have he : (∫ ω, |ambientSum h X ω| ^ q ∂μ) = ∫ Y, |canonicalSum h Y| ^ q ∂Measure.pi ν :=
    integral_comp_of_measurePreserving hT hI.aestronglyMeasurable
  have he' : (∫ ω, |ambientDecoupledSum h X ω| ^ q ∂μ.prod μ) =
      ∫ Z, |decoupledSum (upperKernel h) Z| ^ q ∂(Measure.pi ν).prod (Measure.pi ν) :=
    integral_comp_of_measurePreserving hTT hJ.aestronglyMeasurable
  rw [he, he']
  exact hb

omit [IsProbabilityMeasure μ] in
/-- The original source theorem for arbitrary measurable independent realizations
with possibly different marginal laws. The joint law is derived, and every
integrability, centering, moment and exponential assertion is transported as a conclusion. -/
theorem canonical_pairs_independent (hm : 1 ≤ m)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν i)
    (hf : ∀ i j, i < j → Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, i < j → ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, i < j → ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j, i < j →
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    Measurable (ambientSum h X) ∧
      Integrable (ambientSum h X) μ ∧
      (∫ ω, ambientSum h X ω ∂μ) = 0 ∧
      (∀ k : ℕ, 1 ≤ k →
        Integrable (fun ω => ambientSum h X ω ^ (2 * k)) μ ∧
          (∫ ω, ambientSum h X ω ^ (2 * k) ∂μ) ≤
            (8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
              ((2 * k).factorial : ℝ)) ∧
      (∀ τ : ℝ, |τ| * (8 * Real.sqrt 2 * Real.exp 1 * L) < 1 →
        Integrable (fun ω => Real.exp (τ * ambientSum h X ω / (m : ℝ))) μ ∧
          (∫ ω, Real.exp (τ * ambientSum h X ω / (m : ℝ)) ∂μ) ≤
            (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
              (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2)) ∧
      Filter.Tendsto (fun τ : ℝ =>
        (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
          (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2)) (𝓝 0) (𝓝 1) := by
  obtain ⟨hS, hI, hmean, hM, hE, hlim⟩ := canonical_pairs ν h hm hf hleft hright hL hsource
  have hT := measurePreserving_independentVector ν μ X hX hInd hLaw
  have hAS : Measurable (ambientSum h X) := hS.comp hT.measurable
  have hAI : Integrable (ambientSum h X) μ := hT.integrable_comp_of_integrable hI
  have he : (∫ ω, ambientSum h X ω ∂μ) = ∫ Y, canonicalSum h Y ∂Measure.pi ν :=
    integral_comp_of_measurePreserving hT hI.aestronglyMeasurable
  refine ⟨hAS, hAI, he.trans hmean, ?_, ?_, hlim⟩
  · intro k hk
    have hp := hM k hk
    have hAP : Integrable (fun ω => ambientSum h X ω ^ (2 * k)) μ :=
      hT.integrable_comp_of_integrable hp.1
    have heP : (∫ ω, ambientSum h X ω ^ (2 * k) ∂μ) =
        ∫ Y, canonicalSum h Y ^ (2 * k) ∂Measure.pi ν :=
      integral_comp_of_measurePreserving hT hp.1.aestronglyMeasurable
    exact ⟨hAP, heP.trans_le hp.2⟩
  · intro τ hτ
    have he := hE τ hτ
    have hAE : Integrable (fun ω => Real.exp (τ * ambientSum h X ω / (m : ℝ))) μ :=
      hT.integrable_comp_of_integrable he.1
    have heE : (∫ ω, Real.exp (τ * ambientSum h X ω / (m : ℝ)) ∂μ) =
        ∫ Y, Real.exp (τ * canonicalSum h Y / (m : ℝ)) ∂Measure.pi ν :=
      integral_comp_of_measurePreserving hT he.1.aestronglyMeasurable
    exact ⟨hAE, heE.trans_le he.2⟩

end PeriodicAttractiveLogGas.CanonicalIndependentRealizations
