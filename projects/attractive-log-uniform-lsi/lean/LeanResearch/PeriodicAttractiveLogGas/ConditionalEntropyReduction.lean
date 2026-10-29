import LeanResearch.PeriodicAttractiveLogGas.ConditionalRelativeEntropy
import LeanResearch.PeriodicAttractiveLogGas.RelativeEntropyReferenceChange
import LeanResearch.PeriodicAttractiveLogGas.SourceConditionalEntropyEnergy
import LeanResearch.PeriodicAttractiveLogGas.ReferenceFamilyExistence

/-! The actual normalized section tilts for the source entropy reduction.
Zero-mass sections use the original Markov kernel and have zero KL cost.
The final integrated source inequality and defective LSI are separate steps.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.ConditionalEntropyReduction

open ConditionalEntropyDisintegration RelativeEntropyReferenceChange

/-- The source defect coefficient, with the own-cell term retained. -/
def defectConstant (J : ℕ) (β₀ C₂ : ℝ) : ℝ :=
  3 * β₀ * ReferenceSelfTerms.selfBound J + Real.log (ResidualExponential.sharpConstant β₀ C₂)

section Tilt
variable {A B Ω : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω]
  (κ : Kernel A B) [IsMarkovKernel κ] {F : A × B → ℝ}

/-- The genuine Markov section tilt has the stated finite logarithmic
entropy at every outside point, including its zero-mass fallback. -/
theorem conditionalTilt_kl (hF : Measurable F) {K : ℝ}
    (hb : ∀ a b, 0 ≤ F (a,b) ∧ F (a,b) ≤ K) (a : A) :
    klDiv (conditionalTiltKernel κ F hF hb a) (κ a) ≠ ∞ ∧
    (klDiv (conditionalTiltKernel κ F hF hb a) (κ a)).toReal =
      conditionalLogEntropy κ F a := by
  by_cases hz : sectionMass κ F a = 0
  · have ht : conditionalTiltKernel κ F hF hb a = κ a := by
      simp only [conditionalTiltKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hz, ite_true]
    have he : conditionalLogEntropy κ F a = 0 := by
      unfold conditionalLogEntropy
      rw [normalizedTilt_zero_mass hz]
      simp
    simp [ht, he]
  · have hm : 0 < sectionMass κ F a :=
      lt_of_le_of_ne (sectionMass_bounds κ hF hb a).1 (Ne.symm hz)
    have hf : Measurable (fun b => F (a,b)) := hF.comp measurable_prodMk_left
    have hba : ∀ᵐ b ∂κ a, 0 ≤ F (a,b) ∧ F (a,b) ≤ K := Eventually.of_forall (hb a)
    let : IsProbabilityMeasure (normalizedTilt (κ a) (fun b => F (a,b))) :=
      normalizedTilt_probability (hba.mono fun b h => h.1)
        (RelativeEntropyVariational.bounded_density_integrable hf hba).1 hm
    have hlog := (entropy_normalizedTilt (P := κ a) hf hba).1
    have hq0 : ∀ᵐ b ∂κ a, 0 ≤ F (a,b) / sectionMass κ F a :=
      hba.mono fun b h => div_nonneg h.1 hm.le
    rw [conditionalTiltKernel_apply κ hF hb a hz]
    exact ⟨klDiv_ne_top_of_log_density rfl (hf.div_const _) hq0 hlog,
      toReal_klDiv_eq_log_density rfl (hf.div_const _) hq0 hlog⟩

/-- The source tilt's actual outside marginal and Markov conditional law
are derived from the original law's disintegration through the same split. -/
theorem tilt_equiv_disintegration (P : Measure Ω) [IsProbabilityMeasure P]
    (e : Ω ≃ᵐ A × B) (ρ : Measure A) [IsProbabilityMeasure ρ]
    (hsplit : P.map e = ρ ⊗ₘ κ) {G : Ω → ℝ} (hG : Measurable G)
    {K : ℝ} (hb : ∀ x, 0 ≤ G x ∧ G x ≤ K) (hS : 0 < ∫ x, G x ∂P) :
    let F' := G ∘ e.symm
    let hF' : Measurable F' := hG.comp e.symm.measurable
    let hb' : ∀ a b, 0 ≤ F' (a,b) ∧ F' (a,b) ≤ K := fun a b => hb (e.symm (a,b))
    (∫ a, sectionMass κ F' a ∂ρ) = ∫ x, G x ∂P ∧
    (normalizedTilt P G).map (fun x => (e x).1) = normalizedTilt ρ (sectionMass κ F') ∧
    ((normalizedTilt P G).map (fun x => (e x).1)) ⊗ₘ conditionalTiltKernel κ F' hF' hb' =
      (normalizedTilt P G).map e := by
  dsimp only
  let F' := G ∘ e.symm
  have hf : Measurable F' := hG.comp e.symm.measurable
  have hfb : ∀ a b, 0 ≤ F' (a,b) ∧ F' (a,b) ≤ K := fun a b => hb (e.symm (a,b))
  have hi := (RelativeEntropyVariational.bounded_density_integrable (P := ρ ⊗ₘ κ) hf
    (Eventually.of_forall fun p => hfb p.1 p.2)).1
  have hm : (∫ a, sectionMass κ F' a ∂ρ) = ∫ x, G x ∂P := by
    simp only [sectionMass]
    rw [← Measure.integral_compProd hi, ← hsplit,
      integral_map_of_stronglyMeasurable e.measurable hf.stronglyMeasurable]
    simp only [F', Function.comp_apply, e.symm_apply_apply]
  have hs : 0 < ∫ a, sectionMass κ F' a ∂ρ := by rw [hm]; exact hS
  have hmap := normalizedTilt_equiv (P := P) e hG
  rw [hsplit] at hmap
  have hout : (normalizedTilt P G).map (fun x => (e x).1) =
      normalizedTilt ρ (sectionMass κ F') := by
    calc
      _ = ((normalizedTilt P G).map e).fst := by
        rw [Measure.fst, Measure.map_map measurable_fst e.measurable]
        rfl
      _ = _ := by rw [hmap, normalizedTilt_outside_marginal κ ρ hf hfb hs]
  refine ⟨hm, hout, ?_⟩
  rw [hout, hmap, normalizedTilt_disintegration κ ρ hf hfb hs]

end Tilt

end PeriodicAttractiveLogGas.ConditionalEntropyReduction
