import DGPS.Lipschitz.T01ConditionalMeanField
import DGPS.Lipschitz.T01CenteredDrift

/-!
# Current absolute species made from arbitrary conditional marginals

The family in the mean-field rate inequality is constructed from the actual conditional
densities. Its density derivative is the normalized marginal derivative, rather than a
formal score. These statements concern the bounded positive regularization stage.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Arbitrary revealed subsets preserve both the absolute domain and the actual density
weak gradient; the same marginal derivative enters the conditional-expectation score formula. -/
theorem ae_conditional_absolute_density_gradient {d N : ℕ}
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    (hQm : Measurable Q) (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ)
    (hGm : ∀ a, Measurable (fun y => GQ y a))
    (hG2 : ∀ a, MemLp (fun y => GQ y a) 2 volume)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (S : Finset (Fin N)) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ i, i ∉ S →
      ∃ ρ : AbsoluteDensity d,
        (∀ x, ρ.density x = SharpLSI.FL.condDensS Q S i a x) ∧
        IsWeakGradient ρ.density
          (fun x => WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i a x)) := by
  let hQ : SharpLSI.FL.IsBddDens Q c C := ⟨hQm, hc, hQc, hQC⟩
  have hdom := (conditional_marginal_scores_preserve_absolute_domains hQm hc hQc hQC
    hQw hGm hG2 ν hν).1 S
  have hw : ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ i, i ∉ S →
      SharpLSI.IsWeakGrad (SharpLSI.FL.condDensS Q S i a)
        (SharpLSI.FL.gradCondS Q GQ S i a) ∧
      (∀ k, MemLp (fun x => SharpLSI.FL.gradCondS Q GQ S i a x k) 2 (haar d)) := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∉ S
    · filter_upwards [SharpLSI.FL.ae_isWeakGrad_condDensS hQ hi hQw
          (fun p => (hG2 p).integrable one_le_two),
        SharpLSI.FL.ae_memLp_gradCondS (Q := Q) hi hGm hG2] with a ha hb _
      exact ⟨ha, hb⟩
    · exact Eventually.of_forall fun a h => (hi h).elim
  have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
  filter_upwards [hdom, hw] with a ha hwa
  intro i hi
  obtain ⟨ρ, hρ⟩ := ha i hi
  have hm : Measurable (SharpLSI.FL.condDensS Q S i a) :=
    (SharpLSI.FL.measurable_condDensS hQ S i).of_uncurry_left
  have hρ2 : MemLp (SharpLSI.FL.condDensS Q S i a) 2 (haar d) := by
    apply (memLp_top_of_bound hm.aestronglyMeasurable (C / c) ?_).mono_exponent le_top
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        ((div_pos hc hC).le.trans (SharpLSI.FL.condDensS_bounds hQ S i a x).1)]
      exact (SharpLSI.FL.condDensS_bounds hQ S i a x).2
  have hg := isWeakGradient_of_legacy_pair (hwa i hi).1 hρ2
    (memLp_piLp_iff.mpr (hwa i hi).2)
  refine ⟨ρ, hρ, ?_⟩
  exact hg.congr_ae (Eventually.of_forall fun x => (hρ x).symm) (EventuallyEq.refl _ _)

/-- Apply the actual species rate to any finite list of unrevealed labels. In particular,
a bijective enumeration of the unrevealed labels gives the per-subset mean-field inequality.
No exchangeability is required, and entropy finiteness follows internally. -/
theorem ae_conditional_species_meanfield {d N : ℕ}
    (A : InteractionData d) (b : AbsoluteDrift A)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    (hQm : Measurable Q) (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ)
    (hGm : ∀ a, Measurable (fun y => GQ y a))
    (hG2 : ∀ a, MemLp (fun y => GQ y a) 2 volume)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (S : Finset (Fin N))
    (q : ℕ+) (label : Fin q → Fin N) (hlabel : ∀ s, label s ∉ S) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∃ ρ : Fin q → AbsoluteDensity d,
      (∀ s x, (ρ s).density x = SharpLSI.FL.condDensS Q S (label s) a x) ∧
      let F := SpeciesFamily.uniform q ρ
      ENNReal.ofReal (2 * r *
        ((∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
          (μ : Measure (Torus d))).toReal) +
        t01CenteredCorrection A μ (densityMeasure (barycenter F)))) ≤
      ∑ s : Fin q, ENNReal.ofReal (1 / (q : ℝ)) * ∫⁻ x, ENNReal.ofReal
        (SharpLSI.FL.condDensS Q S (label s) a x *
          ‖(SharpLSI.FL.condDensS Q S (label s) a x)⁻¹ •
            WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (label s) a x) +
            b.force (barycenter F) x‖ ^ 2) ∂haar d := by
  filter_upwards [ae_conditional_absolute_density_gradient hQm hc hQc hQC hQw hGm hG2 ν hν S]
    with a ha
  choose ρ hρ using fun s : Fin q => ha (label s) (hlabel s)
  let F := SpeciesFamily.uniform q ρ
  let hQ : SharpLSI.FL.IsBddDens Q c C := ⟨hQm, hc, hQc, hQC⟩
  have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
  have hpos : ∀ s x, (0 : ℝ) < (ρ s).density x := by
    intro s x
    rw [(hρ s).1 x]
    exact (div_pos hc hC).trans_le (SharpLSI.FL.condDensS_bounds hQ S (label s) a x).1
  refine ⟨ρ, fun s x => (hρ s).1 x, ?_⟩
  have hd := positive_speciesDissipation_eq A b F
    (fun s x => WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (label s) a x))
    (fun s => (hρ s).2) hpos
  refine (two_subrate_reference_species_entropy_le A b hμ hr hrr F).trans_eq ?_
  rw [hd]
  change (∑ s : Fin q, ENNReal.ofReal (1 / (q : ℝ)) * ∫⁻ x, ENNReal.ofReal
    ((ρ s).density x * ‖((ρ s).density x)⁻¹ •
      WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (label s) a x) +
      b.force (barycenter F) x‖ ^ 2) ∂haar d) = _
  simp_rw [(hρ _).1]
  rfl

end DGPS.Lipschitz
