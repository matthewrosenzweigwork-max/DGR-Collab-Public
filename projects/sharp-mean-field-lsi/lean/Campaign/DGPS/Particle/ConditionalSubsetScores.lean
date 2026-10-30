import DGPS.Particle.ConditionalScores
import FullLabeledLSI.Paper.Sec5CondD

/-!
# Absolute domains and conditional scores for arbitrary revealed subsets

The inherited arbitrary-subset marginal and conditional-expectation arguments require only
the joint density and its weak gradient. They are independent of the potential hypotheses.
The absolute competitors below use the campaign domain and a genuine weak-gradient witness.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Arbitrary-subset conditional marginals are current absolute-admissible densities,
and their score is the conditional expectation of the joint score, with conditional Jensen.
No exchangeability, boundedness of the score, or semiconvexity assumption is imposed. -/
theorem conditional_marginal_scores_preserve_absolute_domains {d N : ℕ}
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    (hQm : Measurable Q) (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ)
    (hGm : ∀ a, Measurable (fun y => GQ y a))
    (hG2 : ∀ a, MemLp (fun y => GQ y a) 2 volume)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) :
    (∀ S : Finset (Fin N), ∀ᵐ a ∂(volume : Measure (S → Torus d)),
      ∀ i, i ∉ S → ∃ ρ : AbsoluteDensity d,
        ∀ x, ρ.density x = SharpLSI.FL.condDensS Q S i a x) ∧
    (∀ (S : Finset (Fin N)) (i : Fin N), i ∉ S →
      (∀ k : Fin d,
        (fun X => SharpLSI.FL.gradCondS Q GQ S i (SharpLSI.FL.restrictS S X) (X i) k /
          SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) (X i)) =ᵐ[ν]
          ν[fun Y => GQ (SharpLSI.flat Y) (i, k) / Q Y |
            MeasurableSpace.comap (fun X => (SharpLSI.FL.restrictS S X, X i)) inferInstance]) ∧
      (∑ k, ∫⁻ X, ENNReal.ofReal ((SharpLSI.FL.gradCondS Q GQ S i
          (SharpLSI.FL.restrictS S X) (X i) k /
          SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) (X i)) ^ 2) ∂ν ≤
        ∑ k, ∫⁻ X, ENNReal.ofReal ((GQ (SharpLSI.flat X) (i, k) / Q X) ^ 2) ∂ν)) := by
  let hQ : SharpLSI.FL.IsBddDens Q c C := ⟨hQm, hc, hQc, hQC⟩
  refine ⟨fun S => ?_, fun S i hi => ?_⟩
  · rw [ae_all_iff]
    intro i
    by_cases hi : i ∉ S
    · have hH := SharpLSI.FL.ae_memH1_sqrt_condDensS hQ hi hQw hGm hG2
      filter_upwards [hH] with a ha _
      let u : Torus d → ℝ := fun x => Real.sqrt (SharpLSI.FL.condDensS Q S i a x)
      have hgrad : MemLp (fun x => WithLp.toLp 2 (SharpLSI.weakGrad u x)) 2 (haar d) := by
        apply memLp_piLp_iff.mpr
        exact SharpLSI.memLp_weakGrad_comp ha
      have hu : MemH1 u := ⟨_, isWeakGradient_of_legacy_pair
        (SharpLSI.isWeakGrad_weakGrad ha.1) ha.2.1 hgrad⟩
      have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
      have hρ0 : ∀ x, 0 ≤ SharpLSI.FL.condDensS Q S i a x := fun x =>
        (div_pos hc hC).le.trans (SharpLSI.FL.condDensS_bounds hQ S i a x).1
      refine ⟨{
        sqrt := u
        sqrt_mem := hu
        sqrt_nonneg := Eventually.of_forall fun x => Real.sqrt_nonneg _
        mass_one := ?_ }, ?_⟩
      · simp only [u, Real.sq_sqrt (hρ0 _)]
        exact SharpLSI.FL.integral_condDensS hQ S i a
      · intro x
        exact Real.sq_sqrt (hρ0 x)
    · exact Eventually.of_forall fun a h => (hi h).elim
  · exact ⟨fun k => SharpLSI.FL.score_ae_eq_condExp hQ hi hν hGm k
      ((hG2 (i, k)).integrable one_le_two),
      SharpLSI.FL.lintegral_score_sq_sum_le hQ hi hν hGm⟩

end DGPS.Lipschitz
