import DGPS.Examples.PolynomialScore
import DGPS.Examples.PolynomialMinimizerPositivity

/-! Actual smooth positive representatives of every full-original-domain
polynomial scalar minimizer near zero field. The nonlinear physical score
system and positive representative are both concrete upstream conclusions. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

theorem isSmooth_polynomialEulerCorrection (h r : ℝ) (ρ : AbsoluteDensity 1) :
    IsSmoothPeriodic (polynomialEulerCorrection h r ρ) := by
  let M := polynomialRankOne h
  have hA : IsSmoothPeriodic M.Aq :=
    (M.dφ_smooth.isSmoothPeriodic_coordPartial 0).neg.sub
      ((M.log_smooth.isSmoothPeriodic_coordPartial 0).mul M.dφ_smooth)
  exact (((contDiff_const.mul M.φ_smooth).add (contDiff_const.mul hA)).add
    (contDiff_const.mul (M.dφ_smooth.pow 2)))

private theorem smooth_pt {F : Torus 1 → ℝ} (hF : IsSmoothPeriodic F) :
    ContDiff ℝ ∞ (fun t : ℝ => F (pt t)) :=
  hF.comp (contDiff_pi.mpr fun _ => contDiff_id)

private theorem smooth_of_pt {v : Torus 1 → ℝ}
    (hv : ContDiff ℝ ∞ (fun t : ℝ => v (pt t))) : IsSmoothPeriodic v := by
  have he : (v ∘ torusLift) = fun y : Fin 1 → ℝ => v (pt (y 0)) := by
    funext y
    change v (torusLift y) = v (torusLift (fun _ : Fin 1 => y 0))
    apply congrArg v
    apply congrArg torusLift
    funext i
    exact congrArg y (Subsingleton.elim i 0)
  unfold IsSmoothPeriodic
  rw [he]
  exact hv.comp (contDiff_apply ℝ ℝ (0 : Fin 1))

/-- The actual score system bootstraps without any regularity assumption on
the stored representative. This local ODE argument uses the positive continuous
representative only to justify the logarithm at every point. -/
theorem polynomial_classicalScore_smooth (h r : ℝ) (ρ : AbsoluteDensity 1)
    {v S : Torus 1 → ℝ} (hv : Continuous v) (hS : Continuous S)
    (hvpos : ∀ x, 0 < v x)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2) t)
    (hSd : ∀ t : ℝ, HasDerivAt (fun s => S (pt s))
      (-(S (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2 +
        v (pt t) * polynomialEulerCorrection h r ρ (pt t) / 2 -
          r * (v (pt t) * (Real.log (v (pt t) ^ 2) - Real.log ((polynomialRankOne h).q (pt t)))) -
            polynomialEulerMultiplier h r ρ * v (pt t) / 2) t) :
    IsSmoothPeriodic v ∧ IsSmoothPeriodic S ∧
      IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) := by
  have hσ := smooth_pt ((polynomialRankOne h).log_smooth.isSmoothPeriodic_coordPartial 0)
  have hΞ := smooth_pt (isSmooth_polynomialEulerCorrection h r ρ)
  have hℓ := smooth_pt (polynomialRankOne h).log_smooth
  have hall : ∀ n : ℕ,
      ContDiff ℝ (n : ℕ∞ω) (fun t : ℝ => v (pt t)) ∧
        ContDiff ℝ (n : ℕ∞ω) (fun t : ℝ => S (pt t)) := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiff_zero.mpr (hv.comp continuous_circleParam),
        contDiff_zero.mpr (hS.comp continuous_circleParam)⟩
    | succ n hn =>
      have hσn : ContDiff ℝ (n : ℕ∞ω) (fun t : ℝ => (polynomialRankOne h).dlogq (pt t)) := hσ.of_le (by simp)
      have hΞn : ContDiff ℝ (n : ℕ∞ω)
          (fun t : ℝ => polynomialEulerCorrection h r ρ (pt t)) := hΞ.of_le (by simp)
      have hℓn : ContDiff ℝ (n : ℕ∞ω) (fun t : ℝ => Real.log ((polynomialRankOne h).q (pt t))) := hℓ.of_le (by simp)
      have hlog := (hn.1.pow 2).log (fun t => (pow_pos (hvpos (pt t)) 2).ne')
      constructor
      · change ContDiff ℝ ((n : ℕ∞ω) + 1) (fun t : ℝ => v (pt t))
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun t => (hvd t).differentiableAt, ?_, ?_⟩
        · simp
        · have he : deriv (fun t : ℝ => v (pt t)) =
              fun t => (S (pt t) + v (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2 :=
            funext fun t => (hvd t).deriv
          rw [he]
          exact (hn.2.add (hn.1.mul hσn)).div_const 2
      · change ContDiff ℝ ((n : ℕ∞ω) + 1) (fun t : ℝ => S (pt t))
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun t => (hSd t).differentiableAt, ?_, ?_⟩
        · simp
        · have he : deriv (fun t : ℝ => S (pt t)) = fun t =>
              -(S (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2 +
                v (pt t) * polynomialEulerCorrection h r ρ (pt t) / 2 -
                  r * (v (pt t) * (Real.log (v (pt t) ^ 2) - Real.log ((polynomialRankOne h).q (pt t)))) -
                    polynomialEulerMultiplier h r ρ * v (pt t) / 2 :=
            funext fun t => (hSd t).deriv
          rw [he]
          exact ((((hn.2.mul hσn).neg.div_const 2).add ((hn.1.mul hΞn).div_const 2)).sub
            (contDiff_const.mul (hn.1.mul (hlog.sub hℓn)))).sub
              ((contDiff_const.mul hn.1).div_const 2)
  have hvs : IsSmoothPeriodic v := smooth_of_pt (contDiff_infty.mpr fun n => (hall n).1)
  have hSs : IsSmoothPeriodic S := smooth_of_pt (contDiff_infty.mpr fun n => (hall n).2)
  refine ⟨hvs, hSs, ?_⟩
  exact (hvs.pow 2).log (fun y => (pow_pos (hvpos (torusLift y)) 2).ne')

/-- One interval and one positive root lower bound precede every field,
actual drift and full-domain scalar minimizer. Smoothness is derived from
actual H1 minimality, not imposed on the original competitors. -/
theorem polynomial_scalarMinimizer_smooth_representative :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h), ∀ ρ : AbsoluteDensity 1,
        0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
          scalarRate (canonical_elementary_polynomial_model h) b →
        ∃ v : Torus 1 → ℝ, IsSmoothPeriodic v ∧ ρ.sqrt =ᵐ[haar 1] v ∧
          (∀ x, (1 / 2 : ℝ) ≤ v x) ∧ IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) := by
  obtain ⟨δ, hδ, hpositive⟩ := polynomial_scalarMinimizer_positive_representative
  refine ⟨δ, hδ, fun h hh hhd b ρ hG hmin => ?_⟩
  obtain ⟨vp, hvp, hpae, hp⟩ := hpositive h hh hhd b ρ hG hmin
  obtain ⟨v, S, hv, hS, hae, _, _, hvd, hSd⟩ :=
    polynomial_scalarMinimizer_classicalScore h b ρ hG hmin
  have he : v = vp := Measure.eq_of_ae_eq (hae.symm.trans hpae) hv hvp
  have hvmin : ∀ x, (1 / 2 : ℝ) ≤ v x := fun x => by rw [he]; exact hp x
  have hsm := polynomial_classicalScore_smooth h
    (scalarRate (canonical_elementary_polynomial_model h) b).toReal ρ hv hS
      (fun x => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hvmin x)) hvd hSd
  exact ⟨v, hsm.1, hae, hvmin, hsm.2.2⟩

end DGPS.Examples.PolynomialSpecies
