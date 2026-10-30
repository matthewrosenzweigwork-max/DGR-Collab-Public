import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarScore

/-! Smooth positive representatives of EVERY actual scalar minimizer, derived
from the genuine physical first-order system. No smooth minimizer or Euler
condition is assumed in the actual-model factory. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

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
theorem elementary_classicalScore_smooth (h ε r : ℝ) (ρ : AbsoluteDensity 1)
    {v S : Torus 1 → ℝ} (hv : Continuous v) (hS : Continuous S)
    (hvpos : ∀ x, 0 < v x)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * sigT h (pt t)) / 2) t)
    (hSd : ∀ t : ℝ, HasDerivAt (fun s => S (pt s))
      (-(S (pt t) * sigT h (pt t)) / 2 +
        v (pt t) * elementaryEulerCorrection h ε r ρ (pt t) / 2 -
          r * (v (pt t) * (Real.log (v (pt t) ^ 2) - ellT h (pt t))) -
            elementaryEulerMultiplier h ε r ρ * v (pt t) / 2) t) :
    IsSmoothPeriodic v ∧ IsSmoothPeriodic S ∧
      IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) := by
  have hσ := smooth_pt ((isSmoothPeriodic_ellT h).isSmoothPeriodic_coordPartial 0)
  have hΞ := smooth_pt (isSmooth_elementaryEulerCorrection h ε r ρ)
  have hℓ := smooth_pt (isSmoothPeriodic_ellT h)
  have hall : ∀ n : ℕ,
      ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => v (pt t)) ∧
        ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => S (pt t)) := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiff_zero.mpr (hv.comp continuous_circleParam),
        contDiff_zero.mpr (hS.comp continuous_circleParam)⟩
    | succ n hn =>
      have hσn : ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => sigT h (pt t)) := hσ.of_le (by simp)
      have hΞn : ContDiff ℝ (n : WithTop ℕ∞)
          (fun t : ℝ => elementaryEulerCorrection h ε r ρ (pt t)) := hΞ.of_le (by simp)
      have hℓn : ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => ellT h (pt t)) := hℓ.of_le (by simp)
      have hlog := (hn.1.pow 2).log (fun t => (pow_pos (hvpos (pt t)) 2).ne')
      constructor
      · change ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun t : ℝ => v (pt t))
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun t => (hvd t).differentiableAt, ?_, ?_⟩
        · simp
        · have he : deriv (fun t : ℝ => v (pt t)) =
              fun t => (S (pt t) + v (pt t) * sigT h (pt t)) / 2 :=
            funext fun t => (hvd t).deriv
          rw [he]
          exact (hn.2.add (hn.1.mul hσn)).div_const 2
      · change ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun t : ℝ => S (pt t))
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun t => (hSd t).differentiableAt, ?_, ?_⟩
        · simp
        · have he : deriv (fun t : ℝ => S (pt t)) = fun t =>
              -(S (pt t) * sigT h (pt t)) / 2 +
                v (pt t) * elementaryEulerCorrection h ε r ρ (pt t) / 2 -
                  r * (v (pt t) * (Real.log (v (pt t) ^ 2) - ellT h (pt t))) -
                    elementaryEulerMultiplier h ε r ρ * v (pt t) / 2 :=
            funext fun t => (hSd t).deriv
          rw [he]
          exact ((((hn.2.mul hσn).neg.div_const 2).add ((hn.1.mul hΞn).div_const 2)).sub
            (contDiff_const.mul (hn.1.mul (hlog.sub hℓn)))).sub
              ((contDiff_const.mul hn.1).div_const 2)
  have hvs : IsSmoothPeriodic v := smooth_of_pt (contDiff_infty.mpr fun n => (hall n).1)
  have hSs : IsSmoothPeriodic S := smooth_of_pt (contDiff_infty.mpr fun n => (hall n).2)
  refine ⟨hvs, hSs, ?_⟩
  exact (hvs.pow 2).log (fun y => (pow_pos (hvpos (torusLift y)) 2).ne')

/-- Full original-absolute-H1 minimizers have genuine smooth positive
representatives. Constants are chosen before the coupling, drift and EVERY
minimizer. This is not an assumed smooth-domain optimizer theorem. -/
theorem elementaryModel_scalarMinimizer_smooth_representative (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∃ v : Torus 1 → ℝ, IsSmoothPeriodic v ∧ ρ.sqrt =ᵐ[haar 1] v ∧
              (∀ x, m ≤ v x) ∧ IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) := by
  obtain ⟨δ, hδ, hδr, hclassical⟩ := elementaryModel_scalarMinimizer_classicalScore D
  refine ⟨δ, hδ, hδr, fun h hh hsmall => ?_⟩
  obtain ⟨ε0, m, hε0, hεmax, hm, hminimizer⟩ := hclassical h hh hsmall
  refine ⟨ε0, m, hε0, hεmax, hm, fun ε hε he b ρ hG hmin => ?_⟩
  obtain ⟨v, S, hv, hS, hae, hvmin, hvd, hSd⟩ := hminimizer ε hε he b ρ hG hmin
  have hsm := elementary_classicalScore_smooth h ε (scalarRate (modelData h ε) b).toReal ρ
    hv hS (fun x => hm.trans_le (hvmin x)) hvd hSd
  exact ⟨v, hsm.1, hae, hvmin, hsm.2.2⟩

end DGPS.Examples.ThreeSpeciesCircle
