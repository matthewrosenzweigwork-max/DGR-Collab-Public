import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarSmooth

/-! The actual pointwise physical logarithmic Euler equation of EVERY scalar
minimizer, derived from the true score system. This is the native differential
identity needed before transporting to the model-specific angular chart. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Exact physical logarithmic form of the actual score ODE. -/
theorem elementary_classicalScore_logEuler (h ε r : ℝ) (ρ : AbsoluteDensity 1)
    {v S : Torus 1 → ℝ} (hvpos : ∀ x, 0 < v x)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * sigT h (pt t)) / 2) t)
    (hSd : ∀ t : ℝ, HasDerivAt (fun s => S (pt s))
      (-(S (pt t) * sigT h (pt t)) / 2 +
        v (pt t) * elementaryEulerCorrection h ε r ρ (pt t) / 2 -
          r * (v (pt t) * (Real.log (v (pt t) ^ 2) - ellT h (pt t))) -
            elementaryEulerMultiplier h ε r ρ * v (pt t) / 2) t) :
    let L := fun t : ℝ => Real.log (v (pt t) ^ 2) - ellT h (pt t);
    ∀ t : ℝ, -2 * deriv (deriv L) t - (deriv L t) ^ 2 -
      2 * sigT h (pt t) * deriv L t - 2 * r * L t +
        elementaryEulerCorrection h ε r ρ (pt t) - elementaryEulerMultiplier h ε r ρ = 0 := by
  let L := fun t : ℝ => Real.log (v (pt t) ^ 2) - ellT h (pt t)
  have hL (t : ℝ) : HasDerivAt L (S (pt t) / v (pt t)) t := by
    have hlog := ((hvd t).pow 2).log (pow_ne_zero 2 (hvpos (pt t)).ne')
    have hell := hasDerivAt_smooth_one (isSmoothPeriodic_ellT h) t
    convert hlog.sub hell using 1
    change S (pt t) / v (pt t) =
        (2 * v (pt t) ^ (2 - 1) * ((S (pt t) + v (pt t) * sigT h (pt t)) / 2)) /
          v (pt t) ^ 2 - sigT h (pt t)
    field_simp [(hvpos (pt t)).ne']
    <;> ring
  have hL1 : deriv L = fun t => S (pt t) / v (pt t) := funext fun t => (hL t).deriv
  change ∀ t : ℝ, -2 * deriv (deriv L) t - (deriv L t)^2 -
    2 * sigT h (pt t) * deriv L t - 2 * r * L t +
      elementaryEulerCorrection h ε r ρ (pt t) - elementaryEulerMultiplier h ε r ρ = 0
  intro t
  have hquot := (hSd t).div (hvd t) (hvpos (pt t)).ne'
  have hL2 : deriv (deriv L) t =
      ((-(S (pt t) * sigT h (pt t)) / 2 +
          v (pt t) * elementaryEulerCorrection h ε r ρ (pt t) / 2 -
            r * (v (pt t) * L t) - elementaryEulerMultiplier h ε r ρ * v (pt t) / 2) *
        v (pt t) - S (pt t) * ((S (pt t) + v (pt t) * sigT h (pt t)) / 2)) /
          v (pt t) ^ 2 := by
    rw [hL1]
    exact hquot.deriv
  change -2 * deriv (deriv L) t - (deriv L t) ^ 2 -
    2 * sigT h (pt t) * deriv L t - 2 * r * L t +
      elementaryEulerCorrection h ε r ρ (pt t) - elementaryEulerMultiplier h ε r ρ = 0
  rw [hL2, hL1]
  field_simp [(hvpos (pt t)).ne']
  <;> ring

/-- Every actual full-original-H1 scalar minimizer has a smooth positive AE
representative satisfying the actual pointwise physical logarithmic Euler
equation. No smoothness, positivity or Euler condition is assumed. -/
theorem elementaryModel_scalarMinimizer_logEuler (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∃ v : Torus 1 → ℝ, IsSmoothPeriodic v ∧ ρ.sqrt =ᵐ[haar 1] v ∧
              (∀ x, m ≤ v x) ∧ IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) ∧
              (let r := (scalarRate (modelData h ε) b).toReal;
               let L := fun t : ℝ => Real.log (v (pt t) ^ 2) - ellT h (pt t);
               ∀ t : ℝ, -2 * deriv (deriv L) t - (deriv L t) ^ 2 -
                 2 * sigT h (pt t) * deriv L t - 2 * r * L t +
                   elementaryEulerCorrection h ε r ρ (pt t) -
                     elementaryEulerMultiplier h ε r ρ = 0) := by
  obtain ⟨δ, hδ, hδr, hclassical⟩ := elementaryModel_scalarMinimizer_classicalScore D
  refine ⟨δ, hδ, hδr, fun h hh hsmall => ?_⟩
  obtain ⟨ε0, m, hε0, hεmax, hm, hminimizer⟩ := hclassical h hh hsmall
  refine ⟨ε0, m, hε0, hεmax, hm, fun ε hε he b ρ hG hmin => ?_⟩
  obtain ⟨v, S, hv, hS, hae, hvmin, hvd, hSd⟩ := hminimizer ε hε he b ρ hG hmin
  have hvpos : ∀ x, 0 < v x := fun x => hm.trans_le (hvmin x)
  have hsm := elementary_classicalScore_smooth h ε (scalarRate (modelData h ε) b).toReal ρ
    hv hS hvpos hvd hSd
  exact ⟨v, hsm.1, hae, hvmin, hsm.2.2,
    elementary_classicalScore_logEuler h ε (scalarRate (modelData h ε) b).toReal ρ hvpos hvd hSd⟩

end DGPS.Examples.ThreeSpeciesCircle
