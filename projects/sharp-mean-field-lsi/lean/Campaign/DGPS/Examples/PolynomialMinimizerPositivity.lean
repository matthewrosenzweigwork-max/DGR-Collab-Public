import DGPS.Examples.PolynomialPositiveCapture
import DGPS.Examples.PolynomialScalarSineUpper

/-! A genuine common positive representative for EVERY actual full-domain
polynomial scalar minimizer near zero field. Both the rate upper input and
original-H1 origin capture are discharged by concrete upstream producers. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- One field interval and one fixed lower bound work for every actual drift
and every original-H1 positive-gap scalar minimizer. Stored roots retain only
their original AE convention. No localization or positivity premise occurs. -/
theorem polynomial_scalarMinimizer_positive_representative :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h), ∀ ρ : AbsoluteDensity 1,
        0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
          scalarRate (canonical_elementary_polynomial_model h) b →
        ∃ v : Torus 1 → ℝ, Continuous v ∧ ρ.sqrt =ᵐ[haar 1] v ∧ ∀ x, (1 / 2 : ℝ) ≤ v x := by
  classical
  obtain ⟨δ1, hδ1, hupper1⟩ := polynomial_scalarRate_eventual_upper 1 (by norm_num)
  by_contra hno
  push_neg at hno
  have hcounter (n : ℕ) := hno (min δ1 (1 / ((n : ℝ) + 1)))
    (lt_min hδ1 (by positivity))
  choose hs hpos hsmall bs ρs hGs hmins hbad using hcounter
  have hhs : Tendsto hs atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hpos n).le) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (hsmall n).le.trans (min_le_right _ _)
  have hMq : 0 ≤ a0 + 1 := by unfold a0; positivity
  have hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (hs n)) (bs n) (ρs n) ≤
      ENNReal.ofReal (a0 + 1) := by
    intro n
    rw [hmins n]
    exact hupper1 (hs n) (by rw [abs_of_pos (hpos n)]; exact (hsmall n).trans_le (min_le_left _ _)) (bs n)
  have hnear : ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
      scalarQuotient (canonical_elementary_polynomial_model (hs n)) (bs n) (ρs n) ≤
        ENNReal.ofReal (a0 + t) := by
    intro t ht
    obtain ⟨δ, hδ, hu⟩ := polynomial_scalarRate_eventual_upper t ht
    filter_upwards [hhs.eventually (gt_mem_nhds hδ)] with n hn
    rw [hmins n]
    exact hu (hs n) (by rwa [abs_of_pos (hpos n)]) (bs n)
  obtain ⟨φ, v, _, hv, _, hpositive⟩ :=
    polynomial_scalar_origin_positive_capture hs hhs bs (a0 + 1) hMq ρs hGs hQ hnear
  obtain ⟨n, hn⟩ := hpositive.exists
  obtain ⟨x, hx⟩ := hbad (φ n) (v n) (hv n).1 (hv n).2
  exact (not_lt_of_ge (hn x)) hx

end DGPS.Examples.PolynomialSpecies
