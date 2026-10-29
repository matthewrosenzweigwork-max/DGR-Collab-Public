import DGPS.FiniteN.OrderedRadialNormalization
import DGPS.Circle.BesselMoments

/-!
# Optional ordered exponential radial moment (FIN043)

For a fixed `κ > 2` and the unique positive critical radius `r0`, the selected
ordered radial laws satisfy a uniform exponential moment bound
`∫ exp (t r²) dσ_N ≤ M` for all `N ≥ 1`, with `t = c/4` where `c` is the
quadratic coercivity constant of the radial potential at `r0`.

The Gaussian comparison is carried out in the scaled coordinate `r = r0 + u/√N`,
where the potential difference is at most `c u²` and the moment weight is
dominated by an integrable envelope in `u`. The lower bound on the partition
function from FIN035 holds uniformly for `N ≥ 1`, so no finite case split is
needed.
-/

open MeasureTheory Set Filter
open DGPS.Circle.BesselMoments

namespace DGPS.FiniteN

/-- Pointwise Gaussian comparison for the moment weight `exp (c r² / 4) · W`,
in the scaled coordinate `r = r0 + u/s`. -/
theorem ordered_exp_weight_scaled_le_FIN043 {κ r0 c s u : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r) :
    Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
      ≤ Real.exp (c * r0 ^ 2 / 2) * orderedEnvelope_FIN035 r0 (c / 2) u := by
  have hs0 : 0 < s := by linarith
  have hp : (1 : ℝ) ≤ (r0 + 1 + |u|) ^ 2 := by
    have h1 : (1 : ℝ) ≤ r0 + 1 + |u| := by linarith [abs_nonneg u]
    nlinarith
  have hW : orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
      ≤ orderedEnvelope_FIN035 r0 c u := by
    have h := orderedRadialWeight_scaled_le_FIN035 (κ := κ) (p := 1) (u := u) hr0 hs hU hp
    rwa [one_mul] at h
  have hq : (u / s) ^ 2 ≤ u ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg u) (by nlinarith)
  have hsq : (r0 + u / s) ^ 2 ≤ 2 * r0 ^ 2 + 2 * u ^ 2 := by
    nlinarith [sq_nonneg (r0 - u / s)]
  have hr2 : c / 4 * (r0 + u / s) ^ 2 ≤ c * r0 ^ 2 / 2 + c / 2 * u ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ c / 4)
    nlinarith [h4]
  have hE : Real.exp (c / 4 * (r0 + u / s) ^ 2)
      ≤ Real.exp (c * r0 ^ 2 / 2) * Real.exp (c / 2 * u ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hr2
  have hkey : Real.exp (c / 2 * u ^ 2) * orderedEnvelope_FIN035 r0 c u
      = orderedEnvelope_FIN035 r0 (c / 2) u := by
    have hexp : Real.exp (c / 2 * u ^ 2) * Real.exp (-c * u ^ 2)
        = Real.exp (-(c / 2) * u ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold orderedEnvelope_FIN035
    calc Real.exp (c / 2 * u ^ 2) * ((r0 + 1 + |u|) ^ 3 * Real.exp (-c * u ^ 2))
        = (r0 + 1 + |u|) ^ 3 * (Real.exp (c / 2 * u ^ 2) * Real.exp (-c * u ^ 2)) := by ring
      _ = (r0 + 1 + |u|) ^ 3 * Real.exp (-(c / 2) * u ^ 2) := by rw [hexp]
  have hWnn := orderedRadialWeight_nonneg_FIN035 κ r0 (s ^ 2) (r0 + u / s)
  have hnn : 0 ≤ Real.exp (c * r0 ^ 2 / 2) * Real.exp (c / 2 * u ^ 2) :=
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  calc Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
      ≤ (Real.exp (c * r0 ^ 2 / 2) * Real.exp (c / 2 * u ^ 2)) * orderedEnvelope_FIN035 r0 c u :=
        mul_le_mul hE hW hWnn hnn
    _ = Real.exp (c * r0 ^ 2 / 2) * (Real.exp (c / 2 * u ^ 2) * orderedEnvelope_FIN035 r0 c u) := by
        ring
    _ = Real.exp (c * r0 ^ 2 / 2) * orderedEnvelope_FIN035 r0 (c / 2) u := by rw [hkey]

/-- Integrability of the scaled moment weight and the uniform bound on its integral,
with the partition-function scale `1/s` kept explicit. -/
theorem ordered_exp_moment_numerator_FIN043 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r) :
    Integrable (fun r => Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) ∧
      ∫ r, Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r
        ≤ Real.exp (c * r0 ^ 2 / 2) * (∫ u, orderedEnvelope_FIN035 r0 (c / 2) u) / s := by
  have hs0 : 0 < s := by linarith
  have hEnv : Integrable (orderedEnvelope_FIN035 r0 (c / 2)) :=
    orderedEnvelope_integrable_FIN035 r0 (by linarith)
  have hmeas : Measurable (fun r : ℝ =>
      Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) :=
    (Real.measurable_exp.comp (by fun_prop)).mul (orderedRadialWeight_measurable_FIN035 κ r0 (s ^ 2))
  have hint_u : Integrable (fun u : ℝ =>
      Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)) := by
    refine Integrable.mono' (hEnv.const_mul (Real.exp (c * r0 ^ 2 / 2))) ?_ ?_
    · exact (hmeas.comp (by fun_prop : Measurable (fun u : ℝ => r0 + u / s))).aestronglyMeasurable
    · refine Eventually.of_forall (fun u => ?_)
      have hnn : 0 ≤ Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s) :=
        mul_nonneg (Real.exp_pos _).le (orderedRadialWeight_nonneg_FIN035 _ _ _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact ordered_exp_weight_scaled_le_FIN043 hr0 hc hs hU
  have hint : Integrable (fun r =>
      Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) :=
    ordered_integrable_of_scaled_FIN035 (f := fun r =>
      Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) r0 hs0 hint_u
  refine ⟨hint, ?_⟩
  have hscale : ∫ u, Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
      = s * ∫ r, Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
    ordered_scaled_integral_FIN035 (fun r =>
      Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) r0 hs0
  have hbound : ∫ u, Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
      ≤ ∫ u, Real.exp (c * r0 ^ 2 / 2) * orderedEnvelope_FIN035 r0 (c / 2) u :=
    integral_mono hint_u (hEnv.const_mul _) (fun u => ordered_exp_weight_scaled_le_FIN043 hr0 hc hs hU)
  rw [integral_const_mul] at hbound
  rw [le_div_iff₀ hs0]
  calc (∫ r, Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) * s
      = s * ∫ r, Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r := mul_comm _ _
    _ = ∫ u, Real.exp (c / 4 * (r0 + u / s) ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s) :=
        hscale.symm
    _ ≤ Real.exp (c * r0 ^ 2 / 2) * ∫ u, orderedEnvelope_FIN035 r0 (c / 2) u := hbound

/-- **FIN043.** For `κ > 2` and the positive critical radius `r0` (unique by FIN034),
there are `t > 0` and `M` such that for every `N ≥ 1` the ordered radial law is
integrable against `exp (t r²)` and `∫ exp (t r²) dσ_N ≤ M`. -/
theorem optional_ordered_exponential_radial_moment {κ : ℝ} (hκ : 2 < κ) {r0 : ℝ}
    (hr0 : 0 < r0) (hroot : r0 = κ * besselRatio r0) :
    ∃ t : ℝ, 0 < t ∧ ∃ M : ℝ, ∀ N : ℝ, 1 ≤ N →
      Integrable (fun r => Real.exp (t * r ^ 2)) (orderedRadialLaw_FIN035 κ r0 N) ∧
        ∫ r, Real.exp (t * r ^ 2) ∂(orderedRadialLaw_FIN035 κ r0 N) ≤ M := by
  obtain ⟨r1, _hr1, _hroot1, huniq, c, C, hc, hcC, -, -, hU⟩ :=
    ordered_radial_well_geometry hκ
  have hr : r0 = r1 := huniq r0 hr0 hroot
  rw [← hr] at hU
  have hU1 : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r := fun r hr' => (hU r hr').1
  have hU2 : ∀ r, 0 ≤ r → radialU_orad κ r0 r ≤ C * (r - r0) ^ 2 := fun r hr' => (hU r hr').2
  have hC0 : 0 ≤ C := by linarith
  have hA0 : 0 < r0 * Real.exp (-C) := mul_pos hr0 (Real.exp_pos _)
  have hI0 : 0 ≤ ∫ u, orderedEnvelope_FIN035 r0 (c / 2) u :=
    integral_nonneg (fun u => by unfold orderedEnvelope_FIN035; positivity)
  have hM0 : 0 ≤ Real.exp (c * r0 ^ 2 / 2) * (∫ u, orderedEnvelope_FIN035 r0 (c / 2) u)
      / (r0 * Real.exp (-C)) :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le hI0) hA0.le
  refine ⟨c / 4, by linarith, Real.exp (c * r0 ^ 2 / 2) * (∫ u, orderedEnvelope_FIN035 r0 (c / 2) u)
      / (r0 * Real.exp (-C)), ?_⟩
  intro N hN
  obtain ⟨s, hs1, rfl⟩ : ∃ s : ℝ, 1 ≤ s ∧ s ^ 2 = N :=
    ⟨Real.sqrt N,
      by nlinarith [Real.sqrt_nonneg N, Real.sq_sqrt (show (0 : ℝ) ≤ N by linarith)],
      Real.sq_sqrt (show (0 : ℝ) ≤ N by linarith)⟩
  have hs0 : 0 < s := by linarith
  have hlow := orderedRadialZ_lower_FIN035 hr0 hc hC0 hs1 hU1 hU2
  have hA : 0 < r0 * Real.exp (-C) / s := div_pos hA0 hs0
  have hZpos : 0 < orderedRadialZ_FIN035 κ r0 (s ^ 2) := lt_of_lt_of_le hA hlow
  obtain ⟨hint, hbd⟩ := ordered_exp_moment_numerator_FIN043 hr0 hc hs1 hU1
  refine ⟨?_, ?_⟩
  · exact orderedRadialLaw_integrable_FIN035 hZpos (fun r => Real.exp (c / 4 * r ^ 2)) hint
  · have hlaw : ∫ r, Real.exp (c / 4 * r ^ 2) ∂(orderedRadialLaw_FIN035 κ r0 (s ^ 2))
        = (∫ r, Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r)
          / orderedRadialZ_FIN035 κ r0 (s ^ 2) :=
      orderedRadialLaw_integral_FIN035 hZpos (fun r => Real.exp (c / 4 * r ^ 2))
    rw [hlaw, div_le_iff₀ hZpos]
    calc (∫ r, Real.exp (c / 4 * r ^ 2) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r)
        ≤ Real.exp (c * r0 ^ 2 / 2) * (∫ u, orderedEnvelope_FIN035 r0 (c / 2) u) / s := hbd
      _ = (Real.exp (c * r0 ^ 2 / 2) * (∫ u, orderedEnvelope_FIN035 r0 (c / 2) u)
            / (r0 * Real.exp (-C))) * (r0 * Real.exp (-C) / s) := by
          field_simp
      _ ≤ (Real.exp (c * r0 ^ 2 / 2) * (∫ u, orderedEnvelope_FIN035 r0 (c / 2) u)
            / (r0 * Real.exp (-C))) * orderedRadialZ_FIN035 κ r0 (s ^ 2) :=
          mul_le_mul_of_nonneg_left hlow hM0

end DGPS.FiniteN
