import DGPS.Frontier.EX049.T25
import DGPS.Frontier.EX049.T35

/-!
# EX049.42: Weighted H1 equivalence and inverse multipliers

Task id: EX049.42 (node EX049, leaf formalization, Wave 8).
Title: Weighted H1 equivalence and inverse multipliers.

Let `Q` be a positive periodic `C¹` density on the angular circle with `0 < c ≤ Q ≤ C`. Then
the weighted and the Haar square-integrability conditions agree for every function, hence the
weighted `H¹(Q m)` domain (a function and its same angular weak derivative) equals the Haar
`H¹(m)` domain. Multiplication by `√Q` and by `1 / √Q` preserves the angular `H¹` class, with the
weak product derivative from EX049.35, and the two maps are mutually inverse.

## Provides

- `DGPS.Frontier.EX049.ex049_42_weighted_h1_equivalence_inverse_multipliers`: the full
  statement, a conjunction of ten claims: (1) the integral comparison
  `c ∫ f² dm ≤ ∫ f² Q dm ≤ C ∫ f² dm` for every real `f`; (2) `f` is square integrable for the
  weighted measure exactly when it is for `angHaar`; (3) the weighted weak-pair relation equals
  the Haar one; (4) the weighted `H¹` domain equals `AngularH1`; (5) and (6) the weak product
  derivative for `√Q` and for `1 / √Q`; (7) and (8) both multipliers preserve `AngularH1`;
  (9) and (10) both composites of the two multiplications are the identity.
- Helpers, each with full name `DGPS.Frontier.EX049.<name>`:
  - `IsAngularWeakDerivW_EX04942`: the weighted weak-pair relation for a density `Q`.
  - `measure_bounds_EX04942`: the weighted measure is squeezed between `c` and `C` times `angHaar`.
  - `memLp_weighted_iff_EX04942`: weighted and Haar `L²` memberships agree.
  - `lintegral_bounds_EX04942`: the displayed integral comparison, in `ℝ≥0∞`.
  - `contDiff_sqrt_EX04942`, `contDiff_inv_sqrt_EX04942`: both multipliers have `C¹` lifts.
  - `mul_weak_EX04942`: EX049.35 for an arbitrary circle multiplier with `C¹` lift.

## R5 notes

- The density is a function `Q : AngCircle → ℝ` whose real lift `s ↦ Q ↑s` is `C¹`. The
  specification's "periodic" is automatic for a function on the circle: the lift has period `2π`
  by construction (`periodic_lift_EX04933`). EX049.35 is applied to the pair (lift, periodicity).
  A function of the real line with a periodicity hypothesis is the same data.
- The hypotheses are `ContDiff ℝ 1` of the lift, `0 < c`, `c ≤ Q θ` and `Q θ ≤ C` for all `θ`.
  The upper constant `C` is a real number, so finiteness is built in. `c ≤ C` is not assumed
  because it follows. "Density" is not read as normalization: `∫ Q dm = 1` is not assumed and
  not used, so the statement is slightly more general than the specification.
- The weighted measure is `angHaar.withDensity (fun θ => ENNReal.ofReal (Q θ))`. For `Q = qAng h`
  it is `circleReference h` by definition, so `IsAngularWeakDerivW_EX04942 (qAng h) u g` is the
  relation `IsAngularWeakDerivW_EX04925 h u g` of EX049.25 (same fields).
- "The same angular distributional weak derivative" is the EX049.25 convention: both `u` and `g`
  lie in the weighted `L²`, and the pairing identity is the unweighted one, against `angHaar` with
  smooth circle test functions. No drift-corrected weak derivative is used or claimed.
- The integral comparison is stated in `ℝ≥0∞` with the integrand `f² Q` written out and for every
  real `f`. No measurability is needed, because only monotonicity of the lower integral is used.
  The specification's real-valued display is recovered whenever the integrals are finite.
- The two multipliers are `θ ↦ √(Q θ)` and `θ ↦ 1 / √(Q θ)`, the forms used in EX049.41. They are
  `C¹` on the compact circle because `Q ≥ c > 0` keeps the square root away from zero. The
  density is assumed only `C¹`, so no smoothness beyond `C¹` is used. Their derivative is the
  circle derivative `angDeriv` of the multiplier. Closed formulas for it are not claimed.
- "The two maps are inverse" is proved as two identities of functions on the whole circle
  (`1/√Q * (√Q * v) = v` and `√Q * (1/√Q * v) = v`), which is stronger than inverse maps on the
  subtype of `AngularH1` functions, since the preservation of `AngularH1` is claimed separately.
- EX049.41 (quantified bounds for `q_h`) is a prerequisite only for the later application to
  `q = q_h`. The statement here is for an arbitrary density, so the module does not need it.
  No uniformity over a family of densities is asserted, and the constants may depend on `Q`.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization

/-! ### The weighted domain -/

/-- The weighted angular weak-derivative relation for the density `Q`: `u` and `g` lie in
`L²(Q m)` and `g` is the distributional angular derivative of `u`, tested against smooth circle
functions with the Haar pairing (the convention of EX049.25). -/
structure IsAngularWeakDerivW_EX04942 (Q u g : AngCircle → ℝ) : Prop where
  memLp : MemLp u 2 (angHaar.withDensity fun θ => ENNReal.ofReal (Q θ))
  memLp_deriv : MemLp g 2 (angHaar.withDensity fun θ => ENNReal.ofReal (Q θ))
  ibp : ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
    ∫ θ, u θ * angDeriv ψ θ ∂angHaar = -∫ θ, g θ * ψ θ ∂angHaar

/-! ### Comparison of the weighted and Haar measures -/

lemma measure_bounds_EX04942 {Q : AngCircle → ℝ} {c C : ℝ} (hcQ : ∀ θ, c ≤ Q θ)
    (hQC : ∀ θ, Q θ ≤ C) :
    ENNReal.ofReal c • angHaar ≤ angHaar.withDensity (fun θ => ENNReal.ofReal (Q θ)) ∧
    angHaar.withDensity (fun θ => ENNReal.ofReal (Q θ)) ≤ ENNReal.ofReal C • angHaar := by
  refine ⟨?_, ?_⟩
  · rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun θ => ENNReal.ofReal_le_ofReal (hcQ θ))
  · rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun θ => ENNReal.ofReal_le_ofReal (hQC θ))

lemma memLp_weighted_iff_EX04942 {Q : AngCircle → ℝ} {c C : ℝ} (hc : 0 < c)
    (hcQ : ∀ θ, c ≤ Q θ) (hQC : ∀ θ, Q θ ≤ C) (f : AngCircle → ℝ) :
    MemLp f 2 (angHaar.withDensity fun θ => ENNReal.ofReal (Q θ)) ↔ MemLp f 2 angHaar := by
  obtain ⟨hlow, hup⟩ := measure_bounds_EX04942 hcQ hQC
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hlow' : angHaar ≤
      (ENNReal.ofReal c)⁻¹ • angHaar.withDensity (fun θ => ENNReal.ofReal (Q θ)) := by
    rw [Measure.le_iff'] at hlow ⊢
    intro s
    have := hlow s
    simp only [Measure.smul_apply, smul_eq_mul] at this ⊢
    calc angHaar s = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * angHaar s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := by gcongr
  constructor
  · intro hf
    exact (hf.smul_measure (ENNReal.inv_ne_top.2 hc0)).mono_measure hlow'
  · intro hf
    exact (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hup

lemma lintegral_bounds_EX04942 {Q : AngCircle → ℝ} {c C : ℝ} (hc : 0 < c)
    (hcQ : ∀ θ, c ≤ Q θ) (hQC : ∀ θ, Q θ ≤ C) (f : AngCircle → ℝ) :
    ENNReal.ofReal c * (∫⁻ θ, ENNReal.ofReal (f θ ^ 2) ∂angHaar)
        ≤ ∫⁻ θ, ENNReal.ofReal (f θ ^ 2 * Q θ) ∂angHaar ∧
      ∫⁻ θ, ENNReal.ofReal (f θ ^ 2 * Q θ) ∂angHaar
        ≤ ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal (f θ ^ 2) ∂angHaar) := by
  have hC : 0 ≤ C := (hc.le.trans (hcQ 0)).trans (hQC 0)
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f θ), hcQ θ])
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f θ), hQC θ])

/-! ### The multipliers `√Q` and `1 / √Q` -/

lemma contDiff_sqrt_EX04942 {Q : AngCircle → ℝ}
    (hQ : ContDiff ℝ 1 (fun s : ℝ => Q (s : AngCircle))) (hpos : ∀ θ, 0 < Q θ) :
    ContDiff ℝ 1 (fun s : ℝ => Real.sqrt (Q (s : AngCircle))) :=
  hQ.sqrt (fun _ => (hpos _).ne')

lemma contDiff_inv_sqrt_EX04942 {Q : AngCircle → ℝ}
    (hQ : ContDiff ℝ 1 (fun s : ℝ => Q (s : AngCircle))) (hpos : ∀ θ, 0 < Q θ) :
    ContDiff ℝ 1 (fun s : ℝ => 1 / Real.sqrt (Q (s : AngCircle))) :=
  contDiff_const.div (contDiff_sqrt_EX04942 hQ hpos) (fun _ => (Real.sqrt_pos.2 (hpos _)).ne')

lemma mul_weak_EX04942 {F : AngCircle → ℝ}
    (hF : ContDiff ℝ 1 (fun s : ℝ => F (s : AngCircle))) :
    (∀ v g : AngCircle → ℝ, IsAngularWeakDeriv v g →
      IsAngularWeakDeriv (fun θ => F θ * v θ) (fun θ => angDeriv F θ * v θ + F θ * g θ)) ∧
    (∀ v : AngCircle → ℝ, AngularH1 v → AngularH1 (fun θ => F θ * v θ)) := by
  have hper := periodic_lift_EX04933 F
  have e : (hper.lift : AngCircle → ℝ) = F := by
    funext θ
    obtain ⟨s, rfl⟩ := DGPS.Circle.StationaryFlux.exists_coe θ
    exact hper.lift_coe s
  obtain ⟨-, -, h3, h4⟩ := ex049_35_periodic_c1_multipliers (fun s : ℝ => F (s : AngCircle)) hF hper
  rw [e] at h3 h4
  exact ⟨h3, h4⟩

/-! ### Main statement -/

/-- EX049.42: for a positive `C¹` density `Q` on the circle with `0 < c ≤ Q ≤ C`: the weighted
and Haar integrals and `L²` conditions are comparable, the weighted `H¹` domain equals the Haar
`H¹` domain for the same weak derivative, multiplication by `√Q` and by `1 / √Q` gives weak pairs
and preserves `AngularH1`, and the two multiplications are inverse to each other. -/
theorem ex049_42_weighted_h1_equivalence_inverse_multipliers
    (Q : AngCircle → ℝ) (hQ : ContDiff ℝ 1 (fun s : ℝ => Q (s : AngCircle)))
    (c C : ℝ) (hc : 0 < c) (hcQ : ∀ θ, c ≤ Q θ) (hQC : ∀ θ, Q θ ≤ C) :
    (∀ f : AngCircle → ℝ,
      ENNReal.ofReal c * (∫⁻ θ, ENNReal.ofReal (f θ ^ 2) ∂angHaar)
          ≤ ∫⁻ θ, ENNReal.ofReal (f θ ^ 2 * Q θ) ∂angHaar ∧
        ∫⁻ θ, ENNReal.ofReal (f θ ^ 2 * Q θ) ∂angHaar
          ≤ ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal (f θ ^ 2) ∂angHaar)) ∧
    (∀ f : AngCircle → ℝ,
      MemLp f 2 (angHaar.withDensity fun θ => ENNReal.ofReal (Q θ)) ↔ MemLp f 2 angHaar) ∧
    (∀ u g : AngCircle → ℝ, IsAngularWeakDerivW_EX04942 Q u g ↔ IsAngularWeakDeriv u g) ∧
    (∀ u : AngCircle → ℝ, (∃ g, IsAngularWeakDerivW_EX04942 Q u g) ↔ AngularH1 u) ∧
    (∀ v g : AngCircle → ℝ, IsAngularWeakDeriv v g →
      IsAngularWeakDeriv (fun θ => Real.sqrt (Q θ) * v θ)
        (fun θ => angDeriv (fun θ => Real.sqrt (Q θ)) θ * v θ + Real.sqrt (Q θ) * g θ)) ∧
    (∀ v g : AngCircle → ℝ, IsAngularWeakDeriv v g →
      IsAngularWeakDeriv (fun θ => 1 / Real.sqrt (Q θ) * v θ)
        (fun θ => angDeriv (fun θ => 1 / Real.sqrt (Q θ)) θ * v θ
          + 1 / Real.sqrt (Q θ) * g θ)) ∧
    (∀ v : AngCircle → ℝ, AngularH1 v → AngularH1 (fun θ => Real.sqrt (Q θ) * v θ)) ∧
    (∀ v : AngCircle → ℝ, AngularH1 v → AngularH1 (fun θ => 1 / Real.sqrt (Q θ) * v θ)) ∧
    (∀ v : AngCircle → ℝ,
      (fun θ => 1 / Real.sqrt (Q θ) * (Real.sqrt (Q θ) * v θ)) = v) ∧
    (∀ v : AngCircle → ℝ,
      (fun θ => Real.sqrt (Q θ) * (1 / Real.sqrt (Q θ) * v θ)) = v) := by
  have hpos : ∀ θ, 0 < Q θ := fun θ => hc.trans_le (hcQ θ)
  have hs : ∀ θ, Real.sqrt (Q θ) ≠ 0 := fun θ => (Real.sqrt_pos.2 (hpos θ)).ne'
  have hmem := memLp_weighted_iff_EX04942 hc hcQ hQC
  have h1 := mul_weak_EX04942 (F := fun θ => Real.sqrt (Q θ)) (contDiff_sqrt_EX04942 hQ hpos)
  have h2 := mul_weak_EX04942 (F := fun θ => 1 / Real.sqrt (Q θ))
    (contDiff_inv_sqrt_EX04942 hQ hpos)
  refine ⟨fun f => lintegral_bounds_EX04942 hc hcQ hQC f, hmem, ?_, ?_, h1.1, h2.1, h1.2, h2.2,
    fun v => ?_, fun v => ?_⟩
  · intro u g
    exact ⟨fun H => ⟨(hmem u).1 H.memLp, (hmem g).1 H.memLp_deriv, H.ibp⟩,
      fun H => ⟨(hmem u).2 H.memLp, (hmem g).2 H.memLp_deriv, H.ibp⟩⟩
  · intro u
    constructor
    · rintro ⟨g, H⟩
      exact ⟨g, (hmem u).1 H.memLp, (hmem g).1 H.memLp_deriv, H.ibp⟩
    · rintro ⟨g, H⟩
      exact ⟨g, (hmem u).2 H.memLp, (hmem g).2 H.memLp_deriv, H.ibp⟩
  · funext θ
    rw [← mul_assoc, one_div, inv_mul_cancel₀ (hs θ), one_mul]
  · funext θ
    rw [← mul_assoc, mul_one_div_cancel (hs θ), one_mul]

end DGPS.Frontier.EX049
