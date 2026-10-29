import DGPS.Examples.RoughBoundary.LandscapeConvexity

/-!
# Global three-region positivity persists (RUF023)

Source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.2 (3.2)-(3.4).  Fix `R > 2κ` and
`r₀ = 1/352 = (1/22)/16`.  With `γ = min_{r₀ ≤ ‖t‖ ≤ R} Ψ∞(t) > 0`, every unit feature `U` with exact
first two moments and `‖Ψ - Ψ∞‖_{C⁰(B̄_R)} < γ/2` has `Ψ ≥ 0` with zero only at `t = 0`, all
critical points in `B̄_κ` and all global minima in `B̄_{2κ}`.

Main result: `DGPS.Examples.RoughBoundary.Landscape.global_three_region_positivity_persists`.
-/

open MeasureTheory Set Metric DGPS.Examples.RoughBoundary.ThreeState
open scoped ContDiff Real

namespace DGPS.Examples.RoughBoundary.Landscape

section tiltbounds
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {V : Ω → E2}

omit [IsProbabilityMeasure μ] in
lemma mom_one_eq (t : E2) :
    mom μ V (fun _ => 1) t = ∫ w, Real.exp (inner ℝ t (V w)) ∂μ := by
  simp [mom, pint, expPhi]

lemma mom_one_le (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) :
    mom μ V (fun _ => 1) t ≤ Real.exp ‖t‖ := by
  rw [← mom_one] at *
  have hle : ∀ᵐ w ∂μ, expPhi (V w, t) ≤ Real.exp ‖t‖ := hb.mono fun w hw => by
    have h1 := real_inner_le_norm t (V w)
    have h2 : ‖t‖ * ‖V w‖ ≤ ‖t‖ := mul_le_of_le_one_right (norm_nonneg _) hw
    exact Real.exp_le_exp.mpr (h1.trans h2)
  have := integral_mono_ae (integrable_pint contDiff_expPhi.continuous hV hb t)
    (integrable_const _) hle
  simpa [pint] using this

lemma abs_nm_ell_le (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (c x : E2) :
    |nm μ V (ell c) x| ≤ ‖c‖ := by
  have hZ := mom_one_pos hV hb x
  have hint := integrable_pint contDiff_expPhi.continuous hV hb x
  have hm : mom μ V (ell c) x = ∫ w, ell c (V w) * expPhi (V w, x) ∂μ := by
    simp [mom, pint]
  have hZ' : mom μ V (fun _ => 1) x = ∫ w, expPhi (V w, x) ∂μ := by
    simp [mom, pint]
  have h1 : |mom μ V (ell c) x| ≤ ‖c‖ * mom μ V (fun _ => 1) x := by
    rw [hm, hZ', ← integral_const_mul]
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (hb.mono fun w hw => ?_)
    · have e : 0 < expPhi (V w, x) := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos e]
      have h2 := abs_real_inner_le_norm (V w) c
      have h3 : ‖V w‖ * ‖c‖ ≤ ‖c‖ := mul_le_of_le_one_left (norm_nonneg _) hw
      exact mul_le_mul_of_nonneg_right ((h2.trans h3)) e.le
  unfold nm
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  exact h1

lemma pot_lower (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) :
    ‖t‖ ^ 2 / (2 * κ) - ‖t‖ ≤ pot κ μ V t := by
  have h := Real.log_le_log (mom_one_pos hV hb t) (mom_one_le hV hb t)
  rw [Real.log_exp] at h
  unfold pot
  linarith

lemma norm_le_of_fderiv_pot (κ : ℝ) (hκ : 0 < κ) (hV : Measurable V)
    (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {x : E2} (hx : fderiv ℝ (pot κ μ V) x = 0) : ‖x‖ ≤ κ := by
  have h := fderiv_pot_apply κ hV hb x x
  rw [hx] at h
  have h2 := abs_nm_ell_le hV hb x x
  have h3 : inner ℝ x x / κ = nm μ V (ell x) x := by
    rw [real_inner_self_eq_norm_sq]; simp at h; linarith
  rw [real_inner_self_eq_norm_sq] at h3
  have h4 : ‖x‖ ^ 2 / κ ≤ ‖x‖ := by rw [h3]; exact (le_abs_self _).trans h2
  rw [div_le_iff₀ hκ] at h4
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg x]

end tiltbounds

lemma continuous_orderPotential : Continuous orderPotential :=
  continuous_iff_continuousAt.2 fun t => (hasFDerivAt_orderPotential t).continuousAt

/-- **RUF023, global three-region positivity persists.**  For `R > 2κ` the minimum `γ` of `Ψ∞` over
the annulus `1/352 ≤ ‖t‖ ≤ R` exists and is positive, and every feature `U` (`‖U‖ ≤ 1`, mean `0`,
covariance `I/2`) whose potential is within `γ/2` of `Ψ∞` on `B̄_R` has `Ψ ≥ 0` with zero only at
`0`, all critical points in `B̄_κ` and all global minima in `B̄_{2κ}`. -/
theorem global_three_region_positivity_persists {R : ℝ} (hR : 2 * kappa0 < R) :
    ∃ γ : ℝ, IsLeast (orderPotential '' {t : E2 | (1 / 352 : ℝ) ≤ ‖t‖ ∧ ‖t‖ ≤ R}) γ ∧ 0 < γ ∧
      ∀ U : Torus 1 → E2, Measurable U → (∀ y, ‖U y‖ ≤ 1) →
        ∫ y, U y ∂DGPS.haar 1 = 0 →
        (∀ i j : Fin 2, ∫ y, U y i * U y j ∂DGPS.haar 1 = if i = j then 1 / 2 else 0) →
        (∀ t : E2, ‖t‖ ≤ R →
          |Semicontinuity.featurePotential kappa0 U t - orderPotential t| < γ / 2) →
        (∀ t : E2, 0 ≤ Semicontinuity.featurePotential kappa0 U t) ∧
        (∀ t : E2, Semicontinuity.featurePotential kappa0 U t = 0 ↔ t = 0) ∧
        (∀ t : E2, fderiv ℝ (Semicontinuity.featurePotential kappa0 U) t = 0 → ‖t‖ ≤ kappa0) ∧
        (∀ t : E2, IsMinOn (Semicontinuity.featurePotential kappa0 U) Set.univ t →
          ‖t‖ ≤ 2 * kappa0) := by
  have hκ := kappa0_pos
  have hk1 : kappa0 = 11 / 6 := rfl
  set A : Set E2 := {t : E2 | (1 / 352 : ℝ) ≤ ‖t‖ ∧ ‖t‖ ≤ R} with hA
  have hAc : IsCompact A := by
    have : A = closedBall (0 : E2) R ∩ {t : E2 | (1 / 352 : ℝ) ≤ ‖t‖} := by
      ext t; simp [hA, and_comm]
    rw [this]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hAne : A.Nonempty := by
    have hR0 : 0 < R := by linarith
    refine ⟨R • vertex 0, ?_, ?_⟩
    · simp [norm_smul, norm_vertex, abs_of_pos hR0]; linarith
    · simp [norm_smul, norm_vertex, abs_of_pos hR0]
  obtain ⟨t0, ht0A, ht0min⟩ := hAc.exists_isMinOn hAne continuous_orderPotential.continuousOn
  have ht0ne : t0 ≠ 0 := by
    rintro rfl
    have := ht0A.1
    simp at this
    linarith
  have hγpos : 0 < orderPotential t0 := by
    rcases (order_parameter_chart_and_exact_potential_identity.2.2.2.2.2.2).1 t0 |>.lt_or_eq with h | h
    · exact h
    · exact absurd ((order_parameter_chart_and_exact_potential_identity.2.2.2.2.2.2).2 t0 |>.1 h.symm)
        ht0ne
  refine ⟨orderPotential t0, ⟨⟨t0, ht0A, rfl⟩, ?_⟩, hγpos, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ht0min hs
  intro U hU hb hmean hcov hclose
  set γ := orderPotential t0 with hγ
  have hbb : ∀ᵐ w ∂DGPS.haar 1, ‖U w‖ ≤ 1 := Filter.Eventually.of_forall hb
  have hP : Semicontinuity.featurePotential kappa0 U = pot kappa0 (DGPS.haar 1) U :=
    featurePotential_eq kappa0 U
  have hpos : ∀ t : E2, t ≠ 0 → 0 < Semicontinuity.featurePotential kappa0 U t := by
    intro t ht
    have ht' : 0 < ‖t‖ := norm_pos_iff.2 ht
    by_cases h1 : ‖t‖ ≤ (1 / 22) / 16
    · have := (uniform_convex_neighborhood_of_zero hU hb hmean hcov).2.2.2.2.2.2 t h1
      have : 0 < (1 / 22 : ℝ) / 4 * ‖t‖ ^ 2 := by positivity
      linarith
    by_cases h2 : ‖t‖ ≤ R
    · have hmem : t ∈ A := ⟨by norm_num at h1 ⊢; linarith, h2⟩
      have hm : orderPotential t0 ≤ orderPotential t := ht0min hmem
      have := (abs_lt.1 (hclose t h2)).1
      linarith
    · push Not at h2
      rw [hP]
      have := pot_lower kappa0 hU hbb t
      have h3 : 0 < ‖t‖ ^ 2 / (2 * kappa0) - ‖t‖ := by
        have : 0 < ‖t‖ * (‖t‖ - 2 * kappa0) := mul_pos ht' (by linarith)
        have e : ‖t‖ ^ 2 / (2 * kappa0) - ‖t‖ = ‖t‖ * (‖t‖ - 2 * kappa0) / (2 * kappa0) := by
          field_simp
        rw [e]; positivity
      linarith
  have h0 : Semicontinuity.featurePotential kappa0 U 0 = 0 :=
    (uniform_convex_neighborhood_of_zero hU hb hmean hcov).1
  have hzero : ∀ t : E2, Semicontinuity.featurePotential kappa0 U t = 0 ↔ t = 0 := fun t =>
    ⟨fun h => by by_contra hne; exact (hpos t hne).ne' h, fun h => h ▸ h0⟩
  refine ⟨fun t => ?_, hzero, fun t ht => ?_, fun t ht => ?_⟩
  · by_cases h : t = 0
    · rw [h, h0]
    · exact (hpos t h).le
  · rw [hP] at ht
    exact norm_le_of_fderiv_pot kappa0 hκ hU hbb ht
  · have h1 : Semicontinuity.featurePotential kappa0 U t ≤
        Semicontinuity.featurePotential kappa0 U 0 := ht (mem_univ 0)
    have : t = 0 := (hzero t).1 (le_antisymm (h1.trans h0.le) (by
      by_cases h : t = 0
      · rw [h, h0]
      · exact (hpos t h).le))
    rw [this]; simp; positivity
