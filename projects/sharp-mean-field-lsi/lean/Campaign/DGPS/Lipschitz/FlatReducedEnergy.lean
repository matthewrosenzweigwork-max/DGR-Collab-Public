import DGPS.Lipschitz.EquilibriumDissipation

/-!
# Flat reduced energy from a positive nonlinear rate (LIP035)

Finite-dimensional descent argument: a nonnegative `C¹` function `Ψ` on a Euclidean ball with
gradient `b`, `b 0 = 0`, `D b 0 = 0` and `c₀ Ψ ≤ ‖b‖²` (`c₀ > 0`) vanishes on a neighbourhood
of `0`.  Combined with the Lyapunov–Schmidt graph (LIP034) and the dissipation lower bound
`D ≥ 2 r G` coming from `r < r_*`, this gives that the reduced energy `Ψ(a) = G(q (1 + h(a)))`
is identically zero near `a = 0`.
-/

open MeasureTheory
open scoped ContDiff RealInnerProductSpace ENNReal NNReal

namespace DGPS.Lipschitz

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The descent estimate along the segment `a ↦ a - b a / L` (LIP035, step 2): on a ball where
`b` is `L`-Lipschitz with `b 0 = 0` and `Ψ` has gradient `b`, if the trial point stays in the ball
then `Ψ (a - L⁻¹ b a) ≤ Ψ a - ‖b a‖² / (2 L)`. -/
theorem lip035_descent {Ψ : E → ℝ} {b : E → E} {s : Set E} (hconv : Convex ℝ s)
    {L : ℝ} (hL : 0 < L)
    (hΨ : ∀ a ∈ s, HasGradientAt Ψ (b a) a)
    (hb : ∀ x ∈ s, ∀ y ∈ s, ‖b x - b y‖ ≤ L * ‖x - y‖)
    {a : E} (ha : a ∈ s) (hend : a - L⁻¹ • b a ∈ s) :
    Ψ (a - L⁻¹ • b a) ≤ Ψ a - ‖b a‖ ^ 2 / (2 * L) := by
  set v := b a with hv
  let x : ℝ → E := fun t => a - (t * L⁻¹) • v
  have hxs : ∀ t ∈ Set.Icc (0 : ℝ) 1, x t ∈ s := by
    intro t ht
    have : x t = (1 - t) • a + t • (a - L⁻¹ • v) := by
      simp only [x]
      module
    rw [this]
    exact hconv ha hend (by linarith [ht.2]) ht.1 (by ring)
  have hxd : ∀ t : ℝ, HasDerivAt x (-(L⁻¹ • v)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t * L⁻¹) • v) (L⁻¹ • v) t := by
      have := ((hasDerivAt_id t).mul_const L⁻¹).smul_const v
      simpa using this
    have h2 : HasDerivAt x (0 - L⁻¹ • v) t := (hasDerivAt_const t a).sub h1
    simpa using h2
  have hdist : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖x t - a‖ = t * L⁻¹ * ‖v‖ := by
    intro t ht
    have : x t - a = -((t * L⁻¹) • v) := by simp [x]
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
  let φ : ℝ → ℝ := fun t => Ψ (x t) + (t - t ^ 2 / 2) * (‖v‖ ^ 2 / L)
  have hφd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ
      (-(L⁻¹ * ⟪b (x t), v⟫) + (1 - t) * (‖v‖ ^ 2 / L)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Ψ (x t)) (-(L⁻¹ * ⟪b (x t), v⟫)) t := by
      have hg : HasFDerivAt Ψ (InnerProductSpace.toDual ℝ E (b (x t))) (x t) :=
        hΨ (x t) (hxs t ht)
      have := hg.comp_hasDerivAt t (hxd t)
      refine HasDerivAt.congr_deriv this ?_
      simp [inner_smul_right]
    have h2 : HasDerivAt (fun t : ℝ => (t - t ^ 2 / 2) * (‖v‖ ^ 2 / L)) ((1 - t) * (‖v‖ ^ 2 / L)) t := by
      have h3 : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - t) t := by
        have := (hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)
        exact this.congr_deriv (by norm_num)
      exact h3.mul_const _
    exact h1.add h2
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t ht => (hφd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      rw [(hφd t ht').deriv]
      have hlip := hb (x t) (hxs t ht') a ha
      rw [hdist t ht'] at hlip
      have hLmul : L * (t * L⁻¹ * ‖v‖) = t * ‖v‖ := by field_simp
      rw [hLmul] at hlip
      have hin : ‖v‖ ^ 2 - t * ‖v‖ ^ 2 ≤ ⟪b (x t), v⟫ := by
        have e : ⟪b (x t), v⟫ = ‖v‖ ^ 2 + ⟪b (x t) - v, v⟫ := by
          rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
        have h2 : |⟪b (x t) - v, v⟫| ≤ ‖b (x t) - v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        have h3 : ‖b (x t) - v‖ * ‖v‖ ≤ t * ‖v‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
        nlinarith [neg_abs_le ⟪b (x t) - v, v⟫]
      have : (1 - t) * (‖v‖ ^ 2 / L) = L⁻¹ * (‖v‖ ^ 2 - t * ‖v‖ ^ 2) := by
        field_simp
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hin (inv_nonneg.2 hL.le)]
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [φ, x] at h01
  have e1 : (1 : ℝ) * L⁻¹ = L⁻¹ := one_mul _
  rw [e1] at h01
  simp only [zero_mul, zero_smul, sub_zero] at h01
  have e2 : (1 - 1 ^ 2 / 2 : ℝ) * (‖v‖ ^ 2 / L) = ‖v‖ ^ 2 / (2 * L) := by
    field_simp; norm_num
  rw [e2] at h01
  have h02 : Ψ (a - L⁻¹ • v) + ‖v‖ ^ 2 / (2 * L) ≤ Ψ a := by simpa using h01
  linarith

end Calculus

section FiniteDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The finite-dimensional core of LIP035: a nonnegative function with gradient `b`,
`b 0 = 0`, `D b 0 = 0`, and `c₀ Ψ ≤ ‖b‖²` for `c₀ > 0` vanishes on a ball around `0`. -/
theorem lip035_flat_of_gradient_lower_bound {Ψ : E → ℝ} {b : E → E} {U : Set E}
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hb : ContDiffOn ℝ ∞ b U) (hb0 : b 0 = 0)
    (hDb : fderiv ℝ b 0 = 0)
    (hΨ : ∀ a ∈ U, HasGradientAt Ψ (b a) a) (hnn : ∀ a ∈ U, 0 ≤ Ψ a)
    {c0 : ℝ} (hc0 : 0 < c0) (hrate : ∀ a ∈ U, c0 * Ψ a ≤ ‖b a‖ ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : E) ε ⊆ U ∧ ∀ a ∈ Metric.ball (0 : E) ε, Ψ a = 0 := by
  set L : ℝ := c0 / 4 with hLdef
  have hL : 0 < L := by positivity
  have hcont : ContinuousOn (fderiv ℝ b) U := hb.continuousOn_fderiv_of_isOpen hU (by simp)
  have hca : ContinuousAt (fderiv ℝ b) 0 := hcont.continuousAt (hU.mem_nhds h0)
  have hev : ∀ᶠ x in nhds (0 : E), x ∈ U ∧ ‖fderiv ℝ b x‖ < L := by
    refine Filter.Eventually.and (hU.eventually_mem h0) ?_
    exact hca.norm.eventually_lt continuousAt_const (by simpa [hDb] using hL)
  obtain ⟨ε1, hε1, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : Metric.ball (0 : E) ε1 ⊆ U := fun x hx => (hball x hx).1
  have hlip : ∀ x ∈ Metric.ball (0 : E) ε1, ∀ y ∈ Metric.ball (0 : E) ε1,
      ‖b x - b y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    exact (convex_ball (0 : E) ε1).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hb.differentiableOn (by simp) z (hsub hz)).differentiableAt
        (hU.mem_nhds (hsub hz)))
      (fun z hz => (hball z hz).2.le) hy hx
  refine ⟨ε1 / 2, by positivity, (Metric.ball_subset_ball (by linarith)).trans hsub, ?_⟩
  intro a ha
  have ha1 : a ∈ Metric.ball (0 : E) ε1 :=
    Metric.ball_subset_ball (by linarith) ha
  have han : ‖a‖ < ε1 / 2 := by simpa using ha
  have hba : ‖b a‖ ≤ L * ‖a‖ := by
    have := hlip a ha1 0 (Metric.mem_ball_self hε1)
    simpa [hb0] using this
  have hend : a - L⁻¹ • b a ∈ Metric.ball (0 : E) ε1 := by
    rw [mem_ball_zero_iff]
    calc ‖a - L⁻¹ • b a‖ ≤ ‖a‖ + ‖L⁻¹ • b a‖ := norm_sub_le _ _
      _ = ‖a‖ + L⁻¹ * ‖b a‖ := by rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL]
      _ ≤ ‖a‖ + L⁻¹ * (L * ‖a‖) := by gcongr
      _ = 2 * ‖a‖ := by field_simp; ring
      _ < ε1 := by linarith
  have hdesc := lip035_descent (Ψ := Ψ) (b := b) (convex_ball (0 : E) ε1) hL
    (fun z hz => hΨ z (hsub hz)) hlip ha1 hend
  have hnn' := hnn _ (hsub hend)
  have h1 : ‖b a‖ ^ 2 / (2 * L) ≤ Ψ a := by linarith
  have h2 := hrate a (hsub ha1)
  have h3 : ‖b a‖ ^ 2 ≤ 2 * L * Ψ a := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * L)).1 h1
    linarith
  have h4 : c0 * Ψ a ≤ c0 / 2 * Ψ a := by
    have e : 2 * L = c0 / 2 := by rw [hLdef]; ring
    rw [e] at h3
    linarith
  have h5 := hnn a (hsub ha1)
  nlinarith

end FiniteDim

section Assemble

variable {d : ℕ} {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- A rate `r < r_*` gives `2 r G ≤ D` in the real form `2 r G(ρ) ≤ M` whenever `D(ρ) ≤ M`. -/
theorem lip035_rate_bound (drift : AbsoluteDrift A) {r : ℝ} (hr : 0 < r)
    (hrate : ENNReal.ofReal r < scalarRate A drift) (ρ : AbsoluteDensity d) {M : ℝ} (hM : 0 ≤ M)
    (hD : scalarDissipation A drift ρ ≤ ENNReal.ofReal M) :
    2 * r * (scalarGap A ρ : ℝ) ≤ M := by
  rcases eq_or_ne (scalarGap A ρ) 0 with h0 | h0
  · rw [h0]; simpa using hM
  · have hpos : 0 < scalarGap A ρ := pos_iff_ne_zero.2 h0
    have hq := scalarRate_le_quotient A drift ρ hpos
    have h1 : ENNReal.ofReal r ≤ scalarDissipation A drift ρ / (2 * (scalarGap A ρ : ℝ≥0∞)) :=
      (hrate.trans_le hq).le
    have h2 : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ 0 := by simpa using hpos.ne'
    have h3 : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
    have h4 := (ENNReal.le_div_iff_mul_le (Or.inl h2) (Or.inl h3)).1 h1
    have h5 : ENNReal.ofReal r * (2 * (scalarGap A ρ : ℝ≥0∞)) = ENNReal.ofReal (2 * r * scalarGap A ρ) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_coe_nnreal]
      simp only [ENNReal.ofReal_ofNat]
      ring
    rw [h5] at h4
    exact (ENNReal.ofReal_le_ofReal_iff hM).1 (h4.trans hD)

/-- **LIP035.** Flat reduced energy from a positive nonlinear rate.  Let `0 < r < r_*`.  On the
Lyapunov–Schmidt graph `h(a) = ∑ aᵢ φᵢ + y(a)` of LIP034 (with `y 0 = 0`, `Dy(0) = 0` and
`1 + h(a) > 0`), the reduced energy `Ψ(a) = G(q (1 + h(a)))` vanishes identically on a ball around
`a = 0` contained in the graph neighbourhood: for every `a` in that ball the potential
`lip034_potential` vanishes and the density `q (1 + h(a))` has zero free-energy gap, i.e. it is a
free-energy minimizer. -/
theorem flat_reduced_energy_from_positive_nonlinear_rate (hA : LipschitzData A) {k : ℕ}
    {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (drift : AbsoluteDrift A) {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift) :
    ∃ U : Set (Par k), IsOpen U ∧ (0 : Par k) ∈ U ∧ ∃ y : Par k → Ysub A μ,
      y 0 = 0 ∧ fderiv ℝ y 0 = 0 ∧ ContDiffOn ℝ ∞ y U ∧
      (∀ a ∈ U, ∀ x, 0 < 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : Par k) ε ⊆ U ∧
        ∀ a ∈ Metric.ball (0 : Par k) ε,
          lip034_potential (A := A) (μ : Measure (Torus d))
            (phiMap φ a + (y a : C(Torus d, ℝ))) = 0 ∧
          ∃ ρ : AbsoluteDensity d,
            (densityMeasure ρ : Measure (Torus d)) = perturb (μ : Measure (Torus d))
              (fun x => 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
            scalarGap A ρ = 0 := by
  obtain ⟨U, hUo, h0U, y, hy0, hyd, hsm, hpos, b, c, hbsm, hcsm, hb0, hbd, heq, hgrad, C_D, hC,
    ρ, hρ⟩ := lyapunov_schmidt_graph_for_equilibrium hA hφ hmin
  set Ψ : Par k → ℝ := fun a => lip034_potential (A := A) (μ : Measure (Torus d))
    (phiMap φ a + (y a : C(Torus d, ℝ))) with hΨdef
  have hgap : ∀ a ∈ U, ((scalarGap A (ρ a) : NNReal) : ℝ) = Ψ a := fun a ha => (hρ a ha).2.1
  have hnn : ∀ a ∈ U, 0 ≤ Ψ a := fun a ha => by rw [← hgap a ha]; exact NNReal.coe_nonneg _
  have hbound : ∀ a ∈ U, 2 * r * Ψ a ≤ C_D * ‖b a‖ ^ 2 := fun a ha => by
    rw [← hgap a ha]
    exact lip035_rate_bound drift hr hrate (ρ a) (by positivity) ((hρ a ha).2.2.2 drift)
  have hCpos : 0 < C_D + 1 := by linarith
  have hrate' : ∀ a ∈ U, (2 * r / (C_D + 1)) * Ψ a ≤ ‖b a‖ ^ 2 := fun a ha => by
    rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
    have := hbound a ha
    nlinarith [sq_nonneg ‖b a‖]
  obtain ⟨ε, hε, hsub, hflat⟩ := lip035_flat_of_gradient_lower_bound (Ψ := Ψ) (b := b) hUo h0U
    hbsm hb0 hbd hgrad hnn (by positivity) hrate'
  refine ⟨U, hUo, h0U, y, hy0, hyd, hsm, hpos, ε, hε, hsub, fun a ha => ⟨hflat a ha, ?_⟩⟩
  have haU := hsub ha
  refine ⟨ρ a, (hρ a haU).1, ?_⟩
  have := hgap a haU
  rw [hflat a ha] at this
  exact_mod_cast this

end Assemble

end DGPS.Lipschitz
