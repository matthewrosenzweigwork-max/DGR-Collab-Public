import DGPS.FiniteN.ScalarFoldFIN060A

/-!
# FIN060 (part B): the fold auxiliary Poincare inequality on the line

Transfer of the local Dirichlet rate from the real line to `E1 = ℝ^1` and assembly of the
centered IMS globalization (FIN024) for the fold auxiliary law.
-/

open MeasureTheory Set Metric
open scoped ContDiff

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN056 DGPS.Circle.BesselConcavity

/-- The coordinate map `E1 → ℝ` is volume preserving. -/
theorem measurePreserving_coord_FIN060 :
    MeasurePreserving (fun x : E1 => x 0) volume volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

theorem integral_coord_FIN060 (h : ℝ → ℝ) : ∫ x : E1, h (x 0) = ∫ t, h t := by
  let e : E1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have he : MeasurePreserving e volume volume := measurePreserving_coord_FIN060
  have := he.integral_comp' (f := e) h
  simpa [e] using this

/-- The embedding `ℝ → E1`. -/
noncomputable def embFIN060 (t : ℝ) : E1 := t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

theorem embFIN060_apply (t : ℝ) : embFIN060 t 0 = t := by
  simp [embFIN060]

theorem emb_coord_FIN060 (x : E1) : embFIN060 (x 0) = x := by
  ext i
  fin_cases i
  simp [embFIN060]

theorem contDiff_emb_FIN060 : ContDiff ℝ ∞ embFIN060 :=
  contDiff_id.smul contDiff_const

theorem hasDerivAt_emb_FIN060 (t : ℝ) :
    HasDerivAt embFIN060 (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) t := by
  have h := (hasDerivAt_id t).smul_const (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  rw [one_smul] at h
  exact h

theorem dist_emb_FIN060 (s t : ℝ) : dist (embFIN060 s) (embFIN060 t) = |s - t| := by
  rw [dist_E1_FIN060, embFIN060_apply, embFIN060_apply]

theorem norm_clm_E1_FIN060 (L : E1 →L[ℝ] ℝ) : ‖L‖ = |L (embFIN060 1)| := by
  have h : L = (L (embFIN060 1)) • prFIN060 := by
    ext v
    have hv : v = (v 0) • embFIN060 1 := by
      rw [← emb_coord_FIN060 v]
      ext i
      fin_cases i
      simp [embFIN060]
    conv_lhs => rw [hv]
    simp [prFIN060_apply, mul_comm]
  have h2 : ‖L‖ = ‖(L (embFIN060 1)) • prFIN060‖ := congrArg norm h
  rw [h2, norm_smul_pr_FIN060]

theorem norm_fderiv_comp_emb_FIN060 {G : E1 → ℝ} (hG : ContDiff ℝ ∞ G) (x : E1) :
    ‖fderiv ℝ G x‖ = |deriv (fun t => G (embFIN060 t)) (x 0)| := by
  have hGd : DifferentiableAt ℝ G (embFIN060 (x 0)) :=
    (hG.differentiable (by simp)) _
  have h := hGd.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_emb_FIN060 (x 0))
  have h' : deriv (fun t => G (embFIN060 t)) (x 0) =
      fderiv ℝ G (embFIN060 (x 0)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := h.deriv
  rw [h', emb_coord_FIN060, norm_clm_E1_FIN060]
  have : embFIN060 1 = EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    ext i; fin_cases i; simp [embFIN060]
  rw [this]

theorem ball_emb_FIN060 (m r : ℝ) (t : ℝ) : embFIN060 t ∈ ball (embFIN060 m) r ↔ t ∈ Ioo (m - r) (m + r) := by
  rw [mem_ball, dist_emb_FIN060, abs_sub_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- The line Dirichlet rate on a patch transfers to `E1`. -/
theorem patch_rate_line_FIN060 (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (m r c : ℝ)
    (hrate : ∀ N : ℝ, 1 ≤ N → ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → tsupport f ⊆ Ioo (m - r) (m + r) →
      c * N ^ (2 / 3 : ℝ) * ∫ t, f t ^ 2 * Real.exp (-(N * ψ t)) ≤
        ∫ t, deriv f t ^ 2 * Real.exp (-(N * ψ t)))
    (N : ℝ) (hN : 1 ≤ N) (G : E1 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hGU : tsupport G ⊆ ball (embFIN060 m) r) :
    c * N ^ (2 / 3 : ℝ) * ∫ x, G x ^ 2 ∂(DGPS.FiniteN.imsEta N (psiE ψ)) ≤
      ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(DGPS.FiniteN.imsEta N (psiE ψ)) := by
  set f : ℝ → ℝ := fun t => G (embFIN060 t) with hfdef
  have hf : ContDiff ℝ ∞ f := hG.comp contDiff_emb_FIN060
  have hfs : tsupport f ⊆ Ioo (m - r) (m + r) := by
    have h1 : tsupport f ⊆ embFIN060 ⁻¹' tsupport G := by
      refine closure_minimal ?_ ((isClosed_tsupport G).preimage contDiff_emb_FIN060.continuous)
      intro t ht
      exact subset_tsupport G ht
    intro t ht
    exact (ball_emb_FIN060 m r t).1 (hGU (h1 ht))
  have h := hrate N hN f hf hfs
  have hE : ContDiff ℝ ∞ (psiE ψ) := contDiff_psiE hψ
  rw [DGPS.FiniteN.TiltedXY.Fin049.imsEta_integral_FIN049 N (psiE ψ) hE,
    DGPS.FiniteN.TiltedXY.Fin049.imsEta_integral_FIN049 N (psiE ψ) hE
      (fun x => ‖fderiv ℝ G x‖ ^ 2)]
  have e1 : ∫ x : E1, G x ^ 2 * Real.exp (-(N * psiE ψ x)) =
      ∫ t, f t ^ 2 * Real.exp (-(N * ψ t)) := by
    rw [← integral_coord_FIN060 (fun t => f t ^ 2 * Real.exp (-(N * ψ t)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hfdef, emb_coord_FIN060, psiE]
  have e2 : ∫ x : E1, ‖fderiv ℝ G x‖ ^ 2 * Real.exp (-(N * psiE ψ x)) =
      ∫ t, deriv f t ^ 2 * Real.exp (-(N * ψ t)) := by
    rw [← integral_coord_FIN060 (fun t => deriv f t ^ 2 * Real.exp (-(N * ψ t)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [psiE]
    rw [norm_fderiv_comp_emb_FIN060 hG x, sq_abs]
  rw [e1, e2]
  have hZ : 0 ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * psiE ψ x))))⁻¹.toReal := ENNReal.toReal_nonneg
  calc c * N ^ (2 / 3 : ℝ) * ((∫⁻ x, ENNReal.ofReal (Real.exp (-(N * psiE ψ x))))⁻¹.toReal *
        ∫ t, f t ^ 2 * Real.exp (-(N * ψ t)))
      = (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * psiE ψ x))))⁻¹.toReal *
        (c * N ^ (2 / 3 : ℝ) * ∫ t, f t ^ 2 * Real.exp (-(N * ψ t))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hZ

/-- The gradient gap on the line. -/
theorem gap_line_FIN060 (g : ℝ → ℝ) (hg : Continuous g) (A : Set ℝ) (hA : IsOpen A)
    (ρ cf : ℝ) (hρ : 0 < ρ) (hcf : 0 < cf) (hfar : ∀ t, ρ ≤ |t| → cf * |t| ≤ |g t|)
    (hcrit : ∀ t, g t = 0 → t ∈ A) :
    ∃ c₀ > 0, ∀ t, t ∉ A → c₀ < |g t| := by
  set S : Set ℝ := closedBall 0 ρ \ A with hS
  have hSc : IsCompact S := (isCompact_closedBall _ _).diff hA
  have hfar' : ∀ t, ρ ≤ |t| → cf * ρ ≤ |g t| := fun t ht =>
    (mul_le_mul_of_nonneg_left ht hcf.le).trans (hfar t ht)
  have hcfρ : 0 < cf * ρ := mul_pos hcf hρ
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨cf * ρ / 2, by positivity, fun t ht => ?_⟩
    have hx : ρ ≤ |t| := by
      by_contra hle
      push Not at hle
      have : t ∈ S := ⟨by simpa [abs_le] using hle.le, ht⟩
      rw [hS0] at this
      exact this
    have := hfar' t hx
    linarith
  · obtain ⟨y, hy, hmin⟩ := hSc.exists_isMinOn hSne hg.abs.continuousOn
    have hypos : 0 < |g y| := by
      rcases (abs_nonneg (g y)).eq_or_lt with h | h
      · exact absurd (hcrit y (abs_eq_zero.1 h.symm)) hy.2
      · exact h
    refine ⟨min (cf * ρ / 2) (|g y| / 2), by positivity, fun t ht => ?_⟩
    by_cases hx : ρ ≤ |t|
    · have := hfar' t hx
      have h2 := min_le_left (cf * ρ / 2) (|g y| / 2)
      linarith
    · push Not at hx
      have hxS : t ∈ S := ⟨by simpa [abs_le] using hx.le, ht⟩
      have h1 : |g y| ≤ |g t| := hmin hxS
      have h2 := min_le_right (cf * ρ / 2) (|g y| / 2)
      linarith

/-- Laplace masses for a nondegenerate line minimum. -/
theorem laplace_masses_line_FIN060 (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (t0 : ℝ)
    (hmin : ∀ t, t ≠ t0 → ψ t0 < ψ t) (hpos : 0 < deriv (deriv ψ) t0)
    (hgrow : ∃ b > 0, ∃ C : ℝ, ∀ t, b * (t - t0) ^ 2 - C ≤ ψ t - ψ t0) :
    ∃ Nz : ℝ, 1 ≤ Nz ∧ (∀ N, Nz ≤ N → 0 < ∫ x, Real.exp (-(N * psiE ψ x))) ∧
      ∀ r > 0, ∃ c > 0, ∃ C > 0, ∃ N1 : ℝ, Nz ≤ N1 ∧ ∀ N, N1 ≤ N →
        (DGPS.FiniteN.imsEta N (psiE ψ) {x | r ≤ dist x (embFIN060 t0)}).toReal ≤
          C * Real.exp (-(c * N)) := by
  have hψ2 : ContDiff ℝ 2 (psiE ψ) := (contDiff_psiE hψ).of_le (by simp)
  obtain ⟨b, hb, C, hgrow'⟩ := hgrow
  have hgrowE : ∃ b > 0, ∃ C : ℝ, ∀ w : E1, b * dist w (embFIN060 t0) ^ 2 - C ≤
      psiE ψ w - psiE ψ (embFIN060 t0) := by
    refine ⟨b, hb, C, fun w => ?_⟩
    rw [dist_E1_FIN060, embFIN060_apply, sq_abs]
    simpa [psiE, embFIN060_apply] using hgrow' (w 0)
  have hminE : ∀ w, psiE ψ (embFIN060 t0) ≤ psiE ψ w := by
    intro w
    by_cases h : w 0 = t0
    · simp [psiE, embFIN060_apply, h]
    · exact (hmin (w 0) h).le.trans' (by simp [psiE, embFIN060_apply])
  have huniq : ∀ w, psiE ψ w = psiE ψ (embFIN060 t0) → w = embFIN060 t0 := by
    intro w hw
    by_contra hne
    have : w 0 ≠ t0 := by
      intro h; apply hne; rw [← emb_coord_FIN060 w, h]
    have := hmin (w 0) this
    simp only [psiE, embFIN060_apply] at hw
    linarith
  have hH : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psiE ψ)) (embFIN060 t0) v v := by
    refine ⟨deriv (deriv ψ) t0, hpos, fun v => ?_⟩
    rw [fderiv_fderiv_psiE hψ, embFIN060_apply, norm_E1_FIN060, sq_abs]
    nlinarith
  obtain ⟨⟨L0, hL0, A0, hA0, Nz, hNz, hlb⟩, htail⟩ :=
    DGPS.FiniteN.quadratic_minimum_laplace_bounds_and_gap_tails (E := E1) hψ2 hminE huniq hH hgrowE
  have hZ : ∀ N, Nz ≤ N → 0 < ∫ x, Real.exp (-(N * psiE ψ x)) := by
    intro N hN
    have hN0 : 0 < N := by linarith
    have := (hlb N hN).1
    refine lt_of_lt_of_le ?_ this
    positivity
  refine ⟨Nz, hNz, hZ, fun r hr => ?_⟩
  obtain ⟨c, hc, C', hC', N0, hN0, ht⟩ := htail r hr
  refine ⟨c, hc, C', hC', max N0 Nz, le_max_right _ _, fun N hN => ?_⟩
  have hNz' : Nz ≤ N := (le_max_right _ _).trans hN
  have hN0' : N0 ≤ N := (le_max_left _ _).trans hN
  have hmeas : MeasurableSet {x : E1 | r ≤ dist x (embFIN060 t0)} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  rw [DGPS.FiniteN.TiltedXY.Fin049.imsEta_real_FIN049 N (psiE ψ) (hZ N hNz') _ hmeas]
  rw [div_le_iff₀ (hZ N hNz')]
  exact ht N hN0'

open DGPS.FiniteN.TiltedXY.Fin049 in
/-- Abstract assembly for a smooth line potential with one nondegenerate global minimum and one
further stationary patch on which the Dirichlet rate is `c N^(2/3)`. -/
theorem assembly_line_FIN060 (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (M : ℝ)
    (hM : ∀ t, |deriv (deriv ψ) t| ≤ M)
    (tPlus : ℝ) (hmin : ∀ t, t ≠ tPlus → ψ tPlus < ψ t) (hpos : 0 < deriv (deriv ψ) tPlus)
    (hgrow : ∃ b > 0, ∃ C : ℝ, ∀ t, b * (t - tPlus) ^ 2 - C ≤ ψ t - ψ tPlus)
    (α β c0 : ℝ) (hαβ : α < β) (hc0 : 0 < c0)
    (hcrit : ∀ t, deriv ψ t = 0 → t = tPlus ∨ t ∈ Ioo α β)
    (hrate : ∀ N : ℝ, 1 ≤ N → ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → tsupport f ⊆ Ioo α β →
      c0 * N ^ (2 / 3 : ℝ) * ∫ t, f t ^ 2 * Real.exp (-(N * ψ t)) ≤
        ∫ t, deriv f t ^ 2 * Real.exp (-(N * ψ t)))
    (ρ cf : ℝ) (hρ : 0 < ρ) (hcf : 0 < cf) (hfar : ∀ t, ρ ≤ |t| → cf * |t| ≤ |deriv ψ t|) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ F : E1 → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        ∫ x, F x ∂(DGPS.FiniteN.imsEta N (psiE ψ)) = 0 →
        c * N ^ (2 / 3 : ℝ) * ∫ x, F x ^ 2 ∂(DGPS.FiniteN.imsEta N (psiE ψ)) ≤
          ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(DGPS.FiniteN.imsEta N (psiE ψ)) := by
  have hψE : ContDiff ℝ ∞ (psiE ψ) := contDiff_psiE hψ
  have hψ1 : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
  have hgc : Continuous (deriv ψ) := hg.continuous
  have hg2c : Continuous (deriv (deriv ψ)) := ((contDiff_infty_iff_deriv.1 hg).2).continuous
  have hnorm : ∀ x : E1, ‖fderiv ℝ (psiE ψ) x‖ = |deriv ψ (x 0)| := norm_fderiv_psiE hψ1
  have hnc : Continuous fun x : E1 => ‖fderiv ℝ (psiE ψ) x‖ := by
    have : (fun x : E1 => ‖fderiv ℝ (psiE ψ) x‖) = fun x => |deriv ψ (x 0)| := funext hnorm
    rw [this]
    exact (hgc.comp prFIN060.continuous).abs
  -- the Hessian near the minimum
  obtain ⟨r₀, hr₀, hhess1⟩ : ∃ r₀ > 0, ∀ t, |t - tPlus| < r₀ → deriv (deriv ψ) tPlus / 2 <
      deriv (deriv ψ) t := by
    have hev : ∀ᶠ t in nhds tPlus, deriv (deriv ψ) tPlus / 2 < deriv (deriv ψ) t :=
      continuousAt_const.eventually_lt hg2c.continuousAt (by linarith)
    obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 hev
    exact ⟨r, hr, fun t ht => hb t (by rwa [mem_ball, Real.dist_eq])⟩
  set c₁ : ℝ := deriv (deriv ψ) tPlus / 2 with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  -- patches
  set m : ℝ := (α + β) / 2 with hm
  set r₁ : ℝ := (β - α) / 2 with hr₁def
  have hr₁ : 0 < r₁ := by rw [hr₁def]; linarith
  have e1 : m - r₁ = α := by rw [hm, hr₁def]; ring
  have e2 : m + r₁ = β := by rw [hm, hr₁def]; ring
  let U : Fin 2 → Set E1 := ![ball (embFIN060 tPlus) r₀, ball (embFIN060 m) r₁]
  have hU0 : U 0 = ball (embFIN060 tPlus) r₀ := rfl
  have hU1 : U 1 = ball (embFIN060 m) r₁ := rfl
  have hUj : ∀ j, ∃ p r, U j = ball p r := by
    intro j
    fin_cases j
    · exact ⟨_, _, hU0⟩
    · exact ⟨_, _, hU1⟩
  have hUo : ∀ j, IsOpen (U j) := fun j => by
    obtain ⟨p, r, h⟩ := hUj j
    rw [h]; exact isOpen_ball
  have hUc : ∀ j, IsCompact (closure (U j)) := fun j => by
    obtain ⟨p, r, h⟩ := hUj j
    rw [h]; exact isBounded_ball.isCompact_closure
  -- gradient gap
  obtain ⟨c₀, hc₀, hgap1⟩ := gap_line_FIN060 (deriv ψ) hgc
    (Ioo (tPlus - r₀) (tPlus + r₀) ∪ Ioo α β) (isOpen_Ioo.union isOpen_Ioo) ρ cf hρ hcf hfar
    (fun t ht => by
      rcases hcrit t ht with h | h
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr h)
  have hgap : ∀ x : E1, x ∉ U 0 ∪ U 1 → c₀ < ‖fderiv ℝ (psiE ψ) x‖ := by
    intro x hx
    rw [hnorm]
    apply hgap1
    intro hxA
    apply hx
    rw [hU0, hU1]
    rcases hxA with h | h
    · left
      have := (ball_emb_FIN060 tPlus r₀ (x 0)).2 h
      rwa [emb_coord_FIN060] at this
    · right
      have := (ball_emb_FIN060 m r₁ (x 0)).2 (by rw [e1, e2]; exact h)
      rwa [emb_coord_FIN060] at this
  have hhess : ∀ x ∈ ball (embFIN060 tPlus) r₀, ∀ v : E1,
      c₁ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psiE ψ)) x v v := by
    intro x hx v
    rw [mem_ball, dist_E1_FIN060, embFIN060_apply] at hx
    rw [fderiv_fderiv_psiE hψ, norm_E1_FIN060, sq_abs]
    have := hhess1 (x 0) hx
    nlinarith [sq_nonneg (v 0)]
  have hH : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psiE ψ)) (embFIN060 tPlus) v v :=
    ⟨c₁, hc₁, hhess _ (mem_ball_self hr₀)⟩
  obtain ⟨Nz, hNz1, hZ, hmasses⟩ := laplace_masses_line_FIN060 ψ hψ tPlus hmin hpos hgrow
  have hgcE := hnc
  let W : Set E1 := {x | c₀ < ‖fderiv ℝ (psiE ψ) x‖}
  have hWo : IsOpen W := isOpen_lt continuous_const hgcE
  have hcov : Wᶜ ⊆ ⋃ j, U j := by
    intro x hx
    by_contra hxU
    have hx' : x ∉ U 0 ∪ U 1 := by
      intro h
      apply hxU
      rcases h with h | h
      · exact mem_iUnion.2 ⟨0, h⟩
      · exact mem_iUnion.2 ⟨1, h⟩
    exact hx (hgap x hx')
  have hV : closure (ball (embFIN060 tPlus) (r₀ / 2)) ⊆ U 0 := by
    rw [hU0]
    exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  obtain ⟨χ, hχ, hχ0, hsum, hχU, hχW, hχV, C, hC⟩ :=
    ims_cutoffs_nonneg_FIN049 U hUo hUc W hWo hcov 0 (ball (embFIN060 tPlus) (r₀ / 2)) hV
  -- exterior
  let K : Set E1 := closedBall 0 ρ ∩ {x | c₀ ≤ ‖fderiv ℝ (psiE ψ) x‖}
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ρ).inter_right (isClosed_le continuous_const hgcE)
  have hWX : W ⊆ K ∪ {x | ρ ≤ ‖x‖} := by
    intro x hx
    by_cases h8 : ‖x‖ ≤ ρ
    · exact Or.inl ⟨by simpa using h8, le_of_lt (show c₀ < ‖fderiv ℝ (psiE ψ) x‖ from hx)⟩
    · exact Or.inr (by simpa using (not_le.1 h8).le)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨c', hc', N₂, hext0⟩ := DGPS.FiniteN.noncritical_and_far_exterior_dirichlet_rate (psiE ψ)
    hψE M (norm_fderiv_fderiv_psiE_le hψ hM) K hKc (min c₀ cf)
    (lt_min hc₀ hcf) (fun x hx => (min_le_left _ _).trans hx.2) ρ hρ
    (fun x hx => by
      rw [hnorm, norm_E1_FIN060]
      rw [norm_E1_FIN060] at hx
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)).trans (hfar _ hx))
  -- Laplace tails
  obtain ⟨cA, hcA, AA, hAA, NA, hNzA, htA⟩ := hmasses (r₀ / 2) (by linarith)
  obtain ⟨cB, hcB, AB, hAB, NB, hNzB, htB⟩ := hmasses r₀ hr₀
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℝ, ∀ N, N₁ ≤ N →
      Nz ≤ N ∧ NA ≤ N ∧ NB ≤ N ∧ 2 * AB / cB ≤ N ∧ N₂ ≤ N ∧ 1 ≤ N :=
    ⟨max Nz (max NA (max NB (max (2 * AB / cB) (max N₂ 1)))), fun N hN => by
      simpa [max_le_iff] using hN⟩
  have hfin : ∀ N : ℝ, IsFiniteMeasure (DGPS.FiniteN.imsEta N (psiE ψ)) := fun N =>
    DGPS.FiniteN.Tools.ConditionalPoincareMain.imsEta_finite N (psiE ψ)
  have hcc : 0 < min c0 c' := lt_min hc0 hc'
  refine DGPS.FiniteN.auxiliary_poincare_globalization_with_the_mean (psiE ψ) hψE U
    (K ∪ {x | ρ ≤ ‖x‖}) 0 χ C hχ hsum hC hχU (hχW.trans hWX) (embFIN060 tPlus) r₀ c₁ hc₁ hU0 hhess
    (hχ0 _) N₁ AA cA (1 / 2) hcA (by norm_num) ?_ ?_ (2 / 3) (min c0 c')
    (by norm_num) (by norm_num) hcc ?_ ?_
  · -- mass of the minimum ball
    intro N hN
    obtain ⟨hNz, hNA, hNB, hNm, hN2, hN1⟩ := hN₁ N hN
    have hZN := hZ N hNz
    have hint : Integrable (fun x : E1 => Real.exp (-(N * psiE ψ x))) := by
      by_contra h
      rw [integral_undef h] at hZN
      exact lt_irrefl _ hZN
    have hmeas : MeasurableSet {x : E1 | r₀ ≤ dist x (embFIN060 tPlus)} :=
      (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
    have hcompl : {x : E1 | r₀ ≤ dist x (embFIN060 tPlus)} = (ball (embFIN060 tPlus) r₀)ᶜ := by
      ext x; simp [mem_ball, not_lt]
    have hsum1 : (DGPS.FiniteN.imsEta N (psiE ψ) (ball (embFIN060 tPlus) r₀)).toReal +
        (DGPS.FiniteN.imsEta N (psiE ψ) {x | r₀ ≤ dist x (embFIN060 tPlus)}).toReal = 1 := by
      rw [imsEta_real_FIN049 N (psiE ψ) hZN _ hmeas,
        imsEta_real_FIN049 N (psiE ψ) hZN _ measurableSet_ball,
        ← add_div, div_eq_one_iff_eq hZN.ne', hcompl]
      exact integral_add_compl measurableSet_ball hint
    have htail := htB N hNB
    have hAe : AB * Real.exp (-(cB * N)) ≤ 1 / 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have h1 := Real.add_one_le_exp (cB * N)
      have h2 : 2 * AB ≤ N * cB := (div_le_iff₀ hcB).1 hNm
      nlinarith
    linarith
  · -- the minimum patch cutoff is exponentially close to one
    intro N hN
    obtain ⟨hNz, hNA, hNB, hNm, hN2, hN1⟩ := hN₁ N hN
    have := hfin N
    refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)).trans (htA N hNA)
    intro x (hx : χ (some 0) x ≠ 1)
    show r₀ / 2 ≤ dist x (embFIN060 tPlus)
    by_contra h
    exact hx (hχV x (mem_ball.2 (not_le.1 h)))
  · -- the other patch
    intro j hj N hN G hG hGc hGU
    obtain ⟨hNz, hNA, hNB, hNm, hN2, hN1⟩ := hN₁ N hN
    match j, hj with
    | 0, h => exact absurd rfl h
    | 1, _ =>
      have h := patch_rate_line_FIN060 ψ hψ m r₁ c0
        (fun N hN f hf hs => hrate N hN f hf (by rwa [e1, e2] at hs)) N hN1 G hG hGU
      refine le_trans ?_ h
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (Real.rpow_nonneg (by linarith) _))
        (integral_nonneg fun x => sq_nonneg _)
  · -- the exterior
    intro N hN G hG hGc hGX
    obtain ⟨hNz, hNA, hNB, hNm, hN2, hN1⟩ := hN₁ N hN
    have h := hext0 N hN2 G hG hGc hGX
    have hI : 0 ≤ ∫ x, G x ^ 2 ∂(DGPS.FiniteN.imsEta N (psiE ψ)) :=
      integral_nonneg fun x => sq_nonneg _
    refine le_trans ?_ h
    have h3 : min c0 c' ≤ c' := min_le_right _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (sq_nonneg N)) hI

/-- The fold auxiliary Poincare inequality on the line (smooth compactly supported mean-zero
test functions, `N ≥ N₀`). -/
theorem fold_aux_poincare_FIN060 (κ : ℝ) (hκ : 2 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ F : E1 → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        ∫ x, F x ∂(DGPS.FiniteN.imsEta N (psiE (scalarPsi κ (scalarFoldField κ)))) = 0 →
        c * N ^ (2 / 3 : ℝ) * ∫ x, F x ^ 2 ∂(DGPS.FiniteN.imsEta N
            (psiE (scalarPsi κ (scalarFoldField κ)))) ≤
          ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(DGPS.FiniteN.imsEta N
            (psiE (scalarPsi κ (scalarFoldField κ)))) := by
  have hκ0 : 0 < κ := by linarith
  set hc : ℝ := scalarFoldField κ with hhc
  obtain ⟨-, -, tPlus, htp, -, hcrit, -, -, -, -, -, hpos, hmin, -, -⟩ :=
    fold_auxiliary_cubic_geometry κ hκ
  obtain ⟨α, β, c0, hα, hβ, hc0, hrate⟩ := fold_local_dirichlet_power_two_thirds κ hκ
  have hψ : ContDiff ℝ ∞ (scalarPsi κ hc) := ScalarFoldFIN057.scalarPsi_contDiff_FIN057 κ hc
  have hd1 : deriv (scalarPsi κ hc) = psiDerivFIN056 κ hc := deriv_scalarPsi_FIN056 hκ0 hc
  have hd2 : deriv (deriv (scalarPsi κ hc)) = fun t => 1 / κ - ratioDeriv t := by
    rw [hd1, deriv_psiDeriv_FIN056]
  refine assembly_line_FIN060 (scalarPsi κ hc) hψ (1 / 2) ?_ tPlus hmin hpos ?_ α β c0
    (hα.trans hβ) hc0 ?_ hrate (2 * |hc| + 2 * κ) (1 / (2 * κ)) (by positivity) (by positivity) ?_
  · intro t
    rw [hd2]
    exact abs_psiSecond_le_FIN060 hκ t
  · exact scalarPsi_growth_FIN060 hκ0 hc tPlus
  · intro t ht
    rcases (hcrit t).1 ht with h | h
    · exact Or.inr (by rw [h]; exact ⟨hα, hβ⟩)
    · exact Or.inl h
  · intro t ht
    rw [hd1]
    have := far_gradient_scalar_FIN060 hκ0 hc t ht
    calc 1 / (2 * κ) * |t| = |t| / (2 * κ) := by ring
      _ ≤ _ := this

end DGPS.FiniteN.ScalarFoldFIN060
