import DGPS.Circle.BesselConcavity
/-!
# Ordered radial well geometry (FIN034)

Fix `κ > 2`, let `g = I₁/I₀` (`besselRatio`), `ψ(r) = r²/(2κ) - log I₀(r)` and
`U = ψ - ψ(r₀)`.  The theorem `DGPS.FiniteN.ordered_radial_well_geometry` states that
`r₀ = κ g(r₀)` has a unique positive solution `r₀` and that there are constants `0 < c ≤ C`
(depending only on `κ`) such that, with `a = r₀/2`,

* `c r ≤ -U'(r) ≤ C r` on `[0, a]`;
* `c |r - r₀| ≤ |U'(r)| ≤ C |r - r₀|` on `[a, ∞)`, with `U'` of the sign of `r - r₀`;
* `c (r - r₀)² ≤ U(r) ≤ C (r - r₀)²` for all `r ≥ 0`.

Proof route.  Put `f = ψ' = r/κ - g(r)`.  By EX003/EX004 the derivative `f' = 1/κ - g'` is strictly
increasing and `|f'| ≤ 1/2` on `[0, ∞)`; hence `f` is convex and `1/2`-Lipschitz there.  Existence
of `r₀` uses `f'(0) = 1/κ - 1/2 < 0` and `g < 1`, uniqueness uses the strictly decreasing `g(t)/t`.
Chord inequalities for the convex `f` (through `(0,0)`, `(a, f a)`, `(r₀, 0)`) give the lower bounds
on `[0, r₀]`, the tangent inequality at `r₀` (where `f'(r₀) = 1/κ - g'(r₀) > 0` because
`g' < g/t`) gives the lower bound on `[r₀, ∞)`, and the quadratic comparison follows by integrating
the derivative bounds (monotonicity of auxiliary functions).
-/

open Set Filter Topology
open DGPS.Circle.BesselMoments

namespace DGPS.FiniteN

/-- `ψ(r) = r²/(2κ) - log I₀(r)`, the radial free energy of the ordered row. -/
noncomputable def radialPsi_orad (κ r : ℝ) : ℝ := r ^ 2 / (2 * κ) - Real.log (besselI 0 r)

/-- `U = ψ - ψ(r₀)`. -/
noncomputable def radialU_orad (κ r0 r : ℝ) : ℝ := radialPsi_orad κ r - radialPsi_orad κ r0

/-- `ψ'(r) = r/κ - g(r)`. -/
noncomputable def radialDpsi_orad (κ r : ℝ) : ℝ := r / κ - besselRatio r

/-! ### Upstream facts, repackaged -/

theorem besselI_zero_pos_orad (t : ℝ) : 0 < besselI 0 t := by
  obtain ⟨_, h, -⟩ := DGPS.Examples.bessel_integral_series_and_moment_derivatives
  exact h t

theorem besselI_zero_hasDerivAt_orad (t : ℝ) : HasDerivAt (besselI 0) (besselI 1 t) t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h, -⟩ :=
    DGPS.Examples.bessel_integral_series_and_moment_derivatives
  exact h t

theorem besselRatio_zero_orad : besselRatio 0 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, -⟩ :=
    DGPS.Examples.bessel_integral_series_and_moment_derivatives
  have := h 0
  simp only [neg_zero] at this
  linarith

theorem besselRatio_hasDerivAt_orad (t : ℝ) :
    HasDerivAt besselRatio (deriv besselRatio t) t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    DGPS.Examples.bessel_integral_series_and_moment_derivatives
  exact (h t).1.differentiableAt.hasDerivAt

theorem besselRatio_deriv_pos_lt_orad {t : ℝ} (ht : 0 < t) :
    0 < deriv besselRatio t ∧ deriv besselRatio t < besselRatio t / t ∧
      besselRatio t / t < 1 / 2 :=
  DGPS.Examples.strict_bessel_ratio_inequalities.1 t ht

theorem besselRatio_lt_one_orad {t : ℝ} (ht : 0 < t) : besselRatio t < 1 :=
  (DGPS.Examples.strict_bessel_ratio_inequalities.2.2.2.1 t ht).2

theorem besselRatio_div_strictAntiOn_orad :
    StrictAntiOn (fun t : ℝ => besselRatio t / t) (Ioi 0) :=
  DGPS.Examples.strict_bessel_ratio_inequalities.2.2.1

theorem besselRatio_deriv_zero_orad : deriv besselRatio 0 = 1 / 2 :=
  DGPS.Examples.strict_bessel_concavity_and_fold_parameter.2.1.2.1

theorem besselRatio_deriv_strictAntiOn_orad : StrictAntiOn (deriv besselRatio) (Ici 0) :=
  DGPS.Examples.strict_bessel_concavity_and_fold_parameter.2.1.2.2.1

theorem besselRatio_deriv_mem_orad {t : ℝ} (ht : 0 ≤ t) :
    0 < deriv besselRatio t ∧ deriv besselRatio t ≤ 1 / 2 := by
  rcases ht.eq_or_lt with h | h
  · subst h; rw [besselRatio_deriv_zero_orad]; norm_num
  · have := besselRatio_deriv_pos_lt_orad h
    exact ⟨this.1, (this.2.1.trans this.2.2).le⟩

/-! ### The derivative `f = ψ'` -/

theorem dpsi_hasDerivAt_orad {κ : ℝ} (r : ℝ) :
    HasDerivAt (radialDpsi_orad κ) (1 / κ - deriv besselRatio r) r := by
  have h1 : HasDerivAt (fun r : ℝ => r / κ) (1 / κ) r := by
    simpa using (hasDerivAt_id r).div_const κ
  exact h1.sub (besselRatio_hasDerivAt_orad r)

theorem psi_hasDerivAt_orad {κ : ℝ} (r : ℝ) :
    HasDerivAt (radialPsi_orad κ) (radialDpsi_orad κ r) r := by
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 / (2 * κ)) (r / κ) r := by
    have := ((hasDerivAt_pow 2 r).div_const (2 * κ))
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 := (besselI_zero_hasDerivAt_orad r).log (besselI_zero_pos_orad r).ne'
  exact h1.sub h2

theorem radialU_hasDerivAt_orad {κ : ℝ} (r0 r : ℝ) :
    HasDerivAt (radialU_orad κ r0) (radialDpsi_orad κ r) r :=
  (psi_hasDerivAt_orad r).sub_const (radialPsi_orad κ r0)

theorem dpsi_zero_orad (κ : ℝ) : radialDpsi_orad κ 0 = 0 := by
  simp [radialDpsi_orad, besselRatio_zero_orad]

theorem dpsi_convexOn_orad {κ : ℝ} :
    ConvexOn ℝ (Ici 0) (radialDpsi_orad κ) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    (fun x _ => (dpsi_hasDerivAt_orad x).continuousAt.continuousWithinAt)
    (fun x _ => (dpsi_hasDerivAt_orad x).differentiableAt.differentiableWithinAt) ?_
  intro x hx y hy hxy
  rw [interior_Ici] at hx hy
  rw [(dpsi_hasDerivAt_orad x).deriv, (dpsi_hasDerivAt_orad y).deriv]
  have := besselRatio_deriv_strictAntiOn_orad.antitoneOn (mem_Ici.mpr hx.out.le)
    (mem_Ici.mpr hy.out.le) hxy
  linarith

theorem dpsi_lipschitz_orad {κ : ℝ} (hκ : 2 < κ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |radialDpsi_orad κ y - radialDpsi_orad κ x| ≤ 1 / 2 * |y - x| := by
  have hκ0 : 0 < κ := by linarith
  have hκ1 : 1 / κ < 1 / 2 := by
    rw [div_lt_div_iff₀ hκ0 (by norm_num)]; linarith
  have hκ2 : 0 < 1 / κ := by positivity
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := radialDpsi_orad κ) (s := Ici 0)
    (C := 1 / 2) (fun z _ => (dpsi_hasDerivAt_orad z).differentiableAt) ?_
    (convex_Ici 0) (mem_Ici.mpr hx) (mem_Ici.mpr hy)
  · simpa [Real.norm_eq_abs] using this
  · intro z hz
    rw [(dpsi_hasDerivAt_orad z).deriv, Real.norm_eq_abs, abs_le]
    have := besselRatio_deriv_mem_orad (mem_Ici.mp hz)
    constructor <;> linarith [this.1, this.2]

/-! ### The critical radius -/

theorem exists_critical_radius_orad {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * besselRatio r0 := by
  have hκ0 : 0 < κ := by linarith
  have hκ1 : 1 / κ < 1 / 2 := by
    rw [div_lt_div_iff₀ hκ0 (by norm_num)]; linarith
  -- a small `ε` with `f ε < 0`
  have hd0 : HasDerivAt besselRatio (1 / 2) 0 := by
    have := besselRatio_hasDerivAt_orad 0
    rwa [besselRatio_deriv_zero_orad] at this
  have hsl := hd0.tendsto_slope_zero_right
  obtain ⟨ε, hε1, hε0⟩ := ((hsl.eventually (lt_mem_nhds hκ1)).and
    self_mem_nhdsWithin).exists
  have hεpos : 0 < ε := hε0
  have hfε : radialDpsi_orad κ ε < 0 := by
    simp only [zero_add, besselRatio_zero_orad, sub_zero, smul_eq_mul] at hε1
    unfold radialDpsi_orad
    have : ε / κ < besselRatio ε := by
      have h2 : 1 / κ * ε < ε⁻¹ * besselRatio ε * ε := mul_lt_mul_of_pos_right hε1 hεpos
      have h3 : ε⁻¹ * besselRatio ε * ε = besselRatio ε := by field_simp
      rw [h3] at h2
      calc ε / κ = 1 / κ * ε := by ring
        _ < besselRatio ε := h2
    linarith
  -- a point with `f > 0`
  have hfbig : 0 < radialDpsi_orad κ (κ + 1) := by
    have h1 := besselRatio_lt_one_orad (t := κ + 1) (by linarith)
    unfold radialDpsi_orad
    have : 1 < (κ + 1) / κ := by rw [lt_div_iff₀ hκ0]; linarith
    linarith
  have hεle : ε ≤ κ + 1 := by
    by_contra h
    have h := not_le.mp h
    -- if `ε > κ + 1` then `f ε > 0` as well
    have h1 := besselRatio_lt_one_orad hεpos
    have : 1 < ε / κ := by rw [lt_div_iff₀ hκ0]; linarith
    unfold radialDpsi_orad at hfε
    linarith
  have hcont : ContinuousOn (radialDpsi_orad κ) (Icc ε (κ + 1)) :=
    fun x _ => (dpsi_hasDerivAt_orad x).continuousAt.continuousWithinAt
  obtain ⟨r0, hr0, hfr0⟩ := intermediate_value_Icc hεle hcont
    (show (0 : ℝ) ∈ Icc (radialDpsi_orad κ ε) (radialDpsi_orad κ (κ + 1)) from
      ⟨hfε.le, hfbig.le⟩)
  refine ⟨r0, hεpos.trans_le hr0.1, ?_⟩
  unfold radialDpsi_orad at hfr0
  field_simp at hfr0 ⊢
  linarith

theorem critical_radius_unique_orad {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') {κ : ℝ}
    (hκ : 0 < κ) (h : r = κ * besselRatio r) (h' : r' = κ * besselRatio r') : r = r' := by
  have e : besselRatio r / r = besselRatio r' / r' := by
    have e1 : besselRatio r / r = 1 / κ := by
      field_simp; linarith
    have e2 : besselRatio r' / r' = 1 / κ := by
      field_simp; linarith
    rw [e1, e2]
  exact besselRatio_div_strictAntiOn_orad.injOn hr hr' e

/-! ### Chord inequality -/

theorem chord_orad {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f) {x y r : ℝ} (hx : 0 ≤ x)
    (hxy : x < y) (hxr : x ≤ r) (hry : r ≤ y) :
    f r ≤ ((y - r) * f x + (r - x) * f y) / (y - x) := by
  have hd : 0 < y - x := sub_pos.mpr hxy
  have hd' : y - x ≠ 0 := hd.ne'
  have h := hf.2 (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxy.le))
    (div_nonneg (by linarith) hd.le) (div_nonneg (by linarith) hd.le)
    (show (y - r) / (y - x) + (r - x) / (y - x) = 1 by field_simp; ring)
  have e : ((y - r) / (y - x)) • x + ((r - x) / (y - x)) • y = r := by
    simp only [smul_eq_mul]
    field_simp; ring
  rw [e] at h
  simp only [smul_eq_mul] at h
  calc f r ≤ _ := h
    _ = _ := by field_simp

/-! ### Integrating derivative signs -/

theorem monotoneOn_of_hasDerivAt_orad {φ φ' : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (h : ∀ x ∈ s, 0 ≤ φ' x) : MonotoneOn φ s :=
  monotoneOn_of_deriv_nonneg hs (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hd x).deriv]; exact h x (interior_subset hx))

theorem antitoneOn_of_hasDerivAt_orad {φ φ' : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (h : ∀ x ∈ s, φ' x ≤ 0) : AntitoneOn φ s :=
  antitoneOn_of_deriv_nonpos hs (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hd x).deriv]; exact h x (interior_subset hx))

theorem radialU_sub_quad_hasDerivAt_orad {κ : ℝ} (r0 k r : ℝ) :
    HasDerivAt (fun x => radialU_orad κ r0 x - k * (x - r0) ^ 2)
      (radialDpsi_orad κ r - 2 * k * (r - r0)) r := by
  have h2 : HasDerivAt (fun x : ℝ => k * (x - r0) ^ 2) (2 * k * (r - r0)) r := by
    have := (((hasDerivAt_id r).sub_const r0).pow 2).const_mul k
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  exact (radialU_hasDerivAt_orad r0 r).sub h2

/-- Integrating the derivative bounds: the quadratic comparison for `U`. -/
theorem quadratic_bounds_orad {κ r0 cf : ℝ} (hr0 : 0 < r0) (hcf : 0 < cf)
    (hneg : ∀ r ∈ Icc 0 r0, radialDpsi_orad κ r ≤ 0)
    (hlow1 : ∀ r ∈ Icc (r0 / 2) r0, radialDpsi_orad κ r ≤ -cf * (r0 - r))
    (hlow2 : ∀ r, r0 ≤ r → cf * (r - r0) ≤ radialDpsi_orad κ r)
    (hL : ∀ r, 0 ≤ r → |radialDpsi_orad κ r| ≤ 1 / 2 * |r - r0|) {r : ℝ} (hr : 0 ≤ r) :
    cf / 8 * (r - r0) ^ 2 ≤ radialU_orad κ r0 r ∧
      radialU_orad κ r0 r ≤ 1 / 4 * (r - r0) ^ 2 := by
  have hU0 : radialU_orad κ r0 r0 = 0 := sub_self _
  have hUa := fun k => radialU_sub_quad_hasDerivAt_orad (κ := κ) r0 k
  have hq0 : ∀ k : ℝ, radialU_orad κ r0 r0 - k * (r0 - r0) ^ 2 = 0 := by
    intro k; simp [hU0]
  have ha : 0 < r0 / 2 := by positivity
  have har : r0 / 2 < r0 := by linarith
  constructor
  · -- lower bound
    by_cases hra : r ≤ r0 / 2
    · -- near the origin
      have hU := fun x => radialU_hasDerivAt_orad (κ := κ) r0 x
      have hanti := antitoneOn_of_hasDerivAt_orad (convex_Icc 0 r0) (s := Icc 0 r0)
        (φ := radialU_orad κ r0) hU (fun x hx => hneg x hx)
      have h1 := hanti ⟨hr, hra.trans har.le⟩ ⟨ha.le, har.le⟩ hra
      have hd2 := hUa (cf / 2)
      have hanti2 := antitoneOn_of_hasDerivAt_orad (convex_Icc (r0 / 2) r0) hd2
        (s := Icc (r0 / 2) r0)
        (fun x hx => by
          have h := hlow1 x hx
          have h' : 0 ≤ cf * (r0 - x) := mul_nonneg hcf.le (by linarith [hx.2])
          linarith)
      have h2 := hanti2 ⟨le_rfl, har.le⟩ ⟨har.le, le_rfl⟩ har.le
      beta_reduce at h2
      rw [hq0] at h2
      have hsq : (r - r0) ^ 2 ≤ r0 ^ 2 := by
        have h3 : r0 - r ≤ r0 := by linarith
        have h4 : 0 ≤ r0 - r := by linarith
        nlinarith
      have h5 : cf / 8 * (r - r0) ^ 2 ≤ cf / 8 * r0 ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have h6 : cf / 8 * r0 ^ 2 = cf / 2 * (r0 / 2 - r0) ^ 2 := by ring
      linarith
    · have hra' : r0 / 2 < r := not_le.mp hra
      have hd := hUa (cf / 2)
      rcases le_total r r0 with h | h
      · have hanti := antitoneOn_of_hasDerivAt_orad (convex_Icc (r0 / 2) r0) hd
          (s := Icc (r0 / 2) r0)
          (fun x hx => by
            have h := hlow1 x hx
            have h' : 0 ≤ cf * (r0 - x) := mul_nonneg hcf.le (by linarith [hx.2])
            linarith)
        have h1 := hanti ⟨hra'.le, h⟩ ⟨har.le, le_rfl⟩ h
        beta_reduce at h1
        rw [hq0] at h1
        have h2 : 0 ≤ cf * (r - r0) ^ 2 := by positivity
        linarith
      · have hmono := monotoneOn_of_hasDerivAt_orad (convex_Ici r0) hd (s := Ici r0)
          (fun x hx => by
            have h := hlow2 x (mem_Ici.mp hx)
            have h' : 0 ≤ cf * (x - r0) := mul_nonneg hcf.le (by linarith [mem_Ici.mp hx])
            linarith)
        have h1 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr h) h
        beta_reduce at h1
        rw [hq0] at h1
        have h2 : 0 ≤ cf * (r - r0) ^ 2 := by positivity
        linarith
  · -- upper bound
    have hd := hUa (1 / 4)
    rcases le_total r r0 with h | h
    · have hmono := monotoneOn_of_hasDerivAt_orad (convex_Icc 0 r0) hd (s := Icc 0 r0)
        (fun x hx => by
          have h1 := (abs_le.mp (hL x hx.1)).1
          rw [abs_of_nonpos (by linarith [hx.2])] at h1
          linarith)
      have h1 := hmono ⟨hr, h⟩ ⟨hr0.le, le_rfl⟩ h
      beta_reduce at h1
      rw [hq0] at h1
      linarith
    · have hanti := antitoneOn_of_hasDerivAt_orad (convex_Ici r0) hd (s := Ici r0)
        (fun x hx => by
          have h1 := (abs_le.mp (hL x (hr0.le.trans hx))).2
          rw [abs_of_nonneg (by linarith [mem_Ici.mp hx])] at h1
          linarith)
      have h1 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr h) h
      beta_reduce at h1
      rw [hq0] at h1
      linarith

/-! ### Main estimates -/

theorem well_estimates_orad {κ r0 : ℝ} (hκ : 2 < κ) (hr0 : 0 < r0)
    (hroot : r0 = κ * besselRatio r0) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ r ∈ Icc 0 (r0 / 2), c * r ≤ -radialDpsi_orad κ r ∧ -radialDpsi_orad κ r ≤ C * r) ∧
      (∀ r, r0 / 2 ≤ r →
        c * |r - r0| ≤ |radialDpsi_orad κ r| ∧ |radialDpsi_orad κ r| ≤ C * |r - r0| ∧
          (r < r0 → radialDpsi_orad κ r < 0) ∧ (r0 < r → 0 < radialDpsi_orad κ r)) ∧
      (∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r ∧
        radialU_orad κ r0 r ≤ C * (r - r0) ^ 2) := by
  have hκ0 : 0 < κ := by linarith
  have ha : 0 < r0 / 2 := by positivity
  have ha' : r0 / 2 ≠ 0 := ha.ne'
  have hr0ne : r0 ≠ 0 := hr0.ne'
  have har : r0 / 2 < r0 := by linarith
  have hr0a : r0 - r0 / 2 = r0 / 2 := by ring
  have hconv : ConvexOn ℝ (Ici 0) (radialDpsi_orad κ) := dpsi_convexOn_orad
  have hf0 : radialDpsi_orad κ 0 = 0 := dpsi_zero_orad κ
  have hgr0 : besselRatio r0 = r0 / κ := by field_simp; linarith
  have hG : besselRatio r0 / r0 = 1 / κ := by rw [hgr0]; field_simp
  have hfr0 : radialDpsi_orad κ r0 = 0 := by simp only [radialDpsi_orad]; rw [hgr0]; ring
  -- sign of `f` at `a`
  have hfa : radialDpsi_orad κ (r0 / 2) < 0 := by
    have h1 := besselRatio_div_strictAntiOn_orad (mem_Ioi.mpr ha) (mem_Ioi.mpr hr0) har
    simp only at h1
    rw [hG, lt_div_iff₀ ha] at h1
    simp only [radialDpsi_orad]
    have : 1 / κ * (r0 / 2) = r0 / 2 / κ := by ring
    linarith
  obtain ⟨c5, hc5pos, hc5a⟩ : ∃ c5 : ℝ, 0 < c5 ∧
      radialDpsi_orad κ (r0 / 2) = -c5 * (r0 / 2) :=
    ⟨-radialDpsi_orad κ (r0 / 2) / (r0 / 2), div_pos (by linarith) ha, by field_simp⟩
  -- chord bounds
  have hA : ∀ r ∈ Icc 0 (r0 / 2), radialDpsi_orad κ r ≤ -c5 * r := by
    intro r hr
    have := chord_orad hconv (le_refl (0 : ℝ)) ha hr.1 hr.2
    rw [hf0, hc5a] at this
    refine this.trans (le_of_eq ((div_eq_iff (by rw [sub_zero]; exact ha')).mpr ?_))
    ring
  have hB : ∀ r ∈ Icc (r0 / 2) r0, radialDpsi_orad κ r ≤ -c5 * (r0 - r) := by
    intro r hr
    have := chord_orad hconv ha.le har hr.1 hr.2
    rw [hfr0, hc5a, hr0a] at this
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  -- tangent bound at `r0`
  obtain ⟨m, hm, hC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ r, r0 ≤ r → m * (r - r0) ≤ radialDpsi_orad κ r := by
    have hm : 0 < 1 / κ - deriv besselRatio r0 := by
      have := (besselRatio_deriv_pos_lt_orad hr0).2.1
      rw [hG] at this
      linarith
    refine ⟨1 / κ - deriv besselRatio r0, hm, ?_⟩
    intro r hr
    rcases hr.eq_or_lt with h | h
    · subst h; simp [hfr0]
    · have := hconv.deriv_le_slope (mem_Ici.mpr hr0.le) (mem_Ici.mpr (hr0.le.trans hr)) h
        (dpsi_hasDerivAt_orad r0).differentiableAt
      rw [(dpsi_hasDerivAt_orad r0).deriv, slope_def_field, hfr0, sub_zero,
        le_div_iff₀ (sub_pos.mpr h)] at this
      exact this
  -- Lipschitz bounds
  have hL : ∀ r, 0 ≤ r → |radialDpsi_orad κ r| ≤ 1 / 2 * |r - r0| := by
    intro r hr
    have := dpsi_lipschitz_orad hκ hr0.le hr
    rwa [hfr0, sub_zero] at this
  have hL0 : ∀ r, 0 ≤ r → |radialDpsi_orad κ r| ≤ 1 / 2 * r := by
    intro r hr
    have := dpsi_lipschitz_orad hκ (le_refl (0 : ℝ)) hr
    rwa [hf0, sub_zero, sub_zero, abs_of_nonneg hr] at this
  have hfneg : ∀ r ∈ Icc 0 r0, radialDpsi_orad κ r ≤ 0 := by
    intro r hr
    rcases le_total r (r0 / 2) with h | h
    · have h1 := hA r ⟨hr.1, h⟩
      have h2 : 0 ≤ c5 * r := mul_nonneg hc5pos.le hr.1
      linarith
    · have h1 := hB r ⟨h, hr.2⟩
      have h2 : 0 ≤ c5 * (r0 - r) := mul_nonneg hc5pos.le (by linarith [hr.2])
      linarith
  obtain ⟨cf, hcfpos, hcf5, hcfm⟩ : ∃ cf : ℝ, 0 < cf ∧ cf ≤ c5 ∧ cf ≤ m :=
    ⟨min c5 m, lt_min hc5pos hm, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨c, hc1, hcpos, hc2⟩ : ∃ c : ℝ, c ≤ cf / 8 ∧ 0 < c ∧ c ≤ 1 / 2 :=
    ⟨min (cf / 8) (1 / 2), min_le_left _ _, lt_min (by positivity) (by norm_num),
      min_le_right _ _⟩
  have hcc5 : c ≤ c5 := by linarith
  have hccm : c ≤ m := by linarith
  have hcf' : c ≤ cf / 8 := hc1
  refine ⟨c, 1 / 2, hcpos, hc2, ?_, ?_, ?_⟩
  · intro r hr
    have h1 := hA r hr
    have h3 := (abs_le.mp (hL0 r hr.1)).1
    have h4 : 0 ≤ (c5 - c) * r := mul_nonneg (by linarith) hr.1
    refine ⟨by linarith, by linarith⟩
  · intro r hr
    have hr0' : 0 ≤ r := ha.le.trans hr
    have hLr := hL r hr0'
    refine ⟨?_, by linarith, ?_, ?_⟩
    · rcases le_or_gt r r0 with h | h
      · have h1 := hB r ⟨hr, h⟩
        have h2 : 0 ≤ c5 * (r0 - r) := mul_nonneg hc5pos.le (by linarith)
        have h3 : 0 ≤ (c5 - c) * (r0 - r) := mul_nonneg (by linarith) (by linarith)
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
      · have h1 := hC r h.le
        have h2 : 0 < m * (r - r0) := mul_pos hm (by linarith)
        have h3 : 0 ≤ (m - c) * (r - r0) := mul_nonneg (by linarith) (by linarith)
        rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
        linarith
    · intro h
      have h1 := hB r ⟨hr, h.le⟩
      have h2 : 0 < c5 * (r0 - r) := mul_pos hc5pos (by linarith)
      linarith
    · intro h
      have h1 := hC r h.le
      have h2 : 0 < m * (r - r0) := mul_pos hm (by linarith)
      linarith
  · intro r hr
    have hlow1 : ∀ r ∈ Icc (r0 / 2) r0, radialDpsi_orad κ r ≤ -cf * (r0 - r) := by
      intro r hr
      have h1 := hB r hr
      have h3 : 0 ≤ (c5 - cf) * (r0 - r) := mul_nonneg (by linarith) (by linarith [hr.2])
      linarith
    have hlow2 : ∀ r, r0 ≤ r → cf * (r - r0) ≤ radialDpsi_orad κ r := by
      intro r hr
      have h1 := hC r hr
      have h3 : 0 ≤ (m - cf) * (r - r0) := mul_nonneg (by linarith) (by linarith)
      linarith
    obtain ⟨h1, h2⟩ := quadratic_bounds_orad hr0 hcfpos hfneg hlow1 hlow2 hL hr
    have hsq : 0 ≤ (r - r0) ^ 2 := sq_nonneg _
    constructor
    · have : c * (r - r0) ^ 2 ≤ cf / 8 * (r - r0) ^ 2 := mul_le_mul_of_nonneg_right hcf' hsq
      linarith
    · linarith

/-! ### The packet theorem -/

/-- Ordered radial well geometry (FIN034).  For `κ > 2` the equation `r0 = κ g(r0)`, with
`g = I₁/I₀`, has a unique positive solution `r0`.  With `ψ(r) = r²/(2κ) - log I₀(r)` and
`U = ψ - ψ(r0)`, there are constants `0 < c ≤ C` (depending on `κ`) such that
`c r ≤ -U'(r) ≤ C r` on `[0, r0/2]`, `c |r - r0| ≤ |U'(r)| ≤ C |r - r0|` on `[r0/2, ∞)` with
`U' < 0` left of `r0` and `U' > 0` right of `r0`, and
`c (r - r0)² ≤ U(r) ≤ C (r - r0)²` for all `r ≥ 0`. -/
theorem ordered_radial_well_geometry {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * besselRatio r0 ∧
      (∀ r' : ℝ, 0 < r' → r' = κ * besselRatio r' → r' = r0) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        (∀ r ∈ Icc 0 (r0 / 2),
          c * r ≤ -deriv (radialU_orad κ r0) r ∧ -deriv (radialU_orad κ r0) r ≤ C * r) ∧
        (∀ r, r0 / 2 ≤ r →
          c * |r - r0| ≤ |deriv (radialU_orad κ r0) r| ∧
            |deriv (radialU_orad κ r0) r| ≤ C * |r - r0| ∧
            (r < r0 → deriv (radialU_orad κ r0) r < 0) ∧
            (r0 < r → 0 < deriv (radialU_orad κ r0) r)) ∧
        (∀ r, 0 ≤ r →
          c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r ∧ radialU_orad κ r0 r ≤ C * (r - r0) ^ 2) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨r0, hr0, hroot⟩ := exists_critical_radius_orad hκ
  obtain ⟨c, C, hc, hcC, h1, h2, h3⟩ := well_estimates_orad hκ hr0 hroot
  have hd : ∀ r, deriv (radialU_orad κ r0) r = radialDpsi_orad κ r :=
    fun r => (radialU_hasDerivAt_orad r0 r).deriv
  refine ⟨r0, hr0, hroot, fun r' hr' h' => critical_radius_unique_orad hr' hr0 hκ0 h' hroot,
    c, C, hc, hcC, ?_, ?_, h3⟩
  · intro r hr
    rw [hd]
    exact h1 r hr
  · intro r hr
    simp only [hd]
    exact h2 r hr

end DGPS.FiniteN
