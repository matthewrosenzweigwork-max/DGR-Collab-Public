import DGPS.FiniteN.CriticalXY

/-!
# Critical scaled bounded correction (FIN028)

For `U_N(y) = N ψ(N^{-1/4}‖y‖)` (`N ≥ 1`) the Hessian satisfies `D²U_N ≥ c₀ min(‖y‖²,1) I`;
the bounded correction `q(y) = a (1 - e^{-‖y‖²/2})`, `a = c₀/2`, has oscillation `≤ a` and
`D²(U_N + q) ≥ a e^{-1/2} I` for every `N ≥ 1`.
-/
open scoped ContDiff
open Real

namespace DGPS.FiniteN

section Correction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- the scaled critical potential `U_N(y) = N ψ(N^{-1/4}‖y‖)` -/
noncomputable def criticalScaledPotential (N : ℝ) (y : E) : ℝ :=
  N * criticalPsi (N ^ (-(1 / 4 : ℝ)) * ‖y‖)

/-- the bounded correction `q(y) = a (1 - e^{-‖y‖²/2})` with `a = c₀/2`, `c₀ = (16 e^{1/4})⁻¹` -/
noncomputable def criticalBoundedCorrection (y : E) : ℝ :=
  ((16 * Real.exp (1 / 4))⁻¹ / 2) * (1 - Real.exp (-(‖y‖ ^ 2 / 2)))

theorem hasFDerivAt_comp_smul_const (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (c : ℝ) (y : E) :
    HasFDerivAt (fun y : E => g (c • y)) (c • fderiv ℝ g (c • y)) y := by
  have h1 : HasFDerivAt (fun y : E => c • y) (c • ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).const_smul c
  have h2 := (hg.differentiable (by simp) (c • y)).hasFDerivAt.comp y h1
  refine h2.congr_fderiv ?_
  ext w
  simp

theorem hessian_comp_smul_const (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (c : ℝ) (y v : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => g (c • y))) y v v =
      c ^ 2 * fderiv ℝ (fderiv ℝ g) (c • y) v v := by
  have hF : fderiv ℝ (fun y : E => g (c • y)) = fun y => c • fderiv ℝ g (c • y) :=
    funext fun y => (hasFDerivAt_comp_smul_const g hg c y).fderiv
  rw [hF]
  have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have h1 := (hg'.differentiable (by simp) (c • y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_smul c)
  have h2 : HasFDerivAt (fun y : E => c • fderiv ℝ g (c • y)) _ y := h1.const_smul c
  rw [h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul,
    smul_eq_mul, ContinuousLinearMap.id_apply]
  ring

theorem hessian_const_mul (Φ : E → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (N : ℝ) (z v : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => N * Φ z)) z v v = N * fderiv ℝ (fderiv ℝ Φ) z v v := by
  have e1 : fderiv ℝ (fun z : E => N * Φ z) = fun z => N • fderiv ℝ Φ z :=
    funext fun z => fderiv_const_mul (hΦ.differentiable (by simp) z) N
  have hΦ' : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  have e2 : (fun z : E => N • fderiv ℝ Φ z) = N • fderiv ℝ Φ := rfl
  rw [e1, e2, fderiv_const_smul (hΦ'.differentiable (by simp) z)]
  simp

theorem criticalScaledPotential_eq (N : ℝ) (hN : 1 ≤ N) :
    criticalScaledPotential (E := E) N =
      fun y : E => N * criticalPotential ((N ^ (-(1 / 4 : ℝ))) • y) := by
  funext y
  have hc : 0 < N ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  simp only [criticalScaledPotential, criticalPotential, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc]

theorem criticalScaledPotential_contDiff (N : ℝ) (hN : 1 ≤ N) :
    ContDiff ℝ ∞ (criticalScaledPotential (E := E) N) := by
  rw [criticalScaledPotential_eq N hN]
  have h := (critical_radial_hessian_coercivity (E := E)).1
  exact (contDiff_const.mul (h.comp (contDiff_const_smul _)))

theorem criticalScaledPotential_hessian (N : ℝ) (hN : 1 ≤ N) (y v : E) :
    fderiv ℝ (fderiv ℝ (criticalScaledPotential (E := E) N)) y v v =
      N * (N ^ (-(1 / 4 : ℝ))) ^ 2 *
        fderiv ℝ (fderiv ℝ (criticalPotential (E := E))) ((N ^ (-(1 / 4 : ℝ))) • y) v v := by
  have hΦ := (critical_radial_hessian_coercivity (E := E)).1
  rw [criticalScaledPotential_eq N hN]
  have h1 : (fun y : E => N * criticalPotential ((N ^ (-(1 / 4 : ℝ))) • y)) =
      fun y : E => (fun z : E => N * criticalPotential z) ((N ^ (-(1 / 4 : ℝ))) • y) := rfl
  rw [h1, hessian_comp_smul_const _ (contDiff_const.mul hΦ), hessian_const_mul _ hΦ]
  ring

/-- `N^{-1/2} = (N^{-1/4})²` and `N * N^{-1/2} = √N`; the scaling inequality
`√N min(N^{-1/2}t, 1) ≥ min(t, 1)` -/
theorem scaling_min_ge (N : ℝ) (hN : 1 ≤ N) (t : ℝ) (_ht : 0 ≤ t) :
    min t 1 ≤ N * (N ^ (-(1 / 4 : ℝ))) ^ 2 * min ((N ^ (-(1 / 4 : ℝ))) ^ 2 * t) 1 := by
  have hN0 : 0 < N := by linarith
  set c := N ^ (-(1 / 4 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hN0 _
  have h4 : c ^ 4 * N = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    have : (-(1 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    field_simp
  have hcle : c ≤ 1 := by
    rw [hc]; exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hk : 0 < N * c ^ 2 := by positivity
  have hk1 : 1 ≤ N * c ^ 2 := by
    -- N c² * c² = 1 and c² ≤ 1
    have : (N * c ^ 2) * c ^ 2 = 1 := by nlinarith [h4]
    nlinarith [sq_nonneg c, mul_pos hcpos hcpos, pow_le_one₀ hcpos.le hcle (n := 2)]
  have hNc : N * c ^ 2 * c ^ 2 = 1 := by nlinarith [h4]
  rcases le_total (c ^ 2 * t) 1 with h | h
  · rw [min_eq_left h]
    have : N * c ^ 2 * (c ^ 2 * t) = t := by
      calc N * c ^ 2 * (c ^ 2 * t) = (N * c ^ 2 * c ^ 2) * t := by ring
        _ = t := by rw [hNc]; ring
    rw [this]; exact min_le_left _ _
  · rw [min_eq_right h]
    calc min t 1 ≤ 1 := min_le_right _ _
      _ = 1 * 1 := by ring
      _ ≤ N * c ^ 2 * 1 := by nlinarith

theorem criticalScaledPotential_hessian_ge (N : ℝ) (hN : 1 ≤ N) (y v : E) :
    (16 * Real.exp (1 / 4))⁻¹ * min (‖y‖ ^ 2) 1 * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (criticalScaledPotential (E := E) N)) y v v := by
  rw [criticalScaledPotential_hessian N hN]
  have hc0 : 0 < (16 * Real.exp (1 / 4))⁻¹ := by positivity
  have h := (critical_radial_hessian_coercivity (E := E)).2.1 ((N ^ (-(1 / 4 : ℝ))) • y) v
  have hN0 : 0 < N := by linarith
  have hcpos : 0 < N ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hn : ‖(N ^ (-(1 / 4 : ℝ))) • y‖ ^ 2 = (N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, mul_pow]
  rw [hn] at h
  have hs := scaling_min_ge N hN (‖y‖ ^ 2) (by positivity)
  have hk : 0 < N * (N ^ (-(1 / 4 : ℝ))) ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left h hk.le
  have h3 : (16 * Real.exp (1 / 4))⁻¹ * min (‖y‖ ^ 2) 1 * ‖v‖ ^ 2 ≤
      (16 * Real.exp (1 / 4))⁻¹ * (N * (N ^ (-(1 / 4 : ℝ))) ^ 2 *
        min ((N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2) 1) * ‖v‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hs hc0.le
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  refine h3.trans (le_of_eq_of_le ?_ h2)
  ring

theorem criticalBoundedCorrection_contDiff :
    ContDiff ℝ ∞ (criticalBoundedCorrection (E := E)) := by
  unfold criticalBoundedCorrection
  refine contDiff_const.mul (contDiff_const.sub (Real.contDiff_exp.comp ?_))
  exact ((contDiff_norm_sq ℝ).div_const 2).neg

theorem criticalBoundedCorrection_hessian (z v : E) :
    fderiv ℝ (fderiv ℝ (criticalBoundedCorrection (E := E))) z v v =
      ((16 * Real.exp (1 / 4))⁻¹ / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) *
        (‖v‖ ^ 2 - (inner ℝ z v) ^ 2) := by
  set a : ℝ := (16 * Real.exp (1 / 4))⁻¹ / 2 with ha
  have hgrad : ∀ x : E, HasFDerivAt (criticalBoundedCorrection (E := E))
      ((a * Real.exp (-(‖x‖ ^ 2 / 2))) • innerSL ℝ x) x := by
    intro x
    have hd : HasDerivAt (fun s : ℝ => a * (1 - Real.exp (-(2 * s))))
        (2 * a * Real.exp (-(2 * (‖x‖ ^ 2 / 4)))) (‖x‖ ^ 2 / 4) := by
      have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) (‖x‖ ^ 2 / 4) := by
        exact (((hasDerivAt_id' (‖x‖ ^ 2 / 4)).const_mul (2:ℝ)).neg).congr_deriv (by norm_num)
      have h2 := ((h1.exp).const_sub (1:ℝ)).const_mul a
      convert h2 using 1
      ring
    have h := hasFDerivAt_comp_normSq x hd
    have e : (criticalBoundedCorrection (E := E)) =
        fun y : E => (fun s : ℝ => a * (1 - Real.exp (-(2 * s)))) (‖y‖ ^ 2 / 4) := by
      funext y
      unfold criticalBoundedCorrection
      have : -(2 * (‖y‖ ^ 2 / 4)) = -(‖y‖ ^ 2 / 2) := by ring
      simp only [this]
      rfl
    rw [e]
    refine h.congr_fderiv ?_
    have : -(2 * (‖x‖ ^ 2 / 4)) = -(‖x‖ ^ 2 / 2) := by ring
    rw [this]
    congr 1
    ring
  have hF : fderiv ℝ (criticalBoundedCorrection (E := E)) =
      fun x => (a * Real.exp (-(‖x‖ ^ 2 / 2))) • innerSL ℝ x := funext fun x => (hgrad x).fderiv
  rw [hF]
  have hc : HasFDerivAt (fun x : E => a * Real.exp (-(‖x‖ ^ 2 / 2)))
      ((-(a * Real.exp (-(‖z‖ ^ 2 / 2)))) • innerSL ℝ z) z := by
    have hd : HasDerivAt (fun s : ℝ => a * Real.exp (-(2 * s)))
        (-(2 * a * Real.exp (-(2 * (‖z‖ ^ 2 / 4))))) (‖z‖ ^ 2 / 4) := by
      have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) (‖z‖ ^ 2 / 4) := by
        exact (((hasDerivAt_id' (‖z‖ ^ 2 / 4)).const_mul (2:ℝ)).neg).congr_deriv (by norm_num)
      have h2 := (h1.exp).const_mul a
      convert h2 using 1
      ring
    have h := hasFDerivAt_comp_normSq z hd
    have e : (fun x : E => a * Real.exp (-(‖x‖ ^ 2 / 2))) =
        fun y : E => (fun s : ℝ => a * Real.exp (-(2 * s))) (‖y‖ ^ 2 / 4) := by
      funext y
      have : -(2 * (‖y‖ ^ 2 / 4)) = -(‖y‖ ^ 2 / 2) := by ring
      simp only [this]
    rw [e]
    refine h.congr_fderiv ?_
    have : -(2 * (‖z‖ ^ 2 / 4)) = -(‖z‖ ^ 2 / 2) := by ring
    rw [this]
    congr 1
    ring
  have hg := (innerSL ℝ (E := E)).hasFDerivAt (x := z)
  have h2 := hc.smul hg
  have h3 : HasFDerivAt (fun x : E => (a * Real.exp (-(‖x‖ ^ 2 / 2))) • innerSL ℝ x) _ z := h2
  rw [h3.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have e1 : (innerSL ℝ v) v = ‖v‖ ^ 2 := by simp
  have e2 : (innerSL ℝ z) v = inner ℝ z v := by simp
  rw [e1, e2]
  ring

theorem exp_neg_mul_le_one (u : ℝ) (hu : 0 ≤ u) : Real.exp (-(u / 2)) * u ≤ 1 := by
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u / 2 by positivity)
  have hx : u ≤ Real.exp (u / 2) := by nlinarith [sq_nonneg (u - 2)]
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  linarith

omit [InnerProductSpace ℝ E] in
theorem criticalBoundedCorrection_bounds (y : E) :
    0 ≤ criticalBoundedCorrection y ∧
      criticalBoundedCorrection y ≤ (16 * Real.exp (1 / 4))⁻¹ / 2 := by
  unfold criticalBoundedCorrection
  have ha : 0 < (16 * Real.exp (1 / 4))⁻¹ / 2 := by positivity
  have h1 := Real.exp_pos (-(‖y‖ ^ 2 / 2))
  have h2 : Real.exp (-(‖y‖ ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
  constructor
  · exact mul_nonneg ha.le (by linarith)
  · nlinarith

theorem criticalScaled_sum_hessian_ge (N : ℝ) (hN : 1 ≤ N) (y v : E) :
    ((16 * Real.exp (1 / 4))⁻¹ / 2) * Real.exp (-(1 / 2)) * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun x : E => criticalScaledPotential N x +
        criticalBoundedCorrection x)) y v v := by
  have hU := criticalScaledPotential_contDiff (E := E) N hN
  have hQ := criticalBoundedCorrection_contDiff (E := E)
  have hU' : ContDiff ℝ ∞ (fderiv ℝ (criticalScaledPotential (E := E) N)) :=
    hU.fderiv_right (by simp)
  have hQ' : ContDiff ℝ ∞ (fderiv ℝ (criticalBoundedCorrection (E := E))) :=
    hQ.fderiv_right (by simp)
  have e1 : fderiv ℝ (fun x : E => criticalScaledPotential N x + criticalBoundedCorrection x) =
      fun x => fderiv ℝ (criticalScaledPotential (E := E) N) x +
        fderiv ℝ (criticalBoundedCorrection (E := E)) x :=
    funext fun x => fderiv_add (hU.differentiable (by simp) x) (hQ.differentiable (by simp) x)
  have e2 : (fun x : E => fderiv ℝ (criticalScaledPotential (E := E) N) x +
        fderiv ℝ (criticalBoundedCorrection (E := E)) x) =
      fderiv ℝ (criticalScaledPotential (E := E) N) +
        fderiv ℝ (criticalBoundedCorrection (E := E)) := rfl
  rw [e1, e2, fderiv_add (hU'.differentiable (by simp) y) (hQ'.differentiable (by simp) y)]
  simp only [add_apply]
  have h1 := criticalScaledPotential_hessian_ge (E := E) N hN y v
  rw [criticalBoundedCorrection_hessian]
  set u := ‖y‖ ^ 2 with hu
  set m := ‖v‖ ^ 2 with hm
  set a := (16 * Real.exp (1 / 4))⁻¹ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hm0 : 0 ≤ m := by positivity
  have hu0 : 0 ≤ u := by positivity
  have hcs : (inner ℝ y v) ^ 2 ≤ u * m := by
    have h := abs_real_inner_le_norm y v
    have h2 : (inner ℝ y v) ^ 2 ≤ (‖y‖ * ‖v‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (inner ℝ y v) ^ 2 ≤ (‖y‖ * ‖v‖) ^ 2 := h2
      _ = u * m := by rw [hu, hm]; ring
  set e := Real.exp (-(u / 2)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hE0 : 0 < Real.exp (-(1 / 2)) := Real.exp_pos _
  have hE1 : Real.exp (-(1 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hq : a * e * ((1 - u) * m) ≤ a * e * (m - (inner ℝ y v) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have hc0 : (16 * Real.exp (1 / 4))⁻¹ = 2 * a := by rw [ha]; ring
  rw [hc0] at h1
  rcases le_total u 1 with hu1 | hu1
  · rw [min_eq_left hu1] at h1
    have hEe : Real.exp (-(1 / 2)) ≤ e := Real.exp_le_exp.2 (by linarith)
    have k1 : a * Real.exp (-(1 / 2)) * ((1 - u) * m) ≤ a * e * ((1 - u) * m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEe ha0.le)
        (mul_nonneg (by linarith) hm0)
    have k2 : a * Real.exp (-(1 / 2)) * (u * m) ≤ a * (u * m) := by
      have := mul_nonneg ha0.le (mul_nonneg hu0 hm0)
      nlinarith
    nlinarith
  · rw [min_eq_right hu1] at h1
    have h3 := exp_neg_mul_le_one u hu0
    rw [← he] at h3
    have k1 : a * e * ((1 - u) * m) ≥ -(a * m) := by
      have : a * e * ((1 - u) * m) = a * m * (e - e * u) := by ring
      rw [this]
      nlinarith [mul_nonneg ha0.le hm0]
    nlinarith [mul_nonneg ha0.le hm0, mul_pos ha0 he0]

end Correction

/-- **Critical scaled bounded correction.** For `N ≥ 1`, `U_N(y) = N ψ(N^{-1/4}‖y‖)` is smooth with
`D²U_N ≥ c₀ min(‖y‖², 1) I`, `c₀ = (16 e^{1/4})⁻¹`; the correction `q(y) = a (1 - e^{-‖y‖²/2})`,
`a = c₀/2`, is smooth with oscillation `≤ a`, and `D²(U_N + q) ≥ a e^{-1/2} I` for every `N ≥ 1`. -/
theorem critical_scaled_bounded_correction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    (∀ N : ℝ, 1 ≤ N → ContDiff ℝ ∞ (criticalScaledPotential (E := E) N)) ∧
    (∀ N : ℝ, 1 ≤ N → ∀ y v : E, (16 * Real.exp (1 / 4))⁻¹ * min (‖y‖ ^ 2) 1 * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (criticalScaledPotential (E := E) N)) y v v) ∧
    ContDiff ℝ ∞ (criticalBoundedCorrection (E := E)) ∧
    (∀ y y' : E, |criticalBoundedCorrection y - criticalBoundedCorrection y'| ≤
      (16 * Real.exp (1 / 4))⁻¹ / 2) ∧
    (∀ N : ℝ, 1 ≤ N → ∀ y v : E,
      ((16 * Real.exp (1 / 4))⁻¹ / 2) * Real.exp (-(1 / 2)) * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (fun x : E => criticalScaledPotential N x +
          criticalBoundedCorrection x)) y v v) := by
  refine ⟨criticalScaledPotential_contDiff, criticalScaledPotential_hessian_ge,
    criticalBoundedCorrection_contDiff, ?_, criticalScaled_sum_hessian_ge⟩
  intro y y'
  obtain ⟨a1, a2⟩ := criticalBoundedCorrection_bounds y
  obtain ⟨b1, b2⟩ := criticalBoundedCorrection_bounds y'
  rw [abs_le]
  constructor <;> linarith

end DGPS.FiniteN
