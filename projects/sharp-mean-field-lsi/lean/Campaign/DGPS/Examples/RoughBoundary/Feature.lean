import DGPS.Examples.RoughBoundary.SpikesModulus
import DGPS.Foundations.PeriodicSmoothing

/-!
# The complete phase and unit feature family (RUF005)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` sections 1.4 and 3.1.
-/

open MeasureTheory Set
open scoped Real ContDiff

namespace DGPS.Examples.RoughBoundary.Feature

open DGPS.Examples.RoughBoundary.Spikes (gT gLine fLine hSum hMean pt modulusConst)

/-- `Z_L = ∫₀¹ exp (L cos (6π s)) ds`. -/
noncomputable def Zpart (L : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, Real.exp (L * Real.cos (6 * π * t))

/-- `Q_L(s) = exp (L cos (6π s)) / Z_L`. -/
noncomputable def Qdens (L s : ℝ) : ℝ := Real.exp (L * Real.cos (6 * π * s)) / Zpart L

/-- `A_L(s) = ∫₀ˢ Q_L`. -/
noncomputable def Aprim (L s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, Qdens L t

lemma continuous_expcos (L : ℝ) : Continuous fun t : ℝ => Real.exp (L * Real.cos (6 * π * t)) := by
  fun_prop

lemma zpart_pos {L : ℝ} (_hL : 0 < L) : 0 < Zpart L := by
  unfold Zpart
  exact intervalIntegral.intervalIntegral_pos_of_pos
    ((continuous_expcos L).intervalIntegrable _ _) (fun t => Real.exp_pos _) zero_lt_one

lemma qdens_pos {L : ℝ} (hL : 0 < L) (s : ℝ) : 0 < Qdens L s :=
  div_pos (Real.exp_pos _) (zpart_pos hL)

lemma contDiff_qdens (L : ℝ) : ContDiff ℝ ∞ (Qdens L) := by
  unfold Qdens
  exact (Real.contDiff_exp.comp (contDiff_const.mul
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)))).div_const _

lemma continuous_qdens (L : ℝ) : Continuous (Qdens L) := (contDiff_qdens L).continuous

lemma qdens_periodic (L : ℝ) : Function.Periodic (Qdens L) (1 / 3) := by
  intro s
  unfold Qdens
  have : Real.cos (6 * π * (s + 1 / 3)) = Real.cos (6 * π * s) := by
    have e : 6 * π * (s + 1 / 3) = 6 * π * s + (1 : ℕ) * (2 * π) := by push_cast; ring
    rw [e, Real.cos_add_nat_mul_two_pi]
  rw [this]

lemma qdens_periodic_one (L : ℝ) : Function.Periodic (Qdens L) 1 := by
  have := (qdens_periodic L).nat_mul 3
  simpa using this

lemma integral_qdens_one {L : ℝ} (hL : 0 < L) : ∫ t in (0 : ℝ)..1, Qdens L t = 1 := by
  unfold Qdens
  rw [intervalIntegral.integral_div]
  exact div_self (zpart_pos hL).ne'

lemma qdens_ii (L a b : ℝ) : IntervalIntegrable (Qdens L) volume a b :=
  (continuous_qdens L).intervalIntegrable a b

lemma hasDerivAt_aprim (L s : ℝ) : HasDerivAt (Aprim L) (Qdens L s) s :=
  ((continuous_qdens L).integral_hasStrictDerivAt 0 s).hasDerivAt

lemma integral_qdens_third {L : ℝ} (hL : 0 < L) : ∫ t in (0 : ℝ)..1 / 3, Qdens L t = 1 / 3 := by
  have h := (qdens_periodic L).intervalIntegral_add_zsmul_eq 3 0 (qdens_ii L)
  have e : (0 : ℝ) + (3 : ℤ) • (1 / 3 : ℝ) = 1 := by simp
  rw [e] at h
  rw [integral_qdens_one hL] at h
  simp only [zero_add, zsmul_eq_mul] at h
  push_cast at h
  linarith

lemma aprim_add_third {L : ℝ} (hL : 0 < L) (s : ℝ) : Aprim L (s + 1 / 3) = Aprim L s + 1 / 3 := by
  unfold Aprim
  rw [← intervalIntegral.integral_add_adjacent_intervals (qdens_ii L 0 s) (qdens_ii L s (s + 1 / 3))]
  congr 1
  have := (qdens_periodic L).intervalIntegral_add_eq s 0
  rw [this, zero_add]
  exact integral_qdens_third hL


lemma aprim_add_nat_third {L : ℝ} (hL : 0 < L) (s : ℝ) (n : ℕ) :
    Aprim L (s + n * (1 / 3)) = Aprim L s + n * (1 / 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : s + ((n + 1 : ℕ) : ℝ) * (1 / 3) = (s + n * (1 / 3)) + 1 / 3 := by push_cast; ring
    rw [e, aprim_add_third hL, ih]; push_cast; ring

/-- The phase `θ_{L,ε}(x) = A_L(2x) - 1/6 + ε g(6x)` (a real lift). -/
noncomputable def theta (L ε x : ℝ) : ℝ := Aprim L (2 * x) - 1 / 6 + ε * gT (pt (6 * x))

/-- The a.e. derivative `θ' = 2 Q_L(2x) + 6 ε g'(6x)`, with `g' = h - c`. -/
noncomputable def dtheta (L ε x : ℝ) : ℝ :=
  2 * Qdens L (2 * x) + 6 * ε * (hSum (pt (6 * x)) - hMean)

lemma theta_pt_eq (L ε x : ℝ) :
    theta L ε x = Aprim L (2 * x) - 1 / 6 + ε * gLine (6 * x) := by
  unfold theta; rw [Spikes.gT_pt]

lemma dtheta_eq (L ε x : ℝ) :
    dtheta L ε x = 2 * Qdens L (2 * x) + 6 * ε * fLine (6 * x) := rfl

lemma fLine6_ii (a b : ℝ) : IntervalIntegrable (fun x => fLine (6 * x)) volume a b := by
  have := (Spikes.fLine_ii (6 * a) (6 * b)).comp_mul_left (c := 6) enorm_ne_top enorm_ne_top
  simpa [mul_div_cancel_left₀ _ (by norm_num : (6 : ℝ) ≠ 0)] using this

lemma dtheta_ii (L ε a b : ℝ) : IntervalIntegrable (dtheta L ε) volume a b := by
  have h1 : IntervalIntegrable (fun x => 2 * Qdens L (2 * x)) volume a b :=
    (continuous_const.mul ((continuous_qdens L).comp (continuous_const.mul continuous_id))).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun x => fLine (6 * x)) volume a b := fLine6_ii a b
  have h3 := h1.add (h2.const_mul (6 * ε))
  refine h3.congr ?_
  intro x _
  simp only [dtheta_eq]

lemma theta_eq_integral (L ε x : ℝ) :
    theta L ε x = -1 / 6 + ∫ t in (0 : ℝ)..x, dtheta L ε t := by
  have h1 : IntervalIntegrable (fun x => 2 * Qdens L (2 * x)) volume 0 x :=
    (continuous_const.mul ((continuous_qdens L).comp (continuous_const.mul continuous_id))).intervalIntegrable 0 x
  have h2 : IntervalIntegrable (fun x => fLine (6 * x)) volume 0 x := fLine6_ii 0 x
  have e : ∫ t in (0 : ℝ)..x, dtheta L ε t =
      (∫ t in (0 : ℝ)..x, 2 * Qdens L (2 * t)) + 6 * ε * ∫ t in (0 : ℝ)..x, fLine (6 * t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h1 (h2.const_mul (6 * ε))]
    exact intervalIntegral.integral_congr fun t _ => by simp only [dtheta_eq]
  have a1 : ∫ t in (0 : ℝ)..x, 2 * Qdens L (2 * t) = Aprim L (2 * x) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun t => Qdens L t)
      (by norm_num : (2 : ℝ) ≠ 0)]
    unfold Aprim; simp
  have a2 : 6 * ∫ t in (0 : ℝ)..x, fLine (6 * t) = gLine (6 * x) := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => fLine t) (by norm_num : (6 : ℝ) ≠ 0)]
    unfold gLine; simp
  rw [e, a1, theta_pt_eq]
  have : 6 * ε * ∫ t in (0 : ℝ)..x, fLine (6 * t) = ε * gLine (6 * x) := by rw [← a2]; ring
  rw [this]; ring

lemma continuous_theta (L ε : ℝ) : Continuous (theta L ε) := by
  have : theta L ε = fun x => -1 / 6 + ∫ t in (0 : ℝ)..x, dtheta L ε t := funext (theta_eq_integral L ε)
  rw [this]
  exact continuous_const.add (intervalIntegral.continuous_primitive (fun a b => dtheta_ii L ε a b) 0)

lemma ae_hasDerivAt_theta (L ε : ℝ) : ∀ᵐ x : ℝ, HasDerivAt (theta L ε) (dtheta L ε x) x := by
  have hloc : LocallyIntegrable (dtheta L ε) volume := by
    intro x
    exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 (dtheta_ii L ε (x - 1) (x + 1))⟩
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with t ht
  have := (ht 0).const_add (-1 / 6)
  have e : theta L ε = fun x => -1 / 6 + ∫ t in (0 : ℝ)..x, dtheta L ε t := funext (theta_eq_integral L ε)
  rw [e]; exact this

lemma ac_theta (L ε : ℝ) : AbsolutelyContinuousOnInterval (theta L ε) 0 1 := by
  have h := (dtheta_ii L ε 0 1).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have e : theta L ε = fun x => -1 / 6 + ∫ t in (0 : ℝ)..x, dtheta L ε t := funext (theta_eq_integral L ε)
  rw [e]
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (-1 / 6 : ℝ)) 0 1 :=
    (contDiffOn_const (c := (-1 / 6 : ℝ)) (n := 1) (s := uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  exact hc.add h

lemma theta_add_one {L : ℝ} (hL : 0 < L) (ε x : ℝ) : theta L ε (x + 1) = theta L ε x + 2 := by
  have e1 : Aprim L (2 * (x + 1)) = Aprim L (2 * x) + 2 := by
    have := aprim_add_nat_third hL (2 * x) 6
    have e : 2 * (x + 1) = 2 * x + ((6 : ℕ) : ℝ) * (1 / 3) := by push_cast; ring
    rw [e, this]; push_cast; ring
  have e2 : gT (pt (6 * (x + 1))) = gT (pt (6 * x)) := by
    have : 6 * (x + 1) = 6 * x + ((6 : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    have h6 : pt (6 * x + ((6 : ℕ) : ℝ)) = pt (6 * x) := by
      have := Spikes.pt_add_int (6 * x) 6
      simpa using this
    rw [h6]
  unfold theta; rw [e1, e2]; ring


/-! ### The unit feature -/

/-- Rotation by `π/2` in `ℝ²`. -/
noncomputable def Jrot (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := !₂[-v 1, v 0]

/-- The feature `U_{L,ε}(x) = (cos 2πθ(x), sin 2πθ(x))` on the real line. -/
noncomputable def Ureal (L ε x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * theta L ε x), Real.sin (2 * π * theta L ε x)]

/-- The feature as a function on the torus `Torus 1`. -/
noncomputable def Ufeat (L ε : ℝ) (y : Torus 1) : EuclideanSpace ℝ (Fin 2) :=
  Ureal L ε (SharpLSI.secT y 0)

/-- The a.e. derivative of the phase as a function on the torus. -/
noncomputable def dthetaT (L ε : ℝ) (y : Torus 1) : ℝ := dtheta L ε (SharpLSI.secT y 0)

/-- The a.e. derivative `U' = 2π θ' J U` as a function on the torus. -/
noncomputable def Uprime (L ε : ℝ) (y : Torus 1) : EuclideanSpace ℝ (Fin 2) :=
  (2 * π * dthetaT L ε y) • Jrot (Ufeat L ε y)

@[simp] lemma Ureal_zero (L ε x : ℝ) : Ureal L ε x 0 = Real.cos (2 * π * theta L ε x) := by
  simp [Ureal]

@[simp] lemma Ureal_one (L ε x : ℝ) : Ureal L ε x 1 = Real.sin (2 * π * theta L ε x) := by
  simp [Ureal]

lemma Ureal_periodic {L : ℝ} (hL : 0 < L) (ε : ℝ) : Function.Periodic (Ureal L ε) 1 := by
  intro x
  have h : 2 * π * theta L ε (x + 1) = 2 * π * theta L ε x + (2 : ℕ) * (2 * π) := by
    rw [theta_add_one hL]; push_cast; ring
  unfold Ureal
  rw [h, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

lemma norm_Ureal (L ε x : ℝ) : ‖Ureal L ε x‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

lemma continuous_Ureal (L ε : ℝ) : Continuous (Ureal L ε) := by
  have h := continuous_theta L ε
  have h2 : Continuous fun x : ℝ => (fun i : Fin 2 => if i = 0 then Real.cos (2 * π * theta L ε x)
      else Real.sin (2 * π * theta L ε x)) := by
    refine continuous_pi fun i => ?_
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] <;> fun_prop
  have h3 := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp h2
  convert h3 using 1
  funext x
  ext i
  fin_cases i <;> simp [Ureal]

lemma hasDerivAt_Ureal (L ε x : ℝ) (hx : HasDerivAt (theta L ε) (dtheta L ε x) x) :
    HasDerivAt (fun t => Ureal L ε t 0) (-(2 * π * dtheta L ε x) * Real.sin (2 * π * theta L ε x)) x ∧
    HasDerivAt (fun t => Ureal L ε t 1) ((2 * π * dtheta L ε x) * Real.cos (2 * π * theta L ε x)) x := by
  have h := (hx.const_mul (2 * π))
  refine ⟨?_, ?_⟩
  · simp only [Ureal_zero]
    have := h.cos
    convert this using 1; ring
  · simp only [Ureal_one]
    have := h.sin
    convert this using 1; ring


/-! ### Transfer to the torus -/

lemma haar_eq_map :
    haar 1 = Measure.map (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm volume := by
  have h1 := UnitAddCircle.measurePreserving_mk 0
  simp only [zero_add] at h1
  have h2 := Spikes.measurePreserving_pt.map_eq
  rw [← h2, ← h1.map_eq, Measure.map_map]
  · rfl
  · exact MeasurableEquiv.measurable _
  · exact AddCircle.measurable_mk'

/-- The covering maps `y ↦ n • y` of `Torus 1` preserve the Haar probability measure. -/
lemma mp_zsmul (n : ℤ) (hn : n ≠ 0) :
    MeasurePreserving (fun y : Torus 1 => n • y) (haar 1) (haar 1) := by
  have e1 : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm volume
      (haar 1) := ⟨MeasurableEquiv.measurable _, haar_eq_map.symm⟩
  have e2 : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle) (haar 1) volume := by
    have := e1.symm (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm
    simpa using this
  have e3 : MeasurePreserving (fun x : UnitAddCircle => n • x) volume volume :=
    Measure.measurePreserving_zsmul volume hn
  have := (e1.comp e3).comp e2
  convert this using 1
  funext y
  funext i
  rw [Subsingleton.elim i 0]
  simp

lemma pt_secT (y : Torus 1) : pt (SharpLSI.secT y 0) = y := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact congrFun (SharpLSI.liftT_secT y) 0

lemma zsmul_pt (n : ℤ) (x : ℝ) : n • pt x = pt (n * x) := by
  funext i
  show n • (x : AddCircle (1 : ℝ)) = ((n * x : ℝ) : AddCircle (1 : ℝ))
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]

lemma torusDist_pt_le (s t : ℝ) : DGPS.torusDist (pt s) (pt t) ≤ |s - t| := by
  have := DGPS.torusDist_liftT_le (d := 1) (fun _ => s) (fun _ => t)
  rw [Fin.sum_univ_one, Real.sqrt_sq_eq_abs] at this
  exact this

/-- The density `Q_L` as a function on the torus. -/
noncomputable def Qtor (L : ℝ) (y : Torus 1) : ℝ := Qdens L (SharpLSI.secT y 0)

lemma Qtor_pt (L t : ℝ) : Qtor L (pt t) = Qdens L t :=
  Spikes.periodic_secT (qdens_periodic_one L) t

lemma measurable_Qtor (L : ℝ) : Measurable (Qtor L) :=
  Spikes.measurable_comp_secT (continuous_qdens L)

lemma dtheta_periodic (L ε x : ℝ) : dtheta L ε (x + 1) = dtheta L ε x := by
  unfold dtheta
  have e1 : 2 * (x + 1) = 2 * x + 2 := by ring
  have e2 : Qdens L (2 * x + 2) = Qdens L (2 * x) := by
    have := (qdens_periodic_one L).nat_mul 2 (2 * x)
    simpa using this
  have e3 : pt (6 * (x + 1)) = pt (6 * x) := by
    have : 6 * (x + 1) = 6 * x + ((6 : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    simpa using Spikes.pt_add_int (6 * x) 6
  rw [e1, e2, e3]

lemma dthetaT_pt (L ε t : ℝ) : dthetaT L ε (pt t) = dtheta L ε t :=
  Spikes.periodic_secT (dtheta_periodic L ε) t

lemma dthetaT_eq (L ε : ℝ) (y : Torus 1) :
    dthetaT L ε y = 2 * Qtor L ((2 : ℤ) • y) + 6 * ε * (hSum ((6 : ℤ) • y) - hMean) := by
  obtain ⟨s, rfl⟩ : ∃ s, y = pt s := ⟨_, (pt_secT y).symm⟩
  rw [dthetaT_pt, zsmul_pt, zsmul_pt, Qtor_pt]
  simp [dtheta]

lemma Ufeat_pt {L : ℝ} (hL : 0 < L) (ε t : ℝ) : Ufeat L ε (pt t) = Ureal L ε t := by
  unfold Ufeat
  obtain ⟨n, hn⟩ := Spikes.secT_pt_exists t
  have := ((Ureal_periodic hL ε).int_mul n) (SharpLSI.secT (pt t) 0)
  rw [mul_one] at this
  rw [← this, ← hn]

lemma norm_Ufeat (L ε : ℝ) (y : Torus 1) : ‖Ufeat L ε y‖ = 1 := norm_Ureal _ _ _

lemma Uprime_pt {L : ℝ} (hL : 0 < L) (ε t : ℝ) :
    Uprime L ε (pt t) = (2 * π * dtheta L ε t) • Jrot (Ureal L ε t) := by
  unfold Uprime
  rw [dthetaT_pt, Ufeat_pt hL]


/-! ### Hölder regularity -/

lemma norm_Ureal_sub_le (L ε a b : ℝ) :
    ‖Ureal L ε a - Ureal L ε b‖ ≤ 2 * π * |theta L ε a - theta L ε b| := by
  set u := 2 * π * theta L ε a
  set v := 2 * π * theta L ε b
  have h2 : ‖Ureal L ε a - Ureal L ε b‖ ^ 2 = 2 - 2 * Real.cos (u - v) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, Ureal_zero, Ureal_one, Real.norm_eq_abs, sq_abs]
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq v]
  have h3 : 2 - 2 * Real.cos (u - v) ≤ (u - v) ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := u - v)]
  have e : u - v = 2 * π * (theta L ε a - theta L ε b) := by simp only [u, v]; ring
  have h4 : ‖Ureal L ε a - Ureal L ε b‖ ^ 2 ≤ (2 * π * |theta L ε a - theta L ε b|) ^ 2 := by
    rw [h2, mul_pow, sq_abs]
    calc 2 - 2 * Real.cos (u - v) ≤ (u - v) ^ 2 := h3
      _ = _ := by rw [e]; ring
  exact le_of_sq_le_sq h4 (by positivity)

lemma qdens_le {L : ℝ} (hL : 0 < L) (s : ℝ) : Qdens L s ≤ Real.exp L / Zpart L := by
  unfold Qdens
  apply div_le_div_of_nonneg_right _ (zpart_pos hL).le
  apply Real.exp_le_exp.2
  nlinarith [Real.cos_le_one (6 * π * s)]

lemma abs_aprim_sub_le {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    |Aprim L s - Aprim L t| ≤ Real.exp L / Zpart L * |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Aprim L) (s := Set.univ)
    (C := Real.exp L / Zpart L) (fun x _ => (hasDerivAt_aprim L x).differentiableAt)
    (fun x _ => by
      rw [(hasDerivAt_aprim L x).deriv, Real.norm_eq_abs, abs_of_pos (qdens_pos hL x)]
      exact qdens_le hL x) convex_univ (Set.mem_univ t) (Set.mem_univ s)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- The Hölder constant of the primitive `g`, from RUF004. -/
noncomputable def holderConst (α : ℝ) : ℝ :=
  max (modulusConst * Real.exp (2 / (3 * Real.sqrt (3 * (1 - α)))))
    (2 * hMean * Real.exp (8 * α))

lemma holderConst_nonneg (α : ℝ) : 0 ≤ holderConst α :=
  le_max_of_le_right (by have := Spikes.hMean_pos; positivity)

lemma abs_gT_sub_le {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (x y : Torus 1) :
    |gT x - gT y| ≤ holderConst α * DGPS.torusDist x y ^ α :=
  (Spikes.explicit_sub_lipschitz_modulus_and_every_strict_holder_exponent.2.2 α h0 h1 x y)

lemma torusDist_nonneg' (x y : Torus 1) : 0 ≤ DGPS.torusDist x y := by
  unfold DGPS.torusDist; exact Real.sqrt_nonneg _

lemma torusDist_le_half (x y : Torus 1) : DGPS.torusDist x y ≤ 1 / 2 := by
  rw [Spikes.torusDist_one]
  have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x 0 - y 0) one_ne_zero
  simpa using this


/-- Explicit Hölder bound: `[U]_α ≤ 2π (2 ‖Q_L‖_∞ + |ε| 6^α [g]_α)`, with `‖Q_L‖_∞ = e^L / Z_L`. -/
lemma holder_Ufeat {L : ℝ} (hL : 0 < L) (ε : ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (x y : Torus 1) :
    ‖Ufeat L ε x - Ufeat L ε y‖ ≤
      2 * π * (2 * (Real.exp L / Zpart L) + |ε| * 6 ^ α * holderConst α) *
        DGPS.torusDist x y ^ α := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := Spikes.exists_lifts x y
  rw [Ufeat_pt hL, Ufeat_pt hL]
  set δ := DGPS.torusDist (pt a) (pt b) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ, DGPS.torusDist]; exact Real.sqrt_nonneg _
  have hδ1 : δ ≤ 1 / 2 := torusDist_le_half _ _
  have hba : |a - b| = δ := by rw [abs_sub_comm]; exact hab
  have hK : 0 ≤ Real.exp L / Zpart L := (div_pos (Real.exp_pos _) (zpart_pos hL)).le
  have hC := holderConst_nonneg α
  have hδα : δ ≤ δ ^ α := by
    rcases hδ0.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow h0.ne']
    · calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ α := Real.rpow_le_rpow_of_exponent_ge h (by linarith) h1.le
  have hA : |Aprim L (2 * a) - Aprim L (2 * b)| ≤ Real.exp L / Zpart L * (2 * δ) := by
    refine (abs_aprim_sub_le hL _ _).trans ?_
    have : |2 * a - 2 * b| = 2 * δ := by rw [← hba, ← mul_sub, abs_mul]; norm_num
    rw [this]
  have hG : |gLine (6 * a) - gLine (6 * b)| ≤ holderConst α * (6 ^ α * δ ^ α) := by
    have e1 := abs_gT_sub_le h0 h1 (pt (6 * a)) (pt (6 * b))
    rw [Spikes.gT_pt, Spikes.gT_pt] at e1
    refine e1.trans ?_
    apply mul_le_mul_of_nonneg_left _ hC
    rw [← Real.mul_rpow (by norm_num) hδ0]
    apply Real.rpow_le_rpow (torusDist_nonneg' _ _) _ h0.le
    refine (torusDist_pt_le _ _).trans ?_
    rw [← mul_sub, abs_mul, hba]; norm_num
  have hθ : |theta L ε a - theta L ε b| ≤
      (2 * (Real.exp L / Zpart L) + |ε| * 6 ^ α * holderConst α) * δ ^ α := by
    have e : theta L ε a - theta L ε b =
        (Aprim L (2 * a) - Aprim L (2 * b)) + ε * (gLine (6 * a) - gLine (6 * b)) := by
      rw [theta_pt_eq, theta_pt_eq]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h6 : 0 ≤ (6 : ℝ) ^ α := by positivity
    calc _ ≤ Real.exp L / Zpart L * (2 * δ) + |ε| * (holderConst α * (6 ^ α * δ ^ α)) :=
          add_le_add hA (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ ≤ Real.exp L / Zpart L * (2 * δ ^ α) + |ε| * (holderConst α * (6 ^ α * δ ^ α)) := by
          gcongr
      _ = _ := by ring
  calc ‖Ureal L ε a - Ureal L ε b‖ ≤ 2 * π * |theta L ε a - theta L ε b| := norm_Ureal_sub_le _ _ _ _
    _ ≤ 2 * π * ((2 * (Real.exp L / Zpart L) + |ε| * 6 ^ α * holderConst α) * δ ^ α) :=
        mul_le_mul_of_nonneg_left hθ (by positivity)
    _ = _ := by ring

lemma continuous_Ufeat {L : ℝ} (hL : 0 < L) (ε : ℝ) : Continuous (Ufeat L ε) := by
  rw [continuous_iff_continuousAt]
  intro x
  set C := 2 * π * (2 * (Real.exp L / Zpart L) + |ε| * 6 ^ (1 / 2 : ℝ) * holderConst (1 / 2)) + 1
    with hCdef
  have hK : 0 ≤ Real.exp L / Zpart L := (div_pos (Real.exp_pos _) (zpart_pos hL)).le
  have hCpos : 0 < C := by
    have := holderConst_nonneg (1 / 2)
    positivity
  have hb := DGPS.torusDist_metric.2.2.2.2 x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro e he
  have hδ : 0 < (e / C) ^ 2 := by positivity
  have : ∀ᶠ y in nhds x, DGPS.torusDist x y < (e / C) ^ 2 := hb.mem_of_mem hδ
  filter_upwards [this] with y hy
  rw [dist_eq_norm]
  have h := holder_Ufeat hL ε (α := 1 / 2) (by norm_num) (by norm_num) y x
  have hd : 0 ≤ DGPS.torusDist y x := by unfold DGPS.torusDist; exact Real.sqrt_nonneg _
  have hy' : DGPS.torusDist y x < (e / C) ^ 2 := by
    have : DGPS.torusDist y x = DGPS.torusDist x y := DGPS.torusDist_metric.2.1 _ _
    rwa [this]
  have h2 : DGPS.torusDist y x ^ (1 / 2 : ℝ) < e / C := by
    calc DGPS.torusDist y x ^ (1 / 2 : ℝ) < ((e / C) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_lt_rpow hd hy' (by norm_num)
      _ = e / C := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hM : 0 ≤ 2 * π * (2 * (Real.exp L / Zpart L) + |ε| * 6 ^ (1 / 2 : ℝ) * holderConst (1 / 2)) := by
    have := holderConst_nonneg (1 / 2)
    positivity
  calc ‖Ufeat L ε y - Ufeat L ε x‖ ≤ _ := h
    _ ≤ C * DGPS.torusDist y x ^ (1 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); rw [hCdef]; linarith
    _ < C * (e / C) := mul_lt_mul_of_pos_left h2 hCpos
    _ = e := by field_simp


/-! ### Sobolev regularity -/

lemma norm_Jrot (v : EuclideanSpace ℝ (Fin 2)) : ‖Jrot v‖ = ‖v‖ := by
  simp only [Jrot, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [add_comm]

lemma norm_Uprime (L ε : ℝ) (y : Torus 1) : ‖Uprime L ε y‖ = 2 * π * |dthetaT L ε y| := by
  unfold Uprime
  rw [norm_smul, norm_Jrot, norm_Ufeat, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * π)]

/-- The pulled-back density `y ↦ Q_L(2y)`. -/
noncomputable def Q2 (L : ℝ) (y : Torus 1) : ℝ := Qtor L ((2 : ℤ) • y)

/-- The pulled-back spike part `y ↦ h(6y) - c`. -/
noncomputable def G6 (y : Torus 1) : ℝ := hSum ((6 : ℤ) • y) - hMean

lemma dthetaT_eq' (L ε : ℝ) (y : Torus 1) : dthetaT L ε y = 2 * Q2 L y + 6 * ε * G6 y := by
  rw [dthetaT_eq]; rfl

lemma measurable_Q2 (L : ℝ) : Measurable (Q2 L) :=
  (measurable_Qtor L).comp (mp_zsmul 2 (by norm_num)).measurable

lemma measurable_G6 : Measurable G6 :=
  (Spikes.hSum_meas.comp (mp_zsmul 6 (by norm_num)).measurable).sub measurable_const

lemma measurable_dthetaT (L ε : ℝ) : Measurable (dthetaT L ε) := by
  have : dthetaT L ε = fun y => 2 * Q2 L y + 6 * ε * G6 y := funext (dthetaT_eq' L ε)
  rw [this]
  exact (measurable_const.mul (measurable_Q2 L)).add (measurable_const.mul measurable_G6)

lemma memLp_Qtor_top {L : ℝ} (hL : 0 < L) : MemLp (Qtor L) ⊤ (haar 1) := by
  refine memLp_top_of_bound (measurable_Qtor L).aestronglyMeasurable (Real.exp L / Zpart L)
    (Filter.Eventually.of_forall fun y => ?_)
  unfold Qtor
  rw [Real.norm_eq_abs, abs_of_pos (qdens_pos hL _)]
  exact qdens_le hL _

lemma memLp_Q2 {L : ℝ} (hL : 0 < L) (p : ENNReal) : MemLp (Q2 L) p (haar 1) :=
  ((memLp_Qtor_top hL).mono_exponent le_top).comp_measurePreserving (mp_zsmul 2 (by norm_num))

lemma memLp_G6 {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) : MemLp G6 (ENNReal.ofReal p) (haar 1) :=
  (Spikes.memLp_hSum_sub_mean hp hp2).comp_measurePreserving (mp_zsmul 6 (by norm_num))

lemma eLpNorm_Q2 (L : ℝ) (p : ENNReal) : eLpNorm (Q2 L) p (haar 1) = eLpNorm (Qtor L) p (haar 1) :=
  eLpNorm_comp_measurePreserving (measurable_Qtor L).aestronglyMeasurable (mp_zsmul 2 (by norm_num))

lemma eLpNorm_G6 (p : ENNReal) :
    eLpNorm G6 p (haar 1) = eLpNorm (fun y => hSum y - hMean) p (haar 1) :=
  eLpNorm_comp_measurePreserving (g := fun y => hSum y - hMean)
    (Spikes.hSum_meas.sub measurable_const).aestronglyMeasurable (mp_zsmul 6 (by norm_num))

lemma memLp_dthetaT {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp (dthetaT L ε) (ENNReal.ofReal p) (haar 1) := by
  have : dthetaT L ε = fun y => 2 * Q2 L y + 6 * ε * G6 y := funext (dthetaT_eq' L ε)
  rw [this]
  exact ((memLp_Q2 hL _).const_mul 2).add ((memLp_G6 hp hp2).const_mul (6 * ε))

lemma eLpNorm_Uprime_le (L ε : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun y => ‖Uprime L ε y‖) (ENNReal.ofReal p) (haar 1) ≤
      ENNReal.ofReal (2 * π) *
        (2 * eLpNorm (Qtor L) (ENNReal.ofReal p) (haar 1) +
          ENNReal.ofReal (6 * |ε|) *
            eLpNorm (fun y => hSum y - hMean) (ENNReal.ofReal p) (haar 1)) := by
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have e : (fun y => ‖Uprime L ε y‖) =
      fun y => ‖(2 * π) • ((2 : ℝ) • Q2 L y + (6 * ε) • G6 y)‖ := by
    funext y
    rw [norm_Uprime, dthetaT_eq', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * π),
      Real.norm_eq_abs]
    simp only [smul_eq_mul]
  have hmeas : AEStronglyMeasurable (fun y => (2 * π) • ((2 : ℝ) • Q2 L y + (6 * ε) • G6 y)) (haar 1) :=
    (((measurable_Q2 L).const_smul (2 : ℝ)).add (measurable_G6.const_smul (6 * ε))).const_smul (2 * π) |>.aestronglyMeasurable
  have hn : eLpNorm (fun y => ‖(2 * π) • ((2 : ℝ) • Q2 L y + (6 * ε) • G6 y)‖)
      (ENNReal.ofReal p) (haar 1) =
      eLpNorm (fun y => (2 * π) • ((2 : ℝ) • Q2 L y + (6 * ε) • G6 y)) (ENNReal.ofReal p) (haar 1) :=
    eLpNorm_norm _ hmeas
  rw [e, hn, show (fun y => (2 * π) • ((2 : ℝ) • Q2 L y + (6 * ε) • G6 y)) =
    (2 * π) • (fun y => (2 : ℝ) • Q2 L y + (6 * ε) • G6 y) from rfl, eLpNorm_const_smul]
  have h3 := eLpNorm_add_le (f := fun y => (2 : ℝ) • Q2 L y) (g := fun y => (6 * ε) • G6 y) (μ := haar 1) hp1
  have h4 : eLpNorm (fun y => (2 : ℝ) • Q2 L y + (6 * ε) • G6 y) (ENNReal.ofReal p) (haar 1) ≤
      2 * eLpNorm (Qtor L) (ENNReal.ofReal p) (haar 1) +
        ENNReal.ofReal (6 * |ε|) *
          eLpNorm (fun y => hSum y - hMean) (ENNReal.ofReal p) (haar 1) := by
    refine h3.trans ?_
    have a1 : eLpNorm (fun y => (2 : ℝ) • Q2 L y) (ENNReal.ofReal p) (haar 1) =
        2 * eLpNorm (Qtor L) (ENNReal.ofReal p) (haar 1) := by
      have := eLpNorm_const_smul (μ := haar 1) (p := ENNReal.ofReal p) (2 : ℝ) (Q2 L)
      rw [eLpNorm_Q2] at this
      have e2 : ‖(2 : ℝ)‖ₑ = 2 := by
        rw [Real.enorm_eq_ofReal_abs]; simp
      rw [e2] at this
      exact this
    have a2 : eLpNorm (fun y => (6 * ε) • G6 y) (ENNReal.ofReal p) (haar 1) =
        ENNReal.ofReal (6 * |ε|) *
          eLpNorm (fun y => hSum y - hMean) (ENNReal.ofReal p) (haar 1) := by
      have := eLpNorm_const_smul (μ := haar 1) (p := ENNReal.ofReal p) (6 * ε) G6
      rw [eLpNorm_G6] at this
      rw [show (fun y => (6 * ε) • G6 y) = (6 * ε) • G6 from rfl, this]
      congr 1
      rw [Real.enorm_eq_ofReal_abs, abs_mul]; norm_num
    exact (add_le_add a1.le a2.le)
  have : ‖(2 * π : ℝ)‖ₑ = ENNReal.ofReal (2 * π) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity)]
  rw [this]
  exact mul_le_mul_right h4 _


/-! ### Weak derivative of the unit feature -/

lemma ac_Ureal (L ε : ℝ) (j : Fin 2) : AbsolutelyContinuousOnInterval (fun t => Ureal L ε t j) 0 1 := by
  have h := (ac_theta L ε).const_mul (2 * π)
  fin_cases j
  · have := Real.lipschitzWith_cos.comp_absolutelyContinuousOnInterval h
    simpa [Function.comp_def] using this
  · have := Real.lipschitzWith_sin.comp_absolutelyContinuousOnInterval h
    simpa [Function.comp_def] using this

/-- Abstract weak integration by parts along the lift `pt`. -/
lemma weak_ibp_of_ac {F f : ℝ → ℝ} (hFper : Function.Periodic F 1)
    (hFac : AbsolutelyContinuousOnInterval F 0 1) (hae : ∀ᵐ t : ℝ, HasDerivAt F (f t) t)
    {U c : Torus 1 → ℝ} (hU : ∀ t, U (pt t) = F t) (hc : ∀ t, c (pt t) = f t)
    (hUm : AEStronglyMeasurable U (haar 1)) (hcm : AEStronglyMeasurable c (haar 1))
    {φ : Torus 1 → ℝ} (hφ : DGPS.IsSmoothPeriodic φ) :
    ∫ y, U y * DGPS.coordPartial 0 φ y ∂haar 1 = -∫ y, c y * φ y ∂haar 1 := by
  set ψ : ℝ → ℝ := fun s => φ (pt s) with hψdef
  have hψ := Spikes.contDiff_psi hφ
  have hL : AEStronglyMeasurable (fun y => U y * DGPS.coordPartial 0 φ y) (haar 1) :=
    hUm.mul (Spikes.measurable_coordPartial hφ).aestronglyMeasurable
  have hR : AEStronglyMeasurable (fun y => c y * φ y) (haar 1) :=
    hcm.mul (Spikes.measurable_phi hφ).aestronglyMeasurable
  rw [Spikes.integral_haar_eq hL, Spikes.integral_haar_eq hR,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  have hcp : ∀ t : ℝ, DGPS.coordPartial 0 φ (pt t) = deriv ψ t := fun t => by
    rw [Spikes.coordPartial_eq hφ]
    exact Spikes.periodic_secT (Spikes.deriv_psi_periodic) t
  have e1 : ∫ t in (0 : ℝ)..1, U (pt t) * DGPS.coordPartial 0 φ (pt t) =
      ∫ t in (0 : ℝ)..1, F t * deriv ψ t :=
    intervalIntegral.integral_congr fun t _ => by simp only [hU, hcp]
  have e2 : ∫ t in (0 : ℝ)..1, c (pt t) * φ (pt t) = ∫ t in (0 : ℝ)..1, f t * ψ t :=
    intervalIntegral.integral_congr fun t _ => by simp only [hc, hψdef]
  rw [e1, e2]
  have hψac : AbsolutelyContinuousOnInterval ψ 0 1 :=
    (hψ.contDiffOn (s := uIcc 0 1)).absolutelyContinuousOnInterval
  have key := hFac.integral_mul_deriv_eq_deriv_mul hψac
  have hae' : ∫ x in (0 : ℝ)..1, deriv F x * ψ x = ∫ x in (0 : ℝ)..1, f x * ψ x :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hae] with t ht _
      rw [ht.deriv])
  have hF1 : F 1 = F 0 := by simpa using hFper 0
  have hψ1 : ψ 1 = ψ 0 := by simp only [hψdef]; simpa using congrArg φ (Spikes.pt_add_one 0)
  rw [key, hae', hF1, hψ1]
  ring


lemma Uprime_zero (L ε : ℝ) (y : Torus 1) :
    Uprime L ε y 0 = -(2 * π * dthetaT L ε y) * Ufeat L ε y 1 := by
  simp [Uprime, Jrot]

lemma Uprime_one (L ε : ℝ) (y : Torus 1) :
    Uprime L ε y 1 = (2 * π * dthetaT L ε y) * Ufeat L ε y 0 := by
  simp [Uprime, Jrot]

lemma ae_hasDerivAt_Ureal_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) :
    ∀ᵐ t : ℝ, HasDerivAt (fun s => Ureal L ε s j) (Uprime L ε (pt t) j) t := by
  filter_upwards [ae_hasDerivAt_theta L ε] with t ht
  have h := hasDerivAt_Ureal L ε t ht
  fin_cases j
  · show HasDerivAt (fun s => Ureal L ε s 0) (Uprime L ε (pt t) 0) t
    rw [Uprime_zero, Ufeat_pt hL, dthetaT_pt]
    simpa using h.1
  · show HasDerivAt (fun s => Ureal L ε s 1) (Uprime L ε (pt t) 1) t
    rw [Uprime_one, Ufeat_pt hL, dthetaT_pt]
    simpa using h.2

lemma measurable_Ufeat_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) :
    Measurable fun y => Ufeat L ε y j :=
  ((continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ) |>.comp
    (continuous_Ufeat hL ε))).measurable

lemma measurable_Uprime_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) :
    Measurable fun y => Uprime L ε y j := by
  have h0 := measurable_Ufeat_comp hL ε 0
  have h1 := measurable_Ufeat_comp hL ε 1
  have hd := measurable_dthetaT L ε
  have hc : Measurable fun y => 2 * π * dthetaT L ε y := measurable_const.mul hd
  fin_cases j
  · simp only [Fin.zero_eta, Uprime_zero]
    exact hc.neg.mul h1
  · simp only [Fin.mk_one, Uprime_one]
    exact hc.mul h0

lemma isWeakGradientLp_Ufeat {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2)
    (j : Fin 2) :
    IsWeakGradientLp (ENNReal.ofReal p) (fun y => Ufeat L ε y j)
      (fun y => (!₂[Uprime L ε y j] : Tangent 1)) := by
  have hmu := measurable_Ufeat_comp hL ε j
  have hmc := measurable_Uprime_comp hL ε j
  refine ⟨?_, ?_, ?_⟩
  · refine MemLp.of_bound hmu.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    calc |Ufeat L ε y j| = ‖Ufeat L ε y j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Ufeat L ε y‖ := PiLp.norm_apply_le _ _
      _ = 1 := norm_Ufeat L ε y
  · have hg : Measurable fun y => (!₂[Uprime L ε y j] : Tangent 1) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp
        (measurable_pi_iff.2 fun i => by fin_cases i; simpa using hmc)
    refine MemLp.mono ((memLp_dthetaT hL ε hp hp2).const_mul (2 * π)) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h1 : ‖(!₂[Uprime L ε y j] : Tangent 1)‖ = |Uprime L ε y j| := by
      simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
    rw [h1, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
    calc |Uprime L ε y j| = ‖Uprime L ε y j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Uprime L ε y‖ := PiLp.norm_apply_le _ _
      _ = 2 * π * |dthetaT L ε y| := norm_Uprime L ε y
  · intro φ hφ j'
    have hj : j' = 0 := Subsingleton.elim _ _
    subst hj
    have := weak_ibp_of_ac (F := fun t => Ureal L ε t j) (f := fun t => Uprime L ε (pt t) j)
      (fun x => congrArg (fun v => v j) (Ureal_periodic hL ε x)) (ac_Ureal L ε j)
      (ae_hasDerivAt_Ureal_comp hL ε j) (U := fun y => Ufeat L ε y j)
      (c := fun y => Uprime L ε y j) (fun t => by simp only [Ufeat_pt hL])
      (fun t => rfl) hmu.aestronglyMeasurable hmc.aestronglyMeasurable hφ
    simpa using this

/-- **Complete phase and unit feature family** (RUF005).  For every `L > 0`: the density `Q_L` is
positive, smooth, `1/3`-periodic, bounded by `exp L / Z_L` (attained at `0`), and `A_L` satisfies
`A_L (s + 1/3) = A_L s + 1/3`.  For every `ε`: the phase `θ` satisfies `θ(x+1) = θ(x) + 2`, is
continuous and absolutely continuous with a.e. derivative `2 Q_L(2x) + 6 ε g'(6x)`; the feature
`U = (cos 2πθ, sin 2πθ)` is a continuous periodic unit vector field (on the line and on the torus,
compatible through `pt`) with a.e. derivative `2π θ' J U`; it is `α`-Hölder for every `0 < α < 1`
with the stated constant, and lies in `W^{1,p}` for every `1 ≤ p < 2` (componentwise weak gradient
`U'`), with `‖U'‖_p ≤ 2π (2‖Q_L‖_p + 6|ε|‖g'‖_p)`. -/
theorem complete_phase_and_unit_feature_family {L : ℝ} (hL : 0 < L) :
    (0 < Zpart L ∧ (∀ s, 0 < Qdens L s) ∧ ContDiff ℝ ∞ (Qdens L) ∧
      Function.Periodic (Qdens L) (1 / 3) ∧
      (∀ s, Aprim L (s + 1 / 3) = Aprim L s + 1 / 3) ∧
      (∀ s, Qdens L s ≤ Real.exp L / Zpart L) ∧ Qdens L 0 = Real.exp L / Zpart L) ∧
    ∀ ε : ℝ,
      ((∀ x, theta L ε (x + 1) = theta L ε x + 2) ∧ Continuous (theta L ε) ∧
        AbsolutelyContinuousOnInterval (theta L ε) 0 1 ∧
        (∀ᵐ x : ℝ, HasDerivAt (theta L ε) (dtheta L ε x) x) ∧
        (∀ x, dtheta L ε x = 2 * Qdens L (2 * x) + 6 * ε * (hSum (pt (6 * x)) - hMean))) ∧
      (Continuous (Ureal L ε) ∧ Function.Periodic (Ureal L ε) 1 ∧ (∀ x, ‖Ureal L ε x‖ = 1) ∧
        (∀ x, HasDerivAt (theta L ε) (dtheta L ε x) x →
          ∀ j : Fin 2, HasDerivAt (fun t => Ureal L ε t j)
            (((2 * π * dtheta L ε x) • Jrot (Ureal L ε x)) j) x)) ∧
      (Continuous (Ufeat L ε) ∧ (∀ y, ‖Ufeat L ε y‖ = 1) ∧
        (∀ t, Ufeat L ε (pt t) = Ureal L ε t) ∧
        (∀ y, Uprime L ε y = (2 * π * dthetaT L ε y) • Jrot (Ufeat L ε y))) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ x y : Torus 1,
        ‖Ufeat L ε x - Ufeat L ε y‖ ≤
          2 * π * (2 * (Real.exp L / Zpart L) + |ε| * 6 ^ α * holderConst α) *
            DGPS.torusDist x y ^ α) ∧
      (∀ p : ℝ, 1 ≤ p → p < 2 →
        (∀ j : Fin 2, IsWeakGradientLp (ENNReal.ofReal p) (fun y => Ufeat L ε y j)
          (fun y => (!₂[Uprime L ε y j] : Tangent 1))) ∧
        eLpNorm (fun y => ‖Uprime L ε y‖) (ENNReal.ofReal p) (haar 1) ≤
          ENNReal.ofReal (2 * π) *
            (2 * eLpNorm (Qtor L) (ENNReal.ofReal p) (haar 1) +
              ENNReal.ofReal (6 * |ε|) *
                eLpNorm (fun y => hSum y - hMean) (ENNReal.ofReal p) (haar 1))) := by
  refine ⟨⟨zpart_pos hL, qdens_pos hL, contDiff_qdens L, qdens_periodic L, aprim_add_third hL,
    qdens_le hL, ?_⟩, fun ε => ⟨⟨theta_add_one hL ε, continuous_theta L ε, ac_theta L ε,
    ae_hasDerivAt_theta L ε, fun x => rfl⟩, ⟨continuous_Ureal L ε, Ureal_periodic hL ε,
    norm_Ureal L ε, fun x hx j => ?_⟩, ⟨continuous_Ufeat hL ε, norm_Ufeat L ε, Ufeat_pt hL ε,
    fun y => rfl⟩, fun α h0 h1 => holder_Ufeat hL ε h0 h1, fun p hp hp2 =>
    ⟨isWeakGradientLp_Ufeat hL ε hp hp2, eLpNorm_Uprime_le L ε hp⟩⟩⟩
  · simp [Qdens]
  · have h := hasDerivAt_Ureal L ε x hx
    fin_cases j
    · simpa [Jrot] using h.1
    · simpa [Jrot] using h.2

end DGPS.Examples.RoughBoundary.Feature
