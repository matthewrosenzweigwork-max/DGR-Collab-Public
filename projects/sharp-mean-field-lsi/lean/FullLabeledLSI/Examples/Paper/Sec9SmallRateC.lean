import FullLabeledLSI.Examples.Paper.Sec9Regularity

/-!
# Lemma 9.6, part C: uniqueness of positive periodic solutions of the Euler ODE for small `r`

Lane C of the Section 9 formalization.  For two positive `C²` 1-periodic solutions `F, G` of
`y'' = y (B - r log y)` with `∫₀¹ F² = ∫₀¹ G² = 1`, `c ≤ F, G ≤ M` and `r M² < 4π² c²`, we have `F = G`.

Proof: `v = log F - log G`, `m = FG`, `W = F'G - FG' = m v'`, `W' = -r m v`; integration by parts
on the period gives `∫ m v'² = r ∫ m v²` and (for `r > 0`) `∫ m v = 0`; the circle Poincaré
inequality gives `∫ m v² ≤ (r M²/(4π² c²)) ∫ m v²`.
-/

open Set Filter Topology MeasureTheory
open scoped Real

namespace SharpLSI.FL.Ex.SR

open SharpLSI FL.Ex.Reg

/-! ### Circle Poincaré for `C¹` periodic functions on `[0,1]` -/

theorem integral_torus_eq {G : ℝ → ℝ} (hc : Continuous G) (hp : Function.Periodic G 1) :
    ∫ y : Torus 1, G (secT y 0) ∂haar 1 = ∫ x in (0 : ℝ)..1, G x := by
  have := intervalIntegral_lineT (g := fun y : Torus 1 => G (secT y 0))
    (BM.ofF hc).integrable.aestronglyMeasurable
  simp only [F_secT_lineT hp] at this
  exact this.symm


theorem periodic_deriv_of_hasDerivAt {v v1 : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v1 x) x)
    (hper : Function.Periodic v 1) : Function.Periodic v1 1 := by
  have : v1 = deriv v := funext fun x => (hv x).deriv.symm
  rw [this]
  exact periodic_deriv hper

theorem poincare_1d {v v1 : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v1 x) x) (hv1 : Continuous v1)
    (hper : Function.Periodic v 1) :
    4 * π ^ 2 * ((∫ x in (0 : ℝ)..1, v x ^ 2) - (∫ x in (0 : ℝ)..1, v x) ^ 2) ≤
      ∫ x in (0 : ℝ)..1, v1 x ^ 2 := by
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
  have hv1p := periodic_deriv_of_hasDerivAt hv hper
  set u : Torus 1 → ℝ := fun y => v (secT y 0) with hu
  set g : Torus 1 → Fin 1 → ℝ := fun y _ => v1 (secT y 0) with hg
  have hum : MemLp u 2 (haar 1) := (BM.ofF hvc).memLp
  have hgm : ∀ j, MemLp (fun y => g y j) 2 (haar 1) := fun j => (BM.ofF hv1).memLp
  have hC1 : ContDiff ℝ 1 (u ∘ liftT) := by
    have e : u ∘ liftT = fun z : Fin 1 → ℝ => v (z 0) := comp_secT_lift hper
    rw [e]
    have hvC : ContDiff ℝ 1 v := by
      refine contDiff_one_iff_deriv.2 ⟨fun x => (hv x).differentiableAt, ?_⟩
      have : deriv v = v1 := funext fun x => (hv x).deriv
      rw [this]; exact hv1
    exact hvC.comp (contDiff_apply ℝ ℝ 0)
  have hw0 := isWeakGrad_of_contDiff hC1
  have hgrad : (fun (y : Torus 1) (k : Fin 1) => fderiv ℝ (u ∘ liftT) (secT y) (Pi.single k 1)) = g := by
    funext y k
    have e : u ∘ liftT = fun z : Fin 1 → ℝ => v (z 0) := comp_secT_lift hper
    rw [e]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    have hdiff : DifferentiableAt ℝ (fun z : Fin 1 → ℝ => v (z 0)) (secT y) :=
      ((hv (secT y 0)).differentiableAt).comp (secT y) (differentiableAt_apply 0 _)
    have h1 : HasDerivAt (fun t : ℝ => secT y 0 + t) 1 0 := (hasDerivAt_id 0).const_add _
    have h2 : HasDerivAt v (v1 (secT y 0)) (secT y 0 + 0) := by simpa using hv (secT y 0)
    have h3 := h2.comp (0 : ℝ) h1
    have hd : HasDerivAt (fun t : ℝ => (fun z : Fin 1 → ℝ => v (z 0))
        (secT y + t • (Pi.single 0 1 : Fin 1 → ℝ))) (v1 (secT y 0)) 0 := by
      convert h3 using 1
      · funext t; simp
      · simp
    rw [fderiv_apply_of_line hdiff hd]
  rw [hgrad] at hw0
  have hP := poincare_torus hw0 hum hgm
  have : IsProbabilityMeasure (haar 1) := haar_isProbabilityMeasure 1
  rw [ProbabilityTheory.variance_eq_sub hum] at hP
  simp only [Fin.sum_univ_one] at hP
  have e1 : ∫ y, (u ^ 2) y ∂haar 1 = ∫ x in (0 : ℝ)..1, v x ^ 2 :=
    integral_torus_eq (G := fun t => v t ^ 2) (hvc.pow 2) (fun t => by simp [hper t])
  have e2 : ∫ x, u x ∂haar 1 = ∫ x in (0 : ℝ)..1, v x := integral_torus_eq hvc hper
  have e3 : ∫ y, g y 0 ^ 2 ∂haar 1 = ∫ x in (0 : ℝ)..1, v1 x ^ 2 :=
    integral_torus_eq (G := fun t => v1 t ^ 2) (hv1.pow 2) (fun t => by simp [hv1p t])
  rw [e1, e2, e3] at hP
  exact hP

/-! ### Positivity of the integral of a nonnegative continuous periodic function -/

theorem pos_integral_of_pos_at {g : ℝ → ℝ} (hc : Continuous g) (hnn : ∀ x, 0 ≤ g x)
    (hper : Function.Periodic g 1) {x0 : ℝ} (hx0 : 0 < g x0) : 0 < ∫ x in (0 : ℝ)..1, g x := by
  have hshift := hper.intervalIntegral_add_eq (x0 - 1 / 2) 0
  have h : ∫ x in (0 : ℝ)..1, g x = ∫ x in (x0 - 1 / 2)..(x0 - 1 / 2 + 1), g x := by
    simpa using hshift.symm
  rw [h, intervalIntegral.integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hnn)
    (hc.intervalIntegrable _ _)]
  refine ⟨by linarith, ?_⟩
  have hopen : IsOpen (Function.support g ∩ Ioo (x0 - 1 / 2) (x0 - 1 / 2 + 1)) :=
    ((isOpen_compl_singleton).preimage hc).inter isOpen_Ioo
  have hmem : x0 ∈ Function.support g ∩ Ioo (x0 - 1 / 2) (x0 - 1 / 2 + 1) :=
    ⟨hx0.ne', by constructor <;> linarith⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨x0, hmem⟩)
    (measure_mono (inter_subset_inter_right _ Ioo_subset_Ioc_self))

theorem ftc_periodic {H H' : ℝ → ℝ} (hd : ∀ x, HasDerivAt H (H' x) x) (hc : Continuous H')
    (hp : Function.Periodic H 1) : ∫ x in (0 : ℝ)..1, H' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)]
  have := hp 0
  rw [zero_add] at this
  rw [this, sub_self]

/-! ### Uniqueness -/

theorem periodic_unique {r M c : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r)
    (hsmall : r * M ^ 2 < 4 * π ^ 2 * c ^ 2)
    {F F1 F2 G G1 G2 B : ℝ → ℝ}
    (hFd1 : ∀ x, HasDerivAt F (F1 x) x) (hFd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hGd1 : ∀ x, HasDerivAt G (G1 x) x) (hGd2 : ∀ x, HasDerivAt G1 (G2 x) x)
    (hF2c : Continuous F2) (hG2c : Continuous G2)
    (hFper : Function.Periodic F 1) (hGper : Function.Periodic G 1)
    (hFc : ∀ x, c ≤ F x) (hGc : ∀ x, c ≤ G x) (hFM : ∀ x, F x ≤ M) (hGM : ∀ x, G x ≤ M)
    (hodeF : ∀ x, F2 x = F x * (B x - r * Real.log (F x)))
    (hodeG : ∀ x, G2 x = G x * (B x - r * Real.log (G x)))
    (hmF : ∫ x in (0 : ℝ)..1, F x ^ 2 = 1) (hmG : ∫ x in (0 : ℝ)..1, G x ^ 2 = 1) :
    F = G := by
  have hFp : ∀ x, 0 < F x := fun x => lt_of_lt_of_le hc (hFc x)
  have hGp : ∀ x, 0 < G x := fun x => lt_of_lt_of_le hc (hGc x)
  have hFcont : Continuous F := continuous_iff_continuousAt.2 fun x => (hFd1 x).continuousAt
  have hGcont : Continuous G := continuous_iff_continuousAt.2 fun x => (hGd1 x).continuousAt
  have hF1c : Continuous F1 := continuous_iff_continuousAt.2 fun x => (hFd2 x).continuousAt
  have hG1c : Continuous G1 := continuous_iff_continuousAt.2 fun x => (hGd2 x).continuousAt
  have ii : ∀ {f : ℝ → ℝ}, Continuous f → IntervalIntegrable f volume 0 1 :=
    fun hf => hf.intervalIntegrable _ _
  -- the difference of logarithms
  set v : ℝ → ℝ := fun x => Real.log (F x) - Real.log (G x) with hv
  set v1 : ℝ → ℝ := fun x => F1 x / F x - G1 x / G x with hv1
  have hvd : ∀ x, HasDerivAt v (v1 x) x := fun x =>
    ((hFd1 x).log (hFp x).ne').sub ((hGd1 x).log (hGp x).ne')
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hvd x).continuousAt
  have hv1c : Continuous v1 :=
    (hF1c.div hFcont fun x => (hFp x).ne').sub (hG1c.div hGcont fun x => (hGp x).ne')
  have hvper : Function.Periodic v 1 := fun x => by simp [hv, hFper x, hGper x]
  set m : ℝ → ℝ := fun x => F x * G x with hm
  have hmc : Continuous m := hFcont.mul hGcont
  have hmpos : ∀ x, 0 < m x := fun x => mul_pos (hFp x) (hGp x)
  have hmlo : ∀ x, c ^ 2 ≤ m x := fun x => by
    have := mul_le_mul (hFc x) (hGc x) hc.le (hFp x).le
    nlinarith
  have hmhi : ∀ x, m x ≤ M ^ 2 := fun x => by
    have := mul_le_mul (hFM x) (hGM x) (hGp x).le ((hFp x).le.trans (hFM x))
    nlinarith
  -- the Wronskian
  set W : ℝ → ℝ := fun x => F1 x * G x - F x * G1 x with hW
  set Wd : ℝ → ℝ := fun x => F2 x * G x - F x * G2 x with hWd
  have hWdd : ∀ x, HasDerivAt W (Wd x) x := fun x => by
    have := ((hFd2 x).mul (hGd1 x)).sub ((hFd1 x).mul (hGd2 x))
    refine this.congr_deriv ?_
    simp only [hWd]; ring
  have hWdc : Continuous Wd := (hF2c.mul hGcont).sub (hFcont.mul hG2c)
  have hF1per : Function.Periodic F1 1 := periodic_deriv_of_hasDerivAt hFd1 hFper
  have hG1per : Function.Periodic G1 1 := periodic_deriv_of_hasDerivAt hGd1 hGper
  have hWper : Function.Periodic W 1 := fun x => by simp [hW, hF1per x, hGper x, hFper x, hG1per x]
  have hWdv : ∀ x, Wd x = -r * (m x * v x) := fun x => by
    simp only [hWd, hm, hv]; rw [hodeF x, hodeG x]; ring
  have hWm : ∀ x, W x = m x * v1 x := fun x => by
    have h1 := (hFp x).ne'
    have h2 := (hGp x).ne'
    simp only [hW, hm, hv1]; field_simp
  have hWc : Continuous W := (hF1c.mul hGcont).sub (hFcont.mul hG1c)
  -- ∫ W' = 0
  have I1 : ∫ x in (0 : ℝ)..1, Wd x = 0 := ftc_periodic hWdd hWdc hWper
  -- ∫ (W v)' = 0
  have hWvd : ∀ x, HasDerivAt (fun x => W x * v x) (Wd x * v x + W x * v1 x) x :=
    fun x => (hWdd x).mul (hvd x)
  have hWvc : Continuous fun x => Wd x * v x + W x * v1 x := (hWdc.mul hvc).add (hWc.mul hv1c)
  have I2 : ∫ x in (0 : ℝ)..1, (Wd x * v x + W x * v1 x) = 0 :=
    ftc_periodic hWvd hWvc (fun x => by simp [hWper x, hvper x])
  have hv2c : Continuous fun x => v x ^ 2 := hvc.pow 2
  have hv12c : Continuous fun x => v1 x ^ 2 := hv1c.pow 2
  have hmvc : Continuous fun x => m x * v x := hmc.mul hvc
  have hmv2c : Continuous fun x => m x * v x ^ 2 := hmc.mul (hvc.pow 2)
  have hmv12c : Continuous fun x => m x * v1 x ^ 2 := hmc.mul (hv1c.pow 2)
  -- (★) ∫ m v'² = r ∫ m v²
  have star : ∫ x in (0 : ℝ)..1, m x * v1 x ^ 2 = r * ∫ x in (0 : ℝ)..1, m x * v x ^ 2 := by
    have e : ∀ x, Wd x * v x + W x * v1 x = -r * (m x * v x ^ 2) + m x * v1 x ^ 2 := fun x => by
      rw [hWdv x, hWm x]; ring
    simp_rw [e] at I2
    rw [intervalIntegral.integral_add ((ii hmv2c).const_mul _) (ii hmv12c),
      intervalIntegral.integral_const_mul] at I2
    linarith
  -- ∫ m v = 0 when r > 0
  have hmv0 : 0 < r → ∫ x in (0 : ℝ)..1, m x * v x = 0 := by
    intro hr
    have e : ∀ x, Wd x = -r * (m x * v x) := hWdv
    simp_rw [e] at I1
    rw [intervalIntegral.integral_const_mul] at I1
    have : r * ∫ x in (0 : ℝ)..1, m x * v x = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hr.ne'
    · exact h
  -- v is constant
  have hconst : ∀ x, v x = v 0 := by
    rcases hr0.eq_or_lt with hr | hr
    · -- r = 0 : v' = 0
      subst hr
      have h0 : ∫ x in (0 : ℝ)..1, m x * v1 x ^ 2 = 0 := by rw [star]; ring
      have hv10 : ∀ x, v1 x = 0 := by
        intro x0
        by_contra hne
        have hpos : 0 < m x0 * v1 x0 ^ 2 :=
          mul_pos (hmpos x0) (by positivity)
        have hp := pos_integral_of_pos_at hmv12c (fun x => by have := hmpos x; positivity)
          (fun x => by
            have h1 : v1 (x + 1) = v1 x := by
              simp only [hv1]; rw [hF1per x, hFper x, hG1per x, hGper x]
            simp only [hm]; rw [hFper x, hGper x, h1]) hpos
        linarith
      have hdiff : Differentiable ℝ v := fun x => (hvd x).differentiableAt
      have hd0 : ∀ x, deriv v x = 0 := fun x => by rw [(hvd x).deriv, hv10]
      intro x
      exact is_const_of_deriv_eq_zero hdiff hd0 x 0
    · have hmv := hmv0 hr
      set c0 : ℝ := ∫ x in (0 : ℝ)..1, v x with hc0
      set K : ℝ := ∫ x in (0 : ℝ)..1, m x * v x ^ 2 with hK
      have hK0 : 0 ≤ K := intervalIntegral.integral_nonneg zero_le_one fun x _ => by
        have := hmpos x; positivity
      -- (a) K ≤ ∫ m (v - c0)²
      have hA : K ≤ ∫ x in (0 : ℝ)..1, m x * (v x - c0) ^ 2 := by
        have e : ∀ x, m x * (v x - c0) ^ 2 =
            (m x * v x ^ 2 - 2 * c0 * (m x * v x)) + c0 ^ 2 * m x := fun x => by ring
        simp_rw [e]
        rw [intervalIntegral.integral_add (((ii hmv2c)).sub ((ii hmvc).const_mul _))
          ((ii hmc).const_mul _), intervalIntegral.integral_sub (ii hmv2c) ((ii hmvc).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmv]
        have : 0 ≤ ∫ x in (0 : ℝ)..1, m x :=
          intervalIntegral.integral_nonneg zero_le_one fun x _ => (hmpos x).le
        simp only [mul_zero, sub_zero]
        nlinarith [sq_nonneg c0]
      -- (b)
      have hvm : Continuous fun x => (v x - c0) ^ 2 := (hvc.sub continuous_const).pow 2
      have hB : ∫ x in (0 : ℝ)..1, m x * (v x - c0) ^ 2 ≤
          M ^ 2 * ∫ x in (0 : ℝ)..1, (v x - c0) ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on zero_le_one (ii (hmc.mul hvm)) ((ii hvm).const_mul _)
          fun x _ => mul_le_mul_of_nonneg_right (hmhi x) (sq_nonneg _)
      -- (c)
      have hC : ∫ x in (0 : ℝ)..1, (v x - c0) ^ 2 =
          (∫ x in (0 : ℝ)..1, v x ^ 2) - c0 ^ 2 := by
        have e : ∀ x, (v x - c0) ^ 2 = (v x ^ 2 - 2 * c0 * v x) + c0 ^ 2 := fun x => by ring
        simp_rw [e]
        rw [intervalIntegral.integral_add ((ii hv2c).sub ((ii hvc).const_mul _))
          intervalIntegrable_const, intervalIntegral.integral_sub (ii hv2c)
          ((ii hvc).const_mul _), intervalIntegral.integral_const_mul]
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        rw [← hc0]; ring
      have hD := poincare_1d hvd hv1c hvper
      -- (e)
      have hE : c ^ 2 * ∫ x in (0 : ℝ)..1, v1 x ^ 2 ≤ ∫ x in (0 : ℝ)..1, m x * v1 x ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on zero_le_one ((ii hv12c).const_mul _) (ii hmv12c)
          fun x _ => by nlinarith [hmlo x, sq_nonneg (v1 x)]
      rw [star] at hE
      have hc2 : 0 < c ^ 2 := by positivity
      set P := (∫ x in (0 : ℝ)..1, v x ^ 2) - c0 ^ 2 with hP
      set Q := ∫ x in (0 : ℝ)..1, v1 x ^ 2 with hQ
      rw [hC] at hB
      have h1 : 4 * π ^ 2 * c ^ 2 * K ≤ 4 * π ^ 2 * c ^ 2 * (M ^ 2 * P) :=
        mul_le_mul_of_nonneg_left (hA.trans hB) (by positivity)
      have h2 : c ^ 2 * M ^ 2 * (4 * π ^ 2 * P) ≤ c ^ 2 * M ^ 2 * Q :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      have h3 : M ^ 2 * (c ^ 2 * Q) ≤ M ^ 2 * (r * K) :=
        mul_le_mul_of_nonneg_left hE (sq_nonneg _)
      have hKle : (4 * π ^ 2 * c ^ 2 - r * M ^ 2) * K ≤ 0 := by nlinarith
      have hK00 : K = 0 := by
        by_contra hne
        have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hne)
        have : 0 < (4 * π ^ 2 * c ^ 2 - r * M ^ 2) * K :=
          mul_pos (by linarith) hKpos
        linarith
      have hv0 : ∀ x, v x = 0 := by
        intro x0
        by_contra hne
        have hpos : 0 < m x0 * v x0 ^ 2 := mul_pos (hmpos x0) (by positivity)
        have hp := pos_integral_of_pos_at hmv2c (fun x => by have := hmpos x; positivity)
          (fun x => by simp only [hm]; rw [hFper x, hGper x, hvper x]) hpos
        linarith
      intro x
      rw [hv0 x, hv0 0]
  -- from `v ≡ v 0` to `F = G`
  set c1 := v 0 with hc1
  have hFG : ∀ x, F x = G x * Real.exp c1 := by
    intro x
    have h := hconst x
    simp only [hv] at h
    have : Real.log (F x) = Real.log (G x) + c1 := by linarith
    calc F x = Real.exp (Real.log (F x)) := (Real.exp_log (hFp x)).symm
      _ = Real.exp (Real.log (G x) + c1) := by rw [this]
      _ = G x * Real.exp c1 := by rw [Real.exp_add, Real.exp_log (hGp x)]
  have hmass : Real.exp c1 ^ 2 = 1 := by
    have : ∫ x in (0 : ℝ)..1, F x ^ 2 = Real.exp c1 ^ 2 * ∫ x in (0 : ℝ)..1, G x ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hFG x]; ring
    rw [hmF, hmG] at this
    linarith
  have hexp : Real.exp c1 = 1 := by
    have hpos := Real.exp_pos c1
    nlinarith [hmass]
  funext x
  rw [hFG x, hexp, mul_one]

end SharpLSI.FL.Ex.SR
