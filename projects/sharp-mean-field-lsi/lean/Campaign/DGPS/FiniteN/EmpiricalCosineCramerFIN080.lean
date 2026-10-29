import DGPS.Circle.BesselConcavity
import DGPS.FiniteN.Tools.UnitTorusNormalization

/-!
# FIN080: empirical cosine Cramér estimate from tilting

For `θ₁, …, θ_N` i.i.d. Haar on the circle and `m_N = N⁻¹ ∑ᵢ cos θᵢ`, the rate function is
`I(m) = t(m) m - log I₀(t(m))` on `(-1,1)` with `t = g⁻¹`, `g = I₁/I₀`, and `I = ⊤` elsewhere.
We prove `I' = t`, `I → ∞` at `±1` (via the Riccati equation for `g`, which gives `g → 1` and
`t - log I₀(t) → ∞`, and the Legendre inequality), compact sublevel sets, the upper bound for closed sets
(exponential Chebyshev with the exact moment generating function `I₀(t)^N` and a finite cover),
and the lower bound for open sets (a change of measure written directly as a weighted integral).

Helper names live in `DGPS.FiniteN.EmpiricalCosineCramerFIN080`; the final statement is
`DGPS.FiniteN.empirical_cosine_cramer_estimate_from_tilting`.
-/

open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity
  DGPS.Circle.BesselConcavity

open DGPS.FiniteN.UnitTorusNormalization

namespace DGPS.FiniteN.EmpiricalCosineCramerFIN080

/-- The log-partition function `Λ = log I₀`. -/
noncomputable def logI0 (s : ℝ) : ℝ := Real.log (besselI 0 s)

theorem hasDerivAt_logI0 (s : ℝ) : HasDerivAt logI0 (besselRatio s) s :=
  (hasDerivAt_besselI_zero s).log (besselI_zero_pos s).ne'

theorem logI0_neg (s : ℝ) : logI0 (-s) = logI0 s := by
  simp [logI0, besselI_neg]

theorem ratioDeriv_eq_variance (t : ℝ) : ratioDeriv t = besselVariance t := by
  have h := hasDerivAt_besselRatio t
  rw [← besselVariance_eq t] at h
  exact (hasDerivAt_ratio t).unique h

theorem ratioDeriv_pos' (t : ℝ) : 0 < ratioDeriv t := by
  rw [ratioDeriv_eq_variance]; exact besselVariance_pos t

theorem strictMono_ratio : StrictMono besselRatio :=
  strictMono_of_deriv_pos fun x => by rw [deriv_ratio]; exact ratioDeriv_pos' x

theorem neg_one_lt_ratio (t : ℝ) : -1 < besselRatio t := by
  have := besselRatio_lt_one (-t)
  rw [besselRatio_neg] at this
  linarith

theorem ratio_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ besselRatio t := by
  have := strictMono_ratio.monotone ht
  rwa [ratio_zero] at this

theorem t_mul_ratioDeriv (t : ℝ) :
    t * ratioDeriv t = t - besselRatio t - t * besselRatio t ^ 2 := by
  by_cases ht : t = 0
  · subst ht; simp [ratio_zero]
  · have : ratioDeriv t = 1 - besselRatio t / t - besselRatio t ^ 2 := by
      unfold ratioDeriv
      rw [← ratio_div_eq t ht]
    rw [this]
    field_simp

/-- auxiliary function `z = e^{2t}(2t(1-g) - 1)` -/
noncomputable def zAux (t : ℝ) : ℝ := Real.exp (2 * t) * (2 * (t * (1 - besselRatio t)) - 1)

theorem hasDerivAt_zAux (t : ℝ) :
    HasDerivAt zAux (2 * t * Real.exp (2 * t) * (1 - besselRatio t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := by
    have := (hasDerivAt_id t).const_mul 2
    simpa using this.exp
  have h2 : HasDerivAt (fun t : ℝ => 2 * (t * (1 - besselRatio t)) - 1)
      (2 * (1 * (1 - besselRatio t) + t * (-(ratioDeriv t)))) t := by
    have := ((hasDerivAt_id t).mul ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_ratio t))).const_mul 2
    simpa using this.sub_const 1
  refine (h1.mul h2).congr_deriv ?_
  have e : t * ratioDeriv t = t - besselRatio t - t * besselRatio t ^ 2 := t_mul_ratioDeriv t
  rw [mul_neg, e]; ring

theorem zAux_mono : MonotoneOn zAux (Set.Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_zAux x).continuousAt.continuousWithinAt
  · exact fun x _ => (hasDerivAt_zAux x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_zAux x).deriv]
    have : (0:ℝ) < x := hx
    positivity

/-- auxiliary function `u = e^{t}(t(1-g) - 1)` -/
noncomputable def uAux (t : ℝ) : ℝ := Real.exp t * (t * (1 - besselRatio t) - 1)

theorem hasDerivAt_uAux (t : ℝ) :
    HasDerivAt uAux (-(t * besselRatio t * (1 - besselRatio t) * Real.exp t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp t) t := Real.hasDerivAt_exp t
  have h2 : HasDerivAt (fun t : ℝ => t * (1 - besselRatio t) - 1)
      (1 * (1 - besselRatio t) + t * (-(ratioDeriv t))) t := by
    have := ((hasDerivAt_id t).mul ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_ratio t)))
    simpa using this.sub_const 1
  refine (h1.mul h2).congr_deriv ?_
  have e : t * ratioDeriv t = t - besselRatio t - t * besselRatio t ^ 2 := t_mul_ratioDeriv t
  rw [mul_neg, e]; ring

theorem uAux_anti : AntitoneOn uAux (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_uAux x).continuousAt.continuousWithinAt
  · exact fun x _ => (hasDerivAt_uAux x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_uAux x).deriv]
    have hx' : (0:ℝ) < x := hx
    have hg := ratio_nonneg hx'.le
    have hg1 := besselRatio_lt_one x
    have : 0 ≤ x * besselRatio x * (1 - besselRatio x) * Real.exp x := by
      have : 0 ≤ 1 - besselRatio x := by linarith
      positivity
    linarith

/-- `t (1 - g t) < 1` for `t ≥ 0`. -/
theorem t_one_sub_ratio_lt_one {t : ℝ} (ht : 0 ≤ t) : t * (1 - besselRatio t) < 1 := by
  have h := uAux_anti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have h0 : uAux 0 = -1 := by simp [uAux, ratio_zero]
  rw [h0] at h
  unfold uAux at h
  by_contra hcon
  have hcon := not_lt.1 hcon
  have : 0 ≤ Real.exp t * (t * (1 - besselRatio t) - 1) :=
    mul_nonneg (Real.exp_pos t).le (by linarith)
  linarith

/-- `t (1 - g t) ≥ 1/3` for `t ≥ 1`. -/
theorem one_third_le {t : ℝ} (ht : 1 ≤ t) : 1 / 3 ≤ t * (1 - besselRatio t) := by
  have h := zAux_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ t)) (by linarith)
  have h0 : zAux 0 = -1 := by simp [zAux, ratio_zero]
  rw [h0] at h
  unfold zAux at h
  have he : (3:ℝ) ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t)
    linarith
  by_contra hcon
  have hcon := not_le.1 hcon
  nlinarith [Real.exp_pos (2 * t)]

theorem tendsto_ratio_atTop : Tendsto besselRatio atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => 1 - t⁻¹) atTop (𝓝 1) := by
    have h0 : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := t_one_sub_ratio_lt_one ht.le
    have : 1 - besselRatio t < t⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ ht]
      linarith
    linarith
  · exact Eventually.of_forall fun t => (besselRatio_lt_one t).le


/-- `φ(s) = s - Λ(s)`; the exponent of a tilt toward the endpoint `1`. -/
noncomputable def phi (s : ℝ) : ℝ := s - logI0 s

theorem hasDerivAt_phi (s : ℝ) : HasDerivAt phi (1 - besselRatio s) s :=
  (hasDerivAt_id' s).sub (hasDerivAt_logI0 s)

theorem phi_ge {s : ℝ} (hs : 1 ≤ s) : phi 1 + (1 / 3) * Real.log s ≤ phi s := by
  have hd : ∀ x ∈ Set.Ici (1 : ℝ), HasDerivAt (fun x => phi x - (1 / 3) * Real.log x)
      (1 - besselRatio x - (1 / 3) * x⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : (1 : ℝ) ≤ x := hx
      linarith
    exact (hasDerivAt_phi x).sub ((Real.hasDerivAt_log hx0).const_mul (1 / 3))
  have hmono : MonotoneOn (fun x => phi x - (1 / 3) * Real.log x) (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1 : ℝ) < x := hx
    rw [(hd x hx1.le).deriv]
    have h := one_third_le hx1.le
    have hx0 : 0 < x := by linarith
    have : (1 / 3) * x⁻¹ ≤ 1 - besselRatio x := by
      calc (1 / 3) * x⁻¹ ≤ (x * (1 - besselRatio x)) * x⁻¹ := by gcongr
        _ = 1 - besselRatio x := by field_simp
    linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only [Real.log_one, mul_zero, sub_zero] at this
  linarith

theorem tendsto_phi_atTop : Tendsto phi atTop atTop := by
  have h1 : Tendsto (fun s : ℝ => phi 1 + (1 / 3) * Real.log s) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  exact tendsto_atTop_mono' _ (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
                                  using phi_ge hs) h1

theorem exists_phi_ge (B : ℝ) : ∃ s : ℝ, 0 < s ∧ B ≤ phi s := by
  obtain ⟨s, hs1, hs2⟩ := ((tendsto_atTop.1 tendsto_phi_atTop B).and
    (eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨s, hs2, hs1⟩

/-- Surjectivity of `g = I₁/I₀` onto `(-1, 1)`. -/
theorem exists_ratio_eq {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) : ∃ s, besselRatio s = m := by
  have key : ∀ m ∈ Set.Ico (0 : ℝ) 1, ∃ s, besselRatio s = m := by
    intro m hm
    obtain ⟨S, hS1, hS2⟩ := ((tendsto_ratio_atTop.eventually (eventually_gt_nhds hm.2)).and
      (eventually_ge_atTop (0 : ℝ))).exists
    have := intermediate_value_Icc hS2 continuous_besselRatio.continuousOn
    rw [ratio_zero] at this
    obtain ⟨s, -, hs⟩ := this ⟨hm.1, hS1.le⟩
    exact ⟨s, hs⟩
  rcases le_or_gt 0 m with h | h
  · exact key m ⟨h, hm.2⟩
  · obtain ⟨s, hs⟩ := key (-m) ⟨by linarith, by linarith [hm.1]⟩
    exact ⟨-s, by rw [besselRatio_neg, hs, neg_neg]⟩

/-- The inverse `t = g⁻¹` of the ratio `g = I₁/I₀` (its values off `(-1,1)` are junk). -/
noncomputable def tInv (m : ℝ) : ℝ := Function.invFun besselRatio m

theorem ratio_tInv {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) : besselRatio (tInv m) = m :=
  Function.invFun_eq (exists_ratio_eq hm)

theorem tInv_ratio (s : ℝ) : tInv (besselRatio s) = s :=
  Function.leftInverse_invFun strictMono_ratio.injective s

theorem continuousAt_tInv {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) : ContinuousAt tInv m := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Set.Ioo (-1 : ℝ) 1) ?_
    (Ioo_mem_nhds hm.1 hm.2) ?_
  · intro a ha b hb hab
    by_contra h
    have h2 := strictMono_ratio (not_le.1 h)
    rw [ratio_tInv ha, ratio_tInv hb] at h2
    linarith
  · have : tInv '' Set.Ioo (-1 : ℝ) 1 = Set.univ :=
      Set.eq_univ_of_forall fun s =>
        ⟨besselRatio s, ⟨neg_one_lt_ratio s, besselRatio_lt_one s⟩, tInv_ratio s⟩
    rw [this]
    exact univ_mem

theorem hasDerivAt_tInv {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt tInv (ratioDeriv (tInv m))⁻¹ m := by
  refine HasDerivAt.of_local_left_inverse (continuousAt_tInv hm) (hasDerivAt_ratio (tInv m))
    (ratioDeriv_pos' _).ne' ?_
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with y hy using ratio_tInv hy

/-- The (real-valued) rate `I(m) = t(m) m - log I₀(t(m))`, meaningful on `(-1, 1)`. -/
noncomputable def rateReal (m : ℝ) : ℝ := tInv m * m - logI0 (tInv m)

theorem hasDerivAt_rateReal {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt rateReal (tInv m) m := by
  have hT := hasDerivAt_tInv hm
  have h1 := hT.mul (hasDerivAt_id' m)
  have h2 := (hasDerivAt_logI0 (tInv m)).comp m hT
  refine (h1.sub h2).congr_deriv ?_
  rw [ratio_tInv hm]
  ring

/-- Legendre inequality: `g(s) = m` gives `m r - Λ(r) ≤ m s - Λ(s)` for all `r`. -/
theorem legendre_le {s m : ℝ} (hs : besselRatio s = m) (r : ℝ) :
    m * r - logI0 r ≤ m * s - logI0 s := by
  have hd : ∀ x, HasDerivAt (fun x => logI0 x - m * x) (besselRatio x - m) x := by
    intro x
    have := (hasDerivAt_logI0 x).sub ((hasDerivAt_id' x).const_mul m)
    exact this.congr_deriv (by ring)
  rcases le_total s r with h | h
  · have hmono : MonotoneOn (fun x => logI0 x - m * x) (Set.Ici s) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici s)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have : s < x := hx
      have := strictMono_ratio this
      linarith
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
    simp only at this
    linarith
  · have hanti : AntitoneOn (fun x => logI0 x - m * x) (Set.Iic s) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic s)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Iic] at hx
      rw [(hd x).deriv]
      have : x < s := hx
      have := strictMono_ratio this
      linarith
    have := hanti (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
    simp only at this
    linarith

theorem rateReal_ge_legendre {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) (r : ℝ) :
    m * r - logI0 r ≤ rateReal m := by
  have := legendre_le (ratio_tInv hm) r
  unfold rateReal
  linarith [mul_comm m (tInv m)]

theorem logI0_zero : logI0 0 = 0 := by simp [logI0, besselI, angMode_zero]

theorem rateReal_nonneg {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) : 0 ≤ rateReal m := by
  have := rateReal_ge_legendre hm 0
  simpa [logI0_zero] using this

theorem exists_rate_ge_right (B : ℝ) :
    ∃ δ > 0, ∀ m ∈ Set.Ioo (1 - δ) 1, B ≤ rateReal m := by
  obtain ⟨s, hs0, hs⟩ := exists_phi_ge (B + 1)
  refine ⟨min 1 (1 / s), lt_min one_pos (by positivity), ?_⟩
  intro m hm
  have hδ1 : min 1 (1 / s) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (1 / s) ≤ 1 / s := min_le_right _ _
  have hm' : m ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hm.1], hm.2⟩
  have h1 := rateReal_ge_legendre hm' s
  have h2 : s * (1 - m) < 1 := by
    have : 1 - m < 1 / s := by linarith [hm.1]
    rwa [lt_div_iff₀ hs0, mul_comm] at this
  unfold phi at hs
  nlinarith

theorem exists_rate_ge_left (B : ℝ) :
    ∃ δ > 0, ∀ m ∈ Set.Ioo (-1) (-1 + δ), B ≤ rateReal m := by
  obtain ⟨s, hs0, hs⟩ := exists_phi_ge (B + 1)
  refine ⟨min 1 (1 / s), lt_min one_pos (by positivity), ?_⟩
  intro m hm
  have hδ1 : min 1 (1 / s) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (1 / s) ≤ 1 / s := min_le_right _ _
  have hm' : m ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hm.1, by linarith [hm.2]⟩
  have h1 := rateReal_ge_legendre hm' (-s)
  rw [logI0_neg] at h1
  have h2 : s * (1 + m) < 1 := by
    have : 1 + m < 1 / s := by linarith [hm.2]
    rwa [lt_div_iff₀ hs0, mul_comm] at this
  unfold phi at hs
  nlinarith

theorem tendsto_rateReal_right : Tendsto rateReal (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨δ, hδ, h⟩ := exists_rate_ge_right B
  filter_upwards [Ioo_mem_nhdsLT (by linarith : 1 - δ < 1)] with m hm using h m hm

theorem tendsto_rateReal_left : Tendsto rateReal (𝓝[>] (-1)) atTop := by
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨δ, hδ, h⟩ := exists_rate_ge_left B
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (-1 : ℝ) < -1 + δ)] with m hm using h m hm


/-! ### The empirical cosine and the exact moment generating function -/

/-- `∑ᵢ cos θᵢ`. -/
noncomputable def sumCos (N : ℕ+) (θ : AngParticleSpace N) : ℝ := ∑ i, angCos (θ i)

/-- The empirical cosine `m_N = N⁻¹ ∑ᵢ cos θᵢ`. -/
noncomputable def empCos (N : ℕ+) (θ : AngParticleSpace N) : ℝ := (N : ℝ)⁻¹ * sumCos N θ

theorem N_mul_empCos (N : ℕ+) (θ : AngParticleSpace N) : (N : ℝ) * empCos N θ = sumCos N θ := by
  unfold empCos
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

theorem continuous_sumCos (N : ℕ+) : Continuous (sumCos N) :=
  continuous_finsetSum _ fun i _ => (continuous_angMode 1).comp (continuous_apply i)

theorem continuous_empCos (N : ℕ+) : Continuous (empCos N) :=
  continuous_const.mul (continuous_sumCos N)

theorem abs_sumCos_le (N : ℕ+) (θ : AngParticleSpace N) : |sumCos N θ| ≤ N := by
  unfold sumCos
  calc |∑ i, angCos (θ i)| ≤ ∑ i, |angCos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => abs_angMode_le 1 (θ i)
    _ = N := by simp

theorem abs_empCos_le (N : ℕ+) (θ : AngParticleSpace N) : |empCos N θ| ≤ 1 := by
  unfold empCos
  have hN : (0 : ℝ) < N := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.2 hN)]
  calc (N : ℝ)⁻¹ * |sumCos N θ| ≤ (N : ℝ)⁻¹ * N :=
        mul_le_mul_of_nonneg_left (abs_sumCos_le N θ) (inv_nonneg.2 hN.le)
    _ = 1 := by field_simp

theorem integrable_exp_affine (N : ℕ+) (a b : ℝ) :
    Integrable (fun θ : AngParticleSpace N => Real.exp (a * sumCos N θ + b)) (angParticleHaar N) := by
  have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
  exact (Real.continuous_exp.comp ((continuous_const.mul (continuous_sumCos N)).add
    continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_exp_mul_sumCos (N : ℕ+) (a : ℝ) :
    ∫ θ, Real.exp (a * sumCos N θ) ∂angParticleHaar N = besselI 0 a ^ (N : ℕ) := by
  have h : ∀ θ : AngParticleSpace N,
      Real.exp (a * sumCos N θ) = ∏ i, Real.exp (a * angCos (θ i)) := by
    intro θ; unfold sumCos; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  unfold angParticleHaar
  rw [integral_fintype_prod_eq_pow (fun x : AngCircle => Real.exp (a * angCos x))]
  simp [besselI, angMode_zero]

theorem besselI0_pow_eq_exp (N : ℕ+) (a : ℝ) :
    besselI 0 a ^ (N : ℕ) = Real.exp ((N : ℝ) * logI0 a) := by
  rw [Real.exp_nat_mul]
  unfold logI0
  rw [Real.exp_log (besselI_zero_pos a)]

theorem integral_exp_affine (N : ℕ+) (a b : ℝ) :
    ∫ θ, Real.exp (a * sumCos N θ + b) ∂angParticleHaar N =
      Real.exp ((N : ℝ) * logI0 a + b) := by
  simp_rw [Real.exp_add]
  rw [integral_mul_const, integral_exp_mul_sumCos, besselI0_pow_eq_exp]

/-- Exponential Chebyshev: if `s y - Λ(s) ≥ c` on `A`, then `P(m_N ∈ A) ≤ e^{-Nc}`. -/
theorem measureReal_empCos_le (N : ℕ+) (s c : ℝ) (A : Set ℝ)
    (hA : ∀ y ∈ A, c ≤ s * y - logI0 s) :
    (angParticleHaar N).real {θ | empCos N θ ∈ A} ≤ Real.exp (-((N : ℝ) * c)) := by
  have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
  set ε : ℝ := Real.exp ((N : ℝ) * c) * besselI 0 s ^ (N : ℕ) with hε
  have hI : 0 < besselI 0 s ^ (N : ℕ) := pow_pos (besselI_zero_pos s) _
  have hεpos : 0 < ε := by positivity
  have hint := integrable_exp_affine N s 0
  simp only [add_zero] at hint
  have hM := mul_meas_ge_le_integral_of_nonneg
    (f := fun θ : AngParticleSpace N => Real.exp (s * sumCos N θ))
    (Eventually.of_forall fun θ => (Real.exp_pos _).le) hint ε
  rw [integral_exp_mul_sumCos] at hM
  have hsub : {θ : AngParticleSpace N | empCos N θ ∈ A} ⊆
      {θ | ε ≤ Real.exp (s * sumCos N θ)} := by
    intro θ hθ
    have h1 := hA _ hθ
    have h2 : (N : ℝ) * c ≤ s * sumCos N θ - (N : ℝ) * logI0 s := by
      rw [← N_mul_empCos]
      have : (0 : ℝ) < N := by positivity
      nlinarith
    rw [hε, besselI0_pow_eq_exp, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 := measureReal_mono (μ := angParticleHaar N) hsub (measure_ne_top _ _)
  have h4 : ε * (angParticleHaar N).real {θ | empCos N θ ∈ A} ≤ besselI 0 s ^ (N : ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left h3 hεpos.le) hM
  rw [hε, mul_assoc] at h4
  have h5 : Real.exp ((N : ℝ) * c) * (angParticleHaar N).real {θ | empCos N θ ∈ A} ≤ 1 := by
    have : besselI 0 s ^ (N : ℕ) * (Real.exp ((N : ℝ) * c) * (angParticleHaar N).real {θ | empCos N θ ∈ A})
        ≤ besselI 0 s ^ (N : ℕ) * 1 := by
      nlinarith
    exact le_of_mul_le_mul_left this hI
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  linarith [mul_comm (Real.exp ((N : ℝ) * c)) ((angParticleHaar N).real {θ | empCos N θ ∈ A})]

/-! ### Lower bound without a tilted measure -/

theorem measurableSet_empCos_lt (N : ℕ+) (m ε : ℝ) :
    MeasurableSet {θ : AngParticleSpace N | |empCos N θ - m| < ε} :=
  (isOpen_lt (continuous_abs.comp ((continuous_empCos N).sub continuous_const))
    continuous_const).measurableSet

theorem measureReal_tilt_lower (N : ℕ+) (s m ε l1 l2 : ℝ) (hl1 : 0 < l1) (hl2 : l2 < 0) :
    Real.exp (-((N : ℝ) * (s * m - logI0 s + |s| * ε))) *
        (1 - Real.exp ((N : ℝ) * (logI0 (s + l1) - logI0 s - l1 * (m + ε)))
           - Real.exp ((N : ℝ) * (logI0 (s + l2) - logI0 s - l2 * (m - ε)))) ≤
      (angParticleHaar N).real {θ | |empCos N θ - m| < ε} := by
  have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
  set κ : ℝ := Real.exp (-((N : ℝ) * (s * m - logI0 s + |s| * ε))) with hκ
  have hN : (0 : ℝ) < N := by positivity
  set f0 : AngParticleSpace N → ℝ := fun θ => Real.exp (s * sumCos N θ + (-((N : ℝ) * logI0 s))) with hf0
  set f1 : AngParticleSpace N → ℝ := fun θ => Real.exp ((s + l1) * sumCos N θ
      + (-((N : ℝ) * logI0 s) - l1 * ((N : ℝ) * (m + ε)))) with hf1
  set f2 : AngParticleSpace N → ℝ := fun θ => Real.exp ((s + l2) * sumCos N θ
      + (-((N : ℝ) * logI0 s) - l2 * ((N : ℝ) * (m - ε)))) with hf2
  have i0 : Integrable f0 (angParticleHaar N) := integrable_exp_affine N s (-((N : ℝ) * logI0 s))
  have i1 : Integrable f1 (angParticleHaar N) :=
    integrable_exp_affine N (s + l1) (-((N : ℝ) * logI0 s) - l1 * ((N : ℝ) * (m + ε)))
  have i2 : Integrable f2 (angParticleHaar N) :=
    integrable_exp_affine N (s + l2) (-((N : ℝ) * logI0 s) - l2 * ((N : ℝ) * (m - ε)))
  have i01 : Integrable (fun θ => f0 θ - f1 θ) (angParticleHaar N) := i0.sub i1
  have i012 : Integrable (fun θ => f0 θ - f1 θ - f2 θ) (angParticleHaar N) := i01.sub i2
  have hint : ∫ θ, κ * (f0 θ - f1 θ - f2 θ) ∂angParticleHaar N =
      κ * (1 - Real.exp ((N : ℝ) * (logI0 (s + l1) - logI0 s - l1 * (m + ε)))
           - Real.exp ((N : ℝ) * (logI0 (s + l2) - logI0 s - l2 * (m - ε)))) := by
    rw [integral_const_mul, integral_sub i01 i2, integral_sub i0 i1]
    simp only [hf0, hf1, hf2]
    rw [integral_exp_affine, integral_exp_affine, integral_exp_affine]
    have e0 : (N : ℝ) * logI0 s + -((N : ℝ) * logI0 s) = 0 := by ring
    have e1 : (N : ℝ) * logI0 (s + l1) + (-((N : ℝ) * logI0 s) - l1 * ((N : ℝ) * (m + ε))) =
        (N : ℝ) * (logI0 (s + l1) - logI0 s - l1 * (m + ε)) := by ring
    have e2 : (N : ℝ) * logI0 (s + l2) + (-((N : ℝ) * logI0 s) - l2 * ((N : ℝ) * (m - ε))) =
        (N : ℝ) * (logI0 (s + l2) - logI0 s - l2 * (m - ε)) := by ring
    rw [e0, e1, e2, Real.exp_zero]
  have hmeas := measurableSet_empCos_lt N m ε
  have hpt : ∀ θ, κ * (f0 θ - f1 θ - f2 θ) ≤
      Set.indicator {θ : AngParticleSpace N | |empCos N θ - m| < ε} (1 : AngParticleSpace N → ℝ) θ := by
    intro θ
    have hS := N_mul_empCos N θ
    set e := empCos N θ with he
    set S := sumCos N θ with hSdef
    set E1 := Real.exp (l1 * (S - (N : ℝ) * (m + ε))) with hE1
    set E2 := Real.exp (l2 * (S - (N : ℝ) * (m - ε))) with hE2
    have h1 : f1 θ = f0 θ * E1 := by
      simp only [hf1, hf0, hE1]; rw [← Real.exp_add]; congr 1; ring
    have h2 : f2 θ = f0 θ * E2 := by
      simp only [hf2, hf0, hE2]; rw [← Real.exp_add]; congr 1; ring
    have hw : 0 ≤ κ * f0 θ := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hE1p : 0 < E1 := Real.exp_pos _
    have hE2p : 0 < E2 := Real.exp_pos _
    have hG : κ * (f0 θ - f1 θ - f2 θ) = κ * f0 θ * (1 - E1 - E2) := by rw [h1, h2]; ring
    rw [hG]
    by_cases hB : |e - m| < ε
    · rw [Set.indicator_of_mem (show θ ∈ {θ : AngParticleSpace N | |empCos N θ - m| < ε} from hB)]
      simp only [Pi.one_apply]
      have hle : κ * f0 θ ≤ 1 := by
        rw [hκ, hf0]; simp only
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.2
        have hS' : sumCos N θ = (N : ℝ) * e := hS.symm
        rw [hS']
        have h3 : s * (e - m) ≤ |s| * ε :=
          (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB.le (abs_nonneg s))
        nlinarith [mul_le_mul_of_nonneg_left h3 hN.le]
      nlinarith
    · rw [Set.indicator_of_notMem (show θ ∉ {θ : AngParticleSpace N | |empCos N θ - m| < ε} from hB)]
      have hB' : ε ≤ |e - m| := not_lt.1 hB
      rcases le_abs'.1 hB' with h | h
      · have : 1 ≤ E2 := by
          rw [hE2, ← Real.exp_zero]; apply Real.exp_le_exp.2
          have : S - (N : ℝ) * (m - ε) ≤ 0 := by rw [← hS]; nlinarith
          nlinarith
        nlinarith
      · have : 1 ≤ E1 := by
          rw [hE1, ← Real.exp_zero]; apply Real.exp_le_exp.2
          have : 0 ≤ S - (N : ℝ) * (m + ε) := by rw [← hS]; nlinarith
          nlinarith
        nlinarith
  have hind : Integrable (Set.indicator {θ : AngParticleSpace N | |empCos N θ - m| < ε}
      (1 : AngParticleSpace N → ℝ)) (angParticleHaar N) :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hmono := integral_mono (i012.const_mul κ) hind hpt
  rw [hint] at hmono
  rw [integral_indicator_one hmeas] at hmono
  exact hmono

theorem exists_pos_lt_zero {f : ℝ → ℝ} {c : ℝ} (hd : HasDerivAt f c 0) (hc : c < 0) :
    ∃ l : ℝ, 0 < l ∧ f l - f 0 < 0 := by
  have h := (hd.tendsto_slope_zero_right.eventually (gt_mem_nhds hc)).and self_mem_nhdsWithin
  obtain ⟨l, hl, hl0⟩ := h.exists
  refine ⟨l, hl0, ?_⟩
  simp only [smul_eq_mul, zero_add] at hl
  by_contra hcon
  have hcon := not_lt.1 hcon
  have : 0 ≤ l⁻¹ * (f l - f 0) := mul_nonneg (inv_nonneg.2 hl0.le) hcon
  linarith

theorem exists_neg_lt_zero {f : ℝ → ℝ} {c : ℝ} (hd : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ l : ℝ, l < 0 ∧ f l - f 0 < 0 := by
  have h := (hd.tendsto_slope_zero_left.eventually (lt_mem_nhds hc)).and self_mem_nhdsWithin
  obtain ⟨l, hl, hl0⟩ := h.exists
  refine ⟨l, hl0, ?_⟩
  simp only [smul_eq_mul, zero_add] at hl
  by_contra hcon
  have hcon := not_lt.1 hcon
  have : l⁻¹ * (f l - f 0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hl0.le) hcon
  linarith

theorem tendsto_exp_mul_neg (ψ : ℝ) (hψ : ψ < 0) :
    Tendsto (fun N : ℕ+ => Real.exp ((N : ℝ) * ψ)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos ψ).le (Real.exp_lt_one_iff.2 hψ)).comp
    tendsto_PNat_val_atTop_atTop
  refine h.congr (fun N => ?_)
  simp [Function.comp, ← Real.exp_nat_mul]

theorem exists_tilt_exponents {s m : ℝ} (ε : ℝ) (hs : besselRatio s = m) (hε : 0 < ε) :
    ∃ l1 l2 : ℝ, 0 < l1 ∧ l2 < 0 ∧
      logI0 (s + l1) - logI0 s - l1 * (m + ε) < 0 ∧
      logI0 (s + l2) - logI0 s - l2 * (m - ε) < 0 := by
  have hd1 : HasDerivAt (fun l : ℝ => logI0 (s + l) - logI0 s - l * (m + ε)) (-ε) 0 := by
    have h := (((hasDerivAt_logI0 (s + 0)).comp_const_add s 0).sub_const (logI0 s)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (m + ε))
    refine h.congr_deriv ?_
    simp [hs]
  have hd2 : HasDerivAt (fun l : ℝ => logI0 (s + l) - logI0 s - l * (m - ε)) ε 0 := by
    have h := (((hasDerivAt_logI0 (s + 0)).comp_const_add s 0).sub_const (logI0 s)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (m - ε))
    refine h.congr_deriv ?_
    simp [hs]
  obtain ⟨l1, hl1, h1⟩ := exists_pos_lt_zero hd1 (by linarith)
  obtain ⟨l2, hl2, h2⟩ := exists_neg_lt_zero hd2 hε
  refine ⟨l1, l2, hl1, hl2, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

theorem lower_bound_point {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ+ in atTop,
      (1 / 2 : ℝ) * Real.exp (-((N : ℝ) * (rateReal m + |tInv m| * ε))) ≤
        (angParticleHaar N).real {θ | |empCos N θ - m| < ε} := by
  obtain ⟨l1, l2, hl1, hl2, h1, h2⟩ := exists_tilt_exponents ε (ratio_tInv hm) hε
  have t1 := (tendsto_exp_mul_neg _ h1).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have t2 := (tendsto_exp_mul_neg _ h2).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [t1, t2] with N a b
  refine le_trans ?_ (measureReal_tilt_lower N (tInv m) m ε l1 l2 hl1 hl2)
  have hκ : Real.exp (-((N : ℝ) * (tInv m * m - logI0 (tInv m) + |tInv m| * ε))) =
      Real.exp (-((N : ℝ) * (rateReal m + |tInv m| * ε))) := rfl
  rw [hκ]
  have := Real.exp_pos (-((N : ℝ) * (rateReal m + |tInv m| * ε)))
  nlinarith

/-! ### The rate function and the upper bound -/

/-- The Cramér rate function of `m_N`: `I(m) = t(m) m - log I₀(t(m))` on `(-1,1)` and `⊤` elsewhere. -/
noncomputable def cramerRate (m : ℝ) : EReal :=
  if m ∈ Set.Ioo (-1 : ℝ) 1 then ((rateReal m : ℝ) : EReal) else ⊤

theorem cramerRate_of_mem {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    cramerRate m = ((rateReal m : ℝ) : EReal) := by
  simp [cramerRate, hm]

theorem cramerRate_of_not_mem {m : ℝ} (hm : m ∉ Set.Ioo (-1 : ℝ) 1) : cramerRate m = ⊤ := by
  simp [cramerRate, hm]

theorem cover_point {c x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hc : (c : EReal) < cramerRate x) :
    ∃ s : ℝ, ∃ A ∈ 𝓝 x, ∀ y ∈ A, c ≤ s * y - logI0 s := by
  by_cases hI : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [cramerRate_of_mem hI, EReal.coe_lt_coe_iff] at hc
    refine ⟨tInv x, {y | c < tInv x * y - logI0 (tInv x)}, ?_, fun y hy => hy.le⟩
    exact (isOpen_lt continuous_const
      ((continuous_const.mul continuous_id).sub continuous_const)).mem_nhds hc
  · have hx1 : x = 1 ∨ x = -1 := by
      by_contra hcon
      have hcon := not_or.1 hcon
      exact hI ⟨lt_of_le_of_ne hx.1 (Ne.symm hcon.2), lt_of_le_of_ne hx.2 hcon.1⟩
    obtain ⟨s, hs, hphi⟩ := exists_phi_ge (c + 1)
    have hs1 : s * (1 / s) = 1 := by field_simp
    have hpos : 0 < 1 / s := by positivity
    rcases hx1 with rfl | rfl
    · refine ⟨s, Set.Ioi (1 - 1 / s), Ioi_mem_nhds (by linarith), fun y hy => ?_⟩
      have hy' : 1 - 1 / s < y := hy
      have : s * (1 - 1 / s) < s * y := mul_lt_mul_of_pos_left hy' hs
      unfold phi at hphi
      nlinarith
    · refine ⟨-s, Set.Iio (-1 + 1 / s), Iio_mem_nhds (by linarith), fun y hy => ?_⟩
      have hy' : y < -1 + 1 / s := hy
      have : s * y < s * (-1 + 1 / s) := mul_lt_mul_of_pos_left hy' hs
      rw [logI0_neg]
      unfold phi at hphi
      nlinarith

theorem upper_cover {K : Set ℝ} (hK : IsClosed K) {c : ℝ} (hc : ∀ x ∈ K, (c : EReal) < cramerRate x) :
    ∃ C : ℕ, ∀ N : ℕ+, (angParticleHaar N).real {θ | empCos N θ ∈ K} ≤
      (C : ℝ) * Real.exp (-((N : ℝ) * c)) := by
  have hcomp : IsCompact (K ∩ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.inter_left hK
  have key : ∀ x : ℝ, ∃ (s : ℝ) (A : Set ℝ),
      x ∈ K ∩ Set.Icc (-1 : ℝ) 1 → A ∈ 𝓝 x ∧ ∀ y ∈ A, c ≤ s * y - logI0 s := by
    intro x
    by_cases hx : x ∈ K ∩ Set.Icc (-1 : ℝ) 1
    · obtain ⟨s, A, hA, h⟩ := cover_point hx.2 (hc x hx.1)
      exact ⟨s, A, fun _ => ⟨hA, h⟩⟩
    · exact ⟨0, ∅, fun h => absurd h hx⟩
  choose S A hA using key
  obtain ⟨t, ht, hsub⟩ := hcomp.elim_nhds_subcover A (fun x hx => (hA x hx).1)
  refine ⟨t.card, fun N => ?_⟩
  have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
  have h1 : {θ : AngParticleSpace N | empCos N θ ∈ K} ⊆
      ⋃ x ∈ t, {θ : AngParticleSpace N | empCos N θ ∈ A x} := by
    intro θ hθ
    have hmem : empCos N θ ∈ K ∩ Set.Icc (-1 : ℝ) 1 := ⟨hθ, abs_le.1 (abs_empCos_le N θ)⟩
    have := hsub hmem
    simpa using this
  calc (angParticleHaar N).real {θ | empCos N θ ∈ K}
      ≤ (angParticleHaar N).real (⋃ x ∈ t, {θ : AngParticleSpace N | empCos N θ ∈ A x}) :=
        measureReal_mono (μ := angParticleHaar N) h1 (measure_ne_top _ _)
    _ ≤ ∑ x ∈ t, (angParticleHaar N).real {θ : AngParticleSpace N | empCos N θ ∈ A x} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ t, Real.exp (-((N : ℝ) * c)) :=
        Finset.sum_le_sum fun x hx => measureReal_empCos_le N (S x) c (A x) ((hA x (ht x hx)).2)
    _ = (t.card : ℝ) * Real.exp (-((N : ℝ) * c)) := by simp

/-! ### Assembly in `EReal` -/

/-- `N⁻¹ log P(m_N ∈ S)` as an extended real. -/
noncomputable def logProb (N : ℕ+) (S : Set ℝ) : EReal :=
  (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (angParticleHaar N {θ | empCos N θ ∈ S})

theorem scaled_log_le {a : ℝ} (ha : 0 ≤ a) {p : ENNReal} {q : ℝ} (hq : 0 < q)
    (h : p ≤ ENNReal.ofReal q) : (a : EReal) * ENNReal.log p ≤ ((a * Real.log q : ℝ) : EReal) := by
  have h1 := ENNReal.log_monotone h
  rw [ENNReal.log_ofReal_of_pos hq] at h1
  calc (a : EReal) * ENNReal.log p ≤ (a : EReal) * ((Real.log q : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 ha)
    _ = ((a * Real.log q : ℝ) : EReal) := by rw [← EReal.coe_mul]

theorem le_scaled_log {a : ℝ} (ha : 0 ≤ a) {p : ENNReal} {q : ℝ} (hq : 0 < q)
    (h : ENNReal.ofReal q ≤ p) : ((a * Real.log q : ℝ) : EReal) ≤ (a : EReal) * ENNReal.log p := by
  have h1 := ENNReal.log_monotone h
  rw [ENNReal.log_ofReal_of_pos hq] at h1
  calc ((a * Real.log q : ℝ) : EReal) = (a : EReal) * ((Real.log q : ℝ) : EReal) := by
        rw [EReal.coe_mul]
    _ ≤ (a : EReal) * ENNReal.log p := mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 ha)

theorem ereal_le_neg_of_forall {L J : EReal} (h : ∀ c : ℝ, (c : EReal) < J → L ≤ ((-c : ℝ) : EReal)) :
    L ≤ -J := by
  by_contra hcon
  have hlt := not_le.1 hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have h2 : ((-r : ℝ) : EReal) < J := by
    rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hr1
  have h3 := h _ h2
  rw [neg_neg] at h3
  exact absurd hr2 (not_lt.2 h3)

theorem tendsto_inv_N : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)

theorem cramer_upper {K : Set ℝ} (hK : IsClosed K) :
    limsup (fun N : ℕ+ => logProb N K) atTop ≤ -(⨅ x ∈ K, cramerRate x) := by
  refine ereal_le_neg_of_forall fun c hcJ => ?_
  have hc : ∀ x ∈ K, (c : EReal) < cramerRate x := fun x hx =>
    lt_of_lt_of_le hcJ (iInf₂_le x hx)
  obtain ⟨C, hC⟩ := upper_cover hK hc
  set C' : ℝ := (C : ℝ) + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  set u : ℕ+ → ℝ := fun N => ((N : ℕ) : ℝ)⁻¹ * Real.log C' - c with hu
  have hle : ∀ N : ℕ+, logProb N K ≤ ((u N : ℝ) : EReal) := by
    intro N
    have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
    have hN : (0 : ℝ) < N := by positivity
    have hq : 0 < C' * Real.exp (-((N : ℝ) * c)) := by positivity
    have hP : angParticleHaar N {θ | empCos N θ ∈ K} ≤ ENNReal.ofReal (C' * Real.exp (-((N : ℝ) * c))) := by
      rw [← ofReal_measureReal (μ := angParticleHaar N) (measure_ne_top _ _)]
      apply ENNReal.ofReal_le_ofReal
      refine (hC N).trans ?_
      have := Real.exp_pos (-((N : ℝ) * c))
      rw [hC']; nlinarith
    refine (scaled_log_le (inv_nonneg.2 hN.le) hq hP).trans ?_
    apply EReal.coe_le_coe_iff.2
    rw [Real.log_mul hC'pos.ne' (Real.exp_pos _).ne', Real.log_exp, hu]
    field_simp
    ring_nf
    rfl
  have hlim : Tendsto (fun N : ℕ+ => ((u N : ℝ) : EReal)) atTop (𝓝 ((-c : ℝ) : EReal)) := by
    have : Tendsto u atTop (𝓝 (0 * Real.log C' - c)) := (tendsto_inv_N.mul_const _).sub_const c
    rw [zero_mul, zero_sub] at this
    exact (continuous_coe_real_ereal.tendsto _).comp this
  calc limsup (fun N : ℕ+ => logProb N K) atTop
      ≤ limsup (fun N : ℕ+ => ((u N : ℝ) : EReal)) atTop := limsup_le_limsup (Eventually.of_forall hle)
    _ = ((-c : ℝ) : EReal) := hlim.limsup_eq

theorem lower_point_eps {O : Set ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) {ε ε0 : ℝ}
    (hε : 0 < ε) (hεε0 : ε ≤ ε0) (hball : Metric.ball x ε0 ⊆ O) :
    ((-(rateReal x + |tInv x| * ε) : ℝ) : EReal) ≤ liminf (fun N : ℕ+ => logProb N O) atTop := by
  set a : ℝ := rateReal x + |tInv x| * ε with ha
  set v : ℕ+ → ℝ := fun N => -(((N : ℕ) : ℝ)⁻¹ * Real.log 2) - a with hv
  have hlim : Tendsto (fun N : ℕ+ => ((v N : ℝ) : EReal)) atTop (𝓝 ((-a : ℝ) : EReal)) := by
    have : Tendsto v atTop (𝓝 (-(0 * Real.log 2) - a)) :=
      ((tendsto_inv_N.mul_const _).neg).sub_const a
    rw [zero_mul, neg_zero, zero_sub] at this
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hev : ∀ᶠ N : ℕ+ in atTop, ((v N : ℝ) : EReal) ≤ logProb N O := by
    filter_upwards [lower_bound_point hx hε] with N hN
    have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
    have hNpos : (0 : ℝ) < N := by positivity
    have hq : 0 < (1 / 2 : ℝ) * Real.exp (-((N : ℝ) * a)) := by positivity
    have hsub : {θ : AngParticleSpace N | |empCos N θ - x| < ε} ⊆ {θ | empCos N θ ∈ O} := by
      intro θ hθ
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hθ hεε0
    have hP : ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) * a))) ≤
        angParticleHaar N {θ | empCos N θ ∈ O} := by
      calc ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) * a)))
          ≤ ENNReal.ofReal ((angParticleHaar N).real {θ | |empCos N θ - x| < ε}) :=
            ENNReal.ofReal_le_ofReal hN
        _ = angParticleHaar N {θ | |empCos N θ - x| < ε} := ofReal_measureReal (measure_ne_top _ _)
        _ ≤ _ := measure_mono hsub
    refine le_trans ?_ (le_scaled_log (inv_nonneg.2 hNpos.le) hq hP)
    apply EReal.coe_le_coe_iff.2
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, hv]
    have : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [this]
    have hN0 : ((N : ℕ) : ℝ) ≠ 0 := hNpos.ne'
    simp only
    field_simp
    ring_nf
    rfl
  calc ((-a : ℝ) : EReal) = liminf (fun N : ℕ+ => ((v N : ℝ) : EReal)) atTop := hlim.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hev

theorem lower_point {O : Set ℝ} (hO : IsOpen O) {x : ℝ} (hxO : x ∈ O) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ((-(rateReal x) : ℝ) : EReal) ≤ liminf (fun N : ℕ+ => logProb N O) atTop := by
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.1 hO x hxO
  have hlim : Tendsto (fun ε : ℝ => ((-(rateReal x + |tInv x| * ε) : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((-(rateReal x) : ℝ) : EReal)) := by
    have h1 : Tendsto (fun ε : ℝ => -(rateReal x + |tInv x| * ε)) (𝓝[>] 0) (𝓝 (-(rateReal x))) := by
      have : Tendsto (fun ε : ℝ => -(rateReal x + |tInv x| * ε)) (𝓝 0)
          (𝓝 (-(rateReal x + |tInv x| * 0))) :=
        (continuous_const.add (continuous_const.mul continuous_id)).neg.tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (continuous_coe_real_ereal.tendsto _).comp h1
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hε0] with ε hε
  exact lower_point_eps hx hε.1 hε.2.le hball

theorem cramer_lower {O : Set ℝ} (hO : IsOpen O) :
    -(⨅ x ∈ O, cramerRate x) ≤ liminf (fun N : ℕ+ => logProb N O) atTop := by
  rw [EReal.neg_le]
  refine le_iInf₂ fun x hx => ?_
  by_cases hI : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [cramerRate_of_mem hI, EReal.neg_le, ← EReal.coe_neg]
    exact lower_point hO hx hI
  · rw [cramerRate_of_not_mem hI]
    exact le_top

theorem isCompact_sublevel (r : ℝ) : IsCompact {m : ℝ | cramerRate m ≤ (r : EReal)} := by
  obtain ⟨δ1, hδ1, h1⟩ := exists_rate_ge_right (r + 1)
  obtain ⟨δ2, hδ2, h2⟩ := exists_rate_ge_left (r + 1)
  set δ : ℝ := min δ1 δ2 with hδ
  have hδpos : 0 < δ := lt_min hδ1 hδ2
  have hδ1' : δ ≤ δ1 := min_le_left _ _
  have hδ2' : δ ≤ δ2 := min_le_right _ _
  have hT : Set.Icc (-1 + δ) (1 - δ) ⊆ Set.Ioo (-1 : ℝ) 1 := fun m hm =>
    ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hcont : ContinuousOn rateReal (Set.Icc (-1 + δ) (1 - δ)) := fun m hm =>
    (hasDerivAt_rateReal (hT hm)).continuousAt.continuousWithinAt
  have hclosed : IsClosed (Set.Icc (-1 + δ) (1 - δ) ∩ rateReal ⁻¹' Set.Iic r) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have heq : {m : ℝ | cramerRate m ≤ (r : EReal)} =
      Set.Icc (-1 + δ) (1 - δ) ∩ rateReal ⁻¹' Set.Iic r := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hm
      have hI : m ∈ Set.Ioo (-1 : ℝ) 1 := by
        by_contra hI
        rw [cramerRate_of_not_mem hI] at hm
        exact absurd hm (by simp)
      rw [cramerRate_of_mem hI, EReal.coe_le_coe_iff] at hm
      refine ⟨⟨?_, ?_⟩, hm⟩
      · by_contra hcon
        have hlt : m < -1 + δ := not_le.1 hcon
        have := h2 m ⟨hI.1, by linarith⟩
        linarith
      · by_contra hcon
        have hlt : 1 - δ < m := not_le.1 hcon
        have := h1 m ⟨by linarith, hI.2⟩
        linarith
    · rintro ⟨hm, hr⟩
      rw [cramerRate_of_mem (hT hm), EReal.coe_le_coe_iff]
      exact hr
  rw [heq]
  exact isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left

end DGPS.FiniteN.EmpiricalCosineCramerFIN080

namespace DGPS.FiniteN

open Filter Topology DGPS.Circle.BesselMoments DGPS.FiniteN.UnitTorusNormalization
  DGPS.FiniteN.EmpiricalCosineCramerFIN080

/-- **Cramér estimate for the empirical cosine, from tilting.**

For `θ₁, …, θ_N` i.i.d. Haar on the circle (`angParticleHaar N` on `AngParticleSpace N`) and
`m_N = N⁻¹ ∑ᵢ cos θᵢ` (`empCos N`), with `Λ = log I₀` (`logI0`), `g = I₁/I₀` (`besselRatio`)
and `t = g⁻¹` (`tInv`):

1. `g` is a bijection of `ℝ` onto `(-1,1)` with inverse `t`;
2. the rate `I(m) = t(m) m - Λ(t(m))` (`rateReal`; `cramerRate` is `I` on `(-1,1)` and `⊤`
   elsewhere, in particular `I(±1) = ⊤`) satisfies `I' = t`;
3. `I → ∞` at both endpoints, and the sublevel sets of `cramerRate` are compact (good rate
   function);
4. for every closed `K ⊆ ℝ`, `limsup N⁻¹ log P(m_N ∈ K) ≤ -inf_K I`;
5. for every open `O ⊆ ℝ`, `-inf_O I ≤ liminf N⁻¹ log P(m_N ∈ O)`.

Here `N⁻¹ log P` is taken in `EReal` (`logProb N S`, using `ENNReal.log`). -/
theorem empirical_cosine_cramer_estimate_from_tilting :
    Set.BijOn besselRatio Set.univ (Set.Ioo (-1 : ℝ) 1) ∧
    (∀ m ∈ Set.Ioo (-1 : ℝ) 1, besselRatio (tInv m) = m) ∧
    (∀ s : ℝ, tInv (besselRatio s) = s) ∧
    (∀ m ∈ Set.Ioo (-1 : ℝ) 1,
      cramerRate m = ((tInv m * m - logI0 (tInv m) : ℝ) : EReal)) ∧
    cramerRate 1 = ⊤ ∧ cramerRate (-1) = ⊤ ∧
    (∀ m ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt rateReal (tInv m) m) ∧
    Tendsto rateReal (𝓝[<] 1) atTop ∧ Tendsto rateReal (𝓝[>] (-1)) atTop ∧
    (∀ r : ℝ, IsCompact {m : ℝ | cramerRate m ≤ (r : EReal)}) ∧
    (∀ K : Set ℝ, IsClosed K →
      limsup (fun N : ℕ+ => logProb N K) atTop ≤ -(⨅ x ∈ K, cramerRate x)) ∧
    (∀ O : Set ℝ, IsOpen O →
      -(⨅ x ∈ O, cramerRate x) ≤ liminf (fun N : ℕ+ => logProb N O) atTop) := by
  refine ⟨⟨fun s _ => ⟨neg_one_lt_ratio s, besselRatio_lt_one s⟩,
    strictMono_ratio.injective.injOn, fun m hm => ?_⟩, fun m hm => ratio_tInv hm, tInv_ratio,
    fun m hm => cramerRate_of_mem hm, ?_, ?_, fun m hm => hasDerivAt_rateReal hm,
    tendsto_rateReal_right, tendsto_rateReal_left, isCompact_sublevel,
    fun K hK => cramer_upper hK, fun O hO => cramer_lower hO⟩
  · obtain ⟨s, hs⟩ := exists_ratio_eq hm
    exact ⟨s, Set.mem_univ _, hs⟩
  · exact cramerRate_of_not_mem (by simp)
  · exact cramerRate_of_not_mem (by simp)

end DGPS.FiniteN
