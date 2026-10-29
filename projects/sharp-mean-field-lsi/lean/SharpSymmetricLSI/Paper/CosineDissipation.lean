import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Paper.R37Particle

/-!
# (3.18): the expansion of the cosine dissipation (Phase 3, lane C)

For `u = √ρ ∈ H¹(m)`: `ρ = u²` has weak gradient `2uu'` (`isWeakGrad_sq`, chain rule with
`G_M(t) = M²t²/(M²+t²)` and closedness as `M → ∞`); the Fourier relation for weak gradients at the
modes `±1` gives `∫ 2uu'(g*ρ)' = aQ(ρ)`, and (3.18) follows by expanding the square. This replaces
the approximation argument of Appendix A cited after (3.18).
-/

open MeasureTheory InformationTheory Set Filter Topology Complex
open scoped ENNReal Real ContDiff

namespace SharpLSI

/-! ### The truncations `G_M(t) = M²t²/(M²+t²)` -/

/-- `r_M(t) = M²/(M²+t²)`. -/
noncomputable def ratM (M t : ℝ) : ℝ := M ^ 2 / (M ^ 2 + t ^ 2)

/-- `G_M(t) = t² r_M(t)`. -/
noncomputable def GM (M : ℝ) (t : ℝ) : ℝ := M ^ 2 * t ^ 2 / (M ^ 2 + t ^ 2)

theorem ratM_mem {M : ℝ} (hM : 0 < M) (t : ℝ) : 0 ≤ ratM M t ∧ ratM M t ≤ 1 := by
  unfold ratM
  have h : 0 < M ^ 2 + t ^ 2 := by positivity
  exact ⟨by positivity, (div_le_one h).mpr (by nlinarith [sq_nonneg t])⟩

theorem GM_eq (M t : ℝ) : GM M t = t ^ 2 * ratM M t := by unfold GM ratM; ring

theorem hasDerivAt_GM {M : ℝ} (hM : 0 < M) (t : ℝ) :
    HasDerivAt (GM M) (2 * t * ratM M t ^ 2) t := by
  have h : M ^ 2 + t ^ 2 ≠ 0 := by positivity
  have := (((hasDerivAt_id t).pow 2).const_mul (M ^ 2)).div
    (((hasDerivAt_id t).pow 2).const_add (M ^ 2)) h
  convert this using 1
  · funext s; simp [GM]
  · simp only [ratM, id, Pi.pow_apply]; field_simp; ring

theorem contDiff_GM {M : ℝ} (hM : 0 < M) : ContDiff ℝ 1 (GM M) := by
  have : GM M = fun t => M ^ 2 * t ^ 2 / (M ^ 2 + t ^ 2) := rfl
  rw [this]
  exact (contDiff_const.mul (contDiff_id.pow 2)).div (contDiff_const.add (contDiff_id.pow 2))
    fun t => by positivity

theorem abs_deriv_GM_le {M : ℝ} (hM : 0 < M) (t : ℝ) : |deriv (GM M) t| ≤ M := by
  have h : 0 < M ^ 2 + t ^ 2 := by positivity
  rw [(hasDerivAt_GM hM t).deriv, abs_mul, abs_mul, abs_two,
    abs_of_nonneg (sq_nonneg (ratM M t))]
  unfold ratM
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have h1 : 2 * M * |t| ≤ M ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg (M - |t|), sq_abs t, abs_nonneg t]
  have h2 : M ^ 2 ≤ M ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc 2 * |t| * (M ^ 2) ^ 2 = M ^ 2 * M * (2 * M * |t|) := by ring
    _ ≤ (M ^ 2 + t ^ 2) * M * (M ^ 2 + t ^ 2) := by gcongr
    _ = M * (M ^ 2 + t ^ 2) ^ 2 := by ring

theorem tendsto_ratM (t : ℝ) :
    Tendsto (fun n : ℕ => ratM ((n : ℝ) + 1) t) atTop (𝓝 1) := by
  have hlow : ∀ n : ℕ, 1 - t ^ 2 / ((n : ℝ) + 1) ≤ ratM ((n : ℝ) + 1) t := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    unfold ratM
    rw [le_div_iff₀ (by positivity)]
    have : t ^ 2 / ((n : ℝ) + 1) * ((n : ℝ) + 1) = t ^ 2 := by field_simp
    nlinarith [sq_nonneg t, div_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have h1 : Tendsto (fun n : ℕ => 1 - t ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (t ^ 2)
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow
    fun n => (ratM_mem (by positivity) t).2

theorem deriv_GM {M : ℝ} (hM : 0 < M) : deriv (GM M) = fun t => 2 * t * ratM M t ^ 2 :=
  funext fun t => (hasDerivAt_GM hM t).deriv

/-! ### `ρ = u²` has weak gradient `2uu'` -/

theorem isWeakGrad_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {u : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad u g) (hu : MemLp u 2 volume)
    (hg : ∀ k, MemLp (fun y => g y k) 2 volume) :
    IsWeakGrad (fun y => u y ^ 2) (fun y k => 2 * u y * g y k) := by
  have hui : Integrable u volume := hu.integrable one_le_two
  have hgi : ∀ k, Integrable (fun y => g y k) volume := fun k => (hg k).integrable one_le_two
  have hMp : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hpair : ∀ n : ℕ, IsWeakGrad (fun y => GM ((n : ℝ) + 1) (u y))
      (fun y k => deriv (GM ((n : ℝ) + 1)) (u y) * g y k) := fun n =>
    isWeakGrad_comp h hui hgi (contDiff_GM (hMp n)) (abs_deriv_GM_le (hMp n))
  have iU2 : Integrable (fun y => u y ^ 2) volume := hu.integrable_sq
  have iUG : ∀ k, Integrable (fun y => u y ^ 2 + g y k ^ 2) volume := fun k =>
    iU2.add (hg k).integrable_sq
  have hb2 : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b => by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hum := hu.aestronglyMeasurable
  have hgm : ∀ k, AEStronglyMeasurable (fun y => g y k) volume := fun k => (hg k).aestronglyMeasurable
  have hFi : ∀ n : ℕ, Integrable (fun y => GM ((n : ℝ) + 1) (u y)) volume := fun n =>
    Integrable.mono' iU2 ((contDiff_GM (hMp n)).continuous.comp_aestronglyMeasurable hum)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, GM_eq, abs_mul, abs_of_nonneg (sq_nonneg _),
          abs_of_nonneg (ratM_mem (hMp n) _).1]
        exact mul_le_of_le_one_right (sq_nonneg _) (ratM_mem (hMp n) _).2)
  have hGi : ∀ (n : ℕ) k, Integrable (fun y => deriv (GM ((n : ℝ) + 1)) (u y) * g y k) volume :=
    fun n k => Integrable.mono' (iUG k)
      ((((contDiff_GM (hMp n)).continuous_deriv le_rfl).comp_aestronglyMeasurable hum).mul
        (hgm k)) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, deriv_GM (hMp n)]
        have hr := ratM_mem (hMp n) (u y)
        calc |2 * u y * ratM ((n : ℝ) + 1) (u y) ^ 2 * g y k|
            = |2 * u y * g y k| * ratM ((n : ℝ) + 1) (u y) ^ 2 := by
              rw [show 2 * u y * ratM ((n : ℝ) + 1) (u y) ^ 2 * g y k =
                (2 * u y * g y k) * ratM ((n : ℝ) + 1) (u y) ^ 2 by ring, abs_mul,
                abs_of_nonneg (sq_nonneg (ratM ((n : ℝ) + 1) (u y)))]
          _ ≤ |2 * u y * g y k| * 1 := by gcongr; nlinarith
          _ ≤ _ := by rw [mul_one]; exact hb2 _ _)
  have hgl : ∀ k, Integrable (fun y => 2 * u y * g y k) volume := fun k =>
    Integrable.mono' (iUG k) ((hum.const_mul 2).mul (hgm k))
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb2 _ _)
  refine isWeakGrad_of_tendsto hpair hFi hGi iU2 hgl ?_ fun k => ?_
  · have := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun (n : ℕ) y => ‖GM ((n : ℝ) + 1) (u y) - u y ^ 2‖ₑ) (f := fun _ => 0)
      (fun y => ENNReal.ofReal (u y ^ 2))
      (fun n => ((hFi n).sub iU2).aestronglyMeasurable.enorm)
      (fun n => Eventually.of_forall fun y => by
        dsimp only
        rw [← ofReal_norm, Real.norm_eq_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [GM_eq, show u y ^ 2 * ratM ((n : ℝ) + 1) (u y) - u y ^ 2 =
          -(u y ^ 2 * (1 - ratM ((n : ℝ) + 1) (u y))) by ring, abs_neg, abs_of_nonneg
          (mul_nonneg (sq_nonneg _) (by linarith [(ratM_mem (hMp n) (u y)).2]))]
        exact mul_le_of_le_one_right (sq_nonneg _) (by linarith [(ratM_mem (hMp n) (u y)).1]))
      (by rw [← ofReal_integral_eq_lintegral_ofReal iU2 (Eventually.of_forall fun y =>
        sq_nonneg _)]; exact ENNReal.ofReal_ne_top)
      (Eventually.of_forall fun y => by
        have := ((tendsto_ratM (u y)).const_mul (u y ^ 2)).sub_const (u y ^ 2)
        simp only [mul_one, sub_self] at this
        have h2 := (continuous_enorm.tendsto 0).comp this
        simp only [enorm_zero] at h2
        refine h2.congr fun n => ?_
        simp [GM_eq])
    simpa using this
  · have := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun (n : ℕ) y => ‖deriv (GM ((n : ℝ) + 1)) (u y) * g y k - 2 * u y * g y k‖ₑ)
      (f := fun _ => 0) (fun y => ENNReal.ofReal (u y ^ 2 + g y k ^ 2))
      (fun n => ((hGi n k).sub (hgl k)).aestronglyMeasurable.enorm)
      (fun n => Eventually.of_forall fun y => by
        dsimp only
        rw [← ofReal_norm, Real.norm_eq_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hr := ratM_mem (hMp n) (u y)
        rw [deriv_GM (hMp n), show 2 * u y * ratM ((n : ℝ) + 1) (u y) ^ 2 * g y k -
          2 * u y * g y k = -((2 * u y * g y k) * (1 - ratM ((n : ℝ) + 1) (u y) ^ 2)) by ring,
          abs_neg, abs_mul]
        have h1 : |1 - ratM ((n : ℝ) + 1) (u y) ^ 2| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith
        calc |2 * u y * g y k| * |1 - ratM ((n : ℝ) + 1) (u y) ^ 2|
            ≤ |2 * u y * g y k| * 1 := by gcongr
          _ ≤ _ := by rw [mul_one]; exact hb2 _ _)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (iUG k) (Eventually.of_forall fun y =>
        by positivity)]; exact ENNReal.ofReal_ne_top)
      (Eventually.of_forall fun y => by
        have := ((((tendsto_ratM (u y)).pow 2).const_mul (2 * u y)).mul_const (g y k)).sub_const
          (2 * u y * g y k)
        simp only [one_pow, mul_one, sub_self] at this
        have h2 := (continuous_enorm.tendsto 0).comp this
        simp only [enorm_zero] at h2
        refine h2.congr fun n => ?_
        simp [deriv_GM (hMp n)])
    simpa using this

/-! ### The Fourier relations at the modes `±1` -/

theorem sCos_secT (y : Torus 1) : sCos y = Real.sin (2 * π * secT y 0) := by
  conv_lhs => rw [← liftT_secT y]
  exact expT_im_coe (liftT (secT y)) (secT y 0) rfl

theorem mFourier_neg_one (t : Torus 1) :
    UnitAddTorus.mFourier (-(fun _ : Fin 1 => (1 : ℤ))) t = (starRingEnd ℂ) (expT t) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_one, Pi.neg_apply]
  rw [fourier_neg]; rfl

theorem fourierCoeff_one_re_im {F : Torus 1 → ℝ} (hF : Integrable F (haar 1)) :
    (UnitAddTorus.mFourierCoeff (fun y => (F y : ℂ)) (fun _ => 1)).re = ∫ y, gCos y * F y ∂haar 1 ∧
    (UnitAddTorus.mFourierCoeff (fun y => (F y : ℂ)) (fun _ => 1)).im =
      -∫ y, sCos y * F y ∂haar 1 := by
  have hie : Integrable (fun t => (starRingEnd ℂ) (expT t) • (F t : ℂ)) (haar 1) := by
    refine Integrable.mono' hF.norm ((continuous_star.comp continuous_expT).aestronglyMeasurable.smul
      hF.ofReal.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h1 : ‖expT x‖ = 1 := by simp [expT, fourier_apply]
    rw [norm_smul, Complex.norm_conj, h1, one_mul, Complex.norm_real]
  rw [mFourierCoeff_eq_integral]
  simp_rw [mFourier_neg_one]
  have hr := integral_re hie
  have hm := integral_im hie
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hr hm
  rw [← hr, ← hm, ← integral_neg]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_add, gCos, sCos,
    neg_mul]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

/-- For a weak pair `(f, g)` on the circle:
`∫ cos·g = 2π ∫ sin·f` and `∫ sin·g = -2π ∫ cos·f`. -/
theorem weak_fourier_relations {f : Torus 1 → ℝ} {g : Torus 1 → Fin 1 → ℝ} (h : IsWeakGrad f g)
    (hf : Integrable f (haar 1)) (hg : Integrable (fun y => g y 0) (haar 1)) :
    ∫ y, gCos y * g y 0 ∂haar 1 = 2 * π * ∫ y, sCos y * f y ∂haar 1 ∧
      ∫ y, sCos y * g y 0 ∂haar 1 = -(2 * π) * ∫ y, gCos y * f y ∂haar 1 := by
  have hg' : ∀ j, Integrable (fun y => g y j) (haar 1) := fun j => by
    rw [Subsingleton.elim j 0]; exact hg
  have key := mFourierCoeff_grad h hf hg' (fun _ => 1) 0
  have hG := fourierCoeff_one_re_im hg
  have hF := fourierCoeff_one_re_im hf
  have hre := congrArg Complex.re key
  have him := congrArg Complex.im key
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Int.cast_one, Complex.one_re, Complex.one_im, mul_zero, zero_mul,
    sub_zero, add_zero, mul_one, zero_add, Complex.re_ofNat, Complex.im_ofNat] at hre him
  rw [hG.1, hF.2] at hre
  rw [hG.2, hF.1] at him
  constructor <;> nlinarith [hre, him]

/-! ### (3.18) -/

theorem fderiv_trig_lift (A B : ℝ) (z : Fin 1 → ℝ) :
    fderiv ℝ (fun z : Fin 1 → ℝ => Real.cos (2 * π * z 0) * A + Real.sin (2 * π * z 0) * B) z
        (Pi.single 0 1) =
      2 * π * (-A * Real.sin (2 * π * z 0) + B * Real.cos (2 * π * z 0)) := by
  have hc : ContDiff ℝ ⊤ (fun z : Fin 1 → ℝ =>
      Real.cos (2 * π * z 0) * A + Real.sin (2 * π * z 0) * B) :=
    ((Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).mul contDiff_const).add
      ((Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).mul contDiff_const)
  refine fderiv_apply_of_line ((hc.differentiable (by simp)) z) ?_
  have h1 := ((((hasDerivAt_id (0 : ℝ)).const_add (z 0)).const_mul (2 * π)).cos.mul_const A).add
    ((((hasDerivAt_id (0 : ℝ)).const_add (z 0)).const_mul (2 * π)).sin.mul_const B)
  convert h1 using 1
  · funext t; simp
  · simp; ring

/-- (3.18). -/
theorem cosine_dissipation_expansion_aux {κ : ℝ} (hκ : 0 < κ) {ρ : Torus 1 → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1)
    (hI : fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤) :
    dissipation cosV (cosW κ) ρ = fisherInfo (densMeasure ρ) (haar 1) +
      ENNReal.ofReal (2 * aCos * κ * firstMode ρ) +
      ENNReal.ofReal (κ ^ 2 * ∫ x, ρ x * weakGrad (gConv ρ) x 0 ^ 2 ∂haar 1) := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  have hi := integrable_of_integral_eq_one hρ1
  have hu2ρ : ∀ x, u x ^ 2 = ρ x := fun x => Real.sq_sqrt (hρ0 x)
  -- the Fisher information
  have hcond : densMeasure ρ ≪ haar 1 ∧ MemH1 (haar 1)
      (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (haar 1) x).toReal) := by
    by_contra hc; apply hI; unfold fisherInfo; rw [if_neg hc]
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have huv : (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (haar 1) x).toReal) =ᵐ[haar 1] u := by
    filter_upwards [Measure.rnDeriv_withDensity₀ (haar 1) hm] with x hx
    rw [hu_def, show densMeasure ρ = (haar 1).withDensity _ from rfl, hx,
      ENNReal.toReal_ofReal (hρ0 x)]
  obtain ⟨hH1, hdir⟩ := memH1_congr_ae (Q := haar 1) (Measure.AbsolutelyContinuous.refl _)
    (Measure.AbsolutelyContinuous.refl _) hcond.2 huv
  have hfi : fisherInfo (densMeasure ρ) (haar 1) = 4 * dirichlet (haar 1) u := by
    unfold fisherInfo; rw [if_pos hcond, hdir]
  -- weak gradients
  have hw := isWeakGrad_weakGrad hH1.1
  have hu2 : MemLp u 2 (haar 1) := hH1.2.1
  have hg2 : MemLp (fun x => weakGrad u x 0) 2 (haar 1) :=
    hH1.2.2.of_le (hw.aestronglyMeasurable_grad 0) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ 0)
  have hg2' : ∀ j, MemLp (fun x => weakGrad u x j) 2 (haar 1) := fun j => by
    rw [Subsingleton.elim j 0]; exact hg2
  have hsq := isWeakGrad_sq hw hu2 hg2'
  have hfrel := weak_fourier_relations hsq hu2.integrable_sq
    (by
      refine Integrable.mono' (hu2.integrable_sq.add hg2.integrable_sq)
        ((hu2.aestronglyMeasurable.const_mul 2).mul hg2.aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      show ‖2 * u y * weakGrad u y 0‖ ≤ u y ^ 2 + weakGrad u y 0 ^ 2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [sq_nonneg (u y + weakGrad u y 0),
        sq_nonneg (u y - weakGrad u y 0)])
  simp_rw [hu2ρ] at hfrel
  -- the convolution term
  set A := ∫ y, gCos y * ρ y ∂haar 1 with hA
  set B := ∫ y, sCos y * ρ y ∂haar 1 with hB
  set Gp : Torus 1 → ℝ := fun x => 2 * π * (-A * sCos x + B * gCos x) with hGp
  have hGc : Continuous Gp := continuous_const.mul ((continuous_const.mul continuous_sCos).add
    (continuous_const.mul continuous_gCos))
  have hG1 : ContDiff ℝ 1 (gConv ρ ∘ liftT) := (contDiff_gConv_lift hρ1).of_le le_top
  have hG' : ∀ᵐ x ∂haar 1, weakGrad (gConv ρ) x 0 = Gp x := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hG1] with x hx
    rw [hx]
    simp only
    rw [gConv_lift hρ1, fderiv_trig_lift, hGp, ← gCos_secT, ← sCos_secT]
  -- the dissipation
  rw [dissipation_cos κ hρ1 hH1]
  set Cg := 2 * π * (|A| + |B|) with hCgdef
  have hCg : ∀ x, |Gp x| ≤ Cg := fun x => by
    have hin : |-A * sCos x + B * gCos x| ≤ |A| + |B| := by
      calc |-A * sCos x + B * gCos x| ≤ |-A * sCos x| + |B * gCos x| := abs_add_le _ _
        _ = |A| * |sCos x| + |B| * |gCos x| := by rw [abs_mul, abs_mul, abs_neg]
        _ ≤ |A| * 1 + |B| * 1 := by
            gcongr
            · exact abs_sCos_le x
            · exact abs_gCos_le x
        _ = |A| + |B| := by ring
    rw [hGp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), hCgdef]
    exact mul_le_mul_of_nonneg_left hin (by positivity)
  have hCg0 : 0 ≤ Cg := by positivity
  set u' : Torus 1 → ℝ := fun x => weakGrad u x 0 with hu'
  have iU2 : Integrable (fun x => u x ^ 2) (haar 1) := hu2.integrable_sq
  have iG2 : Integrable (fun x => u' x ^ 2) (haar 1) := hg2.integrable_sq
  have hb2 : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b => by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have i2uu : ∀ {F : Torus 1 → ℝ} {C : ℝ}, 0 ≤ C → Continuous F → (∀ x, |F x| ≤ C) →
      Integrable (fun x => 2 * u x * u' x * F x) (haar 1) := fun {F} {C} hC hF hFb =>
    Integrable.mono' ((iU2.add iG2).const_mul C)
      (((hu2.aestronglyMeasurable.const_mul 2).mul hg2.aestronglyMeasurable).mul
        hF.aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |2 * u x * u' x| * |F x| ≤ (u x ^ 2 + u' x ^ 2) * C :=
              mul_le_mul (hb2 _ _) (hFb x) (abs_nonneg _) (by positivity)
          _ = C * (u x ^ 2 + u' x ^ 2) := by ring)
  have iUG := i2uu hCg0 hGc hCg
  have iUU : Integrable (fun x => u x ^ 2 * Gp x ^ 2) (haar 1) :=
    Integrable.mono' (iU2.const_mul (Cg ^ 2))
      ((hu2.aestronglyMeasurable.pow 2).mul (hGc.aestronglyMeasurable.pow 2))
      (Eventually.of_forall fun x => by
        have hG2 : Gp x ^ 2 ≤ Cg ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg x) 2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm (Cg ^ 2)]
        exact mul_le_mul_of_nonneg_left hG2 (sq_nonneg _))
  have hpt : ∀ x, (2 * u' x + κ * u x * Gp x) ^ 2 =
      4 * u' x ^ 2 + (2 * κ * (2 * u x * u' x * Gp x) + κ ^ 2 * (u x ^ 2 * Gp x ^ 2)) :=
    fun x => by ring
  have iD : Integrable (fun x => (2 * u' x + κ * u x * Gp x) ^ 2) (haar 1) := by
    simp_rw [hpt]
    exact (iG2.const_mul 4).add ((iUG.const_mul _).add (iUU.const_mul _))
  have hL : ∫⁻ x, ENNReal.ofReal ((2 * weakGrad u x 0 + κ * u x * weakGrad (gConv ρ) x 0) ^ 2)
      ∂haar 1 = ENNReal.ofReal (∫ x, (2 * u' x + κ * u x * Gp x) ^ 2 ∂haar 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal iD (Eventually.of_forall fun x => sq_nonneg _)]
    exact lintegral_congr_ae (hG'.mono fun x hx => by dsimp only; rw [hx])
  rw [hL]
  have hexp : ∫ x, (2 * u' x + κ * u x * Gp x) ^ 2 ∂haar 1 =
      4 * (∫ x, u' x ^ 2 ∂haar 1) + (2 * κ * (∫ x, 2 * u x * u' x * Gp x ∂haar 1) +
        κ ^ 2 * ∫ x, u x ^ 2 * Gp x ^ 2 ∂haar 1) := by
    simp_rw [hpt]
    rw [integral_add (f := fun x => 4 * u' x ^ 2)
      (g := fun x => 2 * κ * (2 * u x * u' x * Gp x) + κ ^ 2 * (u x ^ 2 * Gp x ^ 2))
      (iG2.const_mul 4) ((iUG.const_mul _).add (iUU.const_mul _)),
      integral_add (f := fun x => 2 * κ * (2 * u x * u' x * Gp x))
      (g := fun x => κ ^ 2 * (u x ^ 2 * Gp x ^ 2)) (iUG.const_mul _) (iUU.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hmid : ∫ x, 2 * u x * u' x * Gp x ∂haar 1 = aCos * firstMode ρ := by
    have i1 := i2uu zero_le_one continuous_sCos abs_sCos_le
    have i2 := i2uu zero_le_one continuous_gCos abs_gCos_le
    have e : ∀ x, 2 * u x * u' x * Gp x =
        2 * π * (-A * (2 * u x * u' x * sCos x) + B * (2 * u x * u' x * gCos x)) :=
      fun x => by rw [hGp]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
      integral_const_mul]
    have r1 : ∫ x, 2 * u x * u' x * gCos x ∂haar 1 = 2 * π * B := by
      rw [hB, ← hfrel.1]; congr 1; funext x; ring
    have r2 : ∫ x, 2 * u x * u' x * sCos x ∂haar 1 = -(2 * π) * A := by
      rw [hA, ← hfrel.2]; congr 1; funext x; ring
    rw [r1, r2, firstMode_eq hi]
    unfold aCos
    ring
  have hlast : ∫ x, u x ^ 2 * Gp x ^ 2 ∂haar 1 =
      ∫ x, ρ x * weakGrad (gConv ρ) x 0 ^ 2 ∂haar 1 :=
    integral_congr_ae (hG'.mono fun x hx => by dsimp only; rw [hx, hu2ρ])
  have hfisher : fisherInfo (densMeasure ρ) (haar 1) =
      ENNReal.ofReal (4 * ∫ x, u' x ^ 2 ∂haar 1) := by
    rw [hfi]
    unfold dirichlet
    have : ∀ x, sqNorm (weakGrad u x) = u' x ^ 2 := fun x => by
      simp [sqNorm, hu']
    simp_rw [this]
    rw [← ofReal_integral_eq_lintegral_ofReal iG2 (Eventually.of_forall fun x => sq_nonneg _),
      ENNReal.ofReal_mul (by norm_num)]
    simp
  have hX : 0 ≤ ∫ x, u' x ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  have hQ : 0 ≤ firstMode ρ := Complex.normSq_nonneg _
  have hJ : 0 ≤ ∫ x, ρ x * weakGrad (gConv ρ) x 0 ^ 2 ∂haar 1 :=
    integral_nonneg fun x => mul_nonneg (hρ0 x) (sq_nonneg _)
  have ha : 0 ≤ aCos := by unfold aCos; positivity
  rw [hexp, hmid, hlast, hfisher, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end SharpLSI
