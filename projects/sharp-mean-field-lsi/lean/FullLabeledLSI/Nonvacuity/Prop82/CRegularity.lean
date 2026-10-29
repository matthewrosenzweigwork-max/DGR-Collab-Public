import FullLabeledLSI.Nonvacuity.Prop82.CVariation

/-!
# Lane C, module C5: regularity of a raw optimizer

A raw optimizer `ρ` has `√ρ = F ∘ secT` almost everywhere with `F ∈ C²(ℝ)` periodic,
nonnegative, and `F'' = F (B - R log F)` pointwise, where `B` is a smooth bounded trigonometric
polynomial.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

open SharpLSI

theorem nonneg_of_continuous_ae {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ᵐ x : ℝ, 0 ≤ f x) :
    ∀ x, 0 ≤ f x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx⟩ := hcon
  have hopen : IsOpen {y | f y < 0} := isOpen_lt hf continuous_const
  have hpos : 0 < volume {y | f y < 0} := hopen.measure_pos volume ⟨x, hx⟩
  have h0 : volume {y | ¬ 0 ≤ f y} = 0 := ae_iff.1 h
  have : {y | f y < 0} ⊆ {y | ¬ 0 ≤ f y} := fun y hy => not_le.2 hy
  exact absurd (measure_mono_null this h0) hpos.ne'

theorem memH1_congr_ae' {u v : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) (huv : u =ᵐ[haar 1] v) :
    MemH1 (haar 1) v ∧ (fun x => weakGrad v x 0) =ᵐ[haar 1] fun x => weakGrad u x 0 := by
  obtain ⟨hg, hgg⟩ := weakGrad_congr_ae hu.1 huv
  refine ⟨⟨hg, hu.2.1.ae_eq huv, hu.2.2.ae_eq ?_⟩, ?_⟩
  · filter_upwards [hgg] with y hy
    rw [hy]
  · filter_upwards [hgg] with y hy
    rw [hy]

theorem rawOptimizer_congr {ρ σ : Torus 1 → ℝ} (h : RawOptimizer ρ) (hae : ρ =ᵐ[haar 1] σ)
    (h0 : ∀ x, 0 ≤ σ x) (hH : MemH1 (haar 1) (fun x => Real.sqrt (σ x))) : RawOptimizer σ := by
  have hm := SharpLSI.densMeasure_congr_ae hae
  have hD := SharpLSI.dissipation_congr_ae (V := cosV) (W := cosW 1) hae
  refine ⟨⟨h0, ?_, hH, ?_⟩, ?_⟩
  · exact ((integral_congr_ae hae).symm).trans h.1.2.1
  · rw [← hm]; exact h.1.2.2.2
  · rw [← hm, ← hD]; exact h.2

/-- The trigonometric polynomial `B(r) = -(1/8) Σ c_j e_j(r)`. -/
noncomputable def trigB (c : Fin 5 → ℝ) (r : ℝ) : ℝ :=
  -(1 / 8) * (c 0 + c 1 * Real.cos (2 * π * r) + c 2 * Real.sin (2 * π * r) +
    c 3 * Real.cos (2 * π * r) ^ 2 + c 4 * (Real.sin (2 * π * r) * Real.cos (2 * π * r)))

theorem contDiff_trigB (c : Fin 5 → ℝ) : ContDiff ℝ ∞ (trigB c) := by
  unfold trigB
  fun_prop

theorem abs_trigB_le (c : Fin 5 → ℝ) (r : ℝ) :
    |trigB c r| ≤ (1 / 8) * (|c 0| + |c 1| + |c 2| + |c 3| + |c 4|) := by
  unfold trigB
  have h1 := Real.abs_cos_le_one (2 * π * r)
  have h2 := Real.abs_sin_le_one (2 * π * r)
  have a1 : |c 1 * Real.cos (2 * π * r)| ≤ |c 1| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
  have a2 : |c 2 * Real.sin (2 * π * r)| ≤ |c 2| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2
  have a3 : |c 3 * Real.cos (2 * π * r) ^ 2| ≤ |c 3| := by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) h1)
  have a4 : |c 4 * (Real.sin (2 * π * r) * Real.cos (2 * π * r))| ≤ |c 4| := by
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (by nlinarith [abs_nonneg (Real.sin (2 * π * r)), abs_nonneg (Real.cos (2 * π * r))])
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |c 0 + c 1 * Real.cos (2 * π * r) + c 2 * Real.sin (2 * π * r) +
        c 3 * Real.cos (2 * π * r) ^ 2 + c 4 * (Real.sin (2 * π * r) * Real.cos (2 * π * r))|
      ≤ |c 0| + |c 1 * Real.cos (2 * π * r)| + |c 2 * Real.sin (2 * π * r)| +
        |c 3 * Real.cos (2 * π * r) ^ 2| + |c 4 * (Real.sin (2 * π * r) * Real.cos (2 * π * r))| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

theorem gCos_lineT (r : ℝ) : gCos (lineT r) = Real.cos (2 * π * r) := gCos_coe _ _ rfl
theorem sCos_lineT (r : ℝ) : sCos (lineT r) = Real.sin (2 * π * r) := expT_im_coe _ _ rfl

theorem theta_lineT (c : Fin 5 → ℝ) (r : ℝ) :
    -(1 / 8) * (∑ j, c j * eTest j (lineT r)) = trigB c r := by
  unfold trigB
  rw [Fin.sum_univ_five]
  simp only [eTest, gCos_lineT, sCos_lineT]
  ring

theorem hasDerivAt_of_integral_rel {F H : ℝ → ℝ} (hH : Continuous H)
    (hrel : ∀ s t, F t - F s = ∫ r in s..t, H r) (t : ℝ) : HasDerivAt F (H t) t := by
  have h1 := (hH.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (F 0)
  convert h1 using 1
  funext x
  have := hrel 0 x
  linarith

theorem BM.ofF {F : ℝ → ℝ} (hc : Continuous F) : BM (fun y : Torus 1 => F (secT y 0)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0 : ℝ) 1)
  exact ⟨hc.measurable.comp (measurable_secT.eval (a := 0)),
    ⟨C, fun y => by simpa using hC _ (secT_mem_Icc y)⟩⟩

/-- Core of the regularity argument, for a continuous representative. -/
theorem regular_core {F : ℝ → ℝ} (hc : Continuous F) (hp : Function.Periodic F 1)
    (hnn : ∀ x, 0 ≤ F x) {g₀ : Torus 1 → ℝ}
    (hrel : ∀ s t, F t - F s = ∫ r in s..t, g₀ (lineT r))
    (hu : MemH1 (haar 1) (fun y => F (secT y 0)))
    (hgu : (fun y => weakGrad (fun y => F (secT y 0)) y 0) =ᵐ[haar 1] g₀)
    (hopt : RawOptimizer (fun y => F (secT y 0) ^ 2)) :
    ∃ (B : ℝ → ℝ) (M : ℝ), ContDiff ℝ 2 F ∧ ContDiff ℝ ∞ B ∧ (∀ x, |B x| ≤ M) ∧
      (∀ x, deriv (deriv F) x = F x * (B x - realRate * Real.log (F x))) := by
  set ũ : Torus 1 → ℝ := fun y => F (secT y 0) with hũ
  have hBM : BM ũ := BM.ofF hc
  have hũ0 : ∀ y, 0 ≤ ũ y := fun y => hnn _
  obtain ⟨c, hEL⟩ := euler_lagrange hBM hũ0 hu hopt
  -- the candidate weak derivative `h̃`
  set Th : Torus 1 → ℝ := fun x => ∑ j, c j * eTest j x with hTh
  have hThBM : BM Th := by
    have e : Th = fun x => c 0 * eTest 0 x + c 1 * eTest 1 x + c 2 * eTest 2 x +
        c 3 * eTest 3 x + c 4 * eTest 4 x := by
      funext x; simp only [hTh, Fin.sum_univ_five]
    rw [e]
    exact ((((BM.eTest 0).const_mul (c 0)).add ((BM.eTest 1).const_mul (c 1))).add
      ((BM.eTest 2).const_mul (c 2))).add ((BM.eTest 3).const_mul (c 3)) |>.add
      ((BM.eTest 4).const_mul (c 4))
  set ht : Torus 1 → ℝ := fun y => -(1 / 8) * (Th y * ũ y + 4 * realRate * (ũ y * Real.log (ũ y ^ 2)))
    with hht
  have hhtBM : BM ht :=
    (BM.const (-(1 / 8))).mul ((hThBM.mul hBM).add ((BM.const (4 * realRate)).mul hBM.mul_log_sq))
  have hweak : IsWeakGrad (fun y => weakGrad ũ y 0) (fun y _ => ht y) := by
    refine isWeakGrad_of_smooth_tests (memLp_weakGrad_zero hu) hhtBM.memLp ?_
    intro φ hφ
    have hφb := BM.of_isSmoothT hφ
    have h1 := hEL φ hφ
    have i1 := ((hThBM.mul hBM).mul hφb).integrable
    have i2 := (hBM.mul_log_sq.mul hφb).integrable
    have e1 : ∀ y, ht y * φ y = -(1 / 8) * (Th y * (ũ y * φ y)) +
        (-(1 / 2) * realRate) * (ũ y * φ y * Real.log (ũ y ^ 2)) := fun y => by
      simp only [hht]; ring
    simp_rw [e1]
    have i1' : Integrable (fun y => Th y * (ũ y * φ y)) (haar 1) := by
      refine i1.congr (Eventually.of_forall fun y => ?_); simp only; ring
    have i2' : Integrable (fun y => ũ y * φ y * Real.log (ũ y ^ 2)) (haar 1) := by
      refine i2.congr (Eventually.of_forall fun y => ?_); simp only; ring
    rw [integral_add (i1'.const_mul _) (i2'.const_mul _), integral_const_mul, integral_const_mul]
    simp only [hTh] at h1 ⊢
    linarith
  -- continuous representative of the derivative
  obtain ⟨G, hGc, hGp, hGrel, hGae, -⟩ := exists_continuous_rep hweak
    ((memLp_weakGrad_zero hu).integrable one_le_two) hhtBM.integrable
  -- `ũ ∘ lineT = F`, and the integrand is `Hn`
  have hlin : ∀ r, ũ (lineT r) = F r := by
    intro r
    obtain ⟨m, hm⟩ := secT_lineT_sub r
    simp only [hũ, hm]
    simpa using hp.int_mul m r
  set Hn : ℝ → ℝ := fun r => F r * trigB c r - realRate * (F r * Real.log (F r)) with hHn
  have hHnc : Continuous Hn :=
    (hc.mul (contDiff_trigB c).continuous).sub
      (continuous_const.mul (Real.continuous_mul_log.comp hc))
  have hhtline : ∀ r, ht (lineT r) = Hn r := by
    intro r
    simp only [hht, hlin, hHn]
    have h1 : Th (lineT r) = ∑ j, c j * eTest j (lineT r) := rfl
    have h2 := theta_lineT c r
    rw [h1] at *
    rw [Real.log_pow]
    have : (∑ j, c j * eTest j (lineT r)) = -8 * trigB c r := by linarith
    rw [this]; push_cast; ring
  have hGrel' : ∀ s t, G t - G s = ∫ r in s..t, Hn r := by
    intro s t
    rw [hGrel]
    exact intervalIntegral.integral_congr (fun r _ => hhtline r)
  have hGd : ∀ t, HasDerivAt G (Hn t) t := hasDerivAt_of_integral_rel hHnc hGrel'
  -- `F' = G`
  have hae1 : ∀ᵐ r : ℝ, g₀ (lineT r) = G r := by
    have h0 : ∀ᵐ y ∂haar 1, g₀ y = G (secT y 0) := by
      filter_upwards [hgu, hGae] with y h1 h2
      rw [← h1]; exact h2
    filter_upwards [ae_real_of_ae_torus h0] with r hr
    rw [hr]
    obtain ⟨m, hm⟩ := secT_lineT_sub r
    rw [hm]
    simpa using hGp.int_mul m r
  have hFrel : ∀ s t, F t - F s = ∫ r in s..t, G r := by
    intro s t
    rw [hrel]
    exact intervalIntegral.integral_congr_ae (hae1.mono fun r hr _ => hr)
  have hFd : ∀ t, HasDerivAt F (G t) t := hasDerivAt_of_integral_rel hGc hFrel
  have hdF : deriv F = G := funext fun t => (hFd t).deriv
  have hdG : deriv G = Hn := funext fun t => (hGd t).deriv
  have hG1 : ContDiff ℝ 1 G :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hGd t).differentiableAt, by rw [hdG]; exact hHnc⟩
  refine ⟨trigB c, (1 / 8) * (|c 0| + |c 1| + |c 2| + |c 3| + |c 4|), ?_, contDiff_trigB c,
    abs_trigB_le c, ?_⟩
  · have : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) F := by
      refine (contDiff_succ_iff_deriv (n := 1)).2 ⟨fun t => (hFd t).differentiableAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · rw [hdF]; exact hG1
    simpa using this
  · intro x
    rw [hdF, hdG]
    simp only [hHn]; ring

theorem F_secT_lineT {F : ℝ → ℝ} (hp : Function.Periodic F 1) (r : ℝ) :
    F (secT (lineT r) 0) = F r := by
  obtain ⟨m, hm⟩ := secT_lineT_sub r
  rw [hm]
  simpa using hp.int_mul m r

/-- **Regularity of a raw optimizer.** -/
theorem regular_representative {ρ : Torus 1 → ℝ} (h : RawOptimizer ρ) :
    ∃ (F B : ℝ → ℝ) (M : ℝ),
      ContDiff ℝ 2 F ∧ Function.Periodic F 1 ∧ (∀ x, 0 ≤ F x) ∧ ContDiff ℝ ∞ B ∧
      (∀ x, |B x| ≤ M) ∧
      (∀ x, deriv (deriv F) x = F x * (B x - realRate * Real.log (F x))) ∧
      (∫ x in (0 : ℝ)..1, F x ^ 2 = 1) ∧
      (∀ᵐ y ∂(haar 1), Real.sqrt (ρ y) = F (secT y 0)) := by
  have hH : MemH1 (haar 1) (fun y => Real.sqrt (ρ y)) := h.1.2.2.1
  obtain ⟨F, hc, hp, hrel, hae, haeR⟩ := exists_continuous_rep_memH1 hH
  have hnn : ∀ x, 0 ≤ F x := by
    refine nonneg_of_continuous_ae hc ?_
    filter_upwards [haeR] with r hr
    rw [← hr]; exact Real.sqrt_nonneg _
  have hae' : (fun y => Real.sqrt (ρ y)) =ᵐ[haar 1] fun y => F (secT y 0) := hae
  obtain ⟨hu, hgu⟩ := memH1_congr_ae' hH hae'
  have hρae : ρ =ᵐ[haar 1] fun y => F (secT y 0) ^ 2 := by
    filter_upwards [hae'] with y hy
    rw [← hy, Real.sq_sqrt (h.1.1 y)]
  have hsq : (fun x : Torus 1 => Real.sqrt (F (secT x 0) ^ 2)) = fun y : Torus 1 => F (secT y 0) :=
    funext fun x => Real.sqrt_sq (hnn _)
  have hopt : RawOptimizer (fun y => F (secT y 0) ^ 2) :=
    rawOptimizer_congr h hρae (fun x => sq_nonneg _)
    (by rw [hsq]; exact hu)
  obtain ⟨B, M, hF2, hB, hBM, hode⟩ := regular_core hc hp hnn hrel hu hgu hopt
  refine ⟨F, B, M, hF2, hp, hnn, hB, hBM, hode, ?_, hae⟩
  have hBMu := BM.ofF hc
  calc ∫ x in (0 : ℝ)..1, F x ^ 2
      = ∫ x in (0 : ℝ)..1, (fun y : Torus 1 => F (secT y 0) ^ 2) (lineT x) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [F_secT_lineT hp]
    _ = ∫ y, F (secT y 0) ^ 2 ∂haar 1 :=
        intervalIntegral_lineT hBMu.sq.integrable.aestronglyMeasurable
    _ = ∫ y, ρ y ∂haar 1 := (integral_congr_ae hρae).symm
    _ = 1 := h.1.2.1

end SharpLSI.FL.Prop82
