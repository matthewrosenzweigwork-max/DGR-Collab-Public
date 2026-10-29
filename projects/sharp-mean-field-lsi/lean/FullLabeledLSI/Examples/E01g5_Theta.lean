import FullLabeledLSI.Examples.E01g1_Basic

/-!
# Lane D, Task C (E01g5): Taylor remainder of the cubic interaction functional (skeleton)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- `𝒰_r(σ) = 2∫σ (C''*σ) + ∫σ (C'*σ)² + r ∫σ (C*σ)` for a density `σ`. -/
noncomputable def Uf (C : Torus 1 → ℝ) (r : ℝ) (σ : Torus 1 → ℝ) : ℝ :=
  2 * ∫ x, σ x * convT (dT (dT C)) σ x ∂haar 1 + ∫ x, σ x * (convT (dT C) σ x) ^ 2 ∂haar 1 +
    r * ∫ x, σ x * convT C σ x ∂haar 1

/-- The common one-site potential `A = 4 C''*ρ + (C'*ρ)² - 2 C'*(ρ (C'*ρ)) + 2r C*ρ`
(the gradient of `Uf` at `ρ`). -/
noncomputable def Apot (C : Torus 1 → ℝ) (r : ℝ) (ρ : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  4 * convT (dT (dT C)) ρ x + (convT (dT C) ρ x) ^ 2 -
    2 * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x + 2 * r * convT C ρ x

theorem uft_bound {f : Torus 1 → ℝ} (hf : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, ?_, fun x => by simpa using hM x (Set.mem_univ _)⟩
  exact le_trans (norm_nonneg _) (hM 0 (Set.mem_univ _))

theorem uft_continuous_convT {g f : Torus 1 → ℝ} (hg : Continuous g) (hf : Integrable f (haar 1)) :
    Continuous (convT g f) := by
  obtain ⟨M, hM0, hM⟩ := uft_bound hg
  unfold convT
  refine continuous_of_dominated (bound := fun y => M * |f y|) ?_ ?_ (hf.abs.const_mul M) ?_
  · intro x; exact (integrable_conv_mul hg hf x).aestronglyMeasurable
  · intro x
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  · exact Eventually.of_forall fun y =>
      (hg.comp (continuous_sub_right y)).mul continuous_const

theorem uft_abs_convT_le {g f : Torus 1 → ℝ} (hg : Continuous g) (hf : Integrable f (haar 1))
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) (x : Torus 1) :
    |convT g f x| ≤ M * ∫ y, |f y| ∂haar 1 := by
  unfold convT
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono (integrable_conv_mul hg hf x).norm (hf.abs.const_mul M) fun y => ?_
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)

theorem uft_convT_add {g f h : Torus 1 → ℝ} (hg : Continuous g) (hf : Integrable f (haar 1))
    (hh : Integrable h (haar 1)) (x : Torus 1) :
    convT g (fun y => f y + h y) x = convT g f x + convT g h x := by
  unfold convT
  rw [← integral_add (integrable_conv_mul hg hf x) (integrable_conv_mul hg hh x)]
  congr 1; funext y; ring

theorem uft_convT_sub {g f h : Torus 1 → ℝ} (hg : Continuous g) (hf : Integrable f (haar 1))
    (hh : Integrable h (haar 1)) (x : Torus 1) :
    convT g (fun y => f y - h y) x = convT g f x - convT g h x := by
  unfold convT
  rw [← integral_sub (integrable_conv_mul hg hf x) (integrable_conv_mul hg hh x)]
  congr 1; funext y; ring

theorem uft_integrable_mul_cont {f c : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hc : Continuous c) :
    Integrable (fun x => f x * c x) (haar 1) := by
  obtain ⟨M, -, hM⟩ := uft_bound hc
  exact hf.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hM x)

theorem uft_integrable_cont_mul {f c : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hc : Continuous c) :
    Integrable (fun x => c x * f x) (haar 1) := by
  simpa [mul_comm] using uft_integrable_mul_cont hf hc

theorem uft_swap {g f h : Torus 1 → ℝ} (hg : Continuous g) (hf : Integrable f (haar 1))
    (hh : Integrable h (haar 1)) :
    ∫ x, f x * convT g h x ∂haar 1 = ∫ y, h y * convT (fun z => g (-z)) f y ∂haar 1 := by
  obtain ⟨M, -, hM⟩ := uft_bound hg
  have key : Integrable (Function.uncurry fun x y : Torus 1 => f x * (g (x - y) * h y))
      ((haar 1).prod (haar 1)) := by
    have h1 := hf.mul_prod hh
    have h2 : Integrable (fun p : Torus 1 × Torus 1 => g (p.1 - p.2) * (f p.1 * h p.2))
        ((haar 1).prod (haar 1)) :=
      h1.bdd_mul (c := M) (f := fun p : Torus 1 × Torus 1 => g (p.1 - p.2))
        (hg.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
        (Eventually.of_forall fun p => by simpa using hM _)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]; ring
  unfold convT
  calc ∫ x, f x * ∫ y, g (x - y) * h y ∂haar 1 ∂haar 1
      = ∫ x, ∫ y, f x * (g (x - y) * h y) ∂haar 1 ∂haar 1 := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y, ∫ x, f x * (g (x - y) * h y) ∂haar 1 ∂haar 1 := integral_integral_swap key
    _ = _ := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext x
        simp only [neg_sub]; ring


theorem uft_lift1_neg (t : ℝ) : lift1 (-t) = -lift1 t := by
  funext i; fin_cases i
  simp [lift1_apply]

theorem uft_dT_odd_of_even {f : Torus 1 → ℝ} (hf : ∀ x, f (-x) = f x) (x : Torus 1) :
    dT f (-x) = - dT f x := by
  rw [← lift1_rep x, ← uft_lift1_neg, dT_lift1, dT_lift1]
  have e : (fun s : ℝ => f (lift1 (-s))) = fun s => f (lift1 s) := by
    funext s; rw [uft_lift1_neg, hf]
  have := deriv_comp_neg (f := fun s : ℝ => f (lift1 s)) (x := rep x)
  simp only [e] at this
  rw [this]; ring

theorem uft_dT_even_of_odd {f : Torus 1 → ℝ} (hf : ∀ x, f (-x) = - f x) (x : Torus 1) :
    dT f (-x) = dT f x := by
  rw [← lift1_rep x, ← uft_lift1_neg, dT_lift1, dT_lift1]
  have e : (fun s : ℝ => f (lift1 (-s))) = fun s => - f (lift1 s) := by
    funext s; rw [uft_lift1_neg, hf]
  have := deriv_comp_neg (f := fun s : ℝ => f (lift1 s)) (x := rep x)
  simp only [e, deriv.fun_neg] at this
  linarith

theorem uft_smooth_convT_nonneg {g w : Torus 1 → ℝ} (hg : IsSmoothT g) (hw0 : ∀ x, 0 ≤ w x)
    (hwi : Integrable w (haar 1)) : IsSmoothT (convT g w) := by
  have : IsFiniteMeasure (densMeasure w) := ⟨by
    rw [densMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hwi (Eventually.of_forall hw0)]
    exact ENNReal.ofReal_lt_top⟩
  have : convT g w = fun x => ∫ y, g (x - y) ∂densMeasure w := by
    funext x; unfold convT
    have hm : AEMeasurable (fun x => ENNReal.ofReal (w x)) (haar 1) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hwi.aestronglyMeasurable.aemeasurable
    rw [densMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
    congr 1; funext y; ring
  rw [this]; exact isSmoothT_conv hg _

theorem uft_smooth_convT {g w : Torus 1 → ℝ} (hg : IsSmoothT g) (hwi : Integrable w (haar 1)) :
    IsSmoothT (convT g w) := by
  have hgc := continuous_of_smooth hg
  have h1 := uft_smooth_convT_nonneg hg (w := fun x => max (w x) 0) (fun x => le_max_right _ _)
    (hwi.pos_part)
  have h2 := uft_smooth_convT_nonneg hg (w := fun x => max (- w x) 0) (fun x => le_max_right _ _)
    (hwi.neg_part)
  have e : convT g w = fun x => convT g (fun y => max (w y) 0) x - convT g (fun y => max (- w y) 0) x := by
    funext x
    rw [← uft_convT_sub hgc hwi.pos_part hwi.neg_part]
    unfold convT; congr 1; funext y
    rcases le_total 0 (w y) with h | h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
  rw [e, isSmoothT_iff_lift1]
  rw [isSmoothT_iff_lift1] at h1 h2
  exact h1.sub h2

theorem isSmoothT_Apot' {C : Torus 1 → ℝ} (hC : GoodKernel C) (r : ℝ) {ρ : Torus 1 → ℝ}
    (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    IsSmoothT (Apot C r ρ) := by
  have hρi := integrable_of_integral_eq_one' h1
  have s0 := hC.smooth
  have s1 := isSmoothT_dT s0
  have s2 := isSmoothT_dT s1
  have hb : IsSmoothT (convT (dT C) ρ) := uft_smooth_convT s1 hρi
  have hbc := continuous_of_smooth hb
  have hw : IsSmoothT (convT (dT C) (fun y => ρ y * convT (dT C) ρ y)) :=
    uft_smooth_convT s1 (uft_integrable_mul_cont hρi hbc)
  have h2 : IsSmoothT (convT (dT (dT C)) ρ) := uft_smooth_convT s2 hρi
  have h0 : IsSmoothT (convT C ρ) := uft_smooth_convT s0 hρi
  rw [isSmoothT_iff_lift1] at hb hw h2 h0 ⊢
  unfold Apot
  exact (((contDiff_const.mul h2).add (hb.pow 2)).sub (contDiff_const.mul hw)).add
    (contDiff_const.mul h0)


theorem uft_quad_exp {g ρ δ : Torus 1 → ℝ} (hg : Continuous g) (hge : ∀ x, g (-x) = g x)
    (hρ : Integrable ρ (haar 1)) (hδ : Integrable δ (haar 1)) :
    ∫ x, (ρ x + δ x) * convT g (fun y => ρ y + δ y) x ∂haar 1 =
      ∫ x, ρ x * convT g ρ x ∂haar 1 + 2 * ∫ x, δ x * convT g ρ x ∂haar 1 +
        ∫ x, δ x * convT g δ x ∂haar 1 := by
  have cρ := uft_continuous_convT hg hρ
  have cδ := uft_continuous_convT hg hδ
  have i1 : Integrable (fun x => ρ x * convT g ρ x) (haar 1) := uft_integrable_mul_cont hρ cρ
  have i2 : Integrable (fun x => ρ x * convT g δ x) (haar 1) := uft_integrable_mul_cont hρ cδ
  have i3 : Integrable (fun x => δ x * convT g ρ x) (haar 1) := uft_integrable_mul_cont hδ cρ
  have i4 : Integrable (fun x => δ x * convT g δ x) (haar 1) := uft_integrable_mul_cont hδ cδ
  have hsw : ∫ x, ρ x * convT g δ x ∂haar 1 = ∫ x, δ x * convT g ρ x ∂haar 1 := by
    rw [uft_swap hg hρ hδ]
    congr 1; funext y; congr 1
    unfold convT; congr 1; funext z; beta_reduce; rw [hge]
  have hfun : (fun x => (ρ x + δ x) * convT g (fun y => ρ y + δ y) x) =
      fun x => ((ρ x * convT g ρ x + ρ x * convT g δ x) + δ x * convT g ρ x) +
        δ x * convT g δ x := by
    funext x; rw [uft_convT_add hg hρ hδ]; ring
  have i12 : Integrable (fun x => ρ x * convT g ρ x + ρ x * convT g δ x) (haar 1) := i1.add i2
  have i123 : Integrable (fun x => (ρ x * convT g ρ x + ρ x * convT g δ x) + δ x * convT g ρ x)
      (haar 1) := i12.add i3
  rw [hfun, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, hsw]
  ring

theorem uft_quad_bound {g δ : Torus 1 → ℝ} (hg : Continuous g) (hδ : Integrable δ (haar 1))
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    |∫ x, δ x * convT g δ x ∂haar 1| ≤ M * (∫ x, |δ x| ∂haar 1) ^ 2 := by
  have cδ := uft_continuous_convT hg hδ
  have hD0 : 0 ≤ ∫ x, |δ x| ∂haar 1 := integral_nonneg fun x => abs_nonneg _
  have hMD : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have : ∫ x, ‖δ x * convT g δ x‖ ∂haar 1 ≤ ∫ x, (M * ∫ y, |δ y| ∂haar 1) * |δ x| ∂haar 1 := by
    refine integral_mono (uft_integrable_mul_cont hδ cδ).norm (hδ.abs.const_mul _) fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (uft_abs_convT_le hg hδ hM x) (abs_nonneg _)
  refine this.trans ?_
  rw [integral_const_mul]; apply le_of_eq; ring

theorem uft_cubic_exp {c ρ δ : Torus 1 → ℝ} (hc : Continuous c) (hco : ∀ x, c (-x) = - c x)
    (hρ : Integrable ρ (haar 1)) (hδ : Integrable δ (haar 1)) {B : ℝ} (hB : ∀ x, |c x| ≤ B)
    (hρ1 : ∫ x, |ρ x| ∂haar 1 ≤ 1) (hD : ∫ x, |δ x| ∂haar 1 ≤ 2) :
    ∃ R : ℝ, |R| ≤ 5 * B ^ 2 * (∫ x, |δ x| ∂haar 1) ^ 2 ∧
      ∫ x, (ρ x + δ x) * (convT c (fun y => ρ y + δ y) x) ^ 2 ∂haar 1 =
        ∫ x, ρ x * (convT c ρ x) ^ 2 ∂haar 1 +
          (∫ x, δ x * (convT c ρ x) ^ 2 ∂haar 1 -
            2 * ∫ x, δ x * convT c (fun y => ρ y * convT c ρ y) x ∂haar 1) + R := by
  set b := convT c ρ with hbdef
  set e := convT c δ with hedef
  have cb : Continuous b := uft_continuous_convT hc hρ
  have ce : Continuous e := uft_continuous_convT hc hδ
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  set D := ∫ x, |δ x| ∂haar 1 with hDdef
  have hD0 : 0 ≤ D := integral_nonneg fun x => abs_nonneg _
  have hbB : ∀ x, |b x| ≤ B := fun x => by
    have := uft_abs_convT_le hc hρ hB x
    have h2 : B * ∫ y, |ρ y| ∂haar 1 ≤ B * 1 := mul_le_mul_of_nonneg_left hρ1 hB0
    simp only [hbdef]; linarith
  have heB : ∀ x, |e x| ≤ B * D := fun x => uft_abs_convT_le hc hδ hB x
  have i1 : Integrable (fun x => ρ x * b x ^ 2) (haar 1) := uft_integrable_mul_cont hρ (cb.pow 2)
  have i2 : Integrable (fun x => δ x * b x ^ 2) (haar 1) := uft_integrable_mul_cont hδ (cb.pow 2)
  have i3 : Integrable (fun x => ρ x * (b x * e x)) (haar 1) :=
    uft_integrable_mul_cont hρ (cb.mul ce)
  have i4 : Integrable (fun x => δ x * (b x * e x)) (haar 1) :=
    uft_integrable_mul_cont hδ (cb.mul ce)
  have i5 : Integrable (fun x => ρ x * e x ^ 2) (haar 1) := uft_integrable_mul_cont hρ (ce.pow 2)
  have i6 : Integrable (fun x => δ x * e x ^ 2) (haar 1) := uft_integrable_mul_cont hδ (ce.pow 2)
  have i456 : Integrable (fun x => 2 * (δ x * (b x * e x)) + ρ x * e x ^ 2 + δ x * e x ^ 2)
      (haar 1) := ((i4.const_mul 2).add i5).add i6
  have i12 : Integrable (fun x => ρ x * b x ^ 2 + δ x * b x ^ 2) (haar 1) := i1.add i2
  have i123 : Integrable (fun x => ρ x * b x ^ 2 + δ x * b x ^ 2 + 2 * (ρ x * (b x * e x)))
      (haar 1) := i12.add (i3.const_mul 2)
  -- the odd Fubini step
  have hρb : Integrable (fun y => ρ y * b y) (haar 1) := uft_integrable_mul_cont hρ cb
  have hF3 : ∫ x, ρ x * (b x * e x) ∂haar 1 =
      - ∫ x, δ x * convT c (fun y => ρ y * b y) x ∂haar 1 := by
    have := uft_swap hc hρb hδ
    have e1 : (fun x => ρ x * b x * convT c δ x) = fun x => ρ x * (b x * e x) := by
      funext x; simp only [hedef]; ring
    have e2 : ∀ y, convT (fun z => c (-z)) (fun y => ρ y * b y) y =
        - convT c (fun y => ρ y * b y) y := by
      intro y; unfold convT
      rw [← integral_neg]; congr 1; funext z; beta_reduce; rw [hco]; ring
    simp only [e2, mul_neg, integral_neg] at this
    rw [e1] at this
    exact this
  refine ⟨∫ x, 2 * (δ x * (b x * e x)) + ρ x * e x ^ 2 + δ x * e x ^ 2 ∂haar 1, ?_, ?_⟩
  · -- the remainder bound
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (g := fun x => (2 * B * (B * D)) * |δ x| +
      (B * D) ^ 2 * |ρ x| + (B * D) ^ 2 * |δ x|) ?_ ?_).trans ?_
    · exact (((hδ.abs.const_mul _).add (hρ.abs.const_mul _)).add (hδ.abs.const_mul _))
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      have hbx := hbB x
      have hex := heB x
      have h1 : |2 * (δ x * (b x * e x))| ≤ (2 * B * (B * D)) * |δ x| := by
        rw [abs_mul, abs_mul, abs_mul]
        have : |b x| * |e x| ≤ B * (B * D) := mul_le_mul hbx hex (abs_nonneg _) hB0
        have h2 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
        rw [h2]
        nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg (δ x))]
      have h2 : |ρ x * e x ^ 2| ≤ (B * D) ^ 2 * |ρ x| := by
        rw [abs_mul, abs_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hex 2) (abs_nonneg _)
      have h3 : |δ x * e x ^ 2| ≤ (B * D) ^ 2 * |δ x| := by
        rw [abs_mul, abs_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hex 2) (abs_nonneg _)
      calc |2 * (δ x * (b x * e x)) + ρ x * e x ^ 2 + δ x * e x ^ 2|
          ≤ |2 * (δ x * (b x * e x))| + |ρ x * e x ^ 2| + |δ x * e x ^ 2| := abs_add_three _ _ _
        _ ≤ _ := by linarith
    · have jA : Integrable (fun x => 2 * B * (B * D) * |δ x|) (haar 1) := hδ.abs.const_mul _
      have jB : Integrable (fun x => (B * D) ^ 2 * |ρ x|) (haar 1) := hρ.abs.const_mul _
      have jC : Integrable (fun x => (B * D) ^ 2 * |δ x|) (haar 1) := hδ.abs.const_mul _
      have jAB : Integrable (fun x => 2 * B * (B * D) * |δ x| + (B * D) ^ 2 * |ρ x|) (haar 1) :=
        jA.add jB
      rw [integral_add jAB jC, integral_add jA jB, integral_const_mul,
        integral_const_mul, integral_const_mul]
      have hρ1' : 0 ≤ ∫ x, |ρ x| ∂haar 1 := integral_nonneg fun x => abs_nonneg _
      have hBD : 0 ≤ (B * D) ^ 2 := sq_nonneg _
      have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
      -- (2B²D) D + (BD)² ρ₁ + (BD)² D ≤ 5 B² D²
      have e1 : (B * D) ^ 2 * ∫ x, |ρ x| ∂haar 1 ≤ (B * D) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hρ1 hBD
      have e2 : (B * D) ^ 2 * D ≤ (B * D) ^ 2 * 2 := mul_le_mul_of_nonneg_left hD hBD
      nlinarith
  · have hfun : (fun x => (ρ x + δ x) * (convT c (fun y => ρ y + δ y) x) ^ 2) =
        fun x => (ρ x * b x ^ 2 + δ x * b x ^ 2 + 2 * (ρ x * (b x * e x))) +
          (2 * (δ x * (b x * e x)) + ρ x * e x ^ 2 + δ x * e x ^ 2) := by
      funext x; rw [uft_convT_add hc hρ hδ]; simp only [hbdef, hedef]; ring
    rw [hfun, integral_add i123 i456, integral_add i12 (i3.const_mul 2), integral_add i1 i2,
      integral_const_mul, hF3]
    ring


theorem uft_lin_Apot {C : Torus 1 → ℝ} (hC : GoodKernel C) (r : ℝ) {ρ δ : Torus 1 → ℝ}
    (hρ : Integrable ρ (haar 1)) (hδ : Integrable δ (haar 1)) :
    ∫ x, Apot C r ρ x * δ x ∂haar 1 =
      4 * ∫ x, δ x * convT (dT (dT C)) ρ x ∂haar 1 + ∫ x, δ x * (convT (dT C) ρ x) ^ 2 ∂haar 1 -
        2 * ∫ x, δ x * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x ∂haar 1 +
        2 * r * ∫ x, δ x * convT C ρ x ∂haar 1 := by
  have c0 := continuous_of_smooth hC.smooth
  have c1 := continuous_of_smooth (isSmoothT_dT hC.smooth)
  have c2 := continuous_of_smooth (isSmoothT_dT (isSmoothT_dT hC.smooth))
  have cb := uft_continuous_convT c1 hρ
  have cw := uft_continuous_convT c1 (uft_integrable_mul_cont hρ cb)
  have i2 : Integrable (fun x => δ x * convT (dT (dT C)) ρ x) (haar 1) :=
    uft_integrable_mul_cont hδ (uft_continuous_convT c2 hρ)
  have i1 : Integrable (fun x => δ x * (convT (dT C) ρ x) ^ 2) (haar 1) :=
    uft_integrable_mul_cont hδ (cb.pow 2)
  have iw : Integrable (fun x => δ x * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x) (haar 1) :=
    uft_integrable_mul_cont hδ cw
  have i0 : Integrable (fun x => δ x * convT C ρ x) (haar 1) :=
    uft_integrable_mul_cont hδ (uft_continuous_convT c0 hρ)
  have hfun : (fun x => Apot C r ρ x * δ x) = fun x =>
      ((4 * (δ x * convT (dT (dT C)) ρ x) + δ x * (convT (dT C) ρ x) ^ 2) -
        2 * (δ x * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x)) +
        2 * r * (δ x * convT C ρ x) := by
    funext x; unfold Apot; ring
  have j1 : Integrable (fun x => 4 * (δ x * convT (dT (dT C)) ρ x) + δ x * (convT (dT C) ρ x) ^ 2)
      (haar 1) := (i2.const_mul 4).add i1
  have j2 : Integrable (fun x => (4 * (δ x * convT (dT (dT C)) ρ x) + δ x * (convT (dT C) ρ x) ^ 2) -
      2 * (δ x * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x)) (haar 1) :=
    j1.sub (iw.const_mul 2)
  rw [hfun, integral_add j2 (i0.const_mul _), integral_sub j1 (iw.const_mul 2),
    integral_add (i2.const_mul 4) i1, integral_const_mul, integral_const_mul, integral_const_mul]

theorem uft_core {C : Torus 1 → ℝ} (hC : GoodKernel C) (r : ℝ) {ρ δ σ : Torus 1 → ℝ}
    (hσ : ∀ x, σ x = ρ x + δ x)
    (hρ : Integrable ρ (haar 1)) (hδ : Integrable δ (haar 1))
    (hρ1 : ∫ x, |ρ x| ∂haar 1 ≤ 1) (hD : ∫ x, |δ x| ∂haar 1 ≤ 2) {M0 M1 M2 : ℝ}
    (h0 : ∀ x, |C x| ≤ M0) (h1 : ∀ x, |dT C x| ≤ M1) (h2 : ∀ x, |dT (dT C) x| ≤ M2) :
    |Uf C r σ - Uf C r ρ - ∫ x, Apot C r ρ x * (σ x - ρ x) ∂haar 1| ≤
      (2 * M2 + 5 * M1 ^ 2 + |r| * M0) * (∫ x, |σ x - ρ x| ∂haar 1) ^ 2 := by
  obtain rfl : σ = fun x => ρ x + δ x := funext hσ
  have hsub : ∀ x, ρ x + δ x - ρ x = δ x := fun x => by ring
  simp only [hsub]
  have c0 := continuous_of_smooth hC.smooth
  have c1 := continuous_of_smooth (isSmoothT_dT hC.smooth)
  have c2 := continuous_of_smooth (isSmoothT_dT (isSmoothT_dT hC.smooth))
  have e0 : ∀ x, C (-x) = C x := hC.even
  have e1 : ∀ x, dT C (-x) = - dT C x := uft_dT_odd_of_even e0
  have e2 : ∀ x, dT (dT C) (-x) = dT (dT C) x := uft_dT_even_of_odd e1
  obtain ⟨R, hR, hRe⟩ := uft_cubic_exp c1 e1 hρ hδ h1 hρ1 hD
  have q2 := uft_quad_exp c2 e2 hρ hδ
  have q0 := uft_quad_exp c0 e0 hρ hδ
  have b2 := uft_quad_bound c2 hδ h2
  have b0 := uft_quad_bound c0 hδ h0
  rw [uft_lin_Apot hC r hρ hδ]
  unfold Uf
  rw [q2, q0, hRe]
  set D := ∫ x, |δ x| ∂haar 1
  set Q2 := ∫ x, δ x * convT (dT (dT C)) δ x ∂haar 1
  set Q0 := ∫ x, δ x * convT C δ x ∂haar 1
  have hM2 : 0 ≤ M2 := le_trans (abs_nonneg _) (h2 0)
  have hM0 : 0 ≤ M0 := le_trans (abs_nonneg _) (h0 0)
  have eq : 2 * (∫ x, ρ x * convT (dT (dT C)) ρ x ∂haar 1 + 2 * ∫ x, δ x * convT (dT (dT C)) ρ x ∂haar 1 + Q2) +
        (∫ x, ρ x * convT (dT C) ρ x ^ 2 ∂haar 1 +
          (∫ x, δ x * convT (dT C) ρ x ^ 2 ∂haar 1 -
            2 * ∫ x, δ x * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x ∂haar 1) + R) +
        r * (∫ x, ρ x * convT C ρ x ∂haar 1 + 2 * ∫ x, δ x * convT C ρ x ∂haar 1 + Q0) -
      (2 * ∫ x, ρ x * convT (dT (dT C)) ρ x ∂haar 1 + ∫ x, ρ x * convT (dT C) ρ x ^ 2 ∂haar 1 +
        r * ∫ x, ρ x * convT C ρ x ∂haar 1) -
      (4 * ∫ x, δ x * convT (dT (dT C)) ρ x ∂haar 1 + ∫ x, δ x * convT (dT C) ρ x ^ 2 ∂haar 1 -
        2 * ∫ x, δ x * convT (dT C) (fun y => ρ y * convT (dT C) ρ y) x ∂haar 1 +
        2 * r * ∫ x, δ x * convT C ρ x ∂haar 1) = 2 * Q2 + R + r * Q0 := by ring
  rw [eq]
  have hr : |r * Q0| ≤ |r| * M0 * D ^ 2 := by
    rw [abs_mul]
    calc |r| * |Q0| ≤ |r| * (M0 * D ^ 2) := mul_le_mul_of_nonneg_left b0 (abs_nonneg _)
      _ = _ := by ring
  have h2' : |2 * Q2| ≤ 2 * M2 * D ^ 2 := by
    rw [abs_mul, abs_of_pos (two_pos : (0:ℝ) < 2)]; nlinarith
  calc |2 * Q2 + R + r * Q0| ≤ |2 * Q2| + |R| + |r * Q0| := abs_add_three _ _ _
    _ ≤ _ := by nlinarith

theorem Uf_taylor' {C : Torus 1 → ℝ} (hC : GoodKernel C) (r : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ σ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → (∀ x, 0 ≤ σ x) →
      Measurable ρ → Measurable σ → ∫ x, ρ x ∂haar 1 = 1 → ∫ x, σ x ∂haar 1 = 1 →
      |Uf C r σ - Uf C r ρ - ∫ x, Apot C r ρ x * (σ x - ρ x) ∂haar 1| ≤
        K * (∫ x, |σ x - ρ x| ∂haar 1) ^ 2 := by
  obtain ⟨M0, hM0, h0⟩ := uft_bound (continuous_of_smooth hC.smooth)
  obtain ⟨M1, hM1, h1⟩ := uft_bound (continuous_of_smooth (isSmoothT_dT hC.smooth))
  obtain ⟨M2, hM2, h2⟩ := uft_bound (continuous_of_smooth (isSmoothT_dT (isSmoothT_dT hC.smooth)))
  refine ⟨2 * M2 + 5 * M1 ^ 2 + |r| * M0, by positivity, ?_⟩
  intro ρ σ hρ0 hσ0 hρm hσm hρ1 hσ1
  have hρi := integrable_of_integral_eq_one' hρ1
  have hσi := integrable_of_integral_eq_one' hσ1
  have hδi : Integrable (fun x => σ x - ρ x) (haar 1) := hσi.sub hρi
  have hρabs : ∫ x, |ρ x| ∂haar 1 ≤ 1 := by
    have : ∫ x, |ρ x| ∂haar 1 = ∫ x, ρ x ∂haar 1 := by
      congr 1; funext x; exact abs_of_nonneg (hρ0 x)
    rw [this, hρ1]
  have hD : ∫ x, |σ x - ρ x| ∂haar 1 ≤ 2 := by
    have : ∫ x, |σ x - ρ x| ∂haar 1 ≤ ∫ x, (σ x + ρ x) ∂haar 1 :=
      integral_mono hδi.abs (hσi.add hρi) fun x => by
        rw [abs_le]; constructor <;> linarith [hρ0 x, hσ0 x]
    rw [integral_add hσi hρi, hσ1, hρ1] at this
    linarith
  exact uft_core hC r (δ := fun x => σ x - ρ x) (fun x => by ring) hρi hδi hρabs hD h0 h1 h2


/-- `Apot` is smooth for a (bounded measurable) probability density. -/
theorem isSmoothT_Apot {C : Torus 1 → ℝ} (hC : GoodKernel C) (r : ℝ) {ρ : Torus 1 → ℝ}
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1) (hm : Measurable ρ) :
    IsSmoothT (Apot C r ρ) :=
  isSmoothT_Apot' hC r h1

/-- Second-order Taylor remainder: for probability densities `ρ`, `σ`,
`|𝒰_r(σ) - 𝒰_r(ρ) - ∫ A_ρ (σ - ρ)| ≤ K (∫|σ-ρ|)²` with `K` depending only on `C, r`. -/
theorem Uf_taylor {C : Torus 1 → ℝ} (hC : GoodKernel C) (r : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ σ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → (∀ x, 0 ≤ σ x) →
      Measurable ρ → Measurable σ → ∫ x, ρ x ∂haar 1 = 1 → ∫ x, σ x ∂haar 1 = 1 →
      |Uf C r σ - Uf C r ρ - ∫ x, Apot C r ρ x * (σ x - ρ x) ∂haar 1| ≤
        K * (∫ x, |σ x - ρ x| ∂haar 1) ^ 2 :=
  Uf_taylor' hC r

end SharpLSI.FL.Ex.LaneD
