import SharpSymmetricLSI.Paper.Centering

/-!
# Section 4.2: the operator `T` (Phase 3, lane D; R14)

Selfadjointness on `L²_0(μ)`, square integrability of `K`, and (4.4): `T` maps `L²_0(μ)`
boundedly into bounded Lipschitz functions.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `∫|h| ≤ (∫ h²)^{1/2}` on a probability space. -/
theorem integral_abs_le_sqrt' {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {h : α → ℝ} (hh : MemLp h 2 μ) : ∫ x, |h x| ∂μ ≤ Real.sqrt (∫ x, h x ^ 2 ∂μ) := by
  have hi : Integrable h μ := hh.integrable one_le_two
  have h2 : Integrable (fun x => h x ^ 2) μ := hh.integrable_sq
  set a := ∫ x, |h x| ∂μ
  have h0 : 0 ≤ ∫ x, (|h x| - a) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have e : ∫ x, (|h x| - a) ^ 2 ∂μ = ∫ x, h x ^ 2 ∂μ - a ^ 2 := by
    have : ∀ x, (|h x| - a) ^ 2 = h x ^ 2 - 2 * a * |h x| + a ^ 2 := fun x => by
      rw [sub_sq, sq_abs]; ring
    simp_rw [this]
    rw [integral_add (f := fun x => h x ^ 2 - 2 * a * |h x|) (g := fun _ => a ^ 2)
        (h2.sub (hi.abs.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => h x ^ 2) (g := fun x => 2 * a * |h x|) h2 (hi.abs.const_mul _),
      integral_const_mul]
    simp; ring
  rw [e] at h0
  exact Real.le_sqrt_of_sq_le (by linarith)

section T
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

theorem aW_aesm {h : Torus d → ℝ} (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun x => ∫ y, W x y * h y ∂μ) μ :=
  (hyp.continuous_W.measurable.aestronglyMeasurable.mul
    (hh.aemeasurable.comp_snd (μ := μ)).aestronglyMeasurable).integral_prod_right'
    (f := fun p : Torus d × Torus d => W p.1 p.2 * h p.2)

theorem aW_bdd {BW : ℝ} (hBW : ∀ x y, |W x y| ≤ BW) {h : Torus d → ℝ} (hi : Integrable h μ)
    (x : Torus d) : |∫ y, W x y * h y ∂μ| ≤ BW * ∫ y, |h y| ∂μ := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |W x y * h y| ∂μ ≤ ∫ y, BW * |h y| ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hi.abs.const_mul BW)
          (Eventually.of_forall fun y => by
            show |W x y * h y| ≤ BW * |h y|
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hBW x y) (abs_nonneg _))
    _ = _ := integral_const_mul _ _

theorem integral_mul_aW {h₁ h₂ : Torus d → ℝ} (hi₁ : Integrable h₁ μ) (hi₂ : Integrable h₂ μ) :
    ∫ x, h₁ x * ∫ y, W x y * h₂ y ∂μ ∂μ = ∫ x, h₂ x * ∫ y, W x y * h₁ y ∂μ ∂μ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hint : Integrable (Function.uncurry fun x y => h₁ x * (W x y * h₂ y)) (μ.prod μ) := by
    refine Integrable.mono' ((hi₁.abs.mul_prod hi₂.abs).const_mul BW) ?_
      (Eventually.of_forall fun q => ?_)
    · exact (hi₁.aestronglyMeasurable.aemeasurable.comp_fst (ν := μ)).aestronglyMeasurable.mul
        (hyp.continuous_W.measurable.aestronglyMeasurable.mul
          (hi₂.aestronglyMeasurable.aemeasurable.comp_snd (μ := μ)).aestronglyMeasurable)
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have := hBW q
      calc |h₁ q.1| * (|W q.1 q.2| * |h₂ q.2|) ≤ |h₁ q.1| * (BW * |h₂ q.2|) := by gcongr; exact this
        _ = BW * (|h₁ q.1| * |h₂ q.2|) := by ring
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [hyp.symm]; ring

/-- `T` is selfadjoint on `L²_0(μ)`. -/
theorem Top_selfadjoint {h₁ h₂ : Torus d → ℝ} (hh₁ : MemL20 μ h₁) (hh₂ : MemL20 μ h₂) :
    ∫ x, h₁ x * Top W μ h₂ x ∂μ = ∫ x, Top W μ h₁ x * h₂ x ∂μ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hi₁ := hh₁.1.integrable one_le_two
  have hi₂ := hh₂.1.integrable one_le_two
  have hab : ∀ {g h : Torus d → ℝ}, Integrable g μ → Integrable h μ →
      Integrable (fun x => g x * ∫ y, W x y * h y ∂μ) μ := fun {g h} hg hh =>
    Integrable.mono' (hg.abs.mul_const (BW * ∫ y, |h y| ∂μ))
      (hg.aestronglyMeasurable.mul (aW_aesm hyp μ hh.aestronglyMeasurable))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (aW_bdd hyp μ (fun x y => hBW (x, y)) hh x) (abs_nonneg _))
  unfold Top
  have e1 : ∀ x, h₁ x * ((∫ y, W x y * h₂ y ∂μ) - ∫ x', (∫ y, W x' y * h₂ y ∂μ) ∂μ) =
      h₁ x * (∫ y, W x y * h₂ y ∂μ) - (∫ x', (∫ y, W x' y * h₂ y ∂μ) ∂μ) * h₁ x := fun x => by ring
  have e2 : ∀ x, ((∫ y, W x y * h₁ y ∂μ) - ∫ x', (∫ y, W x' y * h₁ y ∂μ) ∂μ) * h₂ x =
      h₂ x * (∫ y, W x y * h₁ y ∂μ) - (∫ x', (∫ y, W x' y * h₁ y ∂μ) ∂μ) * h₂ x := fun x => by ring
  simp_rw [e1, e2]
  rw [integral_sub (hab hi₁ hi₂) (hi₁.const_mul _), integral_sub (hab hi₂ hi₁) (hi₂.const_mul _),
    integral_const_mul, integral_const_mul, hh₁.2, hh₂.2, integral_mul_aW hyp μ hi₁ hi₂]
  simp

/-- `K ∈ L²(μ ⊗ μ)`. -/
theorem centeredKernel_sq_integrable :
    Integrable (fun p : Torus d × Torus d => centeredKernel W μ p.1 p.2 ^ 2) (μ.prod μ) := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hwb : ∀ y, |convMeas W μ y| ≤ BW := fun y => abs_integral_le_of_bdd fun z => hBW (y, z)
  have hIb : |interE W μ μ| ≤ BW := abs_integral_le_of_bdd fun y => abs_integral_le_of_bdd
    fun x => hBW (x, y)
  have hKb : ∀ p : Torus d × Torus d, |centeredKernel W μ p.1 p.2| ≤ 4 * BW := fun p => by
    unfold centeredKernel
    have := hBW p; have := hwb p.1; have := hwb p.2
    have h1 := abs_add_le (W p.1 p.2 - convMeas W μ p.1 - convMeas W μ p.2) (interE W μ μ)
    have h2 := abs_sub (W p.1 p.2 - convMeas W μ p.1) (convMeas W μ p.2)
    have h3 := abs_sub (W p.1 p.2) (convMeas W μ p.1)
    simp only [Function.uncurry] at *
    linarith
  have hKm : Measurable fun p : Torus d × Torus d => centeredKernel W μ p.1 p.2 := by
    unfold centeredKernel
    exact ((hyp.continuous_W.measurable.sub ((measurable_convMeas hyp μ).comp measurable_fst)).sub
      ((measurable_convMeas hyp μ).comp measurable_snd)).add measurable_const
  refine integrable_of_bdd (hKm.pow_const 2) (C := (4 * BW) ^ 2) fun p => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hKb p) 2

/-- **(4.4)**: `|Th| ≤ C‖h‖₂` and `Th` is `C‖h‖₂`-Lipschitz. -/
theorem Top_W1inf : ∃ C : ℝ, ∀ h, MemL20 μ h →
    (∀ x, |Top W μ h x| ≤ C * Real.sqrt (∫ y, h y ^ 2 ∂μ)) ∧
    LipschitzWith (C * Real.sqrt (∫ y, h y ^ 2 ∂μ)).toNNReal (Top W μ h) := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set LW : NNReal := Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  refine ⟨2 * BW + LW, fun h hh => ⟨fun x => ?_, ?_⟩⟩
  · have hi := hh.1.integrable one_le_two
    have hs := integral_abs_le_sqrt' hh.1
    unfold Top
    refine (abs_sub _ _).trans ?_
    have h1 := aW_bdd hyp μ (fun x y => hBW (x, y)) hi x
    have h2 : |∫ x', (∫ y, W x' y * h y ∂μ) ∂μ| ≤ BW * ∫ y, |h y| ∂μ :=
      abs_integral_le_of_bdd fun x' => aW_bdd hyp μ (fun x y => hBW (x, y)) hi x'
    have hLW : (0 : ℝ) ≤ LW := NNReal.coe_nonneg _
    have hsq := Real.sqrt_nonneg (∫ y, h y ^ 2 ∂μ)
    nlinarith [mul_le_mul_of_nonneg_left hs hBW0]
  · have hi := hh.1.integrable one_le_two
    have hs := integral_abs_le_sqrt' hh.1
    have hL : LipschitzWith (LW * (∫ y, |h y| ∂μ).toNNReal) (Top W μ h) := by
      refine lipschitzWith_of_liftT (LipschitzWith.of_dist_le_mul fun a b => ?_)
      simp only [Function.comp, Top, Real.dist_eq]
      rw [sub_sub_sub_cancel_right]
      have hWi : ∀ z, Integrable (fun y => W (liftT z) y * h y) μ := fun z =>
        Integrable.mono' (hi.abs.const_mul BW) ((hyp.continuous_W.measurable.comp
          measurable_prodMk_left).aestronglyMeasurable.mul hi.aestronglyMeasurable)
          (Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right (hBW (liftT z, y)) (abs_nonneg _))
      rw [← integral_sub (hWi a) (hWi b)]
      refine (abs_integral_le_integral_abs).trans ?_
      have hD := dist_nonneg (x := a) (y := b)
      calc ∫ y, |W (liftT a) y * h y - W (liftT b) y * h y| ∂μ
          ≤ ∫ y, (LW : ℝ) * dist a b * |h y| ∂μ := integral_mono_of_nonneg
            (Eventually.of_forall fun _ => abs_nonneg _) (hi.abs.const_mul _)
            (Eventually.of_forall fun y => by
              show |W (liftT a) y * h y - W (liftT b) y * h y| ≤ LW * dist a b * |h y|
              rw [← sub_mul, abs_mul]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              have := (lipschitz_slice hyp y).dist_le_mul a b
              simp only [Function.comp, Real.dist_eq] at this
              exact this)
        _ = _ := by
          rw [integral_const_mul]
          push_cast [Real.coe_toNNReal _ (integral_nonneg fun _ => abs_nonneg _)]
          ring
    refine hL.weaken ?_
    have hsq := Real.sqrt_nonneg (∫ y, h y ^ 2 ∂μ)
    have hI0 : 0 ≤ ∫ y, |h y| ∂μ := integral_nonneg fun _ => abs_nonneg _
    have hLW : (0 : ℝ) ≤ LW := NNReal.coe_nonneg _
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ hI0,
      Real.coe_toNNReal _ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs hLW, mul_nonneg hBW0 hsq]

end T

end SharpLSI
