import FullLabeledLSI.Examples.E01g9_Attain

/-!
# Lane D, Task D (E01h6): `⟨ρ, C*ρ⟩ ≤ 2 M H(ρ)` for a mean-zero kernel with `|C| ≤ M` (Pinsker)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem integral_conv_kernel {C : Torus 1 → ℝ} (hC : GoodKernel C) (y : Torus 1) :
    ∫ x, C (x - y) ∂haar 1 = 0 := by
  rw [integral_sub_right_eq_self (fun z => C z) y]; exact hC.meanZero

theorem integral_kernel_conv {C : Torus 1 → ℝ} (hC : GoodKernel C) (x : Torus 1) :
    ∫ y, C (x - y) ∂haar 1 = 0 := by
  rw [integral_sub_left_eq_self (fun z => C z) (haar 1) x]; exact hC.meanZero

/-- `⟨ρ, C*ρ⟩ ≤ 2 M H(ρ)`. -/
theorem cqR_le_ent {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) {M : ℝ} (hM : ∀ x, |C x| ≤ M)
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hfin : klDiv (densMeasure ρ) (haar 1) ≠ ⊤) : cqR C ρ ≤ 2 * M * entR ρ := by
  have hCc := continuous_of_smooth hC.smooth
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hρi := integrable_of_integral_eq_one' h1
  set v : Torus 1 → ℝ := fun x => ρ x - 1 with hv
  have hvi : Integrable v (haar 1) := hρi.sub (integrable_const _)
  have hv1 : ∫ x, v x ∂haar 1 = 0 := by
    simp only [hv]; rw [integral_sub hρi (integrable_const _), h1]; simp
  -- convT C ρ = convT C v
  have hconv : ∀ x, convT C ρ x = convT C v x := by
    intro x
    unfold convT
    have hCi : ∀ g : Torus 1 → ℝ, Integrable g (haar 1) → Integrable (fun y => C (x - y) * g y) (haar 1) :=
      fun g hg => integrable_conv_mul hCc hg x
    have : (fun y => C (x - y) * ρ y) = fun y => C (x - y) * v y + C (x - y) := by
      funext y; simp only [hv]; ring
    have hI : Integrable (fun y => C (x - y)) (haar 1) :=
      (hCc.comp (continuous_sub_left x)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [this, integral_add (hCi v hvi) hI, integral_kernel_conv hC x]
    simp
  -- ∫ convT C v = 0
  have hint0 : ∫ x, convT C v x ∂haar 1 = 0 := by
    unfold convT
    have hK : Integrable (Function.uncurry fun x y : Torus 1 => C (x - y) * v y) ((haar 1).prod (haar 1)) := by
      refine Integrable.mono' (((hvi.norm.const_mul M)).comp_snd (haar 1)) ?_ (Eventually.of_forall fun p => ?_)
      · exact (hCc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul
          (hvi.aestronglyMeasurable.comp_snd)
      · simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
    rw [integral_integral_swap hK]
    have : ∀ y, ∫ x, C (x - y) * v y ∂haar 1 = 0 := fun y => by
      rw [integral_mul_const, integral_conv_kernel hC y, zero_mul]
    simp [this]
  have hvint : Integrable (fun x => |v x|) (haar 1) := hvi.abs
  -- cq = ∫ v * convT C v
  have hconvint : ∀ x, |convT C v x| ≤ M * ∫ y, |v y| ∂haar 1 := by
    intro x
    unfold convT
    calc |∫ y, C (x - y) * v y ∂haar 1| ≤ ∫ y, |C (x - y) * v y| ∂haar 1 := by
          simpa using norm_integral_le_integral_norm (μ := haar 1) (fun y => C (x - y) * v y)
      _ ≤ ∫ y, M * |v y| ∂haar 1 := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hvint.const_mul M) (Eventually.of_forall fun y => ?_)
          show |C (x - y) * v y| ≤ M * |v y|
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
      _ = _ := by rw [integral_const_mul]
  have hcvc : Continuous (convT C v) := uft_continuous_convT hCc hvi
  set I : ℝ := ∫ y, |v y| ∂haar 1 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  have hcq : cqR C ρ = ∫ x, v x * convT C v x ∂haar 1 := by
    unfold cqR
    have e : (fun x => ρ x * convT C ρ x) = fun x => convT C v x + v x * convT C v x := by
      funext x; rw [hconv x]; simp only [hv]; ring
    rw [e, integral_add (hcvc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((hvi.mul_bdd (c := M * I) hcvc.aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hconvint x)).congr
        (Eventually.of_forall fun x => by simp [mul_comm])), hint0, zero_add]
  have hbound : cqR C ρ ≤ M * I ^ 2 := by
    rw [hcq]
    calc ∫ x, v x * convT C v x ∂haar 1 ≤ |∫ x, v x * convT C v x ∂haar 1| := le_abs_self _
      _ ≤ ∫ x, |v x * convT C v x| ∂haar 1 := by
          simpa using norm_integral_le_integral_norm (μ := haar 1) (fun x => v x * convT C v x)
      _ ≤ ∫ x, |v x| * (M * I) ∂haar 1 := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hvint.mul_const _) (Eventually.of_forall fun x => ?_)
          show |v x * convT C v x| ≤ |v x| * (M * I)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hconvint x) (abs_nonneg _)
      _ = M * I ^ 2 := by rw [integral_mul_const]; ring
  -- Pinsker
  have hP := pinsker_lintegral h0 hρi h1
  rw [← klDiv_densMeasure' h0 h1] at hP
  have hL : ∫⁻ x, ‖ρ x - 1‖ₑ ∂haar 1 = ENNReal.ofReal I := by
    have := ofReal_integral_norm_eq_lintegral_enorm hvi
    simp only [Real.norm_eq_abs] at this
    exact this.symm
  rw [hL, ← ENNReal.ofReal_pow hI0] at hP
  have hP2 : I ^ 2 ≤ 2 * entR ρ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfin) hP
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul] at h
    simpa [entR] using h
  calc cqR C ρ ≤ M * I ^ 2 := hbound
    _ ≤ M * (2 * entR ρ) := mul_le_mul_of_nonneg_left hP2 hM0
    _ = 2 * M * entR ρ := by ring

end SharpLSI.FL.Ex.LaneD
