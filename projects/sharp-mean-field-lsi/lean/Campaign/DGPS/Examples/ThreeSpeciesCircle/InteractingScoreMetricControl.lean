import DGPS.Examples.ThreeSpeciesCircle.InteractingRootUniformControl

/-! Actual score L2 control by the original Haar-H1 metric. No minimizer,
Euler equation or positive stored-root hypothesis is used. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The two actual physical score fields are close in Haar L2 whenever their
original roots are close in the actual original-H1 metric. All integrals are
shown integrable before monotonicity is used. -/
theorem ordinaryRoot_scoreDifference_integral_bound (h : ℝ) (σ ρ : AbsoluteDensity 1)
    {u v : Torus 1 → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hσu : σ.sqrt =ᵐ[haar 1] u) (hρv : ρ.sqrt =ᵐ[haar 1] v) :
    (∫ x, ((2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x) -
        (2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - u x * sigT h x)) ^ 2 ∂haar 1) ≤
      (8 + 2 * (6 * Real.pi * |h|) ^ 2) * ordinaryRootH1Deviation σ ρ u ^ 2 := by
  let G : Torus 1 → Tangent 1 := fun x =>
    weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x
  let g : Torus 1 → ℝ := fun x => G x 0
  let z : Torus 1 → ℝ := fun x => v x - u x
  let a := (eLpNorm (fun x => ρ.sqrt x - u x) 2 (haar 1)).toReal
  let b := (eLpNorm G 2 (haar 1)).toReal
  let S := 6 * Real.pi * |h|
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hσ := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσu (ae_eq_refl _)
  have hG : MemLp G 2 (haar 1) :=
    (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad.sub hσ.memLp_grad
  have hg : MemLp g 2 (haar 1) := memLp_coord hG 0
  have hz : MemLp z 2 (haar 1) := memLp_two_of_continuous (hv.sub hu)
  have hscore : MemLp (fun x => 2 * g x - z x * sigT h x) 2 (haar 1) :=
    (hg.const_mul 2).sub (memLp_two_of_continuous ((hv.sub hu).mul (continuous_sigT h)))
  have ha2 : a ^ 2 = ∫ x, z x ^ 2 ∂haar 1 := by
    dsimp only [a]
    have hroot : MemLp (fun x => ρ.sqrt x-u x) 2 (haar 1) := ρ.memLp_sqrt.sub hσ.memLp
    rw [toReal_eLpNorm_two hroot,
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    apply integral_congr_ae
    filter_upwards [hρv] with x hx
    change (ρ.sqrt x - u x) ^ 2 = (v x - u x) ^ 2
    rw [hx]
  have hb2 : b ^ 2 = ∫ x, g x ^ 2 ∂haar 1 := by
    dsimp only [b]
    rw [toReal_eLpNorm_two_vec hG,
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [g]
      simp [EuclideanSpace.norm_sq_eq]
  have hpoint (x : Torus 1) : (2 * g x - z x * sigT h x) ^ 2 ≤
      8 * g x ^ 2 + (2 * S ^ 2) * z x ^ 2 := by
    have hs : (sigT h x) ^ 2 ≤ S ^ 2 := by
      have ht := (sq_le_sq₀ (abs_nonneg (sigT h x)) hS).2 (abs_sigT_le h x)
      simpa only [sq_abs] using ht
    have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (z x))
    nlinarith [sq_nonneg (2 * g x + z x * sigT h x)]
  have hInt : (∫ x, (2 * g x - z x * sigT h x) ^ 2 ∂haar 1) ≤
      8 * (∫ x, g x ^ 2 ∂haar 1) + (2 * S ^ 2) * (∫ x, z x ^ 2 ∂haar 1) := by
    have ht := integral_mono hscore.integrable_sq
      ((hg.integrable_sq.const_mul 8).add (hz.integrable_sq.const_mul (2 * S ^ 2))) hpoint
    change (∫ x, (2*g x-z x*sigT h x)^2 ∂haar 1)≤
      ∫ x, 8*g x^2+(2*S^2)*z x^2 ∂haar 1 at ht
    rw [integral_add (hg.integrable_sq.const_mul 8) (hz.integrable_sq.const_mul (2 * S ^ 2)),
      integral_const_mul, integral_const_mul] at ht
    exact ht
  have hEq : (fun x => ((2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x) -
        (2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - u x * sigT h x)) ^ 2) =
      fun x => (2 * g x - z x * sigT h x) ^ 2 := by
    funext x
    dsimp only [g, z, G]
    simp only [PiLp.sub_apply]
    ring
  rw [hEq]
  rw [← ha2, ← hb2] at hInt
  change (∫ x, (2 * g x - z x * sigT h x) ^ 2 ∂haar 1) ≤ (8 + 2 * S ^ 2) * (a + b) ^ 2
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hA : a ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg b]
  have hB : b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg a]
  have hSA := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 2 * S ^ 2)
  nlinarith [hSA]

end DGPS.Examples.ThreeSpeciesCircle
