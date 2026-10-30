import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform control of the actual logarithmic ODE nonlinearity on a fixed
positive interval. The same spatially uniform constant controls its Haar L2
difference. No minimizer, Euler or higher-regularity premise is used. -/

noncomputable section
open MeasureTheory Filter Topology Set

namespace DGPS.Examples.ThreeSpeciesCircle

def interactingLogNonlinearity (h : ℝ) (x : Torus 1) (z : ℝ) : ℝ :=
  z * (Real.log (z ^ 2) - ellT h x)

theorem interactingLogNonlinearity_hasDerivAt (h : ℝ) (x : Torus 1)
    (z : ℝ) (hz : 0 < z) :
    HasDerivAt (interactingLogNonlinearity h x)
      (Real.log (z ^ 2) + 2 - ellT h x) z := by
  have hlog := ((hasDerivAt_id z).pow 2).log (pow_ne_zero 2 hz.ne')
  convert (hasDerivAt_id z).mul (hlog.sub_const (ellT h x)) using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq]
    field_simp [hz.ne']
    <;> ring

private theorem continuous_logNonlinearity_field (h : ℝ) (u : Torus 1 → ℝ)
    (hu : Continuous u) (hup : ∀ x, 0 < u x) :
    Continuous (fun x => interactingLogNonlinearity h x (u x)) := by
  exact hu.mul (((hu.pow 2).log (fun x => pow_ne_zero 2 (hup x).ne')).sub
    (isSmoothPeriodic_ellT h).continuous_torus)

/-- The actual nonlinearity has one uniform positive Lipschitz constant before
every spatial point and every pair of continuous fields in the fixed interval.
The integrated estimate is a genuine finite Haar integral inequality. -/
theorem interactingLogNonlinearity_uniform_control (h m M : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (x : Torus 1) (z w : ℝ), z ∈ Icc m M → w ∈ Icc m M →
        |interactingLogNonlinearity h x z - interactingLogNonlinearity h x w| ≤
          C * |z - w|) ∧
      (∀ (u v : Torus 1 → ℝ), Continuous u → Continuous v →
        (∀ x, u x ∈ Icc m M) → (∀ x, v x ∈ Icc m M) →
        (∫ x, (interactingLogNonlinearity h x (u x) -
          interactingLogNonlinearity h x (v x)) ^ 2 ∂haar 1) ≤
            C ^ 2 * ∫ x, (u x - v x) ^ 2 ∂haar 1) := by
  have hlog : ContinuousOn (fun z : ℝ => Real.log (z ^ 2) + 2) (Icc m M) := by
    apply ContinuousOn.add_const
    exact (continuous_id.pow 2).continuousOn.log
      (fun z hz => pow_ne_zero 2 (hm.trans_le hz.1).ne')
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hlog
  obtain ⟨L, hL⟩ := isCompact_univ.exists_bound_of_continuousOn
    (isSmoothPeriodic_ellT h).continuous_torus.continuousOn
  let C := |B| + |L| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbound (x : Torus 1) (z : ℝ) (hz : z ∈ Icc m M) :
      ‖Real.log (z ^ 2) + 2 - ellT h x‖ ≤ C := by
    calc
      _ ≤ ‖Real.log (z ^ 2) + 2‖ + ‖ellT h x‖ := norm_sub_le _ _
      _ ≤ B + L := add_le_add (hB z hz) (hL x (mem_univ x))
      _ ≤ C := by dsimp only [C]; linarith [le_abs_self B, le_abs_self L]
  have hLip (x : Torus 1) (z w : ℝ) (hz : z ∈ Icc m M) (hw : w ∈ Icc m M) :
      |interactingLogNonlinearity h x z - interactingLogNonlinearity h x w| ≤ C * |z - w| := by
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := interactingLogNonlinearity h x)
      (f' := fun z => Real.log (z ^ 2) + 2 - ellT h x) (C := C)
      (fun z hz => (interactingLogNonlinearity_hasDerivAt h x z
        (hm.trans_le hz.1)).hasDerivWithinAt)
      (hbound x) (convex_Icc m M) hw hz
    simpa only [Real.norm_eq_abs] using he
  refine ⟨C, hC, hLip, ?_⟩
  intro u v hu hv hub hvb
  have hRu := continuous_logNonlinearity_field h u hu (fun x => hm.trans_le (hub x).1)
  have hRv := continuous_logNonlinearity_field h v hv (fun x => hm.trans_le (hvb x).1)
  have hi : Integrable (fun x => (interactingLogNonlinearity h x (u x) -
      interactingLogNonlinearity h x (v x)) ^ 2) (haar 1) :=
    ((hRu.sub hRv).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (fun x => (u x - v x) ^ 2) (haar 1) :=
    ((hu.sub hv).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, C ^ 2 * (u x - v x) ^ 2 ∂haar 1 := by
      apply integral_mono hi (hd.const_mul (C ^ 2))
      intro x
      have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC.le (abs_nonneg _))).2
        (hLip x (u x) (v x) (hub x) (hvb x))
      simpa only [sq_abs, mul_pow] using hs
    _ = _ := integral_const_mul _ _

end DGPS.Examples.ThreeSpeciesCircle
