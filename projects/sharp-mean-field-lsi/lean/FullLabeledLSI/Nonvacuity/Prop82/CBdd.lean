import FullLabeledLSI.Nonvacuity.Prop82.CCircle
import FullLabeledLSI.Nonvacuity.Prop82.CClosed

/-!
# Lane C: bounded measurable functions on the circle (bookkeeping for C4)
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

open SharpLSI

/-- Bounded measurable functions on the circle. -/
structure BM (f : Torus 1 → ℝ) : Prop where
  meas : Measurable f
  bdd : ∃ C, ∀ x, |f x| ≤ C

namespace BM

theorem integrable {f : Torus 1 → ℝ} (h : BM f) : Integrable f (haar 1) := by
  obtain ⟨C, hC⟩ := h.bdd
  exact Integrable.of_bound h.meas.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem const (c : ℝ) : BM (fun _ => c) := ⟨measurable_const, ⟨|c|, fun _ => le_rfl⟩⟩

theorem add {f g : Torus 1 → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.add hg.meas, ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩⟩

theorem sub {f g : Torus 1 → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x - g x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.sub hg.meas, ⟨C + D, fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩⟩

theorem mul {f g : Torus 1 → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  refine ⟨hf.meas.mul hg.meas, ⟨C * D, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))

theorem const_mul {f : Torus 1 → ℝ} (hf : BM f) (c : ℝ) : BM (fun x => c * f x) :=
  (BM.const c).mul hf

theorem sq {f : Torus 1 → ℝ} (hf : BM f) : BM (fun x => f x ^ 2) := by
  simpa [pow_two] using hf.mul hf

theorem of_continuous {f : Torus 1 → ℝ} (hf : Continuous f) : BM f := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨hf.measurable, ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩⟩

end BM

theorem BM.gCos : BM gCos := BM.of_continuous continuous_gCos
theorem BM.sCos : BM sCos := BM.of_continuous continuous_sCos

theorem BM.of_isSmoothT {φ : Torus 1 → ℝ} (h : IsSmoothT φ) : BM φ :=
  BM.of_continuous (continuous_of_isSmoothT h)

/-- The five test functions `1, cos, sin, cos², sin·cos` of the Euler–Lagrange multipliers. -/
noncomputable def eTest (j : Fin 5) (x : Torus 1) : ℝ :=
  match j with
  | 0 => 1
  | 1 => gCos x
  | 2 => sCos x
  | 3 => gCos x ^ 2
  | 4 => sCos x * gCos x

theorem BM.eTest (j : Fin 5) : BM (eTest j) := by
  fin_cases j
  · exact BM.const 1
  · exact BM.gCos
  · exact BM.sCos
  · exact BM.gCos.sq
  · exact BM.sCos.mul BM.gCos

/-- Quadratic expansion of `∫ e (a + t b)²`. -/
theorem integral_quad {e a b : Torus 1 → ℝ} (he : BM e) (ha : BM a) (hb : BM b) (t : ℝ) :
    ∫ x, e x * (a x + t * b x) ^ 2 ∂haar 1 =
      (∫ x, e x * a x ^ 2 ∂haar 1) + 2 * t * (∫ x, e x * (a x * b x) ∂haar 1) +
        t ^ 2 * (∫ x, e x * b x ^ 2 ∂haar 1) := by
  have h1 := (he.mul ha.sq).integrable
  have h2 := (he.mul (ha.mul hb)).integrable
  have h3 := (he.mul hb.sq).integrable
  have : ∀ x, e x * (a x + t * b x) ^ 2 =
      e x * a x ^ 2 + (2 * t) * (e x * (a x * b x)) + t ^ 2 * (e x * b x ^ 2) := fun x => by ring
  simp_rw [this]
  have h12 : Integrable (fun x => e x * a x ^ 2 + (2 * t) * (e x * (a x * b x))) (haar 1) :=
    h1.add (h2.const_mul _)
  rw [integral_add h12 (h3.const_mul _), integral_add h1 (h2.const_mul _),
    integral_const_mul, integral_const_mul]

/-- A function with weak derivative in `L²` and itself in `L²` is in `H¹`. -/
theorem memH1_of_isWeakGrad {w G : Torus 1 → ℝ} (hw : IsWeakGrad w (fun y _ => G y))
    (hw2 : MemLp w 2 (haar 1)) (hG2 : MemLp G 2 (haar 1)) :
    MemH1 (haar 1) w ∧ (fun x => weakGrad w x 0) =ᵐ[haar 1] G := by
  have hae : weakGrad w =ᵐ[haar 1] fun y _ => G y := weakGrad_ae_eq hw
  have hae0 : (fun x => weakGrad w x 0) =ᵐ[haar 1] G := by
    filter_upwards [hae] with x hx
    exact congrFun hx 0
  refine ⟨⟨⟨_, hw⟩, hw2, ?_⟩, hae0⟩
  refine hG2.norm.ae_eq ?_
  filter_upwards [hae] with x hx
  rw [hx]
  simp [sqNorm, Real.sqrt_sq_eq_abs]

end SharpLSI.FL.Prop82
