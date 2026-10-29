import LeanResearch.PeriodicAttractiveLogGas.KernelLemma
import LeanResearch.PeriodicAttractiveLogGas.RectangleDilation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Far-field Green oscillation on the reference rectangles

Source Lemma 3.3, lines 493--496. The actual potential is the finite weighted
sum of the regular Green representative at the torus differences. Rewriting
each summand with the actual regular Euclidean lift proves its ordinary
derivative by the affine chain rule. Riesz duality preserves the norm, and
the affine factor `J⁻¹` cancels the `J` in the separation estimate.

Separation on the whole closed reference rectangle is the geometric input:
every torus distance to every listed source is at least `R/J`. It is to be
discharged by the mesh geometry. No derivative or oscillation conclusion is
assumed. The kernel-constant premise is exactly the already proved gradient
conclusion of Lemma 2.1; its existence is recalled explicitly below.

This is a SOURCE_ONLY candidate. Its author has not run Lean, builds,
transitive-axiom inspection, or a protected verifier on these bytes.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology ContDiff

namespace PeriodicAttractiveLogGas
namespace GreenFarOscillation

open RectangleDilation

/-- Precisely the earlier kernel-gradient bound, with the actual Euclidean
Riesz gradient and quotient radius. It does not concern the new potential. -/
def KernelGradientBound (C₁ : ℝ) : Prop :=
  ∀ z : Torus, z ≠ 0 → ‖greenGradient z‖ ≤ C₁ / torusEuclideanNorm z

theorem exists_kernelGradientBound : ∃ C₁ : ℝ, 0 < C₁ ∧ KernelGradientBound C₁ := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_torus_bounds
  exact ⟨C, hC, fun z hz ↦ (hb z hz).2.1⟩

theorem convex_closed (b : Kind) : Convex ℝ (closed b) := by
  intro Z hZ W hW s t hs ht hst
  apply (mem_closed_iff b _).mpr
  have hZ' := (mem_closed_iff b Z).mp hZ
  have hW' := (mem_closed_iff b W).mp hW
  intro j
  change 0 ≤ s * Z j + t * W j ∧ s * Z j + t * W j ≤ width b j
  refine ⟨add_nonneg (mul_nonneg hs (hZ' j).1) (mul_nonneg ht (hW' j).1), ?_⟩
  calc
    s * Z j + t * W j ≤ s * width b j + t * width b j :=
      add_le_add (mul_le_mul_of_nonneg_left (hZ' j).2 hs)
        (mul_le_mul_of_nonneg_left (hW' j).2 ht)
    _ = (s + t) * width b j := by ring
    _ = width b j := by rw [hst, one_mul]

theorem width_zero_le_two (b : Kind) : width b 0 ≤ 2 := by
  cases b <;> norm_num [width, doubleRectangleWidth]

theorem width_one_eq_one (b : Kind) : width b 1 = 1 := by
  cases b <;> norm_num [width, doubleRectangleWidth]

/-- A common diameter bound for the square and the double rectangle, in
the physical Euclidean norm. It is sharp for the double rectangle. -/
theorem norm_sub_le_sqrt_five (b : Kind) {Z W : PlanarSpace}
    (hZ : Z ∈ closed b) (hW : W ∈ closed b) : ‖Z - W‖ ≤ Real.sqrt 5 := by
  have hz := (mem_closed_iff b Z).mp hZ
  have hw := (mem_closed_iff b W).mp hW
  have hz0 : 0 ≤ Z 0 ∧ Z 0 ≤ 2 := ⟨(hz 0).1, (hz 0).2.trans (width_zero_le_two b)⟩
  have hw0 : 0 ≤ W 0 ∧ W 0 ≤ 2 := ⟨(hw 0).1, (hw 0).2.trans (width_zero_le_two b)⟩
  have hz1 : 0 ≤ Z 1 ∧ Z 1 ≤ 1 := by simpa only [width_one_eq_one] using hz 1
  have hw1 : 0 ≤ W 1 ∧ W 1 ≤ 1 := by simpa only [width_one_eq_one] using hw 1
  have h0 : |Z 0 - W 0| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 : |Z 1 - W 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs0 : (Z 0 - W 0) ^ 2 ≤ 4 := by
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hs1 : (Z 1 - W 1) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsq : ‖Z - W‖ ^ 2 ≤ 5 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Z 0 - W 0) ^ 2 + (Z 1 - W 1) ^ 2 ≤ 5
    linarith
  calc
    ‖Z - W‖ = Real.sqrt (‖Z - W‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt hsq

/-- One actual Green summand, expressed in reference coordinates. -/
def referenceSource (a : PlanarSpace) (J : ℝ) (y : Torus) (Z : PlanarSpace) : ℝ :=
  regularGreenRepresentative (torusQuotient (affine a J Z) - y)

theorem quotient_affine_sub_centeredLift (a : PlanarSpace) (J : ℝ) (y : Torus)
    (Z : PlanarSpace) :
    torusQuotient (affine a J Z - centeredLift y) =
      torusQuotient (affine a J Z) - y := by
  rw [torusQuotient_sub, torusQuotient_centeredLift]

/-- This is a global function identity, not a derivative-compatibility
assumption. Translation by any chosen lift of the torus source is legitimate
because the checked representative has the exact periodic lift identity. -/
theorem referenceSource_eq_regularGreenLift (a : PlanarSpace) (J : ℝ) (y : Torus) :
    referenceSource a J y = fun Z ↦ regularGreenLift (affine a J Z - centeredLift y) := by
  funext Z
  calc
    referenceSource a J y Z =
        regularGreenRepresentative (torusQuotient (affine a J Z - centeredLift y)) := by
      simp only [referenceSource, quotient_affine_sub_centeredLift]
    _ = _ := regularGreenRepresentative_lift _

theorem hasFDerivAt_referenceSource (a : PlanarSpace) (J : ℝ) (y : Torus)
    {Z : PlanarSpace} (hZ : torusQuotient (affine a J Z) - y ≠ 0) :
    HasFDerivAt (referenceSource a J y)
      (J⁻¹ • greenDifferential (torusQuotient (affine a J Z) - y)) Z := by
  have hquot := quotient_affine_sub_centeredLift a J y Z
  have hx : affine a J Z - centeredLift y ∈ offIntegerLattice := by
    change torusQuotient (affine a J Z - centeredLift y) ≠ 0
    rw [hquot]
    exact hZ
  have hg : DifferentiableAt ℝ regularGreenLift (affine a J Z - centeredLift y) :=
    (contDiffOn_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds hx)).differentiableAt (by simp)
  have ha := (hasFDerivAt_affine a J Z).sub_const (centeredLift y)
  have hmap :
      (fderiv ℝ regularGreenLift (affine a J Z - centeredLift y)).comp
          (J⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace) =
        J⁻¹ • greenDifferential (torusQuotient (affine a J Z) - y) := by
    rw [← greenDifferential_of_lift hquot]
    ext v
    simp
  rw [referenceSource_eq_regularGreenLift]
  exact (hg.hasFDerivAt.comp Z ha).congr_fderiv hmap

theorem fderiv_referenceSource (a : PlanarSpace) (J : ℝ) (y : Torus)
    {Z : PlanarSpace} (hZ : torusQuotient (affine a J Z) - y ≠ 0) :
    fderiv ℝ (referenceSource a J y) Z =
      J⁻¹ • greenDifferential (torusQuotient (affine a J Z) - y) :=
  (hasFDerivAt_referenceSource a J y hZ).fderiv

theorem gradient_referenceSource (a : PlanarSpace) (J : ℝ) (y : Torus)
    {Z : PlanarSpace} (hZ : torusQuotient (affine a J Z) - y ≠ 0) :
    rectangleOrdinaryGradient (referenceSource a J y) Z =
      J⁻¹ • greenGradient (torusQuotient (affine a J Z) - y) := by
  simp only [rectangleOrdinaryGradient, fderiv_referenceSource a J y hZ,
    map_smul, greenGradient]

theorem ne_zero_of_separation {J R : ℝ} (hJ : 0 < J) (hR : 0 < R)
    {z : Torus} (hz : R / J ≤ torusEuclideanNorm z) : z ≠ 0 :=
  (torusEuclideanNorm_pos_iff z).mp ((div_pos hR hJ).trans_le hz)

/-- Exact cancellation of the inverse dilation factor with the physical
separation scale. No dimension or norm-equivalence factor enters here. -/
theorem norm_scaled_greenDifferential_le {J R C₁ : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    {z : Torus} (hz : R / J ≤ torusEuclideanNorm z) :
    ‖J⁻¹ • greenDifferential z‖ ≤ C₁ / R := by
  have hn := hkernel z (ne_zero_of_separation hJ hR hz)
  have hi : 0 ≤ J⁻¹ := inv_nonneg.mpr hJ.le
  calc
    ‖J⁻¹ • greenDifferential z‖ = J⁻¹ * ‖greenGradient z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hi, norm_greenGradient]
    _ ≤ J⁻¹ * (C₁ / torusEuclideanNorm z) := mul_le_mul_of_nonneg_left hn hi
    _ ≤ J⁻¹ * (C₁ / (R / J)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁ (div_pos hR hJ) hz) hi
    _ = C₁ / R := by field_simp [hJ.ne', hR.ne']

variable {ι : Type*} [Fintype ι]

/-- The actual finite weighted reference potential. Empty families and
zero weights use the ordinary finite-sum conventions. -/
def referencePotential (a : PlanarSpace) (J : ℝ) (y : ι → Torus)
    (w : ι → ℝ) (Z : PlanarSpace) : ℝ :=
  ∑ i, w i * referenceSource a J (y i) Z

theorem hasFDerivAt_referencePotential (a : PlanarSpace) (J : ℝ)
    (y : ι → Torus) (w : ι → ℝ) {Z : PlanarSpace}
    (hZ : ∀ i, torusQuotient (affine a J Z) - y i ≠ 0) :
    HasFDerivAt (referencePotential a J y w)
      (∑ i, w i • (J⁻¹ • greenDifferential (torusQuotient (affine a J Z) - y i))) Z := by
  classical
  simpa only [referencePotential, Pi.smul_apply, smul_eq_mul] using!
    (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      (hasFDerivAt_referenceSource a J (y i) (hZ i)).const_smul (w i))

theorem fderiv_referencePotential (a : PlanarSpace) (J : ℝ)
    (y : ι → Torus) (w : ι → ℝ) {Z : PlanarSpace}
    (hZ : ∀ i, torusQuotient (affine a J Z) - y i ≠ 0) :
    fderiv ℝ (referencePotential a J y w) Z =
      ∑ i, w i • (J⁻¹ • greenDifferential (torusQuotient (affine a J Z) - y i)) :=
  (hasFDerivAt_referencePotential a J y w hZ).fderiv

theorem gradient_referencePotential (a : PlanarSpace) (J : ℝ)
    (y : ι → Torus) (w : ι → ℝ) {Z : PlanarSpace}
    (hZ : ∀ i, torusQuotient (affine a J Z) - y i ≠ 0) :
    rectangleOrdinaryGradient (referencePotential a J y w) Z =
      ∑ i, w i • (J⁻¹ • greenGradient (torusQuotient (affine a J Z) - y i)) := by
  simp only [rectangleOrdinaryGradient, fderiv_referencePotential a J y w hZ,
    map_sum, map_smul, greenGradient]

/-- Pointwise ordinary differentiability follows from separation, even
at a boundary point of the closed reference rectangle. -/
theorem differentiableAt_referencePotential_of_separated (a : PlanarSpace)
    {J R : ℝ} (hJ : 0 < J) (hR : 0 < R) (y : ι → Torus) (w : ι → ℝ)
    {Z : PlanarSpace}
    (hsep : ∀ i, R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i)) :
    DifferentiableAt ℝ (referencePotential a J y w) Z :=
  (hasFDerivAt_referencePotential a J y w
    (fun i ↦ ne_zero_of_separation hJ hR (hsep i))).differentiableAt

theorem norm_fderiv_referencePotential_le (a : PlanarSpace)
    {J R C₁ β₀ : ℝ} (hJ : 0 < J) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ β₀)
    {Z : PlanarSpace}
    (hsep : ∀ i, R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i)) :
    ‖fderiv ℝ (referencePotential a J y w) Z‖ ≤ β₀ * C₁ / R := by
  classical
  rw [fderiv_referencePotential a J y w
    (fun i ↦ ne_zero_of_separation hJ hR (hsep i))]
  calc
    _ ≤ ∑ i, ‖w i • (J⁻¹ • greenDifferential
        (torusQuotient (affine a J Z) - y i))‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖J⁻¹ • greenDifferential
        (torusQuotient (affine a J Z) - y i)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * (C₁ / R) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (norm_scaled_greenDifferential_le hJ hR hC₁ hkernel (hsep i)) (hw i)
    _ = (∑ i, w i) * (C₁ / R) := (Finset.sum_mul _ _ _).symm
    _ ≤ β₀ * (C₁ / R) := mul_le_mul_of_nonneg_right hweight (div_nonneg hC₁ hR.le)
    _ = β₀ * C₁ / R := by ring

theorem norm_gradient_referencePotential_le (a : PlanarSpace)
    {J R C₁ β₀ : ℝ} (hJ : 0 < J) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ β₀)
    {Z : PlanarSpace}
    (hsep : ∀ i, R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i)) :
    ‖rectangleOrdinaryGradient (referencePotential a J y w) Z‖ ≤ β₀ * C₁ / R := by
  rw [norm_rectangleOrdinaryGradient]
  exact norm_fderiv_referencePotential_le a hJ hR hC₁ hkernel y w hw hweight hsep

/-- The ordinary mean-value estimate on the actual convex rectangle.
Only separation on that rectangle, not on the whole plane, is required. -/
theorem referencePotential_sub_le (b : Kind) (a : PlanarSpace)
    {J R C₁ β₀ : ℝ} (hJ : 0 < J) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ β₀)
    (hsep : ∀ Z ∈ closed b, ∀ i,
      R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i))
    {Z W : PlanarSpace} (hZ : Z ∈ closed b) (hW : W ∈ closed b) :
    |referencePotential a J y w Z - referencePotential a J y w W| ≤
      (β₀ * C₁ / R) * ‖Z - W‖ := by
  have h := (convex_closed b).norm_image_sub_le_of_norm_fderiv_le
    (fun X hX ↦ differentiableAt_referencePotential_of_separated a hJ hR y w (hsep X hX))
    (fun X hX ↦ norm_fderiv_referencePotential_le a hJ hR hC₁ hkernel
      y w hw hweight (hsep X hX)) hW hZ
  simpa only [Real.norm_eq_abs] using h

/-- Exact source oscillation constant in reference coordinates. The proof
allows `β₀ = 0`, individual zero weights, and an empty finite source family. -/
theorem referencePotential_oscillation_le (b : Kind) (a : PlanarSpace)
    {J R C₁ β₀ : ℝ} (hJ : 0 < J) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ β₀)
    (hsep : ∀ Z ∈ closed b, ∀ i,
      R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i))
    {Z W : PlanarSpace} (hZ : Z ∈ closed b) (hW : W ∈ closed b) :
    |referencePotential a J y w Z - referencePotential a J y w W| ≤
      Real.sqrt 5 * β₀ * C₁ / R := by
  have hβ₀ : 0 ≤ β₀ := (Finset.sum_nonneg fun i _ ↦ hw i).trans hweight
  have hB : 0 ≤ β₀ * C₁ / R := div_nonneg (mul_nonneg hβ₀ hC₁) hR.le
  calc
    _ ≤ (β₀ * C₁ / R) * ‖Z - W‖ :=
      referencePotential_sub_le b a hJ hR hC₁ hkernel y w hw hweight hsep hZ hW
    _ ≤ (β₀ * C₁ / R) * Real.sqrt 5 :=
      mul_le_mul_of_nonneg_left (norm_sub_le_sqrt_five b hZ hW) hB
    _ = Real.sqrt 5 * β₀ * C₁ / R := by ring

/-- The full requested far-field statement with only the actual kernel
constant and the explicit geometric separation as inputs. -/
theorem referencePotential_farField_estimates (b : Kind) (a : PlanarSpace)
    {J R C₁ β₀ : ℝ} (hJ : 0 < J) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ β₀)
    (hsep : ∀ Z ∈ closed b, ∀ i,
      R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i)) :
    (∀ Z ∈ closed b,
      DifferentiableAt ℝ (referencePotential a J y w) Z ∧
        ‖fderiv ℝ (referencePotential a J y w) Z‖ ≤ β₀ * C₁ / R) ∧
      ∀ Z ∈ closed b, ∀ W ∈ closed b,
        |referencePotential a J y w Z - referencePotential a J y w W| ≤
          Real.sqrt 5 * β₀ * C₁ / R := by
  constructor
  · intro Z hZ
    exact ⟨differentiableAt_referencePotential_of_separated a hJ hR y w (hsep Z hZ),
      norm_fderiv_referencePotential_le a hJ hR hC₁ hkernel y w hw hweight (hsep Z hZ)⟩
  · intro Z hZ W hW
    exact referencePotential_oscillation_le b a hJ hR hC₁ hkernel y w hw hweight hsep hZ hW

theorem continuousOn_referencePotential_of_separated (b : Kind) (a : PlanarSpace)
    {J R : ℝ} (hJ : 0 < J) (hR : 0 < R) (y : ι → Torus) (w : ι → ℝ)
    (hsep : ∀ Z ∈ closed b, ∀ i,
      R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y i)) :
    ContinuousOn (referencePotential a J y w) (closed b) := by
  intro Z hZ
  exact (differentiableAt_referencePotential_of_separated a hJ hR y w
    (hsep Z hZ)).continuousAt.continuousWithinAt

/-- The zero-total-weight endpoint is identically zero everywhere, even
without separation. In particular, no division by the coupling is used. -/
theorem referencePotential_eq_zero_of_weight_sum_nonpos (a : PlanarSpace) (J : ℝ)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ 0) :
    referencePotential a J y w = 0 := by
  classical
  have hw0 : ∀ i, w i = 0 := by
    intro i
    apply le_antisymm _ (hw i)
    exact (Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)).trans hweight
  funext Z
  simp [referencePotential, hw0]

end GreenFarOscillation
end PeriodicAttractiveLogGas
