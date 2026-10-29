import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Bounded measurable fields of genuine linear maps act continuously on
L2. This is the multiplication estimate needed for source Lemma 2.7: scalar
multiplication by a bounded cutoff and multiplication of a scalar L2 function
by the cutoff's bounded almost-everywhere gradient. All pointwise
representative equalities are explicitly almost everywhere. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

variable {α F G : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (A : α → F →L[ℝ] G) (hA : AEStronglyMeasurable A μ)
  {C : ℝ} (hbound : ∀ x, ‖A x‖ ≤ C)

include hA hbound

theorem memLp_boundedField_apply (f : Lp F 2 μ) : MemLp (fun x ↦ A x (f x)) 2 μ := by
  have heval : Continuous (fun p : (F →L[ℝ] G) × F ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  apply (Lp.memLp f).of_le_mul
    (heval.comp_aestronglyMeasurable (hA.prodMk (Lp.aestronglyMeasurable f)))
  exact Eventually.of_forall (fun x ↦
    (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)))

def boundedFieldL2 (f : Lp F 2 μ) : Lp G 2 μ :=
  (memLp_boundedField_apply A hA hbound f).toLp (fun x ↦ A x (f x))

theorem boundedFieldL2_coe (f : Lp F 2 μ) :
    boundedFieldL2 A hA hbound f =ᵐ[μ] (fun x ↦ A x (f x)) :=
  (memLp_boundedField_apply A hA hbound f).coeFn_toLp

theorem norm_boundedFieldL2_le (f : Lp F 2 μ) :
    ‖boundedFieldL2 A hA hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedFieldL2_coe A hA hbound f] with x hx
  rw [hx]
  exact (A x).le_opNorm (f x) |>.trans
    (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

theorem boundedFieldL2_add (f g : Lp F 2 μ) :
    boundedFieldL2 A hA hbound (f + g) =
      boundedFieldL2 A hA hbound f + boundedFieldL2 A hA hbound g := by
  apply Lp.ext
  filter_upwards [boundedFieldL2_coe A hA hbound (f + g),
    boundedFieldL2_coe A hA hbound f, boundedFieldL2_coe A hA hbound g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (boundedFieldL2 A hA hbound f) (boundedFieldL2 A hA hbound g)]
    with x hfg hf hg hsum hout
  simp only [hfg, hsum, hout, Pi.add_apply, hf, hg, map_add]

theorem boundedFieldL2_smul (c : ℝ) (f : Lp F 2 μ) :
    boundedFieldL2 A hA hbound (c • f) = c • boundedFieldL2 A hA hbound f := by
  apply Lp.ext
  filter_upwards [boundedFieldL2_coe A hA hbound (c • f),
    boundedFieldL2_coe A hA hbound f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (boundedFieldL2 A hA hbound f)] with x hcf hf hin hout
  simp only [hcf, hin, hout, Pi.smul_apply, hf, map_smul]

/-- The operator bound is the pointwise field bound, with no measure-mass
factor and no particle-number normalization. -/
def boundedFieldL2CLM : Lp F 2 μ →L[ℝ] Lp G 2 μ :=
  LinearMap.mkContinuous
    { toFun := boundedFieldL2 A hA hbound
      map_add' := boundedFieldL2_add A hA hbound
      map_smul' := boundedFieldL2_smul A hA hbound }
    C (norm_boundedFieldL2_le A hA hbound)

theorem boundedFieldL2CLM_coe (f : Lp F 2 μ) :
    boundedFieldL2CLM A hA hbound f =ᵐ[μ] (fun x ↦ A x (f x)) :=
  boundedFieldL2_coe A hA hbound f

theorem norm_boundedFieldL2CLM_sub_le (f g : Lp F 2 μ) :
    ‖boundedFieldL2CLM A hA hbound f - boundedFieldL2CLM A hA hbound g‖ ≤
      C * ‖f - g‖ := by
  rw [← map_sub]
  exact norm_boundedFieldL2_le A hA hbound (f - g)

end PeriodicAttractiveLogGas
