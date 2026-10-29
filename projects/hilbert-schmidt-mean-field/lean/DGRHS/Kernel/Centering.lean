import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

/-!
DGR, arXiv:2609.02743v1, equation (2.1), source lines 370–378.
The real-valued centering below is used only after integrability is established.
These generic probability-space lemmas are supporting results, not the singular
pointwise energy convention or the full paper's exported theorem statements.
-/

open MeasureTheory

namespace DGRHS

variable {α : Type*} [MeasurableSpace α]

/-- First marginal potential of a real integrable two-body interaction. -/
noncomputable def potential (μ : Measure α) (W : α → α → ℝ) (x : α) : ℝ :=
  ∫ y, W x y ∂μ

/-- Second marginal, retained explicitly before symmetry has been established. -/
noncomputable def secondPotential (μ : Measure α) (W : α → α → ℝ) (y : α) : ℝ :=
  ∫ x, W x y ∂μ

/-- Half of the pair energy, with the source's normalization. -/
noncomputable def interactionEnergy (μ : Measure α) (W : α → α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ z, W z.1 z.2 ∂μ.prod μ

/-- Hoeffding centering: subtract both marginals and add the pair mean. -/
noncomputable def centeredKernel (μ : Measure α) (W : α → α → ℝ) (x y : α) : ℝ :=
  W x y - potential μ W x - secondPotential μ W y +
    ∫ z, W z.1 z.2 ∂μ.prod μ

variable (μ : Measure α) [IsProbabilityMeasure μ] (W : α → α → ℝ)

lemma integrable_potential (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    Integrable (potential μ W) μ :=
  hW.integral_prod_left

lemma integrable_secondPotential (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    Integrable (secondPotential μ W) μ :=
  hW.integral_prod_right

lemma integral_potential (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    ∫ x, potential μ W x ∂μ = 2 * interactionEnergy μ W := by
  simp only [potential, interactionEnergy]
  rw [← show (∫ z, W z.1 z.2 ∂μ.prod μ) = ∫ x, ∫ y, W x y ∂μ ∂μ from integral_prod (fun z => W z.1 z.2) hW]
  ring

lemma integral_secondPotential (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    ∫ y, secondPotential μ W y ∂μ = 2 * interactionEnergy μ W := by
  simp only [secondPotential, interactionEnergy]
  rw [← show (∫ z, W z.1 z.2 ∂μ.prod μ) = ∫ y, ∫ x, W x y ∂μ ∂μ from integral_prod_symm (fun z => W z.1 z.2) hW]
  ring

lemma integrable_centeredKernel (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    Integrable (Function.uncurry (centeredKernel μ W)) (μ.prod μ) := by
  exact ((hW.sub ((integrable_potential μ W hW).comp_fst μ)).sub
    ((integrable_secondPotential μ W hW).comp_snd μ)).add (integrable_const _)

lemma integral_centeredKernel_right (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    ∀ᵐ x ∂μ, ∫ y, centeredKernel μ W x y ∂μ = 0 := by
  filter_upwards [hW.prod_right_ae] with x hx
  change Integrable (fun y => W x y) μ at hx
  have hc : Integrable (fun _ : α => potential μ W x) μ := integrable_const _
  have hd : Integrable (fun _ : α => ∫ z, W z.1 z.2 ∂μ.prod μ) μ :=
    integrable_const _
  unfold centeredKernel
  rw [integral_add (f := fun y => W x y - potential μ W x - secondPotential μ W y)
    (g := fun _ => ∫ z, W z.1 z.2 ∂μ.prod μ)
    ((hx.sub hc).sub (integrable_secondPotential μ W hW)) hd,
    integral_sub (f := fun y => W x y - potential μ W x)
    (g := secondPotential μ W) (hx.sub hc) (integrable_secondPotential μ W hW),
    integral_sub (f := fun y => W x y) (g := fun _ => potential μ W x) hx hc]
  simp only [integral_const]
  simp only [probReal_univ, one_smul]
  rw [show (∫ y, secondPotential μ W y ∂μ) = ∫ z, W z.1 z.2 ∂μ.prod μ from
    (integral_prod_symm (fun z => W z.1 z.2) hW).symm]
  simp [potential]

lemma integral_centeredKernel_left (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    ∀ᵐ y ∂μ, ∫ x, centeredKernel μ W x y ∂μ = 0 := by
  filter_upwards [hW.prod_left_ae] with y hy
  change Integrable (fun x => W x y) μ at hy
  have hc : Integrable (fun _ : α => secondPotential μ W y) μ := integrable_const _
  have hd : Integrable (fun _ : α => ∫ z, W z.1 z.2 ∂μ.prod μ) μ :=
    integrable_const _
  unfold centeredKernel
  rw [integral_add (f := fun x => W x y - potential μ W x - secondPotential μ W y)
    (g := fun _ => ∫ z, W z.1 z.2 ∂μ.prod μ)
    ((hy.sub (integrable_potential μ W hW)).sub hc) hd,
    integral_sub (f := fun x => W x y - potential μ W x)
    (g := fun _ => secondPotential μ W y) (hy.sub (integrable_potential μ W hW)) hc,
    integral_sub (f := fun x => W x y) (g := potential μ W)
    hy (integrable_potential μ W hW)]
  simp only [integral_const]
  simp only [probReal_univ, one_smul]
  rw [show (∫ x, potential μ W x ∂μ) = ∫ z, W z.1 z.2 ∂μ.prod μ from
    (integral_prod (fun z => W z.1 z.2) hW).symm]
  simp [secondPotential]

omit [IsProbabilityMeasure μ] in
lemma secondPotential_eq_potential (hW : ∀ x y, W x y = W y x) :
    secondPotential μ W = potential μ W := by
  funext y
  unfold secondPotential potential
  congr 1
  funext x
  exact hW x y

omit [IsProbabilityMeasure μ] in
lemma centeredKernel_symmetric (hW : ∀ x y, W x y = W y x) :
    ∀ x y, centeredKernel μ W x y = centeredKernel μ W y x := by
  intro x y
  simp only [centeredKernel, secondPotential_eq_potential μ W hW, hW x y]
  ring

end DGRHS

#print axioms DGRHS.integrable_centeredKernel
#print axioms DGRHS.integral_centeredKernel_right
#print axioms DGRHS.integral_centeredKernel_left

#print axioms DGRHS.centeredKernel_symmetric

#print axioms DGRHS.integrable_potential
#print axioms DGRHS.integrable_secondPotential
#print axioms DGRHS.integral_potential
#print axioms DGRHS.integral_secondPotential
#print axioms DGRHS.secondPotential_eq_potential
#check DGRHS.integrable_potential
#check DGRHS.integrable_secondPotential
#check DGRHS.integral_potential
#check DGRHS.integral_secondPotential
#check DGRHS.integrable_centeredKernel
#check DGRHS.integral_centeredKernel_right
#check DGRHS.integral_centeredKernel_left
#check DGRHS.secondPotential_eq_potential
#check DGRHS.centeredKernel_symmetric
