/- Source 391–407: the exact deterministic factor relating canonical and
modulated normalizers. All exponential integrals used below are proper;
physical adapters discharge the sole abstract modulated properness input. -/
import DGRHS.CLT.EquilibriumCollisionWeight
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {ν₀ μ : Measure S}

lemma equilibrium_density_relation_iff (f : S → ℝ) :
    ν₀.tilted f=μ ↔ ν₀.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (f x)/(∫ y,Real.exp (f y) ∂ν₀)))=μ := Iff.rfl

theorem equilibrium_partition_factor [SigmaFinite ν₀] [NeZero ν₀]
    [IsProbabilityMeasure μ] (W : S → S → ℝ) (hW : ∀ x y,W x y=W y x)
    (V : S → ℝ) (β : ℝ) (N : ℕ) (hN : 0 < N)
    (hEL : ν₀.tilted (fun x => -β*(V x+DGRHS.potential μ W x))=μ)
    (hmod : Integrable (fun x : Fin N → S => Real.exp (-β*(N : ℝ)*
      sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ))) :
    (∫ x : Fin N → S,Real.exp (-β*sourceHamiltonian W V N x)
      ∂Measure.pi (fun _ : Fin N => ν₀))=
      (∫ x,Real.exp (-β*(V x+DGRHS.potential μ W x)) ∂ν₀)^N *
      Real.exp (β*(N : ℝ)*DGRHS.interactionEnergy μ W) *
      (∫ x : Fin N → S,Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) := by
  let f := fun x => -β*(V x+DGRHS.potential μ W x)
  let g := fun x : Fin N → S => -β*(N : ℝ)*sourceCanonicalModulatedEnergy
    (fun p => DGRHS.centeredKernel μ W p.1 p.2)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x
  let Y := fun x : Fin N → S => ∑ i,f (x i)
  let H := fun x : Fin N → S => -β*sourceHamiltonian W V N x
  let c := -β*(N : ℝ)*DGRHS.interactionEnergy μ W
  have hf := integrable_exp_of_tilted_probability f hEL
  have hp := equilibrium_modulated_eq_canonical (μ := μ) W hW V β N hN hEL hmod
  have hepi := measure_pi_tilted (μ := ν₀) f hf N
  rw [show ν₀.tilted f=μ from hEL] at hepi
  have he (x : Fin N → S) : Y x+g x=H x+c := by
    dsimp only [Y,f,g,H,c]
    convert equilibrium_exponent_splitting (μ := μ) W hW V β N hN x using 1 <;> ring
  have heint : (∫ x,Real.exp (g x) ∂Measure.pi (fun _ : Fin N => μ))=
      Real.exp c * (∫ x,Real.exp (H x) ∂Measure.pi (fun _ : Fin N => ν₀)) /
        (∫ x,Real.exp (f x) ∂ν₀)^N := by
    rw [hepi,integral_exp_tilted]
    change (∫ x,Real.exp (Y x+g x) ∂Measure.pi (fun _ : Fin N => ν₀)) /
      (∫ x,Real.exp (Y x) ∂Measure.pi (fun _ : Fin N => ν₀)) = _
    simp_rw [he,Real.exp_add]
    rw [integral_mul_const]
    rw [show (∫ x,Real.exp (Y x) ∂Measure.pi (fun _ : Fin N => ν₀))=
      (∫ x,Real.exp (f x) ∂ν₀)^N from integral_exp_sum_coordinates f N]
    ring
  have hz : (∫ x,Real.exp (f x) ∂ν₀)^N ≠ 0 := pow_ne_zero _ (integral_exp_pos hf).ne'
  have hc : Real.exp c*Real.exp (-c)=1 := by rw [←Real.exp_add];simp
  rw [show β*(N : ℝ)*DGRHS.interactionEnergy μ W = -c by dsimp [c];ring]
  change (∫ x,Real.exp (H x) ∂Measure.pi (fun _ : Fin N => ν₀))=
    (∫ x,Real.exp (f x) ∂ν₀)^N * Real.exp (-c) *
      (∫ x,Real.exp (g x) ∂Measure.pi (fun _ : Fin N => μ))
  rw [heint]
  field_simp
  linear_combination -(∫ x,Real.exp (H x) ∂Measure.pi (fun _ : Fin N => ν₀))*hc
end DGRHS.CLT
#check @DGRHS.CLT.equilibrium_density_relation_iff
#check @DGRHS.CLT.equilibrium_partition_factor
#print axioms DGRHS.CLT.equilibrium_density_relation_iff
#print axioms DGRHS.CLT.equilibrium_partition_factor
