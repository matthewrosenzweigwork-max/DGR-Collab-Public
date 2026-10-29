import DGRHS.CLT.EquilibriumPartition
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-! Source543--566: the actual macroscopic free energy and thermal density
identity on the finite-potential-energy domain. The entropy is the logarithm
of the genuine Lebesgue Radon--Nikodym density, as in the source; it is derived
integrable from thermal EL and integrable V, rather than assumed separately.
The original phrase "thermal equilibrium measure" still needs its precise
finite-energy domain identified before this supporting interface is declared
the entire original corollary. No infinite integral is replaced by toReal. -/
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S]

def macroscopicFreeEnergy (ν₀ μ : Measure S) (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) : ℝ :=
  (∫ x, V x ∂μ) + DGRHS.interactionEnergy μ W + β⁻¹ * (∫ x, llr μ ν₀ x ∂μ)

theorem equilibrium_entropy_free_energy (ν₀ μ : Measure S) [SigmaFinite ν₀]
    [IsProbabilityMeasure μ] (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hW : Integrable (Function.uncurry W) (μ.prod μ)) (hV : Integrable V μ)
    (hEL : ν₀.tilted (fun x => -β * (V x + DGRHS.potential μ W x)) = μ) :
    Integrable (llr μ ν₀) μ ∧
      (∫ x, llr μ ν₀ x ∂μ) =
        -Real.log (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀) -
          β * (∫ x, V x ∂μ) - 2 * β * DGRHS.interactionEnergy μ W ∧
      -β * macroscopicFreeEnergy ν₀ μ W V β =
        Real.log (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀) +
          β * DGRHS.interactionEnergy μ W := by
  let f := fun x => -β * (V x + DGRHS.potential μ W x)
  have hf := integrable_exp_of_tilted_probability f hEL
  have hμν : μ ≪ ν₀ := by rw [← hEL]; exact tilted_absolutelyContinuous ν₀ f
  have he : llr μ ν₀ =ᵐ[μ] (fun x => f x - Real.log (∫ y, Real.exp (f y) ∂ν₀)) := by
    have h := hμν.ae_le (log_rnDeriv_tilted_left_self hf)
    rw [hEL] at h
    exact h
  have hF := DGRHS.integrable_potential μ W hW
  have hfi : Integrable f μ := (hV.add hF).const_mul (-β)
  have hllr : Integrable (llr μ ν₀) μ :=
    (hfi.sub (integrable_const _)).congr he.symm
  have hInt : (∫ x, llr μ ν₀ x ∂μ) =
      -Real.log (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀) -
        β * (∫ x, V x ∂μ) - 2 * β * DGRHS.interactionEnergy μ W := by
    rw [integral_congr_ae he, integral_sub hfi (integrable_const _), integral_const]
    dsimp only [f]
    rw [integral_const_mul, integral_add hV hF, DGRHS.integral_potential μ W hW]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
    ring
  refine ⟨hllr, hInt, ?_⟩
  unfold macroscopicFreeEnergy
  rw [hInt]
  field_simp
  <;> ring

theorem equilibrium_partition_macroscopic_factor (ν₀ μ : Measure S)
    [SigmaFinite ν₀] [NeZero ν₀] [IsProbabilityMeasure μ]
    (W : S → S → ℝ) (hSym : ∀ x y, W x y = W y x)
    (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hW : Integrable (Function.uncurry W) (μ.prod μ)) (hV : Integrable V μ)
    (hEL : ν₀.tilted (fun x => -β * (V x + DGRHS.potential μ W x)) = μ)
    (N : ℕ) (hN : 0 < N)
    (hmod : Integrable (fun x : Fin N → S => Real.exp (-β * (N : ℝ) *
      sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ))) :
    (∫ x : Fin N → S, Real.exp (-β * sourceHamiltonian W V N x)
      ∂Measure.pi (fun _ : Fin N => ν₀)) =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy ν₀ μ W V β) *
        (∫ x : Fin N → S, Real.exp (-β * (N : ℝ) * sourceCanonicalModulatedEnergy
          (fun p => DGRHS.centeredKernel μ W p.1 p.2)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
          ∂Measure.pi (fun _ : Fin N => μ)) := by
  let f := fun x => -β * (V x + DGRHS.potential μ W x)
  have hf := integrable_exp_of_tilted_probability f hEL
  have hZ : 0 < (∫ x, Real.exp (f x) ∂ν₀) := integral_exp_pos hf
  have hMacro := (equilibrium_entropy_free_energy ν₀ μ W V β hβ hW hV hEL).2.2
  have hPref : (∫ x, Real.exp (f x) ∂ν₀)^N *
      Real.exp (β * (N : ℝ) * DGRHS.interactionEnergy μ W) =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy ν₀ μ W V β) := by
    rw [← Real.exp_log hZ, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp only [f]
    linear_combination -(N : ℝ) * hMacro
  rw [equilibrium_partition_factor W hSym V β N hN hEL hmod, hPref]

end DGRHS.CLT
#check @DGRHS.CLT.macroscopicFreeEnergy
#print axioms DGRHS.CLT.macroscopicFreeEnergy
#check @DGRHS.CLT.equilibrium_entropy_free_energy
#print axioms DGRHS.CLT.equilibrium_entropy_free_energy
#check @DGRHS.CLT.equilibrium_partition_macroscopic_factor
#print axioms DGRHS.CLT.equilibrium_partition_macroscopic_factor
