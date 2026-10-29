/- Actual canonical collision-zero Boltzmann weight and normalization.
Null collisions and proper positive integral are proved in physical adapters. -/
import DGRHS.CLT.EquilibriumSplitting
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S]

def canonicalSingularWeight (W : S → S → ℝ) (V : S → ℝ) (β : ℝ)
    (N : ℕ) (x : Fin N → S) : ℝ≥0∞ := by
  classical
  exact if ∀ i j : Fin N,i≠j → x i≠x j then
    ENNReal.ofReal (Real.exp (-β*sourceHamiltonian W V N x)) else 0

def canonicalSingularPartition (ν₀ : Measure S) (W : S → S → ℝ)
    (V : S → ℝ) (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x,canonicalSingularWeight W V β N x ∂Measure.pi (fun _ : Fin N => ν₀)

def canonicalSingularLaw (ν₀ : Measure S) (W : S → S → ℝ)
    (V : S → ℝ) (β : ℝ) (N : ℕ) : Measure (Fin N → S) :=
  (Measure.pi (fun _ : Fin N => ν₀)).withDensity
    (fun x => canonicalSingularWeight W V β N x/canonicalSingularPartition ν₀ W V β N)

lemma canonicalSingularLaw_eq_tilted (ν₀ : Measure S)
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (N : ℕ)
    [NeZero (Measure.pi (fun _ : Fin N => ν₀))]
    (hi : Integrable (fun x => Real.exp (-β*sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => ν₀)))
    (hc : ∀ᵐ x : Fin N → S ∂Measure.pi (fun _ : Fin N => ν₀),
      ∀ i j : Fin N,i≠j → x i≠x j) :
    0 < canonicalSingularPartition ν₀ W V β N ∧
      canonicalSingularPartition ν₀ W V β N < ∞ ∧
      canonicalSingularLaw ν₀ W V β N=
        (Measure.pi (fun _ : Fin N => ν₀)).tilted (fun x => -β*sourceHamiltonian W V N x) := by
  classical
  have hw : canonicalSingularWeight W V β N =ᵐ[Measure.pi (fun _ : Fin N => ν₀)]
      (fun x => ENNReal.ofReal (Real.exp (-β*sourceHamiltonian W V N x))) := by
    filter_upwards [hc] with x hx
    simp only [canonicalSingularWeight,if_pos hx]
  have hp : canonicalSingularPartition ν₀ W V β N=ENNReal.ofReal
      (∫ x,Real.exp (-β*sourceHamiltonian W V N x) ∂Measure.pi (fun _ : Fin N => ν₀)) := by
    unfold canonicalSingularPartition
    rw [lintegral_congr_ae hw]
    exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
      fun x => (Real.exp_pos _).le)).symm
  refine ⟨by rw [hp];exact ENNReal.ofReal_pos.mpr (integral_exp_pos hi),
    by rw [hp];exact ENNReal.ofReal_lt_top,?_⟩
  unfold canonicalSingularLaw Measure.tilted
  apply withDensity_congr_ae
  filter_upwards [hw] with x hx
  rw [hx,hp]
  exact (ENNReal.ofReal_div_of_pos (integral_exp_pos hi)).symm

lemma equilibrium_product_reference (ν₀ μ : Measure S) [SigmaFinite ν₀] [NeZero ν₀]
    [IsProbabilityMeasure μ] (f : S → ℝ) (hEL : ν₀.tilted f=μ) (N : ℕ) :
    Measure.pi (fun _ : Fin N => ν₀) ≪ Measure.pi (fun _ : Fin N => μ) ∧
      Measure.pi (fun _ : Fin N => ν₀) ≠ 0 := by
  have hi := integrable_exp_of_tilted_probability f hEL
  have hY := integrable_exp_sum_coordinates f hi N
  have he := measure_pi_tilted f hi N
  rw [hEL] at he
  constructor
  · rw [he]
    exact absolutelyContinuous_tilted hY
  · intro hz
    have hm : (Measure.pi (fun _ : Fin N => μ)) univ=1 := measure_univ
    rw [he,hz,tilted_zero_measure] at hm
    simpa using hm
end DGRHS.CLT
#check @DGRHS.CLT.canonicalSingularWeight
#check @DGRHS.CLT.canonicalSingularPartition
#check @DGRHS.CLT.canonicalSingularLaw
#check @DGRHS.CLT.canonicalSingularLaw_eq_tilted
#check @DGRHS.CLT.equilibrium_product_reference
#print axioms DGRHS.CLT.canonicalSingularWeight
#print axioms DGRHS.CLT.canonicalSingularPartition
#print axioms DGRHS.CLT.canonicalSingularLaw
#print axioms DGRHS.CLT.canonicalSingularLaw_eq_tilted
#print axioms DGRHS.CLT.equilibrium_product_reference
