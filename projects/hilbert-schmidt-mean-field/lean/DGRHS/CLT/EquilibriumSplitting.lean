/- Original canonical/modulated equilibrium splitting. The Euler-Lagrange
law is a normalized one-body exponential relation; product normalization,
Hamiltonian cancellation and canonical properness are proved, not assumed.
Physical singular adapters separately discharge modulated-weight properness. -/
import DGRHS.CLT.ProductTilt
import DGRHS.CLT.SourceRawEnergy
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {ν₀ μ : Measure S}

lemma integrable_exp_of_tilted_probability (f : S → ℝ) [IsProbabilityMeasure μ]
    (h : ν₀.tilted f=μ) : Integrable (fun x => Real.exp (f x)) ν₀ := by
  by_contra hi
  have hm : μ univ=1 := measure_univ
  rw [←h,tilted_of_not_integrable hi] at hm
  simpa using hm

lemma tilted_add_const_of_integrable [NeZero ν₀] (Y : S → ℝ)
    (hi : Integrable (fun x => Real.exp (Y x)) ν₀) (c : ℝ) :
    ν₀.tilted (fun x => Y x+c)=ν₀.tilted Y := by
  letI := isProbabilityMeasure_tilted hi
  calc
    _ = (ν₀.tilted Y).tilted (fun _ => c) := (tilted_tilted hi (fun _ => c)).symm
    _ = ν₀.tilted Y := tilted_const _ c

/-- Actual source mean-field Hamiltonian; spatial collisions retain the
chosen kernel representative pending the singular AE law adapter. -/
def sourceHamiltonian (W : S → S → ℝ) (V : S → ℝ) (N : ℕ) (x : Fin N → S) : ℝ :=
  (2*(N : ℝ))⁻¹*DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) x+∑ i,V (x i)

lemma equilibrium_exponent_splitting (W : S → S → ℝ)
    (hW : ∀ x y,W x y=W y x) (V : S → ℝ) (β : ℝ) (N : ℕ) (hN : 0 < N)
    (x : Fin N → S) :
    (∑ i,-β*(V (x i)+DGRHS.potential μ W (x i)))+
      (-β*(N : ℝ)*sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)=
      -β*sourceHamiltonian W V N x-β*(N : ℝ)*DGRHS.interactionEnergy μ W := by
  rw [sourceCanonicalModulatedEnergy_raw μ W hW N hN x]
  simp only [sourceHamiltonian,Finset.sum_mul,←Finset.mul_sum,Finset.sum_add_distrib]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp
  <;> ring

/-- Under the source Euler-Lagrange probability relation, the modulated law
IS the canonical ensemble; canonical properness is derived from modulated
properness and actual product normalization. -/
theorem equilibrium_modulated_eq_canonical [SigmaFinite ν₀] [NeZero ν₀]
    [IsProbabilityMeasure μ] (W : S → S → ℝ) (hW : ∀ x y,W x y=W y x)
    (V : S → ℝ) (β : ℝ) (N : ℕ) (hN : 0 < N)
    (hEL : ν₀.tilted (fun x => -β*(V x+DGRHS.potential μ W x))=μ)
    (hmod : Integrable (fun x : Fin N → S => Real.exp (-β*(N : ℝ)*
      sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ))) :
    Integrable (fun x : Fin N → S => Real.exp (-β*sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => ν₀)) ∧
    (Measure.pi (fun _ : Fin N => μ)).tilted (fun x => -β*(N : ℝ)*
      sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)=
      (Measure.pi (fun _ : Fin N => ν₀)).tilted (fun x => -β*sourceHamiltonian W V N x) := by
  let f := fun x => -β*(V x+DGRHS.potential μ W x)
  let g := fun x : Fin N → S => -β*(N : ℝ)*sourceCanonicalModulatedEnergy
    (fun p => DGRHS.centeredKernel μ W p.1 p.2)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x
  let Y := fun x : Fin N → S => ∑ i,f (x i)
  let H := fun x : Fin N → S => -β*sourceHamiltonian W V N x
  let c := -β*(N : ℝ)*DGRHS.interactionEnergy μ W
  have hf := integrable_exp_of_tilted_probability f hEL
  have hY := integrable_exp_sum_coordinates f hf N
  have hepi : Measure.pi (fun _ : Fin N => μ)=(Measure.pi (fun _ : Fin N => ν₀)).tilted Y := by
    have hx := measure_pi_tilted (μ := ν₀) f hf N
    rw [show ν₀.tilted f=μ from hEL] at hx
    exact hx
  have hgi : Integrable (fun x => Real.exp (g x)) ((Measure.pi (fun _ : Fin N => ν₀)).tilted Y) := by
    rw [←hepi]
    exact hmod
  have he (x : Fin N → S) : Y x+g x=H x+c := by
    dsimp only [Y,f,g,H,c]
    convert equilibrium_exponent_splitting (μ := μ) W hW V β N hN x using 1 <;> ring
  have hi : Integrable (fun x => Real.exp (H x+c)) (Measure.pi (fun _ : Fin N => ν₀)) := by
    have hh := (integrable_tilted_iff hY (fun x => Real.exp (g x))).mp hgi
    simp only [smul_eq_mul,←Real.exp_add] at hh
    change Integrable (fun x => Real.exp (Y x+g x)) _ at hh
    simpa only [he] using hh
  have hH : Integrable (fun x => Real.exp (H x)) (Measure.pi (fun _ : Fin N => ν₀)) := by
    have hh := integrable_exp_add_const (fun x => H x+c) hi (-c)
    simpa only [add_neg_cancel_right] using hh
  letI : NeZero (Measure.pi (fun _ : Fin N => ν₀)) := ⟨by
    intro hz
    have hm : (Measure.pi (fun _ : Fin N => μ)) univ=1 := measure_univ
    rw [hepi,hz,tilted_zero_measure] at hm
    simpa using hm⟩
  refine ⟨hH,?_⟩
  rw [hepi,tilted_tilted hY]
  have hefun : Y+g=fun x => H x+c := by funext x;exact he x
  rw [hefun,tilted_add_const_of_integrable H hH c]
end DGRHS.CLT
#check @DGRHS.CLT.integrable_exp_of_tilted_probability
#check @DGRHS.CLT.tilted_add_const_of_integrable
#check @DGRHS.CLT.sourceHamiltonian
#check @DGRHS.CLT.equilibrium_exponent_splitting
#check @DGRHS.CLT.equilibrium_modulated_eq_canonical
#print axioms DGRHS.CLT.integrable_exp_of_tilted_probability
#print axioms DGRHS.CLT.tilted_add_const_of_integrable
#print axioms DGRHS.CLT.sourceHamiltonian
#print axioms DGRHS.CLT.equilibrium_exponent_splitting
#print axioms DGRHS.CLT.equilibrium_modulated_eq_canonical
