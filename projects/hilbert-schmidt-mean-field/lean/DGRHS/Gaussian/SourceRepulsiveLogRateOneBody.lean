import DGRHS.Gaussian.SourceRepulsiveLogRateData
import DGRHS.Concentration.SourceAffineComparison
import Mathlib.Analysis.Complex.Exponential

/-! Original quantitative repulsive-log one-body obligation, without a raw
pair-log-square premise. The bounded-density every-x upper bound and original
proper exp(-4 beta F) supply F in L2. The scalar domination proof is adapted
from the unchanged root DGRHS.Attractive.memLp_two_of_lower_bound_exp;
only native Mathlib exponential domination is used here, no attractive smallness.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c,
source504-529 /1939-2158. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace DGRHS.SourceRepulsiveLogRate
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

lemma memLp_two_of_upper_bound_neg_exp {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (F : S→ℝ)
    (hF : AEStronglyMeasurable F μ) (U θ : ℝ) (hθ : 0<θ)
    (hupper : ∀ᵐ x ∂μ,F x≤U)
    (hexp : Integrable (fun x=>Real.exp (-θ*F x)) μ) : MemLp F 2 μ := by
  apply (memLp_two_iff_integrable_sq hF).mpr
  apply ((integrable_const (U^2)).add (hexp.const_mul (2/θ^2))).mono' (hF.pow 2)
  filter_upwards [hupper] with x hx
  change ‖(F x)^2‖ ≤ U^2+(2/θ^2)*Real.exp (-θ*F x)
  rw [Real.norm_eq_abs,abs_sq]
  change (F x)^2≤U^2+(2/θ^2)*Real.exp (-θ*F x)
  by_cases hf : F x≤0
  · have hp := Real.pow_div_factorial_le_exp (-θ*F x) (by nlinarith) 2
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,
      Nat.cast_one,mul_one] at hp
    have ht : 0<θ^2 := sq_pos_of_pos hθ
    have hpow : (F x)^2≤(2/θ^2)*Real.exp (-θ*F x) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ht).mpr
      nlinarith
    linarith [sq_nonneg U]
  · have hpos : 0<F x := lt_of_not_ge hf
    have hsq : (F x)^2≤U^2 := by nlinarith
    exact hsq.trans (le_add_of_nonneg_right (by positivity))

lemma physicalPotential_memLp_two (β : ℝ) (hβ : 0<β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    MemLp (logPhysicalPotential (gaussianRieszDensityMeasure ρ)) 2 (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let q := (Fintype.card ι:ℝ)/4
  have hq : 0<q := by dsimp [q];positivity
  have hdim : 0<(Fintype.card ι:ℝ)/2-q := by dsimp [q];linarith
  have hm : AEStronglyMeasurable (logPhysicalPotential μ) μ :=
    (stronglyMeasurable_logPhysicalPair (ι:=ι)).integral_prod_right'.aestronglyMeasurable
  apply memLp_two_of_upper_bound_neg_exp μ _ hm
    (gaussianRieszPhysicalPotentialConstant q M ι) (4*β) (by positivity)
  · exact Filter.Eventually.of_forall fun x=>
      (logPhysicalPotential_proper_bounds q hq hdim ρ M hM hρ hpair x).2.2
  · convert htail using 1
    funext x
    congr 1
    ring

lemma physical_affine_prefactor (β : ℝ) (ρ : EuclideanSpace ℝ ι→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
    Real.exp (β*(∫ x,DGRHS.potential μ W x ∂μ)-β*DGRHS.interactionEnergy μ W)=
      Real.exp (β*DGRHS.interactionEnergy μ W) := by
  dsimp only
  rw [DGRHS.integral_potential (gaussianRieszDensityMeasure ρ)
    (fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)) hpair]
  congr 1
  ring

lemma exists_affine_comparison_constant (β : ℝ) (hβ : 0<β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
    let h := hoeffdingCentered μ logPhysicalPair
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    ∃ D : ℝ,0≤D ∧ ∀ N : ℕ,1≤N →
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N=>μ)) ∧
      |sourceAffinePartition μ β I h F N-Real.exp (β*I)*canonicalPartition μ β h N|≤D/Real.sqrt (N:ℝ) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
  let h := hoeffdingCentered μ logPhysicalPair
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  have hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  have hF : MemLp F 2 μ := physicalPotential_memLp_two β hβ hd ρ M hM hρ hpair htail
  obtain ⟨_,MS,hS⟩ := DGRHS.CLT.sourceLogWeight_higher β 2 hβ.le (by norm_num) hd ρ M hM hρ hpair
  obtain ⟨MC,MK,hC,bC,_⟩ := exists_double_moments β hβ.le hd ρ M hM hρ hpair htail
  let D := |β| *Real.sqrt (variance F μ)*(Real.sqrt MS+Real.exp (β*I)*Real.sqrt MC)
  refine ⟨D,by dsimp [D];positivity,fun N hN=>?_⟩
  have h := sourceAffinePartition_comparison μ β I h hh F hF N hN MS MC
    (hS N).1 (hC N) (hS N).2 (bC N)
  rw [physical_affine_prefactor β ρ hpair] at h
  exact ⟨h.1,h.2.2⟩
end DGRHS.SourceRepulsiveLogRate
#check @DGRHS.SourceRepulsiveLogRate.memLp_two_of_upper_bound_neg_exp
#print axioms DGRHS.SourceRepulsiveLogRate.memLp_two_of_upper_bound_neg_exp
#check @DGRHS.SourceRepulsiveLogRate.physicalPotential_memLp_two
#print axioms DGRHS.SourceRepulsiveLogRate.physicalPotential_memLp_two
#check @DGRHS.SourceRepulsiveLogRate.physical_affine_prefactor
#print axioms DGRHS.SourceRepulsiveLogRate.physical_affine_prefactor
#check @DGRHS.SourceRepulsiveLogRate.exists_affine_comparison_constant
#print axioms DGRHS.SourceRepulsiveLogRate.exists_affine_comparison_constant
