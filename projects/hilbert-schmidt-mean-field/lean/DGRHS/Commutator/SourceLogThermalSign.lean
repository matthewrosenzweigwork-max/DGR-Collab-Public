import DGRHS.Commutator.SourceLogThermalMinimumZero
import DGRHS.Gaussian.LogPhysicalConvolution

/-! Deriving the sign of the original logarithmic pointwise multiplier.
The original bounded-density and proper pair-log hypotheses bound the
one-body potentials above, while the actual N=2 offdiagonal energy blows up.
No sign of Cpt or velocity regularity is needed for this inference. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceLog_twoParticle_offDiagonal (z : E) :
    DGRHS.CanonicalVariance.offDiagonalSum logPhysicalPair
      (fun i : Fin 2=>if i=0 then 0 else z)=2*logPhysicalPair (0,z) := by
  classical
  have hdiag : (Finset.univ : Finset (Fin 2)).offDiag = {(0,1),(1,0)} := by
    ext ⟨a,b⟩
    fin_cases a <;> fin_cases b <;> simp
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  rw [hdiag]
  simp [logPhysicalPair,two_mul]

theorem sourceLog_twoParticle_energy_unbounded (hd : 0<(Fintype.card ι:ℝ))
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (R : ℝ) :
    ∃ ω : Fin 2→E,R<sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
      (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
      2 ω := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hd)
  let i : ι := Classical.arbitrary ι
  let q : ℝ := (Fintype.card ι:ℝ)/4
  have hq : 0<q := by dsimp [q];positivity
  have hqd : 0<(Fintype.card ι:ℝ)/2-q := by dsimp [q];linarith
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : E=>logPhysicalPair (a,b)
  let I := DGRHS.interactionEnergy μ W
  let B := gaussianRieszPhysicalPotentialConstant q M ι
  let r := Real.exp (-4*(R+B-I+1))
  have hr : 0<r := Real.exp_pos _
  let z : E := EuclideanSpace.single i r
  let ω : Fin 2→E := fun j=>if j=0 then 0 else z
  have hz : ‖z‖=r := by simp [z,PiLp.norm_single,abs_of_pos hr]
  have hW : logPhysicalPair (0,z)=4*(R+B-I+1) := by
    simp [logPhysicalPair,hz,r]
  have hpot0 := (logPhysicalPotential_proper_bounds q hq hqd ρ M hM hρ hpair 0).2.2
  have hpotz := (logPhysicalPotential_proper_bounds q hq hqd ρ M hM hρ hpair z).2.2
  change DGRHS.potential μ W 0≤B at hpot0
  change DGRHS.potential μ W z≤B at hpotz
  have hraw := sourceCanonicalModulatedEnergy_raw μ W
    (fun a b=>by dsimp [W,logPhysicalPair];rw [norm_sub_rev]) 2 (by norm_num) ω
  have hsum : DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω=
      2*logPhysicalPair (0,z) := sourceLog_twoParticle_offDiagonal z
  refine ⟨ω,?_⟩
  change R<sourceCanonicalModulatedEnergy (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
    (DGRHS.potential μ W) I 2 ω
  rw [hraw,hsum,hW]
  norm_num [ω,Fin.sum_univ_two]
  change R<1/8*(2*(4*(R+B-I+1)))-1/2*(DGRHS.potential μ W 0+DGRHS.potential μ W z)+I
  linarith

theorem sourceLog_thermal_pointwise_constant_nonneg
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (n : ℕ) (v : E→E) (Cpw Cpt : ℝ)
    (hpoint : ∀ N : ℕ,1≤N→∀ ω : Fin N→E,
      |sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N ω|≤
        Cpw*(sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
          (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b))) N ω+
          Cpt*Real.log (Real.exp 1+(N:ℝ))/(N:ℝ))) : 0≤Cpw := by
  by_contra hc
  have hcneg : Cpw<0 := lt_of_not_ge hc
  obtain ⟨ω,hω⟩ := sourceLog_twoParticle_energy_unbounded hd ρ M hM hρ hpair
    (-Cpt*Real.log (Real.exp 1+(2:ℝ))/2)
  have hb := hpoint 2 (by norm_num) ω
  have hpos : 0<sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
      (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b))) 2 ω+
      Cpt*Real.log (Real.exp 1+(2:ℝ))/2 := by linarith
  have hneg := mul_neg_of_neg_of_pos hcneg hpos
  norm_num only [Nat.cast_ofNat] at hb
  exact (not_lt_of_ge ((abs_nonneg _).trans hb)) hneg

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceLog_twoParticle_offDiagonal
#print axioms DGRHS.Commutator.sourceLog_twoParticle_offDiagonal
#check @DGRHS.Commutator.sourceLog_twoParticle_energy_unbounded
#print axioms DGRHS.Commutator.sourceLog_twoParticle_energy_unbounded
#check @DGRHS.Commutator.sourceLog_thermal_pointwise_constant_nonneg
#print axioms DGRHS.Commutator.sourceLog_thermal_pointwise_constant_nonneg
