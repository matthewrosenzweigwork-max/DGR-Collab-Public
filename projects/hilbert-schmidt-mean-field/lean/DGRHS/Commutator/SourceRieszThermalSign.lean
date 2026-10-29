import DGRHS.Commutator.SourceRieszEntropicTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The original every-configuration thermal bound forces its multiplier to
be nonnegative. This is derived from the actual two-particle singular energy,
not inserted as an extra hypothesis. Source corollary
entropicCommutatorTemperatureInterpolation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_twoParticle_offDiagonal (s : ℝ) (z : E) :
    DGRHS.CanonicalVariance.offDiagonalSum
      (gaussianRieszPhysicalPair s) (fun i : Fin 2 => if i=0 then 0 else z) =
      2*gaussianRieszPhysicalPair s (0,z) := by
  classical
  have hdiag : (Finset.univ : Finset (Fin 2)).offDiag = {(0,1),(1,0)} := by
    ext ⟨a,b⟩
    fin_cases a <;> fin_cases b <;> simp
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  rw [hdiag]
  simp [gaussianRieszPhysicalPair, norm_sub_rev, two_mul]

/-- The literal canonical physical energy is unbounded above for N=2.
The one-body terms use the existing proper bounded-density estimate. -/
theorem sourceRiesz_twoParticle_energy_unbounded (s M : ℝ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (R : ℝ) :
    ∃ ω : Fin 2→E, R<DGRHS.CLT.sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) 2 ω := by
  classical
  have hcard : 0<(Fintype.card ι:ℝ) := hs.trans hd
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hcard)
  let i : ι := Classical.arbitrary ι
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, 4*(R+B+1)*s≤r^(-s) :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually
      (eventually_ge_atTop (4*(R+B+1)*s))
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0,0<r :=
    Filter.mem_inf_of_right (Set.Subset.refl _)
  obtain ⟨r,hr,hpow⟩ := (hrpos.and hev).exists
  let z : E := EuclideanSpace.single i r
  let ω : Fin 2→E := fun j=>if j=0 then 0 else z
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : E=>gaussianRieszPhysicalPair s (a,b)
  have hz : ‖z‖=r := by simp [z, PiLp.norm_single, abs_of_pos hr]
  have hW : 4*(R+B+1)≤gaussianRieszPhysicalPair s (0,z) := by
    simp only [gaussianRieszPhysicalPair, zero_sub, norm_neg, hz]
    exact (le_div_iff₀ hs).2 hpow
  have hraw := DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ W
    (fun a b=>by dsimp [W,gaussianRieszPhysicalPair];rw [norm_sub_rev]) 2 (by norm_num) ω
  have hsum : DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω =
      2*gaussianRieszPhysicalPair s (0,z) := sourceRiesz_twoParticle_offDiagonal s z
  have hpot := sourceRieszLocal_oneBody_bound ρ s M 1 hs hd hM (by norm_num) hρ 2 (by norm_num) ω
  simp only [one_mul] at hpot
  change (2:ℝ)⁻¹*(∑ j : Fin 2,DGRHS.potential μ W (ω j))-
    DGRHS.interactionEnergy μ W≤B at hpot
  refine ⟨ω,?_⟩
  change R<DGRHS.CLT.sourceCanonicalModulatedEnergy
    (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) 2 ω
  rw [hraw,hsum]
  norm_num only [Nat.cast_ofNat] at *
  norm_num at hpot ⊢
  nlinarith

theorem sourceRiesz_thermal_pointwise_constant_nonneg (s M : ℝ) (n : ℕ)
    (hs : 0<s) (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (v : E→E) (Cpw Cpt : ℝ)
    (hpoint : ∀ N : ℕ,1≤N→∀ ω : Fin N→E,
      |sourceRieszLocalTransportEnergy ρ s n v N ω|≤Cpw*
        (DGRHS.CLT.sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
          (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))/(N:ℝ))) : 0≤Cpw := by
  by_contra hc
  have hcneg : Cpw<0 := lt_of_not_ge hc
  obtain ⟨ω,hω⟩ := sourceRiesz_twoParticle_energy_unbounded s M hs hd hM ρ hρ
    (-Cpt*(2:ℝ)^(s/(Fintype.card ι:ℝ))/2)
  have hb := hpoint 2 (by norm_num) ω
  have hpos : 0<DGRHS.CLT.sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) 2 ω+
      Cpt*(2:ℝ)^(s/(Fintype.card ι:ℝ))/2 := by linarith
  have hneg := mul_neg_of_neg_of_pos hcneg hpos
  norm_num only [Nat.cast_ofNat] at hb
  exact (not_lt_of_ge ((abs_nonneg _).trans hb)) hneg

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_twoParticle_offDiagonal
#print axioms DGRHS.Commutator.sourceRiesz_twoParticle_offDiagonal
#check @DGRHS.Commutator.sourceRiesz_twoParticle_energy_unbounded
#print axioms DGRHS.Commutator.sourceRiesz_twoParticle_energy_unbounded
#check @DGRHS.Commutator.sourceRiesz_thermal_pointwise_constant_nonneg
#print axioms DGRHS.Commutator.sourceRiesz_thermal_pointwise_constant_nonneg
