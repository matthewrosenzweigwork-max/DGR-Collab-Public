import DGRHS.Gaussian.SharpnessFiniteParticleLower
import DGRHS.Gaussian.SharpnessPowerFactory
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical Topology
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

/-- Actual supercritical centered partition divergence from the physical
bounded probability density. No full singular L2 input is imposed. -/
theorem sharpness_supercritical_centered_partition_diverges (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (hsuper : (Fintype.card ι : ℝ) < 2*s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (β : ℝ) (hβ : 0 < β) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    (∀ N : ℕ,1 ≤ N → Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic H N x))
      (Measure.pi (fun _ => μ))) ∧
    Tendsto (fun N : ℕ => ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x)
      ∂Measure.pi (fun _ => μ)) atTop atTop := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let c := β^2/(8*(1+β*(4*B)))
  have hB : 0 ≤ B := ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
    (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨a,ha0,z,q,hq,K,hK,hI,hFactory⟩ :=
    sharpness_exists_power_compression_factory s hs ha ρ hρm M hM hρ
  let I := sharpnessInitialBox z q hq
  have hw : ∀ i,I.upper i-I.lower i = 2*q := by intro i; dsimp [I,sharpnessInitialBox]; ring
  have hproper (N : ℕ) (hN : 1 ≤ N) :=
    (sharpness_physical_dyadic_particle_comparison s hs ha ρ hρm M hM hρ a ha0 I (2*q)
      (by positivity) hw hI 0 N hN β hβ.le).1
  refine ⟨hproper,?_⟩
  apply tendsto_atTop.2
  intro b
  have hcK : 0 < c*K := mul_pos hc hK
  have hδ : Tendsto (fun m : ℕ => (2*q)/(2:ℝ)^m) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)),
      Eventually.of_forall (fun m => by change 0 < (2*q)/(2:ℝ)^m; positivity)⟩
  have hg := (tendsto_rpow_neg_nhdsGT_zero (by linarith : (Fintype.card ι:ℝ)-2*s < 0)).comp hδ
  have hgK := Tendsto.const_mul_atTop hcK hg
  obtain ⟨m,hm,hbig⟩ := ((eventually_ge_atTop 4).and
    (hgK.eventually (eventually_gt_atTop (b+2)))).exists
  change b+2 < c*K*((2*q)/(2:ℝ)^m)^((Fintype.card ι:ℝ)-2*s) at hbig
  let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
  let κ := sharpnessCompression μ H A
  obtain ⟨_,_,_,_,_,_,hHS⟩ := hFactory m hm
  have hHS' := mul_le_mul_of_nonneg_left hHS hc.le
  change c*(K*((2*q)/(2:ℝ)^m)^((Fintype.card ι:ℝ)-2*s)) ≤ c*(∫ p,κ p^2 ∂μ.prod μ) at hHS'
  have heBig : b+2 ≤ Real.exp (c*(∫ p,κ p^2 ∂μ.prod μ)) := by
    have he := Real.add_one_le_exp (c*(∫ p,κ p^2 ∂μ.prod μ))
    nlinarith
  let D := sharpnessGoodDiagonalCoefficient s M a ι*((2*q)/(2:ℝ)^m)^(-s)+8*B
  let E := (26*β^2+12*β^3)*(Real.exp (β*D/2)*(1+D^4))^2
  have hErr : Tendsto (fun N : ℕ => E/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hE : ∀ᶠ N : ℕ in atTop,E/(N:ℝ) < 1 := hErr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 1,hE] with N hN hEN
  have hmain := (sharpness_physical_finite_particle_lower s hs ha ρ hρm M hM hρ a ha0 I (2*q)
    (by positivity) hw hI m N hN β hβ.le).2
  change Real.exp (c*(∫ p,κ p^2 ∂μ.prod μ))-E/(N:ℝ) ≤ _ at hmain
  linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_supercritical_centered_partition_diverges
#check @DGRHS.Gaussian.sharpness_supercritical_centered_partition_diverges
