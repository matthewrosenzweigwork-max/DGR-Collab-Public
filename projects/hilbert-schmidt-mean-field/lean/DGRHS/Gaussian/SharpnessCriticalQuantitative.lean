import DGRHS.Gaussian.SharpnessSourcePartitionTransfer
import DGRHS.Gaussian.SharpnessGrowthArithmetic

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical Topology
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

/-- The original positive logarithmic-power sharpness lower bound at s=d/2.
Every scale, moment, feature and spectrum is derived from the physical density. -/
theorem sharpness_critical_source_partition_rate (s : ℝ) (hs : 0 < s)
    (hcrit : 2*s = (Fintype.card ι:ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (β : ℝ) (hβ : 0 < β) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,
      C*(Real.log (N:ℝ))^c ≤ ∫ x,Real.exp
        (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H (DGRHS.potential μ W)
          (DGRHS.interactionEnergy μ W) N x) ∂Measure.pi (fun _ => μ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let c := β^2/(8*(1+β*(4*B)))
  have ha : 0 < (Fintype.card ι:ℝ)-s := by linarith
  have hB : 0 ≤ B := ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
    (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨a,ha0,z,q,hq,K,hK,hI,hFactory⟩ :=
    sharpness_exists_critical_compression_factory s hs hcrit ρ hρm M hM hρ
  let I := sharpnessInitialBox z q hq
  let G := sharpnessGoodDiagonalCoefficient s M a ι
  let b := (2:ℝ)^s
  let v := (2*q)^(-s)
  have hw : ∀ i,I.upper i-I.lower i = 2*q := by intro i; dsimp [I,sharpnessInitialBox]; ring
  have hG : 0 ≤ G := by
    dsimp [G,sharpnessGoodDiagonalCoefficient]
    have hh := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hs
  have hv : 0 < v := by dsimp [v]; positivity
  obtain ⟨t,ht,hscale⟩ := sharpness_exists_small_error_scale b v (8*B) G β hb hv (by positivity) hG hβ.le 4
  obtain ⟨r,hr,C0,hC0,hgrowth⟩ := sharpness_critical_scale_growth b v t (c*K) hb hv ht (mul_pos hc hK)
  let C := Real.exp (-β*DGRHS.interactionEnergy μ W)*C0/2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r,hr,C,hC,?_⟩
  filter_upwards [hscale,eventually_ge_atTop 1] with N hscaleN hN
  obtain ⟨m,hm,hlo,hhi,herr⟩ := hscaleN
  let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
  let κ := sharpnessCompression μ H A
  obtain ⟨_,_,_,_,_,_,hHS⟩ := hFactory m hm
  have hHS' := mul_le_mul_of_nonneg_left hHS hc.le
  change c*(K*((m-3:ℕ):ℝ)) ≤ c*(∫ p,κ p^2 ∂μ.prod μ) at hHS'
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hg := hgrowth m (by omega) (Real.log (N:ℝ)) hlog hhi
  have heGrow : C0*(Real.log (N:ℝ))^r ≤ Real.exp (c*(∫ p,κ p^2 ∂μ.prod μ)) := by
    exact hg.trans (Real.exp_le_exp.mpr (by nlinarith [hHS']))
  have hiκ : 0 ≤ ∫ p,κ p^2 ∂μ.prod μ := integral_nonneg (fun _ => sq_nonneg _)
  have hOne : 1 ≤ Real.exp (c*(∫ p,κ p^2 ∂μ.prod μ)) := Real.one_le_exp (mul_nonneg hc.le hiκ)
  have hfinite := (sharpness_physical_finite_particle_lower s hs ha ρ hρm M hM hρ a ha0 I (2*q)
    (by positivity) hw hI m N hN β hβ.le).2
  have heD : G*((2*q)/(2:ℝ)^m)^(-s)+8*B = 8*B+G*(v*b^m) := by
    rw [sharpness_dyadic_inverse_power _ _ (by positivity)]
    dsimp [v,b]
    ring
  change Real.exp (c*(∫ p,κ p^2 ∂μ.prod μ))-
    (26*β^2+12*β^3)*(Real.exp (β*(G*((2*q)/(2:ℝ)^m)^(-s)+8*B)/2)*
      (1+(G*((2*q)/(2:ℝ)^m)^(-s)+8*B)^4))^2/(N:ℝ) ≤ _ at hfinite
  rw [heD] at hfinite
  have hcenter : C0*(Real.log (N:ℝ))^r/2 ≤ ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x)
      ∂Measure.pi (fun _ => μ) := by linarith
  have hsource := (sharpness_riesz_source_partition_lower s hs ha ρ M hM hρ β hβ.le N hN).2
  have hh := mul_le_mul_of_nonneg_left hcenter (Real.exp_nonneg (-β*DGRHS.interactionEnergy μ W))
  have hh' : C*(Real.log (N:ℝ))^r ≤ Real.exp (-β*DGRHS.interactionEnergy μ W)*
      (∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x) ∂Measure.pi (fun _ => μ)) := by
    convert hh using 1 <;> dsimp [C] <;> ring
  exact hh'.trans hsource

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_critical_source_partition_rate
#check @DGRHS.Gaussian.sharpness_critical_source_partition_rate
