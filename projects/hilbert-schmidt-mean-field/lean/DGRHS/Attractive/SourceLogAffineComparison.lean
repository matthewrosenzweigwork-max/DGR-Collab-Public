/- Source one-body reduction for the actual attractive logarithmic interaction.
All higher particle moments and one-body L2 are supplied from the ORIGINAL row,
singular L1, bounded-density and exp(4 beta h_att) hypotheses. The proper
empirical-variance comparison is reused with its native unbounded-F interface. -/
import DGRHS.Attractive.LowerBoundExpL2
import DGRHS.Attractive.FactorialCanonicalComparison
import DGRHS.Attractive.SourceLogPartition
import DGRHS.Concentration.SourceAffineComparison
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem attractiveLog_source_affine_comparison
    (ρ : EuclideanSpace ℝ ι→ℝ) (M C β : ℝ) (hd : 0<(Fintype.card ι:ℝ))
    (hM : 0≤M) (hC : 0<C) (hβ : 0<β)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : (∫⁻ z,singularAbsLog z
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))<∞)
    (hrows : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal (|DGRHS.centeredKernel (gaussianRieszDensityMeasure ρ)
        attractiveLogInteraction x y|^p) ∂gaussianRieszDensityMeasure ρ)≤
          ENNReal.ofReal (C^p*(p.factorial:ℝ)))
    (hsmall : (2*β)*(attractiveMomentConstant*C)<1)
    (htail : Integrable (fun x=>Real.exp (4*β*DGRHS.potential
      (gaussianRieszDensityMeasure ρ) attractiveLogInteraction x))
      (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := fun (z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι)=>DGRHS.centeredKernel μ attractiveLogInteraction z.1 z.2
    let F := DGRHS.potential μ attractiveLogInteraction
    let I := DGRHS.interactionEnergy μ attractiveLogInteraction
    ∃ D : ℝ,0≤D ∧ ∀ N : ℕ,1≤N →
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
        (Measure.pi (fun _ : Fin N=>μ)) ∧
      |(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
          ∂Measure.pi (fun _ : Fin N=>μ))-
        Real.exp (β*I)*DGRHS.Concentration.canonicalPartition μ β h N|≤D/Real.sqrt (N:ℝ) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let h := fun (z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι)=>DGRHS.centeredKernel μ attractiveLogInteraction z.1 z.2
  let F := DGRHS.potential μ attractiveLogInteraction
  let I := DGRHS.interactionEnergy μ attractiveLogInteraction
  have hp := ((singularAbsLog_finite_iff μ).mp hpair).1
  have hNeg : Function.uncurry (attractiveLogInteraction
      (E:=EuclideanSpace ℝ ι)) = -logPhysicalPair := by
    funext z
    simp only [Function.uncurry,attractiveLogInteraction,logPhysicalPair,Pi.neg_apply,neg_neg]
  have hWi : Integrable (Function.uncurry (attractiveLogInteraction
      (E:=EuclideanSpace ℝ ι))) (μ.prod μ) := by
    rw [hNeg]
    exact hp.neg
  have hWm : StronglyMeasurable (Function.uncurry (attractiveLogInteraction
      (E:=EuclideanSpace ℝ ι))) := by
    rw [hNeg]
    exact (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).neg.stronglyMeasurable
  have hm : Measurable h := (stronglyMeasurable_hoeffdingCentered μ _ hWm).measurable
  have hr : RowFactorialMoments μ h C := rowFactorialMoments_of_lintegral μ h hm C hC.le hrows
  have h2 := joint_memLp μ h hm C hr 2 (by omega)
  have hF := attractiveLogPotential_memLp_two β hβ hd ρ M hM hρ hp htail
  have hWs : ∀ x y : EuclideanSpace ℝ ι,attractiveLogInteraction x y=attractiveLogInteraction y x := by
    intro x y
    unfold attractiveLogInteraction
    rw [norm_sub_rev]
  have hs : ∀ x y,h (x,y)=h (y,x) := DGRHS.centeredKernel_symmetric μ _ hWs
  have hc : ∀ᵐ y ∂μ,∫ x,h (x,y) ∂μ=0 := DGRHS.integral_centeredKernel_left μ _ hWi
  have hbase : β*(attractiveMomentConstant*C)<1 := by
    nlinarith [mul_nonneg attractiveMomentConstant_pos.le hC.le]
  let MS := attractiveUniformConstant μ C (2*β)
  let MC := 2/(1-(β*(attractiveMomentConstant*C))^2)
  let D := |β| *Real.sqrt (variance F μ)*(Real.sqrt MS+Real.exp (β*I)*Real.sqrt MC)
  refine ⟨D,by dsimp [D];positivity,?_⟩
  intro N hN
  have hn : 0<N := by omega
  have ht2 : Integrable (fun x=>Real.exp (2*(2*β)*F x)) μ := by
    convert htail using 1
    funext x
    dsimp [F]
    congr 1
    ring
  have hu := attractiveLog_source_uniform μ hpair C (2*β) hC.le hrows
    (by positivity) hsmall ht2 N hn
  simp_rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ hn] at hu
  have he (x : Fin N→EuclideanSpace ℝ ι) :
      2*DGRHS.CLT.sourceParticleExponent h F I β N x=
        DGRHS.CLT.sourceParticleExponent h F I (2*β) N x := by
    unfold DGRHS.CLT.sourceParticleExponent
    ring
  have hiS : Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
      (2*DGRHS.CLT.sourceParticleExponent h F I β N x)) (Measure.pi (fun _ : Fin N=>μ)) := by
    simp_rw [he]
    simpa only [DGRHS.CLT.sourceParticleExponent,h,F,I] using hu.1
  have hbS : (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
      (2*DGRHS.CLT.sourceParticleExponent h F I β N x)
      ∂Measure.pi (fun _ : Fin N=>μ))≤MS := by
    simp_rw [he]
    simpa only [DGRHS.CLT.sourceParticleExponent,h,F,I,MS,attractiveUniformConstant] using hu.2
  have hcanon := attractiveCanonical_uniform_exponential μ h hm C hr hs hc β
    (by simpa only [abs_of_nonneg hβ.le] using hbase) N
  have hcE (x : Fin N→EuclideanSpace ℝ ι) : β*attractiveNormalizedStatistic N h x=
      -β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
    rw [attractiveStatistic_eq_neg_normalized]
    ring
  simp_rw [hcE] at hcanon
  have hz := DGRHS.Concentration.sourceAffinePartition_comparison μ β I h h2 F hF
    N hN MS MC hiS hcanon.1 hbS hcanon.2
  have hscalar : β*(∫ x,F x ∂μ)-β*I=β*I := by
    rw [DGRHS.integral_potential μ attractiveLogInteraction hWi]
    dsimp [I]
    ring
  rw [hscalar] at hz
  constructor
  · simpa only [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ hn,
      DGRHS.CLT.sourceParticleExponent,h,F,I,μ] using hz.1
  · rw [DGRHS.Concentration.sourceEnergy_partition_eq_affine μ β I h F N hN]
    exact hz.2.2
end DGRHS.Attractive
#check @DGRHS.Attractive.attractiveLog_source_affine_comparison
#print axioms DGRHS.Attractive.attractiveLog_source_affine_comparison
