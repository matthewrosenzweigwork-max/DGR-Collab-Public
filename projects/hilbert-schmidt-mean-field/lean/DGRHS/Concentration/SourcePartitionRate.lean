import DGRHS.Concentration.SourceCutoffRate
import DGRHS.Gaussian.RieszGaussianEuclideanLaplace
import DGRHS.CLT.CanonicalPartitionComparison
import DGRHS.CLT.SourceMeanZeroPartition

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.Concentration
universe u

/-- The two checked particle conventions agree for every N, including N=0,1.
Only unequal indices are removed, without a spatial diagonal restriction. -/
lemma sourceKernelParticleStatistic_eq_normalized {Ω : Type*} [MeasurableSpace Ω]
    (h : Ω×Ω→ℝ) (N : ℕ) (x : Fin N→Ω) :
    DGRHS.Gaussian.sourceKernelParticleStatistic h N x =
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  classical
  unfold DGRHS.Gaussian.sourceKernelParticleStatistic
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum DGRHS.CanonicalVariance.offDiagonalSum
  rw [Fintype.card_fin]
  congr 1
  symm
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        if p.1=p.2 then 0 else h (x p.1,x p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [(Finset.mem_offDiag.mp hp).2.2,ite_false]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N))×ˢFinset.univ,
        if p.1=p.2 then 0 else h (x p.1,x p.2) := by
      apply Finset.sum_subset
      · intro p hp
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_univ _⟩
      · intro p hp hnot
        have he : p.1=p.2 := by
          by_contra hn
          exact hnot (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hn⟩)
        simp only [he,ite_true]
    _ = _ := by rw [Finset.sum_product]

/-- The true fixed-scale quantitative bound implies cutoff partition convergence. -/
lemma partition_tendsto_of_reciprocal_error (Y : ℕ→ℝ) (y A : ℝ)
    (h : ∀ n,1≤n→|Y n-y|≤A/(n:ℝ)) : Tendsto Y atTop (𝓝 y) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlim : Tendsto (fun n : ℕ ↦ A/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg (Y n-y))
    ((eventually_ge_atTop 1).mono fun n hn ↦ ?_) hlim
  simpa only [Real.norm_eq_abs] using h n hn

def canonicalPartition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β : ℝ) (h : Ω×Ω→ℝ) (N : ℕ) : ℝ :=
  ∫ x : Fin N→Ω,Real.exp (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
    ∂Measure.pi (fun _ : Fin N ↦ μ)

/-- True proper second moments and the actual L2 residual give a uniform
finite-particle comparison. No partition difference is assumed. -/
lemma canonicalPartition_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (β : ℝ)
    (h k : Ω×Ω→ℝ) (hhm : Measurable h) (hkm : Measurable k)
    (hh : MemLp h 2 (μ.prod μ)) (hk : MemLp k 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (ks : ∀ᵐ p ∂μ.prod μ,k p.swap=k p)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0) (kc : ∀ᵐ x ∂μ,(∫ y,k (x,y) ∂μ)=0)
    (R MH MK : ℝ) (hR : ‖(hh.sub hk).toLp (fun p ↦ h p-k p)‖≤R)
    (hH : ∀ N,1≤N→Integrable (fun x : Fin N→Ω ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)))
    (hK : ∀ N,1≤N→Integrable (fun x : Fin N→Ω ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x)) (Measure.pi (fun _ : Fin N ↦ μ)))
    (bH : ∀ N,1≤N→(∫ x : Fin N→Ω,Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤MH)
    (bK : ∀ N,1≤N→(∫ x : Fin N→Ω,Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤MK) :
    ∀ N,1≤N→|canonicalPartition μ β h N-canonicalPartition μ β k N|≤
      (|β|/2*Real.sqrt 2)*R*(Real.sqrt MH+Real.sqrt MK) := by
  intro N hN
  have hb := DGRHS.CLT.canonical_partition_difference_le (ι := Fin N)
    h k hhm hkm hh hk hs ks hc kc β (hH N hN) (hK N hN)
  have hr0 : 0≤R := (norm_nonneg _).trans hR
  have hsqrt := add_le_add (Real.sqrt_le_sqrt (bH N hN)) (Real.sqrt_le_sqrt (bK N hN))
  exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hR (by positivity)) hsqrt (by positivity) (by positivity))

/-- Actual Riesz cutoff source determinant and proper partition limit/rate.
The rate comes from the constructed Fourier feature theorem, not a hypothesis. -/
theorem exists_riesz_cutoff_partition_rate {ι : Type u} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (β s η : ℝ) (hβ : 0≤β) (hs : 0<s) (hη : 0<η) :
    ∃ (hh : MemLp (fun p : (EuclideanSpace ℝ ι)×(EuclideanSpace ℝ ι) ↦
      DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) 2 (μ.prod μ))
      (σ : Type u) (eig : σ→ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i,DGRHS.Kernel.integralOperator
        (fun p ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) hh (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      0<DGRHS.Gaussian.rieszGaussianLaplaceConstant β (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s ∧
      Tendsto (canonicalPartition μ β (fun p ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2))
        atTop (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      ∀ N,1≤N→ Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
        (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
          (fun p ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) x))
          (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        |canonicalPartition μ β (fun p ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) N-
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹| ≤
          DGRHS.Gaussian.rieszGaussianLaplaceConstant β (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s *
          Real.exp (DGRHS.Gaussian.rieszGaussianLaplaceConstant β (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s *η^(-s))/(N:ℝ) := by
  obtain ⟨hh,σ,eig,e,hi,he,_,_,_,hD,hC,hRate⟩ :=
    DGRHS.Gaussian.gaussianRieszEuclideanTruncatedLaplace β s η hβ hs hη μ
  simp_rw [sourceKernelParticleStatistic_eq_normalized] at hRate
  refine ⟨hh,σ,eig,e,hi,he,hD,hC,?_,hRate⟩
  apply partition_tendsto_of_reciprocal_error
  exact fun N hN ↦ (hRate N hN).2

/-- The full source log normalizer and its positive determinant limit are
constructed from the actual canonical operator and proper uniform double
moments. No partition limit, Gaussian field or lower bound is assumed. -/
theorem exists_canonicalMeanZero_log_partition_limit {Ω : Type u} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (hβ : 0≤β) (h : Ω×Ω→ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
    (hpos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v))
    (M : ℝ)
    (hDouble : ∀ N,Integrable (fun x : Fin N→Ω ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)))
    (bDouble : ∀ N,(∫ x : Fin N→Ω,Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤M) :
    ∃ (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      1≤(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹ ∧
      Tendsto (canonicalPartition μ β h) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N ↦ Real.log (canonicalPartition μ β h N)) atTop
        (𝓝 (Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∀ N,Integrable (fun x : Fin N→Ω ↦ Real.exp
        (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        1≤canonicalPartition μ β h N ∧
        |Real.log (canonicalPartition μ β h N)-
          Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)| ≤
          |canonicalPartition μ β h N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹| := by
  have hExp (N : ℕ) (x : Fin N→Ω) : DGRHS.CLT.sourceParticleExponent h (fun _ ↦ 0) 0 β N x =
      -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
    simp [DGRHS.CLT.sourceParticleExponent]
  have hExpDouble (N : ℕ) : (fun x : Fin N→Ω ↦ Real.exp (2*DGRHS.CLT.sourceParticleExponent h (fun _ ↦ 0) 0 β N x)) =
      (fun x ↦ Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [hExp]
    congr 1
    ring
  obtain ⟨κ,eig,e,hκ,he,hLimit⟩ := DGRHS.CLT.exists_sourceMeanZeroPartitionLimit h hh hs hc hpos
  obtain ⟨hD,_,hT⟩ := hLimit (fun _ ↦ 0) (integrable_const 0) 0 β 2 M hβ (by norm_num)
    (fun N ↦ by rw [hExpDouble]; exact hDouble N)
    (fun N ↦ by rw [hExpDouble]; exact bDouble N)
  have hT' : Tendsto (canonicalPartition μ β h) atTop
      (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) := by
    change Tendsto (fun N ↦ ∫ x : Fin N→Ω,Real.exp (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) ∂Measure.pi (fun _ : Fin N ↦ μ)) atTop _
    simpa only [hExp,integral_zero,mul_zero,sub_zero,Real.exp_zero,one_mul] using hT
  have hProper (N : ℕ) : Integrable (fun x : Fin N→Ω ↦ Real.exp
      (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)) := by
    have hu := DGRHS.CLT.memLp_normalizedOffDiagonalSum (ι := Fin N) h hh
    apply (DGRHS.CLT.memLp_exp_of_integrable_double
      (fun x : Fin N→Ω ↦ -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      (hu.aemeasurable.const_mul _) ?_).integrable (by norm_num)
    convert hDouble N using 1
    funext x
    congr 1
    ring
  have hOne (N : ℕ) : 1≤canonicalPartition μ β h N := by
    have hu := (DGRHS.CanonicalVariance.integrable_offDiagonalSum μ h hh (ι := Fin N)).const_mul
      ((N:ℝ)⁻¹)
    have hu0 : (∫ x : Fin N→Ω,DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x
        ∂Measure.pi (fun _ : Fin N ↦ μ))=0 := by
      unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum
      rw [integral_const_mul,DGRHS.CanonicalVariance.integral_offDiagonalSum_eq_zero μ h hh hc]
      simp
    apply canonical_exponential_integral_one_le (Measure.pi (fun _ : Fin N ↦ μ))
      (fun x : Fin N→Ω ↦ -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      (by simpa only [DGRHS.CanonicalVariance.normalizedOffDiagonalSum,Fintype.card_fin] using hu.const_mul (-β/2))
      (hProper N)
    rw [integral_const_mul,hu0,mul_zero]
  obtain ⟨hz,hLog,hErr⟩ := log_partition_limit_and_error (canonicalPartition μ β h)
    ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹) hT' (fun N _ ↦ hOne N)
  refine ⟨κ,eig,e,hκ,he,hD,hz,hT',hLog,fun N ↦ ⟨hProper N,hOne N,?_⟩⟩
  exact abs_log_sub_le_abs_sub_of_one_le _ _ (hOne N) hz
#print axioms DGRHS.Concentration.sourceKernelParticleStatistic_eq_normalized
#check @DGRHS.Concentration.sourceKernelParticleStatistic_eq_normalized
#print axioms DGRHS.Concentration.partition_tendsto_of_reciprocal_error
#check @DGRHS.Concentration.partition_tendsto_of_reciprocal_error
#print axioms DGRHS.Concentration.canonicalPartition_comparison
#check @DGRHS.Concentration.canonicalPartition_comparison
#print axioms DGRHS.Concentration.exists_riesz_cutoff_partition_rate
#check @DGRHS.Concentration.exists_riesz_cutoff_partition_rate
#print axioms DGRHS.Concentration.exists_canonicalMeanZero_log_partition_limit
#check @DGRHS.Concentration.exists_canonicalMeanZero_log_partition_limit
end DGRHS.Concentration
