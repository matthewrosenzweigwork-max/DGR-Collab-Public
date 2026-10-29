import DGRHS.Concentration.SourcePartitionRate
import DGRHS.Concentration.SourceRateThreshold

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.Concentration
universe u

lemma riesz_cutoff_canonical_data {ι : Type u} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (hs : 0<s) (hη : 0<η) :
    let q := fun p : (EuclideanSpace ℝ ι)×(EuclideanSpace ℝ ι) ↦
      DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2
    Measurable q ∧ (∀ᵐ p ∂μ.prod μ,q p.swap=q p) ∧
      (∀ᵐ x ∂μ,(∫ y,q (x,y) ∂μ)=0) := by
  let k := DGRHS.Gaussian.centeredGaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη μ
  have hk := DGRHS.Gaussian.stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη μ
  have hPoint (a b : EuclideanSpace ℝ ι) :
      DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ a b = inner ℝ (k a) (k b) :=
    (DGRHS.Gaussian.inner_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ a b).symm
  dsimp only
  simp_rw [hPoint]
  change Measurable (DGRHS.Gaussian.featureKernel k) ∧
    (∀ᵐ p ∂μ.prod μ,DGRHS.Gaussian.featureKernel k p.swap=DGRHS.Gaussian.featureKernel k p) ∧
    (∀ᵐ x ∂μ,(∫ y,DGRHS.Gaussian.featureKernel k (x,y) ∂μ)=0)
  refine ⟨((hk.comp_measurable measurable_fst).inner (hk.comp_measurable measurable_snd)).measurable,
    Eventually.of_forall (DGRHS.Gaussian.featureKernel_symmetric k),?_⟩
  exact Eventually.of_forall (DGRHS.Gaussian.integral_featureKernel_right k
    (DGRHS.Gaussian.memLp_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ 2)
    (DGRHS.Gaussian.integral_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ))

/-- The genuine full canonical source rate: both determinant limits, every
finite-particle comparison, the source cutoff choice and finite-N absorption
are derived. The inputs are actual kernel and proper moment controls, not
partition rates, spectral matching or determinant continuity. -/
theorem exists_uniform_riesz_log_partition_rate {ι : Type u} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (β s r η₀ A MH MK : ℝ) (hβ : 0≤β) (hs : 0<s) (hr : 0<r)
    (hη₀ : 0<η₀) (hA : 0≤A)
    (h : (EuclideanSpace ℝ ι)×(EuclideanSpace ℝ ι)→ℝ)
    (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
    (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
    (hPos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v))
    (hDouble : ∀ N,Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)))
    (bDouble : ∀ N,(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤MH)
    (kDouble : ∀ η,0<η→η≤η₀→∀ N,1≤N→Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (fun p ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) x))
        (Measure.pi (fun _ : Fin N ↦ μ)))
    (bkDouble : ∀ η,0<η→η≤η₀→∀ N,1≤N→(∫ x : Fin N→EuclideanSpace ℝ ι,
      Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (fun p ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) x)
          ∂Measure.pi (fun _ : Fin N ↦ μ))≤MK)
    (hResidual : ∀ η,0<η→η≤η₀→∀ hq : MemLp
      (fun p : (EuclideanSpace ℝ ι)×(EuclideanSpace ℝ ι) ↦ DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2)
        2 (μ.prod μ),‖(hh.sub hq).toLp (fun p ↦ h p-DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2)‖≤A*η^r) :
    ∃ (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      Tendsto (canonicalPartition μ β h) atTop (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N ↦ Real.log (canonicalPartition μ β h N)) atTop
        (𝓝 (Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∃ C : ℝ,0≤C ∧ ∀ N,1≤N→
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
          (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        |canonicalPartition μ β h N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(r/s)) ∧
        |Real.log (canonicalPartition μ β h N)-Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(r/s)) := by
  obtain ⟨κ,eig,e,hκ,he,hD,_,hT,hLog,hAll⟩ :=
    exists_canonicalMeanZero_log_partition_limit μ β hβ h hh hSym hCan hPos MH hDouble bDouble
  let z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹
  let L := DGRHS.Gaussian.rieszGaussianLaplaceConstant β (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s
  have hL : 0<L := by
    obtain ⟨_,_,_,_,_,_,_,hL,_,_⟩ := exists_riesz_cutoff_partition_rate μ β s η₀ hβ hs hη₀
    exact hL
  let B := (|β|/2*Real.sqrt 2)*(Real.sqrt MH+Real.sqrt MK)*A
  have hB : 0≤B := by dsimp [B]; positivity
  let D := 2*B*(2*L)^(r/s)*(1+Real.log (Real.exp 1+1)/Real.log 2)^(r/s)+
    L*(Real.log (Real.exp 1+1)+2*(r/s))^(r/s)
  obtain ⟨N₀,hN₀⟩ := sourceRieszRateCutoff_eventually_small L s η₀ hL hs hη₀
  let f := fun N : ℕ ↦ (Real.log (Real.exp 1+(N:ℝ)))^(-(r/s))
  have hf : ∀ N,0<f N := by
    intro N
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    have he1 : 1<Real.exp (1:ℝ) := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (zero_lt_one : (0:ℝ)<1)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hLarge : ∀ N,1≤N→N₀≤N→|canonicalPartition μ β h N-z|≤D*f N := by
    intro N hN hNN
    obtain ⟨hN2,hη,hηsmall⟩ := hN₀ N hNN
    let η := sourceRieszRateCutoff L s (N:ℝ)
    let q := fun p : (EuclideanSpace ℝ ι)×(EuclideanSpace ℝ ι) ↦
      DGRHS.Gaussian.centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2
    obtain ⟨hq,σ,c,b,_,_,_,_,hY,hRate⟩ := exists_riesz_cutoff_partition_rate μ β s η hβ hs hη
    obtain ⟨hqm,hqs,hqc⟩ := riesz_cutoff_canonical_data μ s η hs hη
    have hComp := canonicalPartition_comparison μ β h q hhm hqm hh hq hSym hqs hCan hqc
      (A*η^r) MH MK (hResidual η hη hηsmall hq)
      (fun n _ ↦ hDouble n) (kDouble η hη hηsmall)
      (fun n _ ↦ bDouble n) (bkDouble η hη hηsmall)
    have hComp' : ∀ n,1≤n→|canonicalPartition μ β h n-canonicalPartition μ β q n|≤B*η^r := by
      intro n hn
      convert hComp n hn using 1 <;> dsimp [B] <;> ring
    have hError := partition_error_assembly (canonicalPartition μ β h) (canonicalPartition μ β q)
      z ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*c i)))⁻¹) (B*η^r) hT hY hComp' N hN
    have hOpt := sourceRieszRateCutoff_bound B L s r (N:ℝ) hB hL hs hr (by exact_mod_cast hN2)
    apply (hError.trans (add_le_add le_rfl (hRate N hN).2)).trans
    convert hOpt using 1 <;> dsimp [η,L,D,f] <;> ring
  obtain ⟨hC,hRate⟩ := partition_rate_all_positive (canonicalPartition μ β h) z f hf D N₀ hLarge
  let C := max D 0+∑ j ∈ Finset.range N₀,|canonicalPartition μ β h j-z|/f j
  refine ⟨κ,eig,e,hκ,he,hD,hT,hLog,C,hC,?_⟩
  intro N hN
  exact ⟨(hAll N).1,hRate N hN,((hAll N).2.2).trans (hRate N hN)⟩

#print axioms DGRHS.Concentration.riesz_cutoff_canonical_data
#print axioms DGRHS.Concentration.exists_uniform_riesz_log_partition_rate
#check @DGRHS.Concentration.exists_uniform_riesz_log_partition_rate
end DGRHS.Concentration
