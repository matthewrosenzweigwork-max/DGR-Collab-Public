import DGRHS.Concentration.SourceRateAssembly
import DGRHS.Gaussian.GaussianRieszAllCutoffMoment
import DGRHS.Gaussian.GaussianRieszFullMoment
import DGRHS.Gaussian.GaussianRieszFullPositivity

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.Concentration
universe u
open DGRHS.Gaussian

/-- Exact source exponent normalization, valid also for the empty array. -/
lemma iidNegativeStatistic_exponent_eq_normalized {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (h : Ω×Ω→ℝ) (N : ℕ) (x : Fin N→Ω) :
    β*iidNegativeStatistic N h x = -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  have hSum : iidCoupledSum N h x = ∑ i : Fin N,∑ j : Fin N,if i=j then 0 else h (x i,x j) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    simp only [ne_eq,ite_not]
  rw [← sourceKernelParticleStatistic_eq_normalized]
  unfold iidNegativeStatistic DGRHS.Gaussian.sourceKernelParticleStatistic
  rw [hSum]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual normalized full Riesz partition and its log have the original
logarithmic rate for every positive N. All proper uniform moments, canonical
conditions, positive source spectrum and remainder control are constructed
from bounded-density physical data, not supplied as final-rate premises. -/
theorem gaussianRieszPhysical_log_partition_rate {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (ha : 0<(Fintype.card ι:ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
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
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) ∧
        |Real.log (canonicalPartition μ β h N)-Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) := by
  let μ := gaussianRieszDensityMeasure ρ
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
  let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
  have hhm : Measurable h :=
    (stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_gaussianRieszPhysicalPair s)).measurable
  have hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p := by
    apply Eventually.of_forall
    intro p
    exact DGRHS.centeredKernel_symmetric μ (fun a b ↦ gaussianRieszPhysicalPair s (a,b))
      (fun a b ↦ by simp only [gaussianRieszPhysicalPair,norm_sub_rev]) p.2 p.1
  have hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0 :=
    DGRHS.integral_centeredKernel_right μ (fun a b ↦ gaussianRieszPhysicalPair s (a,b))
      ((memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num))
  have hPos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v) :=
    gaussianRieszPhysicalOperator_positive s hs ha ρ M hM hρ
  obtain ⟨MF,hF⟩ := gaussianRieszPhysical_uniform_exponential s (2*β) hs (by positivity) ha ρ M hM hρ
  obtain ⟨MK,hK⟩ := gaussianRieszCutoff_uniform_exponential s (2*β) hs (by positivity) ha ρ M hM hρ
  have hEF (N : ℕ) : (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp ((2*β)*iidNegativeStatistic N h x)) =
      (fun x ↦ Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [iidNegativeStatistic_exponent_eq_normalized]
    congr 1
    ring
  have hEK (η : ℝ) (hη : 0<η) (N : ℕ) :
      (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp ((2*β)*iidNegativeStatistic N
        (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) x)) =
      (fun x ↦ Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (fun p ↦ centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) x)) := by
    funext x
    rw [iidNegativeStatistic_exponent_eq_normalized]
    have hEq : hoeffdingCentered μ (gaussianRieszTruncatedPair s η) =
        (fun p ↦ centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) :=
      funext (gaussianRieszCenteredTruncatedPair_eq_source s η hs hη μ)
    rw [hEq]
    congr 1
    ring
  have hMF : 1≤MF := by
    have hb := (hF 1 le_rfl).2
    simpa [iidNegativeStatistic,iidCoupledSum,DGRHS.Decoupling.offDiagonalSum] using hb
  have hDouble : ∀ N,Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)) := by
    intro N
    by_cases hN : N=0
    · subst N
      simpa [DGRHS.CanonicalVariance.normalizedOffDiagonalSum] using
        (integrable_const (1:ℝ) : Integrable (fun _ : Fin 0→EuclideanSpace ℝ ι ↦ (1:ℝ)) (Measure.pi (fun _ : Fin 0 ↦ μ)))
    · have hb := (hF N (by omega)).1
      rw [hEF N] at hb
      exact hb
  have bDouble : ∀ N,(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤MF := by
    intro N
    by_cases hN : N=0
    · subst N
      simpa [DGRHS.CanonicalVariance.normalizedOffDiagonalSum] using hMF
    · have hb := (hF N (by omega)).2
      rw [hEF N] at hb
      exact hb
  let A := 4*gaussianRieszShortRangeRateConstant s M ι
  have hA : 0≤A := by dsimp [A,gaussianRieszShortRangeRateConstant]; positivity
  have hResidual (η : ℝ) (hη : 0<η) (_ : η≤1)
      (hq : MemLp (fun p : (EuclideanSpace ℝ ι)×(EuclideanSpace ℝ ι) ↦ centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) 2 (μ.prod μ)) :
      ‖(hh.sub hq).toLp (fun p ↦ h p-centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2)‖≤
        A*η^((Fintype.card ι:ℝ)/2-s) := by
    have hEq : (fun p ↦ h p-centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) =ᵐ[μ.prod μ]
        hoeffdingCentered μ (gaussianRieszShortPair s η) := by
      filter_upwards [ae_gaussianRiesz_centered_difference s η hs hη ha ρ M hM hρ] with p hp
      rw [← gaussianRieszCenteredTruncatedPair_eq_source s η hs hη μ p]
      exact hp
    have hSub : MemLp (fun p ↦ h p-centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) 2 (μ.prod μ) := hh.sub hq
    rw [hSub.toLp_congr (memLp_gaussianRieszCenteredShortPair s η hη ha ρ M hM hρ) hEq]
    exact norm_gaussianRieszCenteredShortPair_le s η hη ha ρ M hM hρ
  obtain ⟨κ,eig,e,hκ,he,hD,hT,hLog,C,hC,hRate⟩ := exists_uniform_riesz_log_partition_rate μ β s
    ((Fintype.card ι:ℝ)/2-s) 1 A MF MK hβ hs ha (by norm_num) hA h hhm hh hSym hCan hPos hDouble bDouble
    (fun η hη _ N hN ↦ by have hb := (hK η hη N hN).1;rw [hEK η hη N] at hb;exact hb)
    (fun η hη _ N hN ↦ by have hb := (hK η hη N hN).2;rw [hEK η hη N] at hb;exact hb)
    hResidual
  have hExponent : ((Fintype.card ι:ℝ)/2-s)/s=((Fintype.card ι:ℝ)-2*s)/(2*s) := by field_simp <;> ring
  refine ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hT,hLog,C,hC,?_⟩
  intro N hN
  simpa only [hExponent] using hRate N hN

#print axioms DGRHS.Concentration.iidNegativeStatistic_exponent_eq_normalized
#print axioms DGRHS.Concentration.gaussianRieszPhysical_log_partition_rate
#check @DGRHS.Concentration.gaussianRieszPhysical_log_partition_rate
end DGRHS.Concentration
