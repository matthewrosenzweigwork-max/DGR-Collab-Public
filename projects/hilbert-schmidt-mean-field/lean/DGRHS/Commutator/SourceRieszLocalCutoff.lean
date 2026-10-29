import DGRHS.Commutator.SourceRieszTruncatedTransportKernelLongMeasurable
import DGRHS.Commutator.SourceRieszTransportKernelEuclidean
import DGRHS.Commutator.SourceRieszLocalFullControl

/-! Actual source local-commutator cutoff and coefficient. The full compact
sphere bound and genuine Gaussian profile bound determine the constant;
no favorable derivative, moment or numerator hypothesis is supplied. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

 def sourceRieszLocalFullConstant (s : ℝ) (n : ℕ) : ℝ :=
  Classical.choose (exists_sourceRieszTransportKernel_bound (E:=EuclideanSpace ℝ ι) s n)

def sourceRieszLocalProfileConstant (s : ℝ) (n : ℕ) : ℝ :=
  1+max (s*sourceRieszLocalFullConstant (ι:=ι) s n) (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)

lemma sourceRieszLocalProfileConstant_properties (s : ℝ) (n : ℕ) :
    0<sourceRieszLocalProfileConstant (ι:=ι) s n ∧
    s*sourceRieszLocalFullConstant (ι:=ι) s n ≤ sourceRieszLocalProfileConstant (ι:=ι) s n ∧
    sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s ≤ sourceRieszLocalProfileConstant (ι:=ι) s n := by
  have hC := sourceRieszGaussianDerivativeConstant_pos n
  have hp : 0<sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s := by positivity
  unfold sourceRieszLocalProfileConstant
  have h1 := le_max_left (s*sourceRieszLocalFullConstant (ι:=ι) s n) (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)
  have h2 := le_max_right (s*sourceRieszLocalFullConstant (ι:=ι) s n) (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)
  constructor
  · linarith
  constructor <;> linarith

lemma sourceRieszLocal_full_transport_bound (s : ℝ) (n : ℕ) (hs : 0<s)
    {K : ℝ≥0} {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    |sourceRieszTransportKernel n s v p| ≤
      sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n*gaussianRieszPhysicalPair s p := by
  have hB := (Classical.choose_spec (exists_sourceRieszTransportKernel_bound (E:=EuclideanSpace ℝ ι) s n)).2 hv p
  change |sourceRieszTransportKernel n s v p| ≤ sourceRieszLocalFullConstant (ι:=ι) s n*(K:ℝ)^n*‖p.1-p.2‖^(-s) at hB
  calc
    _ ≤ _ := hB
    _ = (s*sourceRieszLocalFullConstant (ι:=ι) s n)*(K:ℝ)^n*gaussianRieszPhysicalPair s p := by
      unfold gaussianRieszPhysicalPair
      field_simp [hs.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).2.1 (by positivity))
      (by unfold gaussianRieszPhysicalPair;positivity)

def sourceRieszLocalCoefficient (s : ℝ) (n : ℕ) (K γ : ℝ) : ℝ :=
  γ/(4*sourceRieszLocalProfileConstant (ι:=ι) s n*K^n)

lemma sourceRieszLocalCoefficient_nonneg (s : ℝ) (n : ℕ) (K γ : ℝ) (hK : 0≤K) (hγ : 0≤γ) :
    0≤sourceRieszLocalCoefficient (ι:=ι) s n K γ := by
  have hC := (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).1
  unfold sourceRieszLocalCoefficient
  positivity

lemma sourceRieszLocalCoefficient_mul_le (s : ℝ) (n : ℕ) (K γ : ℝ) (hK : 0≤K) (hγ : 0≤γ) :
    4*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
      (sourceRieszLocalProfileConstant (ι:=ι) s n*K^n) ≤ γ := by
  have hC := (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).1
  by_cases h : K^n=0
  · simp [sourceRieszLocalCoefficient,h,hγ]
  · unfold sourceRieszLocalCoefficient
    have he : 4*(γ/(4*sourceRieszLocalProfileConstant (ι:=ι) s n*K^n))*(sourceRieszLocalProfileConstant (ι:=ι) s n*K^n)=γ := by
      field_simp [h,hC.ne']
    exact he.le

def sourceRieszLocalRawCutoff (s η : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0)
    (v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι) (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) : ℝ :=
  -4*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*sourceRieszLongTransportKernel n s η v p+
    2*γ*gaussianRieszEuclideanTruncation s (2*η) (p.1-p.2)

lemma sourceRieszLocalRawCutoff_bound (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    |sourceRieszLocalRawCutoff s η n γ σ K v p| ≤
      3*γ*gaussianRieszEuclideanTruncation s η (p.1-p.2) := by
  let ε := sourceRieszLocalCoefficient (ι:=ι) s n K γ
  let A := sourceRieszLocalProfileConstant (ι:=ι) s n
  have hε : 0≤ε := sourceRieszLocalCoefficient_nonneg (ι:=ι) s n K γ K.coe_nonneg hγ
  have hA : 0<A := (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).1
  have he := sourceRieszLocalCoefficient_mul_le (ι:=ι) s n K γ K.coe_nonneg hγ
  have hg : 0≤gaussianRieszEuclideanTruncation s η (p.1-p.2) := gaussianRieszEuclideanTruncation_nonneg s η hs hη _
  have hg2 : 0≤gaussianRieszEuclideanTruncation s (2*η) (p.1-p.2) := gaussianRieszEuclideanTruncation_nonneg s (2*η) hs (by positivity) _
  have hκ : |sourceRieszLongTransportKernel n s η v p| ≤ A*(K:ℝ)^n*gaussianRieszEuclideanTruncation s η (p.1-p.2) :=
    (sourceRieszLongTransportKernel_all_order_bound n s η hs hη hv p).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).2.2 (by positivity)) hg)
  have hm : gaussianRieszEuclideanTruncation s (2*η) (p.1-p.2) ≤ gaussianRieszEuclideanTruncation s η (p.1-p.2) := by
    by_cases hp : p.1=p.2
    · simp only [hp,sub_self]
      unfold gaussianRieszEuclideanTruncation
      norm_num [norm_zero]
      apply mul_le_mul_of_nonneg_left _ (gaussianRieszSourceCoefficient_pos s hs).le
      apply setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt (by linarith : -s-1 < -1) hη)
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact Real.rpow_nonneg (hη.trans ht).le _
      · exact Filter.Eventually.of_forall (fun t ht=> (by linarith : η≤2*η).trans_lt ht)
    · exact sourceRieszLongRange_scale_mono s η (2*η) hs hη (by linarith) (sub_ne_zero.mpr hp)
  unfold sourceRieszLocalRawCutoff
  change |-4*σ*ε*sourceRieszLongTransportKernel n s η v p+2*γ*gaussianRieszEuclideanTruncation s (2*η) (p.1-p.2)|≤_
  calc
    _ ≤ |-4*σ*ε*sourceRieszLongTransportKernel n s η v p|+|2*γ*gaussianRieszEuclideanTruncation s (2*η) (p.1-p.2)| := abs_add_le _ _
    _ ≤ 4*ε*(A*(K:ℝ)^n*gaussianRieszEuclideanTruncation s η (p.1-p.2))+
        2*γ*gaussianRieszEuclideanTruncation s (2*η) (p.1-p.2) := by
      rw [abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg hε,abs_of_nonneg (by positivity : 0≤(4:ℝ)),
        abs_of_nonneg (mul_nonneg (by positivity : 0≤2*γ) hg2)]
      gcongr
      nlinarith [hσ]
    _ ≤ _ := by
      have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤2*γ)
      have he' := mul_le_mul_of_nonneg_right he hg
      change 4*ε*(A*(K:ℝ)^n)*_≤_ at he'
      nlinarith

end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszLocalFullConstant
#print axioms DGRHS.Commutator.sourceRieszLocalFullConstant
#check DGRHS.Commutator.sourceRieszLocalProfileConstant
#print axioms DGRHS.Commutator.sourceRieszLocalProfileConstant
#check DGRHS.Commutator.sourceRieszLocalProfileConstant_properties
#print axioms DGRHS.Commutator.sourceRieszLocalProfileConstant_properties
#check DGRHS.Commutator.sourceRieszLocal_full_transport_bound
#print axioms DGRHS.Commutator.sourceRieszLocal_full_transport_bound
#check DGRHS.Commutator.sourceRieszLocalCoefficient
#print axioms DGRHS.Commutator.sourceRieszLocalCoefficient
#check DGRHS.Commutator.sourceRieszLocalCoefficient_nonneg
#print axioms DGRHS.Commutator.sourceRieszLocalCoefficient_nonneg
#check DGRHS.Commutator.sourceRieszLocalCoefficient_mul_le
#print axioms DGRHS.Commutator.sourceRieszLocalCoefficient_mul_le
#check DGRHS.Commutator.sourceRieszLocalRawCutoff
#print axioms DGRHS.Commutator.sourceRieszLocalRawCutoff
#check DGRHS.Commutator.sourceRieszLocalRawCutoff_bound
#print axioms DGRHS.Commutator.sourceRieszLocalRawCutoff_bound
