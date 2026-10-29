import DGRHS.Attractive.SignedFeatureRate

/-! All positive particle numbers, including beta=0 and N=1. The finite
range below absorption is controlled by actual proper second moments. The
coefficient is linear in the actual diagonal exponential integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian

lemma feature_rate_coefficient_polynomial (b r e M : ℝ) (hb : 0≤b)
    (hr : 0≤r) (he : 0≤e) (hM : 1≤M) :
    Real.sqrt (3*(2+r*M+e*M+108*(b+r+e)*M))+Real.sqrt (432*(b+r+e)*M) ≤
      (8+3*r+3*e+756*(b+r+e))*M := by
  have hMn : 0≤M := by linarith
  have hbound (x : ℝ) (hx : 0≤x) : Real.sqrt x≤1+x := by
    nlinarith [Real.sq_sqrt hx,sq_nonneg (Real.sqrt x-1/2)]
  calc
    _ ≤ (1+3*(2+r*M+e*M+108*(b+r+e)*M))+(1+432*(b+r+e)*M) :=
      add_le_add (hbound _ (by positivity)) (hbound _ (by positivity))
    _ ≤ _ := by nlinarith

universe u v
variable {X : Type u} {H : Type v} [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

theorem exists_positiveFeature_allN_partition_rate [MeasurableSpace.CountablyGenerated X]
    (β : ℝ) (hβ : 0≤β) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x,k x ∂μ)=0)
    (hp : ∀ N : ℕ,1≤N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ)))
    (U : ℝ) (hU : ∀ N : ℕ,1≤N →
      (∫ x,positiveFeatureParticleExp (2*β) k N x ∂Measure.pi (fun _ : Fin N => μ))≤U)
    (hgap : |2*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖<1) :
    let M := ∫ x,Real.exp (a*‖k x‖^2) ∂μ
    let cb := positiveFeatureQuadraticFourthConstant β a
    let cr := positiveFeatureCubicFourthConstant β a
    let ce := positiveFeatureRemainderFourthConstant β a
    let L := Real.exp ((2*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ)/
      (2*(1-|2*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖)))
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)),Countable ι ∧
      (∀ i,DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM)) (b i)=eig i • b i) ∧
      ∀ N : ℕ,1≤N →
        Integrable (positiveFeatureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ))-
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β*eig i)))⁻¹| ≤
          (Real.sqrt (32*β/a)+8+3*cr+3*ce+756*(cb+cr+ce))*M*
            (Real.sqrt U+Real.sqrt L)/Real.sqrt (N:ℝ) := by
  dsimp only
  obtain ⟨ι,eig,e,hι,he,hdet,hsmall,hlarge⟩ :=
    exists_positiveFeature_partition_rate β hβ k hk a ha hM hmean hp U hU hgap
  refine ⟨ι,eig,e,hι,he,?_⟩
  intro N hN
  obtain ⟨hi,hz0,hzB⟩ := hsmall N hN
  refine ⟨hi,?_⟩
  let M := ∫ x,Real.exp (a*‖k x‖^2) ∂μ
  let cb := positiveFeatureQuadraticFourthConstant β a
  let cr := positiveFeatureCubicFourthConstant β a
  let ce := positiveFeatureRemainderFourthConstant β a
  let L := Real.exp ((2*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ)/
    (2*(1-|2*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖)))
  have hfactor : 0≤Real.sqrt U+Real.sqrt L := by positivity
  have hMl : 1≤M := one_le_integral_featureDiagonalExponential k a ha.le hM
  have hMn : 0≤M := by linarith
  have hcb : 0≤cb := by unfold cb positiveFeatureQuadraticFourthConstant gaussianDiagonalMomentConstant;positivity
  have hcr : 0≤cr := by unfold cr positiveFeatureCubicFourthConstant gaussianDiagonalMomentConstant;positivity
  have hce : 0≤ce := by unfold ce positiveFeatureRemainderFourthConstant gaussianDiagonalMomentConstant;positivity
  have hP : 0≤8+3*cr+3*ce+756*(cb+cr+ce) := by positivity
  have hpoly := feature_rate_coefficient_polynomial cb cr ce M hcb hcr hce hMl
  have hn0 : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hN)
  have hsn : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.2 hn0
  by_cases hscale : 32*β≤a*(N:ℝ)
  · apply (hlarge N hN hscale).2.trans
    have hh : (Real.sqrt (3*(2+cr*M+ce*M+108*(cb+cr+ce)*M))+
        Real.sqrt (432*(cb+cr+ce)*M)) ≤
        (Real.sqrt (32*β/a)+8+3*cr+3*ce+756*(cb+cr+ce))*M := by
      apply hpoly.trans
      nlinarith [mul_nonneg (Real.sqrt_nonneg (32*β/a)) hMn]
    have hb := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh hfactor) hsn.le
    dsimp only [M,cb,cr,ce,L] at hb
    exact hb
  · have hth : (N:ℝ)<32*β/a := (lt_div_iff₀ ha).2 (by nlinarith [lt_of_not_ge hscale])
    have hsq := Real.sqrt_le_sqrt hth.le
    have hc : Real.sqrt (N:ℝ)≤(Real.sqrt (32*β/a)+8+3*cr+3*ce+756*(cb+cr+ce))*M := by
      apply hsq.trans
      nlinarith [mul_nonneg (Real.sqrt_nonneg (32*β/a)) (sub_nonneg.mpr hMl),mul_nonneg hP hMn]
    have herr : |(∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ))-
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β*eig i)))⁻¹| ≤
        Real.sqrt U+Real.sqrt (Real.exp ((2*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ)/
          (2*(1-|2*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
            (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖)))) := by
      apply abs_sub_le_iff.mpr
      constructor <;> linarith [hdet.1,hdet.2,Real.sqrt_nonneg U,Real.sqrt_nonneg
        (Real.exp ((2*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ)/
          (2*(1-|2*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
            (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖))))]
    apply (le_div_iff₀ hsn).2
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right herr hsn.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by dsimp only [M,cb,cr,ce];ring

end DGRHS.Attractive
#check DGRHS.Attractive.exists_positiveFeature_allN_partition_rate
#print axioms DGRHS.Attractive.exists_positiveFeature_allN_partition_rate
#print axioms DGRHS.Attractive.feature_rate_coefficient_polynomial
