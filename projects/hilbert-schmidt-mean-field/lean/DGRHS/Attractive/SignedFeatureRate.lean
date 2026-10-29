import DGRHS.Attractive.SignedFeatureCompleteData
import DGRHS.Attractive.FeatureGoodSetIntegratedRate

/-! Source positive-sign feature rate on countably generated particle spaces.
The Gaussian field, coefficient moments, Taylor expansion, proper powers and
signed determinant law are constructed from the stated source inputs. This
uses the recorded elementary residual adaptation rather than the original
integrated fourth-derivative identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian

lemma feature_goodSet_sqrt_rate (n r e m : ℝ) (hn : 1≤n)
    (hr : 0≤r) (he : 0≤e) (hm : 0≤m) :
    Real.sqrt (3*((1+r)/n+(1+e)/n^2+108*m/n^2))+
      Real.sqrt (432*m/n^4) ≤
      (Real.sqrt (3*(2+r+e+108*m))+Real.sqrt (432*m))/Real.sqrt n := by
  have hn0 : 0<n := by linarith
  have hn2 : n≤n^2 := by nlinarith
  have hn4 : n≤n^4 := by nlinarith [sq_nonneg (n^2-1)]
  have hd : 3*((1+r)/n+(1+e)/n^2+108*m/n^2)≤3*(2+r+e+108*m)/n := by
    calc
      _ ≤ 3*((1+r)/n+(1+e)/n+108*m/n) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply add_le_add
        · exact add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) hn0 hn2)
        · exact div_le_div_of_nonneg_left (by positivity) hn0 hn2
      _ = _ := by ring
  have hb : 432*m/n^4≤432*m/n := div_le_div_of_nonneg_left (by positivity) hn0 hn4
  have hsd := Real.sqrt_le_sqrt hd
  have hsb := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_div (by positivity) n] at hsd hsb
  calc
    _ ≤ Real.sqrt (3*(2+r+e+108*m))/Real.sqrt n+Real.sqrt (432*m)/Real.sqrt n :=
      add_le_add hsd hsb
    _ = _ := by ring

universe u v
variable {X : Type u} {H : Type v} [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

theorem exists_positiveFeature_partition_rate [MeasurableSpace.CountablyGenerated X]
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
      (0≤(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β*eig i)))⁻¹ ∧
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β*eig i)))⁻¹≤Real.sqrt L) ∧
      (∀ N : ℕ,1≤N →
        Integrable (positiveFeatureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ)) ∧
        0≤(∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ)) ∧
        (∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ))≤Real.sqrt U) ∧
      ∀ N : ℕ,1≤N →32*β≤a*(N:ℝ) →
        Integrable (positiveFeatureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ))-
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β*eig i)))⁻¹| ≤
          (Real.sqrt (3*(2+cr*M+ce*M+108*(cb+cr+ce)*M))+
            Real.sqrt (432*(cb+cr+ce)*M))*(Real.sqrt U+Real.sqrt L)/Real.sqrt (N:ℝ) := by
  dsimp only
  obtain ⟨j,b,f,hf,g,hj,hg,hg2,hW,hexp,hL,hiB,hbB,hiR,hbR,hiR2,hbR2,hNdata⟩ :=
    exists_positiveFeature_goodSet_data β hβ k hk a ha hM hmean hp U hU hgap
  letI : Countable j := hj
  obtain ⟨ι,eig,e,hι,he,_,_,_,hQ⟩ := exists_positiveQuadraticCoefficient_laplace
    b f hf β k hk a ha hM hmean g hg hg2 hW
  have hgap1 : |1*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖<1 := by
    have hh : |β|≤|2*β| := by rw [abs_mul];norm_num;linarith [abs_nonneg β]
    simpa only [one_mul] using lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) hgap
  have hq := (hQ 1 hgap1).2
  simp only [one_mul,neg_one_mul] at hq
  have hDm : StronglyMeasurable (fun x => ‖k x‖^2) := hk.norm.pow 2
  have hBs := stronglyMeasurable_positiveQuadraticCoefficient (μ := μ) β _ hDm g hg
  have hb2 := (memLp_two_iff_integrable_sq
    (Real.continuous_exp.comp_stronglyMeasurable hBs).aestronglyMeasurable).1 hexp
  have hmeanB := integral_sq_mean_le _ (hexp.integrable (by norm_num)) hb2
  refine ⟨ι,eig,e,hι,he,⟨by positivity,?_⟩,?_,?_⟩
  · rw [←hq]
    exact Real.le_sqrt_of_sq_le (hmeanB.trans hL)
  · intro N hN
    obtain ⟨_,hpow,hpowB,heAN,_,_⟩ := hNdata N hN
    have hp2 := (memLp_two_iff_integrable_sq
      ((stronglyMeasurable_positiveFeatureFactor β k hk g hg N).pow N).aestronglyMeasurable).1 hpow
    refine ⟨integrable_positiveFeatureParticleExp_of_doubled β k hk N (hp N hN),
      integral_nonneg (fun x => (Real.exp_pos _).le),?_⟩
    rw [heAN]
    exact Real.le_sqrt_of_sq_le ((integral_sq_mean_le _ (hpow.integrable (by norm_num)) hp2).trans hpowB)
  intro N hN hscale
  refine ⟨integrable_positiveFeatureParticleExp_of_doubled β k hk N (hp N hN),?_⟩
  obtain ⟨hpos,hpow,hpowB,heAN,htaylor,hEn⟩ := hNdata N hN
  obtain ⟨hiE,hbE,hiE2,hbE2⟩ := hEn hscale
  have hcompare := source_taylor_good_bad_integral_bound IsonormalProcess.iidStdGaussian
    (positiveFeatureFactor μ β k g N) (positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g)
    (positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g)
    (positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N) N hN
    (stronglyMeasurable_positiveFeatureFactor β k hk g hg N).measurable
    (stronglyMeasurable_positiveQuadraticCoefficient (μ := μ) β _ hDm g hg).measurable
    hpos hpow hexp hiR2 hiE2 hiB hiR hiE htaylor
  dsimp only at hcompare
  rw [heAN,←hq]
  apply hcompare.trans
  let M := ∫ x,Real.exp (a*‖k x‖^2) ∂μ
  let cb := positiveFeatureQuadraticFourthConstant β a
  let cr := positiveFeatureCubicFourthConstant β a
  let ce := positiveFeatureRemainderFourthConstant β a
  have hMn : 0≤M := integral_nonneg (fun x => (Real.exp_pos _).le)
  have hcb : 0≤cb := by unfold cb positiveFeatureQuadraticFourthConstant gaussianDiagonalMomentConstant;positivity
  have hcr : 0≤cr := by unfold cr positiveFeatureCubicFourthConstant gaussianDiagonalMomentConstant;positivity
  have hce : 0≤ce := by unfold ce positiveFeatureRemainderFourthConstant gaussianDiagonalMomentConstant;positivity
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hsum : (∫ ω,positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4 ∂IsonormalProcess.iidStdGaussian)+
      (∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4 ∂IsonormalProcess.iidStdGaussian)+
      (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4 ∂IsonormalProcess.iidStdGaussian)≤
        (cb+cr+ce)*M := by
    calc
      _ ≤ cb*M+cr*M+ce*M := add_le_add (add_le_add hbB hbR) hbE
      _ = _ := by ring
  have hδ := add_le_add
    (Real.sqrt_le_sqrt (show 3*((∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^2 ∂IsonormalProcess.iidStdGaussian)/(N:ℝ)+
      (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^2 ∂IsonormalProcess.iidStdGaussian)/(N:ℝ)^2+
      108*((∫ ω,positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4 ∂IsonormalProcess.iidStdGaussian)+
      (∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4 ∂IsonormalProcess.iidStdGaussian)+
      (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4 ∂IsonormalProcess.iidStdGaussian))/(N:ℝ)^2)≤
      3*((1+cr*M)/(N:ℝ)+(1+ce*M)/(N:ℝ)^2+108*((cb+cr+ce)*M)/(N:ℝ)^2) by gcongr))
    (Real.sqrt_le_sqrt (show 432*((∫ ω,positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4 ∂IsonormalProcess.iidStdGaussian)+
      (∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4 ∂IsonormalProcess.iidStdGaussian)+
      (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4 ∂IsonormalProcess.iidStdGaussian))/(N:ℝ)^4≤
      432*((cb+cr+ce)*M)/(N:ℝ)^4 by gcongr))
  have hδ' := hδ.trans (feature_goodSet_sqrt_rate N (cr*M) (ce*M) ((cb+cr+ce)*M) hn
    (mul_nonneg hcr hMn) (mul_nonneg hce hMn) (mul_nonneg (by linarith) hMn))
  have hfactor := add_le_add (Real.sqrt_le_sqrt hpowB) (Real.sqrt_le_sqrt hL)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hδ' (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by
      dsimp only [M, cb, cr, ce]
      ring

end DGRHS.Attractive
#check DGRHS.Attractive.exists_positiveFeature_partition_rate
#print axioms DGRHS.Attractive.exists_positiveFeature_partition_rate
#print axioms DGRHS.Attractive.feature_goodSet_sqrt_rate
