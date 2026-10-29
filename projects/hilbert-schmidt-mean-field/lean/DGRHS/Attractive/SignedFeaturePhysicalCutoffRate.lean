import DGRHS.Attractive.SignedFeaturePhysicalDiagonal
import DGRHS.Attractive.LogPhysicalInterpolationBridge
import DGRHS.Attractive.FactorialCanonicalComparison

/- Actual attractive fixed-cutoff rate from the original row/density/tail data.
The physical field, proper diagonal moment, proper doubled particle moment and
uniform actual operator margin are derived, not supplied as conclusions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem exists_gaussianLogPhysical_cutoff_feature_rate
    (ρ : EuclideanSpace ℝ ι→ℝ) (M C β : ℝ)
    (hd : 0<(Fintype.card ι:ℝ)) (hM : 0≤M) (hC : 0<C) (hβ : 0<β)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (hrows : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal (|DGRHS.centeredKernel (gaussianRieszDensityMeasure ρ)
        attractiveLogInteraction x y|^p) ∂gaussianRieszDensityMeasure ρ)≤
        ENNReal.ofReal (C^p*(p.factorial:ℝ)))
    (hsmall : β<gaussianLogQuantitativeThreshold C M (Fintype.card ι:ℝ))
    (htail : Integrable (fun x=>Real.exp
      (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ K : ℝ,0≤K ∧ ∀ η : ℝ,0<η → η≤1 →
      let q := hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogPhysicalInterpolation η 0)
      ∃ (hh : MemLp q 2 ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (κ : Type u) (eig : κ→ℝ)
        (b : HilbertBasis κ ℝ (Lp ℝ 2 (gaussianRieszDensityMeasure ρ))),Countable κ ∧
        (∀ i,DGRHS.Kernel.integralOperator q hh (b i)=eig i • b i) ∧
        ∀ N : ℕ,1≤N →
          Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
            (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x))
            (Measure.pi (fun _ : Fin N=>(gaussianRieszDensityMeasure ρ))) ∧
          |(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
            (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
            ∂Measure.pi (fun _ : Fin N=>(gaussianRieszDensityMeasure ρ)))-
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>-β*eig i)))⁻¹| ≤
            K*η^(-2*β)/Real.sqrt (N:ℝ) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let R := gaussianLogInterpolationRowConstant C M (Fintype.card ι:ℝ)
  let U := 2/(1-(β*(attractiveMomentConstant*R))^2)
  let L0 := Real.exp ((2*β)^2*(2*R^2)/(2*(1-2*β*(2*R))))
  let A := 2*M*((2*Real.pi)^((Fintype.card ι:ℝ)/2)/(Fintype.card ι:ℝ))+
    (1/4:ℝ)+(∫ p,logPhysicalPair p ∂μ.prod μ)
  let T := ∫ x,Real.exp (-4*β*logPhysicalPotential μ x) ∂μ
  let cb := positiveFeatureQuadraticFourthConstant β (2*β)
  let cr := positiveFeatureCubicFourthConstant β (2*β)
  let ce := positiveFeatureRemainderFourthConstant β (2*β)
  let G := Real.sqrt (32*β/(2*β))+8+3*cr+3*ce+756*(cb+cr+ce)
  let K := G*Real.exp (2*β*A)*T*(Real.sqrt U+Real.sqrt L0)
  have hT : 0≤T := integral_nonneg (fun _=> (Real.exp_pos _).le)
  have hcb : 0≤cb := by dsimp [cb,positiveFeatureQuadraticFourthConstant,gaussianDiagonalMomentConstant];positivity
  have hcr : 0≤cr := by dsimp [cr,positiveFeatureCubicFourthConstant,gaussianDiagonalMomentConstant];positivity
  have hce : 0≤ce := by dsimp [ce,positiveFeatureRemainderFourthConstant,gaussianDiagonalMomentConstant];positivity
  have hG : 0≤G := by dsimp [G];positivity
  refine ⟨K,by dsimp [K];positivity,fun η hη hη1=>?_⟩
  let q := hoeffdingCentered μ (gaussianLogPhysicalInterpolation η 0)
  obtain ⟨hr,hm,hgap⟩ := gaussianLogPhysical_interpolation_rows_margin η 0 β
    hη hη1 (by norm_num) (by norm_num) hd ρ M C hM hC hρ hpair hrows hβ.le hsmall
  let hh := joint_memLp μ q hm R hr 2 (by omega)
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  letI : TopologicalSpace.SeparableSpace (Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) :=
    separableSpace_gaussianLogPhaseHilbert η
  letI : MeasurableSpace (Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) := borel _
  letI : BorelSpace (Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) := ⟨rfl⟩
  have hk := stronglyMeasurable_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  have hmean := integral_gaussianLogCenteredInfiniteFeature_eq_zero η hη hd ρ M hM hρ hpair
  have he := hoeffdingCentered_gaussianLogInterpolation_eq η 0 hη hd ρ M hM hρ hpair
  have hGram : q =ᵐ[μ.prod μ] featureKernel k := by
    filter_upwards [ae_logPhysical_centered_difference η hη hd ρ M hM hρ hpair,
      ae_gaussianLogTruncatedPair_eq_infiniteFeatureGram η hη hd ρ M hM hρ hpair] with z hz hg
    have hq := congrFun he z
    dsimp [gaussianLogAlgebraicInterpolation] at hq
    simp only [sub_zero,mul_one,one_mul] at hq
    change hoeffdingCentered μ logPhysicalPair z-
      hoeffdingCentered μ (gaussianLogTruncatedPair η) z=
        hoeffdingCentered μ (gaussianLogShortPair η) z at hz
    change q z=inner ℝ (k z.1) (k z.2)
    dsimp [q]
    rw [hq]
    dsimp [k]
    linarith
  have hfulls : ∀ x y : EuclideanSpace ℝ ι,logPhysicalPair (x,y)=logPhysicalPair (y,x) := by
    intro x y;unfold logPhysicalPair;rw [norm_sub_rev]
  have hraws : ∀ x y : EuclideanSpace ℝ ι,
      gaussianLogPhysicalInterpolation η 0 (x,y)=gaussianLogPhysicalInterpolation η 0 (y,x) := by
    intro x y;unfold gaussianLogPhysicalInterpolation
    rw [hfulls,gaussianLogShortPair_symmetric η x y]
  have hs : ∀ x y,q (x,y)=q (y,x) := DGRHS.centeredKernel_symmetric μ _ hraws
  have hir : Integrable (gaussianLogPhysicalInterpolation η 0) (μ.prod μ) :=
    hpair.sub (((memLp_gaussianLogShortPair η hη hd ρ M hM hρ).integrable (by norm_num)).const_mul (1-0))
  have hc : ∀ᵐ y ∂μ,∫ x,q (x,y) ∂μ=0 := DGRHS.integral_centeredKernel_left μ _ hir
  have hrsmall := gaussianLogQuantitativeThreshold_row_small C M _ β hC hM hd hβ.le hsmall
  have hu := factorialCanonical_positive_uniform q hm R β hr hs hc hβ.le hrsmall
  have hp : ∀ N : ℕ,1≤N → Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)) (Measure.pi (fun _ : Fin N=>μ)) := fun N _ => (hu N).1
  have hU : ∀ N : ℕ,1≤N → (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x) ∂Measure.pi (fun _ : Fin N=>μ))≤U := fun N _ => (hu N).2
  have hg : |2*β| *‖DGRHS.Kernel.integralOperator q hh‖<1 := by
    simpa only [abs_of_nonneg (by positivity : 0≤2*β)] using hgap
  obtain ⟨hMeta,bMeta⟩ := gaussianLogFeature_diagonal_exponential β η hβ.le hη hη1 hd ρ M hM hρ hpair htail
  obtain ⟨κ,eig,b,hκ,hb,hRate⟩ := exists_sourceKernel_positive_feature_rate
    β hβ.le q hh k hk (2*β) (by positivity) hMeta hmean hGram hp U hU hg
  have hR : 0≤R := hr.nonneg
  have hmarg : 2*β*(2*R)<1 := by
    have hle := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right attractiveMomentConstant_four_le hR) hβ.le
    nlinarith
  have hL := feature_HS_margin_exponential_uniform β
    (∫ z,q z^2 ∂μ.prod μ) ‖DGRHS.Kernel.integralOperator q hh‖ (2*R^2) (2*R)
    hβ.le (integral_nonneg (fun _=>sq_nonneg _))
    (rowMoment_actual_operator_norm_le q hm R hr)
    (rowMoment_joint_second_bound q hm R hr) hmarg
  simp only [abs_of_nonneg (by positivity : 0≤2*β)] at hRate
  refine ⟨hh,κ,eig,b,hκ,hb,fun N hN=>?_⟩
  obtain ⟨hi,heRate⟩ := hRate N hN
  refine ⟨hi,heRate.trans ?_⟩
  have hprod := mul_le_mul bMeta
    (add_le_add le_rfl (Real.sqrt_le_sqrt hL))
    (by positivity : 0≤Real.sqrt U+Real.sqrt (Real.exp ((2*β)^2*(∫ z,q z^2 ∂μ.prod μ)/(2*(1-2*β*‖DGRHS.Kernel.integralOperator q hh‖)))))
    (by positivity : 0≤Real.exp (2*β*A)*η^(-2*β)*T)
  have hscale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hG)
    (Real.sqrt_nonneg (N:ℝ))
  convert hscale using 1 <;> dsimp [G,cb,cr,ce,L0,K,A,T,μ] <;> ring

end DGRHS.Attractive
#check @DGRHS.Attractive.exists_gaussianLogPhysical_cutoff_feature_rate
#print axioms DGRHS.Attractive.exists_gaussianLogPhysical_cutoff_feature_rate
