import DGRHS.Attractive.SignedFeaturePhysicalCutoffRate
import DGRHS.Attractive.SignedFeatureRateAssembly
import DGRHS.Attractive.SignedCanonicalPartitionLimit
import DGRHS.Attractive.SignedFeaturePhysicalComparison

/- The full physical canonical determinant comparison follows by passing the
actual finite-particle cutoff comparison to the two actual partition limits.
This is an alternative to trace-power determinant continuity. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem exists_gaussianLogPhysical_canonical_cutoff_rate
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
    let q := hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair
    ∃ (hh : MemLp q 2 ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
      (κ : Type u) (eig : κ→ℝ) (b : HilbertBasis κ ℝ (Lp ℝ 2 (gaussianRieszDensityMeasure ρ))),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperator q hh (b i)=eig i • b i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i=>-β*eig i) ∧
      Tendsto (fun N=>∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>-β*eig i)))⁻¹)) ∧
      ∃ A B : ℝ,0≤A ∧ 0≤B ∧ ∀ η : ℝ,0<η → η≤1 → ∀ N : ℕ,1≤N →
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
          (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x))
          (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
        |(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
          (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
          ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))-
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>-β*eig i)))⁻¹| ≤
          2*A*η^((Fintype.card ι:ℝ)/2)+B*η^(-2*β)/Real.sqrt (N:ℝ) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let q := hoeffdingCentered μ logPhysicalPair
  have hr := logPhysical_factorial_rows_of_attractive μ C hC.le hrows
  have hm : Measurable q := (stronglyMeasurable_hoeffdingCentered μ _
    (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).stronglyMeasurable).measurable
  have hraws : ∀ x y : EuclideanSpace ℝ ι,logPhysicalPair (x,y)=logPhysicalPair (y,x) := by
    intro x y;unfold logPhysicalPair;rw [norm_sub_rev]
  have hs : ∀ x y,q (x,y)=q (y,x) := DGRHS.centeredKernel_symmetric μ _ hraws
  have hc : ∀ᵐ y ∂μ,∫ x,q (x,y) ∂μ=0 := DGRHS.integral_centeredKernel_left μ _ hpair
  have htwobeta : 2*β<attractiveBetaThreshold C := by
    have h := hsmall.trans_le (gaussianLogQuantitativeThreshold_half C M _)
    linarith
  have htwo := (attractiveBetaThreshold_lt_iff hC).mp htwobeta
  have hbase : β*(attractiveMomentConstant*C)<1 := by
    nlinarith [mul_nonneg attractiveMomentConstant_pos.le hC.le]
  have hhalf : (β/2)*(attractiveMomentConstant*C)<1 := by
    nlinarith [mul_nonneg attractiveMomentConstant_pos.le hC.le]
  let hh := joint_memLp μ q hm C hr 2 (by omega)
  obtain ⟨κ,eig,b,f,hf,hκ,hb,ht⟩ := exists_factorialCanonical_positive_partition_limit q hm C hr hs hc
  have hlim := ht β hβ.le hbase
  have hg := rowMoment_actual_operator_weak_margin q hm C β hr hβ.le hbase
  have hpdet (i : κ) : 0<1+(-β*eig i) := by
    have hp := DGRHS.Kernel.attractive_eigenvalue_factor_pos q hh eig b hb hβ.le hg i
    linarith
  have hdet := DGRHS.Kernel.regularizedDet_pos
    (DGRHS.Kernel.summable_scaled_eigenvalue_sq eig
      (DGRHS.Kernel.summable_integralOperator_eigenvalue_sq q hh eig b hb) (-β)) hpdet
  obtain ⟨B,hB,hCut⟩ := exists_gaussianLogPhysical_cutoff_feature_rate
    ρ M C β hd hM hC hβ hρ hpair hrows hsmall htail
  let R := gaussianLogInterpolationRowConstant C M (Fintype.card ι:ℝ)
  let A := (β/2*Real.sqrt 2)*
    (4*(Real.sqrt (M*Real.pi^((Fintype.card ι:ℝ)/2))/((Fintype.card ι:ℝ)/2)))*
    (2*Real.sqrt (2/(1-(β*(attractiveMomentConstant*R))^2)))
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨hh,κ,eig,b,hκ,hb,hdet,hlim,A,B,hA,hB,?_⟩
  intro η hη hη1 N hN
  have hi := (factorialCanonical_positive_uniform q hm C (β/2) hr hs hc
    (by positivity) hhalf N).1
  obtain ⟨hhη,κη,eigη,bη,hκη,hbη,hRate⟩ := hCut η hη hη1
  let Y := fun n=>∫ x : Fin n→EuclideanSpace ℝ ι,Real.exp
    (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
      (hoeffdingCentered μ (gaussianLogPhysicalInterpolation η 0)) x)
    ∂Measure.pi (fun _ : Fin n=>μ)
  let y := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>-β*eigη i)))⁻¹
  have hY : ∀ n,1≤n→|Y n-y|≤B*η^(-(2*β))/Real.sqrt (n:ℝ) :=
    fun n hn=>by simpa only [Y,y,μ,neg_mul] using (hRate n hn).2
  have hcomp : ∀ n,1≤n→|(∫ x : Fin n→EuclideanSpace ℝ ι,Real.exp
      (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
      ∂Measure.pi (fun _ : Fin n=>μ))-Y n|≤A*η^((Fintype.card ι:ℝ)/2) := by
    intro n hn
    have he := signedFeaturePhysical_truncation_comparison η β hη hη1 hd
      ρ M C hM hC hρ hpair hrows hβ.le hsmall n
    convert he using 1 <;> dsimp [A,Y,R,μ,q] <;> ring
  refine ⟨hi,?_⟩
  simpa only [neg_mul] using partition_error_of_sqrt_cutoff_rate _ Y _ y A B (2*β) _ η hlim hY hcomp N hN

end DGRHS.Attractive
#check @DGRHS.Attractive.exists_gaussianLogPhysical_canonical_cutoff_rate
#print axioms DGRHS.Attractive.exists_gaussianLogPhysical_canonical_cutoff_rate
