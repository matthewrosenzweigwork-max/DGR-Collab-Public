import DGRHS.Gaussian.SourceRepulsiveLogRateCutoff
import DGRHS.Gaussian.SourceRepulsiveLogRateData

/-! Actual full canonical logarithmic positive-power rate. Genuine finite-N
comparisons and both constructed partition limits yield the determinant
truncation error; no determinant continuity or spectral matching premise. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.SourceRepulsiveLogRate
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

lemma cutoff_canonical_data (η : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let q := hoeffdingCentered μ (gaussianLogTruncatedPair η)
    Measurable q ∧ (∀ᵐ p ∂μ.prod μ,q p.swap=q p) ∧ (∀ᵐ x ∂μ,(∫ y,q (x,y) ∂μ)=0) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hr : StronglyMeasurable (gaussianLogTruncatedPair (ι:=ι) η) :=
    stronglyMeasurable_logPhysicalPair.sub (stronglyMeasurable_gaussianLogShortPair η hη hd)
  refine ⟨(stronglyMeasurable_hoeffdingCentered μ _ hr).measurable,?_,?_⟩
  · apply Eventually.of_forall
    intro p
    exact DGRHS.centeredKernel_symmetric μ (fun a b=>gaussianLogTruncatedPair η (a,b))
      (fun a b=>by simp only [gaussianLogTruncatedPair,logPhysicalPair,gaussianLogShortPair,
        gaussianLogShortRange,norm_sub_rev]) p.2 p.1
  · exact DGRHS.integral_centeredKernel_right μ (fun a b=>gaussianLogTruncatedPair η (a,b))
      (integrable_gaussianLogTruncatedPair_source η hη hd ρ M hM hρ hpair)

lemma full_cutoff_residual (η : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let q := hoeffdingCentered μ (gaussianLogTruncatedPair η)
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    let hq := memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair
    ‖(hh.sub hq).toLp (fun p=>h p-q p)‖≤
      (4*(Real.sqrt (M*Real.pi^((Fintype.card ι:ℝ)/2))/((Fintype.card ι:ℝ)/2)))*η^((Fintype.card ι:ℝ)/2) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  let hq := memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair
  have hdif := ae_logPhysical_centered_difference η hη hd ρ M hM hρ hpair
  change ‖(hh.sub hq).toLp (_ - _)‖≤_
  rw [(hh.sub hq).toLp_congr (memLp_gaussianLogCenteredShortPair η hη hd ρ M hM hρ) hdif]
  simpa only [mul_assoc] using norm_gaussianLogCenteredShortPair_le η hη hd ρ M hM hρ

 theorem exists_canonical_partition_rate (β : ℝ) (hβ : 0≤β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i)=eig i • e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i=>β*eig i) ∧
      HasProd (fun i=>(1+β*eig i)*Real.exp (-(β*eig i))) (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)) ∧
      Tendsto (canonicalPartition μ β h) atTop (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹)) ∧
      ∃ c C : ℝ,0<c ∧ c≤1/2 ∧ 0≤C ∧ ∀ N : ℕ,1≤N →
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
          (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
        |canonicalPartition μ β h N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹|≤
          C*(Real.exp 1+(N:ℝ))^(-c) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let h := hoeffdingCentered μ logPhysicalPair
  let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  obtain ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,hT⟩ := exists_full_canonical_limit β hβ hd ρ M hM hρ hpair htail
  refine ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,hT,?_⟩
  by_cases hzero : β=0
  · subst β
    refine ⟨1/2,0,by norm_num,le_rfl,le_rfl,?_⟩
    intro N hN
    constructor
    · simpa only [neg_zero,zero_div,zero_mul,Real.exp_zero] using
        (integrable_const (1:ℝ) : Integrable (fun _ : Fin N→EuclideanSpace ℝ ι=>(1:ℝ)) (Measure.pi (fun _ : Fin N=>μ)))
    · simp [canonicalPartition,DGRHS.Kernel.regularizedDet]
  have hβp : 0<β := lt_of_le_of_ne hβ (Ne.symm hzero)
  obtain ⟨L,hL,hCut⟩ := exists_cutoff_partition_rate β hβp hd ρ M hM hρ hpair htail
  obtain ⟨MH,MK,hDouble,bDouble,kDouble⟩ := exists_double_moments β hβ hd ρ M hM hρ hpair htail
  let r := (Fintype.card ι:ℝ)/2
  have hr : 0<r := by dsimp [r];positivity
  let A := 4*(Real.sqrt (M*Real.pi^((Fintype.card ι:ℝ)/2))/((Fintype.card ι:ℝ)/2))
  let B := (|β|/2*Real.sqrt 2)*(Real.sqrt MH+Real.sqrt MK)*A
  have hB : 0≤B := by dsimp [B,A];positivity
  let c := min (sourceLogRatePower L*r) (1/2:ℝ)
  have hc0 : 0<c := lt_min (mul_pos (sourceLogRatePower_bounds L hL).1 hr) (by norm_num)
  have hc1 : c≤1/2 := min_le_right _ _
  let C := (2*B+L*Real.exp L)*(Real.exp 1+1)^c
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨c,C,hc0,hc1,hC,?_⟩
  intro N hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  let η := sourceLogRateCutoff L (N:ℝ)
  obtain ⟨hη,hη1,_,_,_⟩ := sourceLogRateCutoff_identities L (N:ℝ) r hL hn
  let q := hoeffdingCentered μ (gaussianLogTruncatedPair η)
  let hq := memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair
  obtain ⟨σ,a,b,hσ,hb,hDetq,hProdq,hY,hRateq⟩ := hCut η hη hη1
  obtain ⟨hqm,hqs,hqc⟩ := cutoff_canonical_data η hη hd ρ M hM hρ hpair
  have hhm : Measurable h := (stronglyMeasurable_logPhysicalCenteredPair μ).measurable
  have hComp := canonicalPartition_comparison μ β h q hhm hqm hh hq hs hqs hc hqc
    (A*η^r) MH MK (full_cutoff_residual η hη hd ρ M hM hρ hpair)
    (fun n _=>hDouble n) (fun n hn=>(kDouble η hη hη1 n hn).1)
    (fun n _=>bDouble n) (fun n hn=>(kDouble η hη hη1 n hn).2)
  have hComp' : ∀ n,1≤n → |canonicalPartition μ β h n-canonicalPartition μ β q n|≤B*η^r := by
    intro n hn
    convert hComp n hn using 1 <;> dsimp [B] <;> ring
  have hAssemble := partition_error_assembly (canonicalPartition μ β h) (canonicalPartition μ β q)
    ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹)
    ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*a i)))⁻¹) (B*η^r) hT hY hComp' N hN
  have hOpt := (sourceLogRateCutoff_bound B L r (N:ℝ) hB hL hr hn).2
  have hShift : (N:ℝ)^(-c)≤(Real.exp 1+1)^c*(Real.exp 1+(N:ℝ))^(-c) :=
    inverse_rpow_comparison (Real.exp 1+(N:ℝ)) (N:ℝ) (Real.exp 1+1) c
      (by positivity) (by positivity) (by positivity) hc0.le
      (by nlinarith [mul_nonneg (Real.exp_pos (1:ℝ)).le (sub_nonneg.mpr hn)])
  have hu := DGRHS.CLT.memLp_normalizedOffDiagonalSum (ι:=Fin N) h hh
  have hi : Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
      (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N=>μ)) := by
    apply (DGRHS.CLT.memLp_exp_of_integrable_double _ (hu.aemeasurable.const_mul _) ?_).integrable (by norm_num)
    convert hDouble N using 1
    funext x
    congr 1
    ring
  refine ⟨hi,?_⟩
  calc
    _ ≤ 2*(B*η^r)+|canonicalPartition μ β q N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*a i)))⁻¹| := hAssemble
    _ ≤ 2*B*η^r+L*Real.exp (L*(1+Real.log (1/η)))/(N:ℝ) := by
      convert add_le_add le_rfl (hRateq N hN).2 using 1 <;> ring
    _ ≤ (2*B+L*Real.exp L)*(N:ℝ)^(-c) := hOpt
    _ ≤ C*(Real.exp 1+(N:ℝ))^(-c) := by
      simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hShift (show 0≤2*B+L*Real.exp L by positivity)

end DGRHS.SourceRepulsiveLogRate
#check @DGRHS.SourceRepulsiveLogRate.cutoff_canonical_data
#print axioms DGRHS.SourceRepulsiveLogRate.cutoff_canonical_data
#check @DGRHS.SourceRepulsiveLogRate.full_cutoff_residual
#print axioms DGRHS.SourceRepulsiveLogRate.full_cutoff_residual
#check @DGRHS.SourceRepulsiveLogRate.exists_canonical_partition_rate
#print axioms DGRHS.SourceRepulsiveLogRate.exists_canonical_partition_rate
