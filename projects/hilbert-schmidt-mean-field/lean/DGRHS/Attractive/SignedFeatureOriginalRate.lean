import DGRHS.Attractive.SignedFeaturePhysicalCanonicalRate
import DGRHS.Attractive.SourceLogAffineComparison

/- Literal original attractive-log quantitative partition theorem. The original
singular pair-L1, factorial rows, bounded density and exp(4 beta F_att) are the
only data. SAME source operator, correct determinant sign, properness and
cutoff/one-body bounds are derived before the conservative checked optimizer. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

lemma source_integralOperator_neg {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (h : S×S→ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    DGRHS.Kernel.integralOperator (-h) hh.neg = -DGRHS.Kernel.integralOperator h hh := by
  unfold DGRHS.Kernel.integralOperator
  rw [MemLp.toLp_neg,map_neg]

theorem exists_attractiveLog_original_quantitative_rate
    (ρ : EuclideanSpace ℝ ι→ℝ) (M C β : ℝ)
    (hd : 0<(Fintype.card ι:ℝ)) (hM : 0≤M) (hC : 0<C) (hβ : 0<β)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : (∫⁻ z,singularAbsLog z ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))<∞)
    (hrows : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal (|DGRHS.centeredKernel (gaussianRieszDensityMeasure ρ)
        attractiveLogInteraction x y|^p) ∂gaussianRieszDensityMeasure ρ)≤
        ENNReal.ofReal (C^p*(p.factorial:ℝ)))
    (hsmall : β<gaussianLogQuantitativeThreshold C M (Fintype.card ι:ℝ))
    (htail : Integrable (fun x=>Real.exp
      (4*β*DGRHS.potential (gaussianRieszDensityMeasure ρ) attractiveLogInteraction x))
      (gaussianRieszDensityMeasure ρ)) :
    let h := fun (z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι)=>
      DGRHS.centeredKernel (gaussianRieszDensityMeasure ρ) attractiveLogInteraction z.1 z.2
    let I := DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) attractiveLogInteraction
    ∃ (hh : MemLp h 2 ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
      (κ : Type u) (eig : κ→ℝ) (b : HilbertBasis κ ℝ (Lp ℝ 2 (gaussianRieszDensityMeasure ρ))),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperator h hh (b i)=eig i • b i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i=>β*eig i) ∧
      ∃ K c : ℝ,0≤K ∧ 0<c ∧ c≤1/4 ∧ ∀ N : ℕ,1≤N →
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h
            (DGRHS.potential (gaussianRieszDensityMeasure ρ) attractiveLogInteraction) I N x))
          (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
        attractiveLogPartition (gaussianRieszDensityMeasure ρ) β N<∞ ∧
        |(attractiveLogPartition (gaussianRieszDensityMeasure ρ) β N).toReal-
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹|≤
          K*(Real.exp 1+(N:ℝ))^(-c) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let h := fun (z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι)=>DGRHS.centeredKernel μ attractiveLogInteraction z.1 z.2
  let I := DGRHS.interactionEnergy μ attractiveLogInteraction
  let q := hoeffdingCentered μ logPhysicalPair
  have hp := ((singularAbsLog_finite_iff μ).mp hpair).1
  have hF (x : EuclideanSpace ℝ ι) : DGRHS.potential μ attractiveLogInteraction x = -logPhysicalPotential μ x := by
    simp only [DGRHS.potential,attractiveLogInteraction,logPhysicalPotential,logPhysicalPair,integral_neg,neg_neg]
  have hTail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential μ x)) μ := by
    convert htail using 1
    funext x
    rw [hF]
    congr 1
    ring
  obtain ⟨hhq,κ,eigq,b,hκ,hbq,hdetq,hlim,A,B,hA,hB,hRate⟩ :=
    exists_gaussianLogPhysical_canonical_cutoff_rate ρ M C β hd hM hC hβ hρ hp hrows hsmall hTail
  have hq : q = -h := logPhysicalCentered_eq_neg_attractive μ
  have hneg : -q = h := by rw [hq];simp
  have hh : MemLp h 2 (μ.prod μ) := by
    have hn : MemLp (-q) 2 (μ.prod μ) := hhq.neg
    rw [hneg] at hn
    exact hn
  have hop : DGRHS.Kernel.integralOperator h hh = -DGRHS.Kernel.integralOperator q hhq := by
    simpa only [hneg] using source_integralOperator_neg μ q hhq
  let eig := fun i=>-eigq i
  have hb : ∀ i,DGRHS.Kernel.integralOperator h hh (b i)=eig i • b i := by
    intro i
    rw [hop]
    have hbi : DGRHS.Kernel.integralOperator q hhq (b i)=eigq i • b i := hbq i
    change -(DGRHS.Kernel.integralOperator q hhq (b i))=(-eigq i) • b i
    rw [hbi]
    simp only [neg_smul]
  have heig : (fun i=>β*eig i)=(fun i=>-β*eigq i) := by funext i;dsimp [eig];ring
  have hdet : 0<DGRHS.Kernel.regularizedDet (fun i=>β*eig i) := by rw [heig];exact hdetq
  have htwobeta : 2*β<attractiveBetaThreshold C := by
    have he := hsmall.trans_le (gaussianLogQuantitativeThreshold_half C M _)
    linarith
  have htwo := (attractiveBetaThreshold_lt_iff hC).mp htwobeta
  obtain ⟨D,hD,hAffine⟩ := attractiveLog_source_affine_comparison
    ρ M C β hd hM hC hβ hρ hpair hrows htwo htail
  let W := Real.exp (β*I)
  let Ce := max (W*B) (2*β)+1
  let r := (Fintype.card ι:ℝ)/2
  let c := attractiveLogRatePower Ce r
  let K := (2*(W*A)+Ce*Real.exp Ce+D)*(Real.exp 1+1)^c
  have hW : 0<W := Real.exp_pos _
  have hCe : 0<Ce := by dsimp [Ce];have he := le_max_right (W*B) (2*β);linarith
  have hBce : W*B≤Ce := by dsimp [Ce];have he := le_max_left (W*B) (2*β);linarith
  have hqce : 2*β≤Ce := by dsimp [Ce];have he := le_max_right (W*B) (2*β);linarith
  have hr : 0<r := by dsimp [r];positivity
  obtain ⟨hc,hcquarter⟩ := attractiveLogRatePower_bounds Ce r hCe hr
  have hK : 0≤K := by dsimp [K];positivity
  have hstat (N : ℕ) (x : Fin N→EuclideanSpace ℝ ι) :
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x =
        -DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
    rw [hq]
    unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum DGRHS.CanonicalVariance.offDiagonalSum
    simp only [Pi.neg_apply,Finset.sum_neg_distrib,mul_neg]
  let Z := fun N=>∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
    (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
    ∂Measure.pi (fun _ : Fin N=>μ)
  let z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>-β*eigq i)))⁻¹
  have hZeq (N : ℕ) : DGRHS.Concentration.canonicalPartition μ β h N=Z N := by
    unfold DGRHS.Concentration.canonicalPartition Z
    congr 1
    funext x
    rw [hstat]
    congr 1
    ring
  refine ⟨hh,κ,eig,b,hκ,hb,hdet,K,c,hK,hc,hcquarter,?_⟩
  intro N hN
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  let η := attractiveLogRateCutoff Ce (N:ℝ)
  obtain ⟨hη,hη1,hOpt⟩ := attractiveLogRateCutoff_bound (W*A) Ce D r (N:ℝ)
    (mul_nonneg hW.le hA) hCe hD hr hNr
  obtain ⟨hProper,hAff⟩ := hAffine N hN
  have hCan := (hRate η hη hη1 N hN).2
  have hmajor := power_cutoff_le_exponential_envelope (W*B) (2*β) Ce η
    (mul_nonneg hW.le hB) hBce hqce hη hη1
  let S := ∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
    (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h
      (DGRHS.potential μ attractiveLogInteraction) I N x)
    ∂Measure.pi (fun _ : Fin N=>μ)
  have hErr : |S-W*z|≤K*(Real.exp 1+(N:ℝ))^(-c) := by
    rw [hZeq] at hAff
    have hDiff : |W*Z N-W*z|=W*|Z N-z| := by rw [←mul_sub,abs_mul,abs_of_pos hW]
    have hCan' : |Z N-z|≤2*A*η^r+B*η^(-2*β)/Real.sqrt (N:ℝ) := hCan
    calc
      _ ≤ |S-W*Z N|+|W*Z N-W*z| := abs_sub_le _ _ _
      _ ≤ D/Real.sqrt (N:ℝ)+W*(2*A*η^r+B*η^(-2*β)/Real.sqrt (N:ℝ)) := by
        rw [hDiff]
        exact add_le_add hAff (mul_le_mul_of_nonneg_left hCan' hW.le)
      _ = 2*(W*A)*η^r+(W*B)*η^(-(2*β))/Real.sqrt (N:ℝ)+D/Real.sqrt (N:ℝ) := by rw [neg_mul];ring
      _ ≤ 2*(W*A)*η^r+Ce*Real.exp (Ce*(1+Real.log (1/η)))/Real.sqrt (N:ℝ)+D/Real.sqrt (N:ℝ) := by
        exact add_le_add (add_le_add le_rfl
          (div_le_div_of_nonneg_right hmajor (Real.sqrt_nonneg _))) le_rfl
      _ ≤ _ := hOpt
  have he : attractiveLogPartition μ β N=ENNReal.ofReal S := by
    unfold attractiveLogPartition
    rw [lintegral_congr_ae (attractiveLogSingularWeight_ae μ hpair β N)]
    exact (ofReal_integral_eq_lintegral_ofReal hProper
      (Filter.Eventually.of_forall fun x=>(Real.exp_pos _).le)).symm
  have hS : 0≤S := integral_nonneg (fun _=>(Real.exp_pos _).le)
  refine ⟨hProper,by rw [he];exact ENNReal.ofReal_lt_top,?_⟩
  rw [he,ENNReal.toReal_ofReal hS,heig]
  exact hErr

end DGRHS.Attractive
#check @DGRHS.Attractive.source_integralOperator_neg
#check @DGRHS.Attractive.exists_attractiveLog_original_quantitative_rate
#print axioms DGRHS.Attractive.source_integralOperator_neg
#print axioms DGRHS.Attractive.exists_attractiveLog_original_quantitative_rate
