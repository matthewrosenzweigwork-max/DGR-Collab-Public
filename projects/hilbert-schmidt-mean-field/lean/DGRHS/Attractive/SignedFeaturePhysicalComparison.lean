/- Dependency-compatible adaptation of the exact root finite-particle proof.
Root CP215706 and B sealed225039 export the same short-rate name in distinct
modules; this new endpoint imports the B copy used by the constructed feature.
Neither accepted reuse body is changed. -/
/- Concrete attractive-sign canonical finite-particle cutoff comparison.
The endpoint exponential-difference/CS argument replaces the printed derivative
in interpolation, with actual source row moments and genuine cutoff L2 rate. -/
import DGRHS.Attractive.LogPhysicalInterpolationBridge
import DGRHS.Attractive.FactorialCanonicalComparison
import DGRHS.Gaussian.GaussianLogOperatorDifference
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem signedFeaturePhysical_truncation_comparison (η β : ℝ)
    (hη : 0<η) (hη1 : η≤1) (hd : 0<(Fintype.card ι:ℝ))
    (ρ : EuclideanSpace ℝ ι→ℝ) (M C : ℝ) (hM : 0≤M) (hC : 0<C)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (hrows : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal (|DGRHS.centeredKernel (gaussianRieszDensityMeasure ρ)
        attractiveLogInteraction x y|^p) ∂gaussianRieszDensityMeasure ρ)≤
        ENNReal.ofReal (C^p*(p.factorial:ℝ)))
    (hβ : 0≤β) (hsmall : β<gaussianLogQuantitativeThreshold C M (Fintype.card ι:ℝ))
    (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let q := hoeffdingCentered μ logPhysicalPair
    let qη := hoeffdingCentered μ (gaussianLogPhysicalInterpolation η 0)
    let R := gaussianLogInterpolationRowConstant C M (Fintype.card ι:ℝ)
    |(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
        ∂Measure.pi (fun _ : Fin N=>μ))-
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum qη x)
        ∂Measure.pi (fun _ : Fin N=>μ))| ≤
      (β/2*Real.sqrt 2)*
        (4*(Real.sqrt (M*Real.pi^((Fintype.card ι:ℝ)/2))/((Fintype.card ι:ℝ)/2))*
          η^((Fintype.card ι:ℝ)/2))*
        (2*Real.sqrt (2/(1-(β*(attractiveMomentConstant*R))^2))) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let q := hoeffdingCentered μ logPhysicalPair
  let qη := hoeffdingCentered μ (gaussianLogPhysicalInterpolation η 0)
  let R := gaussianLogInterpolationRowConstant C M (Fintype.card ι:ℝ)
  have he := hoeffdingCentered_gaussianLogInterpolation_eq η 0 hη hd ρ M hM hρ hpair
  have hcraw : 0≤gaussianLogShortFactorialConstant M (Fintype.card ι:ℝ) := by
    unfold gaussianLogShortFactorialConstant
    positivity
  have hCR : C≤R := by dsimp [R,gaussianLogInterpolationRowConstant];linarith
  have hf0 := logPhysical_factorial_rows_of_attractive μ C hC.le hrows
  have hf := hf0.mono hCR
  have ht0 := gaussianLog_interpolated_factorial_rows η 0 hη hη1 (by norm_num)
    (by norm_num) hd ρ M C hM hρ hf0
  have ht : RowFactorialMoments μ qη R := by
    dsimp only [qη,μ,R]
    rw [he]
    exact ht0
  have hm : Measurable q := (stronglyMeasurable_hoeffdingCentered μ _
    (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).stronglyMeasurable).measurable
  have hmt : Measurable qη := by
    apply (stronglyMeasurable_hoeffdingCentered μ _ _).measurable
    exact (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).stronglyMeasurable.sub
      ((stronglyMeasurable_gaussianLogShortPair η hη hd).const_mul (1-0))
  have hfs : ∀ x y : EuclideanSpace ℝ ι,logPhysicalPair (x,y)=logPhysicalPair (y,x) := by
    intro x y
    unfold logPhysicalPair
    rw [norm_sub_rev]
  have hts : ∀ x y : EuclideanSpace ℝ ι,
      gaussianLogPhysicalInterpolation η 0 (x,y)=gaussianLogPhysicalInterpolation η 0 (y,x) := by
    intro x y
    unfold gaussianLogPhysicalInterpolation
    rw [hfs,gaussianLogShortPair_symmetric η x y]
  have hqs : ∀ x y,q (x,y)=q (y,x) := DGRHS.centeredKernel_symmetric μ _ hfs
  have hqts : ∀ x y,qη (x,y)=qη (y,x) := DGRHS.centeredKernel_symmetric μ _ hts
  have hir : Integrable (gaussianLogPhysicalInterpolation η 0) (μ.prod μ) := by
    exact hpair.sub (((memLp_gaussianLogShortPair η hη hd ρ M hM hρ).integrable
      (by norm_num)).const_mul (1-0))
  have hfc : ∀ᵐ y ∂μ,∫ x,q (x,y) ∂μ=0 := DGRHS.integral_centeredKernel_left μ _ hpair
  have htc : ∀ᵐ y ∂μ,∫ x,qη (x,y) ∂μ=0 := DGRHS.integral_centeredKernel_left μ _ hir
  have hrsmall := gaussianLogQuantitativeThreshold_row_small C M _ β hC hM hd hβ hsmall
  let h2 := joint_memLp μ q hm R hf 2 (by omega)
  let t2 := joint_memLp μ qη hmt R ht 2 (by omega)
  let s2 := memLp_hoeffdingCentered μ _ (stronglyMeasurable_gaussianLogShortPair η hη hd)
    (memLp_gaussianLogShortPair η hη hd ρ M hM hρ)
  have hdiff : (fun z=>q z-qη z)=ᵐ[μ.prod μ] hoeffdingCentered μ (gaussianLogShortPair η) := by
    apply Filter.Eventually.of_forall
    intro z
    have hz := congrFun he z
    dsimp [gaussianLogAlgebraicInterpolation] at hz
    dsimp [q,qη]
    rw [hz]
    ring
  have hn := norm_gaussianLogCenteredShortPair_le η hη hd ρ M hM hρ
  have hn' : ‖(h2.sub t2).toLp (fun z=>q z-qη z)‖ ≤
      4*(Real.sqrt (M*Real.pi^((Fintype.card ι:ℝ)/2))/((Fintype.card ι:ℝ)/2))*
        η^((Fintype.card ι:ℝ)/2) := by
    have heq : (h2.sub t2).toLp (fun z=>q z-qη z) =
        s2.toLp (hoeffdingCentered μ (gaussianLogShortPair η)) :=
      (h2.sub t2).toLp_congr s2 hdiff
    apply (congrArg norm heq).le.trans
    simpa only [mul_assoc] using hn
  have hb := factorialCanonical_positive_comparison q qη hm hmt R R β hf ht hqs hqts
    hfc htc hβ hrsmall hrsmall N
  apply hb.trans
  have hbnon : 0≤Real.sqrt (2/(1-(β*(attractiveMomentConstant*R))^2)) := Real.sqrt_nonneg _
  have hsimp : Real.sqrt (2/(1-(β*(attractiveMomentConstant*R))^2))+
      Real.sqrt (2/(1-(β*(attractiveMomentConstant*R))^2))=
      2*Real.sqrt (2/(1-(β*(attractiveMomentConstant*R))^2)) := by ring
  rw [hsimp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn' (by positivity)) (by positivity)
end DGRHS.Attractive
#check @DGRHS.Attractive.signedFeaturePhysical_truncation_comparison
#print axioms DGRHS.Attractive.signedFeaturePhysical_truncation_comparison
