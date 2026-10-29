/- Proper source sign and representative bridges. Pointwise centering
linearity uses actual every-fixed-row properness, never product-AE restriction.
This closes the source attractive row -> repulsive interpolation input. -/
import DGRHS.Attractive.LogShortInterpolation
import DGRHS.Attractive.SourceLogUniform
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma logPhysicalCentered_eq_neg_attractive (μ : Measure (EuclideanSpace ℝ ι)) :
    hoeffdingCentered μ logPhysicalPair =
      -(fun z=>DGRHS.centeredKernel μ attractiveLogInteraction z.1 z.2) := by
  funext z
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
    attractiveLogInteraction logPhysicalPair
  simp only [Pi.neg_apply,integral_neg]
  ring

theorem logPhysical_factorial_rows_of_attractive (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0≤C)
    (hb : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal (|DGRHS.centeredKernel μ attractiveLogInteraction x y|^p) ∂μ)≤
        ENNReal.ofReal (C^p*(p.factorial:ℝ))) :
    RowFactorialMoments μ (hoeffdingCentered μ logPhysicalPair) C := by
  have hm : Measurable (fun z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι=>
      DGRHS.centeredKernel μ attractiveLogInteraction z.1 z.2) := by
    have hw : StronglyMeasurable (Function.uncurry (attractiveLogInteraction
        (E:=EuclideanSpace ℝ ι))) := by
      have hNeg : Function.uncurry (attractiveLogInteraction
          (E:=EuclideanSpace ℝ ι)) = -logPhysicalPair := by
        funext z
        simp only [Function.uncurry,attractiveLogInteraction,logPhysicalPair,Pi.neg_apply,neg_neg]
      rw [hNeg]
      exact (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).neg.stronglyMeasurable
    exact (stronglyMeasurable_hoeffdingCentered μ _ hw).measurable
  rw [logPhysicalCentered_eq_neg_attractive]
  exact (rowFactorialMoments_of_lintegral μ _ hm C hC hb).neg

def gaussianLogPhysicalInterpolation (η t : ℝ)
    (z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) : ℝ :=
  logPhysicalPair z-(1-t)*gaussianLogShortPair η z

theorem hoeffdingCentered_gaussianLogInterpolation_eq (η t : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogPhysicalInterpolation η t)=
      gaussianLogAlgebraicInterpolation (gaussianRieszDensityMeasure ρ) η t := by
  let μ := gaussianRieszDensityMeasure ρ
  let q := (Fintype.card ι:ℝ)/4
  have hq : 0<q := by dsimp [q];positivity
  have hdim : 0<(Fintype.card ι:ℝ)/2-q := by dsimp [q];linarith
  have hfull (x : EuclideanSpace ℝ ι) : Integrable (fun y=>logPhysicalPair (x,y)) μ :=
    (logPhysicalPotential_proper_bounds q hq hdim ρ M hM hρ hpair x).1
  have hshort (x : EuclideanSpace ℝ ι) : Integrable (fun y=>gaussianLogShortPair η (x,y)) μ :=
    integrable_gaussianLogShortRange_convolution η hη hd ρ M hρ x
  have hfs : ∀ x y : EuclideanSpace ℝ ι,logPhysicalPair (x,y)=logPhysicalPair (y,x) := by
    intro x y
    unfold logPhysicalPair
    rw [norm_sub_rev]
  have hfullL (y : EuclideanSpace ℝ ι) : Integrable (fun x=>logPhysicalPair (x,y)) μ :=
    (hfull y).congr (Filter.Eventually.of_forall fun x=>hfs y x)
  have hshortL (y : EuclideanSpace ℝ ι) : Integrable (fun x=>gaussianLogShortPair η (x,y)) μ :=
    (hshort y).congr (Filter.Eventually.of_forall fun x=>gaussianLogShortPair_symmetric η y x)
  have hiShort : Integrable (gaussianLogShortPair η) (μ.prod μ) :=
    (memLp_gaussianLogShortPair η hη hd ρ M hM hρ).integrable (by norm_num)
  funext z
  unfold gaussianLogPhysicalInterpolation gaussianLogAlgebraicInterpolation
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  rw [integral_sub (hfull z.1) ((hshort z.1).const_mul (1-t)),
    integral_sub (hfullL z.2) ((hshortL z.2).const_mul (1-t)),
    integral_sub hpair (hiShort.const_mul (1-t))]
  simp only [integral_const_mul]
  ring

/- The original every-row assumption yields every-cutoff, every-interpolation
row moments and the actual doubled operator margin at one explicit threshold. -/
theorem gaussianLogPhysical_interpolation_rows_margin (η t β : ℝ)
    (hη : 0<η) (hη1 : η≤1) (ht : 0≤t) (ht1 : t≤1)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M C : ℝ) (hM : 0≤M) (hC : 0<C)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (hb : ∀ p : ℕ,1≤p → ∀ y,
      (∫⁻ x,ENNReal.ofReal (|DGRHS.centeredKernel (gaussianRieszDensityMeasure ρ)
        attractiveLogInteraction x y|^p) ∂gaussianRieszDensityMeasure ρ)≤
        ENNReal.ofReal (C^p*(p.factorial:ℝ)))
    (hβ : 0≤β) (hsmall : β<gaussianLogQuantitativeThreshold C M (Fintype.card ι:ℝ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let q := hoeffdingCentered μ (gaussianLogPhysicalInterpolation η t)
    let Cq := gaussianLogInterpolationRowConstant C M (Fintype.card ι:ℝ)
    ∃ (hq : RowFactorialMoments μ q Cq) (hm : Measurable q),
      2*β*‖DGRHS.Kernel.integralOperator q (joint_memLp μ q hm Cq hq 2 (by omega))‖<1 := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  have hf := logPhysical_factorial_rows_of_attractive μ C hC.le hb
  have hr := gaussianLog_interpolated_factorial_rows η t hη hη1 ht ht1 hd ρ M C hM hρ hf
  have he := hoeffdingCentered_gaussianLogInterpolation_eq η t hη hd ρ M hM hρ hpair
  have hm : Measurable (gaussianLogAlgebraicInterpolation μ η t) := by
    exact (stronglyMeasurable_hoeffdingCentered μ _
      (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).stronglyMeasurable).measurable.sub
      (((stronglyMeasurable_hoeffdingCentered μ _
        (stronglyMeasurable_gaussianLogShortPair η hη hd)).measurable).const_mul (1-t))
  rw [he]
  refine ⟨hr,hm,?_⟩
  exact rowMoment_actual_operator_doubled_margin _ hm _ β hr hβ
    (gaussianLogQuantitativeThreshold_row_small C M _ β hC hM hd hβ hsmall)
end DGRHS.Attractive
#check @DGRHS.Attractive.hoeffdingCentered_gaussianLogInterpolation_eq
#print axioms DGRHS.Attractive.logPhysicalCentered_eq_neg_attractive
#print axioms DGRHS.Attractive.logPhysical_factorial_rows_of_attractive
#print axioms DGRHS.Attractive.hoeffdingCentered_gaussianLogInterpolation_eq
#check @DGRHS.Attractive.gaussianLogPhysical_interpolation_rows_margin
#print axioms DGRHS.Attractive.gaussianLogPhysical_interpolation_rows_margin
