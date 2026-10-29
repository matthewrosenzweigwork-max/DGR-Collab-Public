import DGRHS.Gaussian.GaussianLogCutoffExponentLimit
import DGRHS.Gaussian.GaussianLogCutoffPotentialTail
import DGRHS.Gaussian.GaussianLogFullPositivity

/-! Supporting development. Uniform proper canonical moments for the SAME actual
logarithmic cutoff, under the original full potential exponential tail. No desired
uniform cutoff moment or interpolation conclusion is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

theorem gaussianLogCutoffCanonical_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-2*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ C : ℝ,∀ η : ℝ,0 < η → η ≤ 1 → ∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  let mfull := ∫ p,logPhysicalPair p ∂μ.prod μ
  let c := Real.exp (β*mfull/2)/2
  let Ctail := Real.exp ((2*β)*gaussianLogShortConstant M ι)*
    (∫ x,Real.exp (-(2*β)*logPhysicalPotential μ x) ∂μ)
  have hc : 0 ≤ c := by dsimp [c];positivity
  have htail' : Integrable (fun x => Real.exp (-(2*β)*logPhysicalPotential μ x)) μ := by
    convert htail using 1
    funext x
    congr 1
    ring
  obtain ⟨C,hC⟩ := gaussianLogCutoffSource_uniform_exponential (2*β) (by positivity) hd ρ M hM hρ hpair
  refine ⟨c*(C+Ctail),?_⟩
  intro η hη hη1 n hn
  let F := fun x => ∫ y,gaussianLogTruncatedPair η (x,y) ∂μ
  let m := ∫ p,gaussianLogTruncatedPair η p ∂μ.prod μ
  have hF : Integrable F μ := (integrable_gaussianLogTruncatedPair_source η hη hd ρ M hM hρ hpair).integral_prod_left
  obtain ⟨hTailη,bTailη⟩ := gaussianLogCutoff_potential_uniform_exponential_tail
    (2*β) (by positivity) hd ρ M hM hρ hpair htail' η hη hη1
  have hm : m ≤ mfull := gaussianLogCutoff_pairMean_le_full η hη hd ρ M hM hρ hpair
  have hcη : Real.exp (β*m/2)/2 ≤ c := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hb := mul_le_mul_of_nonneg_left hm hβ
    change β*m/2 ≤ β*mfull/2
    linarith
  let P := Measure.pi (fun _ : Fin n => μ)
  let X := gaussianLogCutoffSourceExponent μ β η n
  let A := fun ω : Fin n → EuclideanSpace ℝ ι => β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogTruncatedPair η)) ω
  let Y := fun ω : Fin n → EuclideanSpace ℝ ι => -β/(n : ℝ)*(∑ i,F (ω i))
  have htwice (ω : Fin n → EuclideanSpace ℝ ι) :
      2*X ω = gaussianLogCutoffSourceExponent μ (2*β) η n ω := by
    dsimp [X,gaussianLogCutoffSourceExponent]
    ring
  have hexpY (ω : Fin n → EuclideanSpace ℝ ι) :
      2*Y ω = -(2*β)/(n : ℝ)*(∑ i,F (ω i)) := by dsimp [Y];ring
  obtain ⟨hY,bY⟩ := log_potential_empirical_exp_integrable_bound μ F hF (2*β) hTailη n hn
  have hS := (hC η hη hη1 n hn).1
  have hmajor : Integrable (fun ω => c*(Real.exp (gaussianLogCutoffSourceExponent μ (2*β) η n ω)+
      Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i))))) P := (hS.add hY).const_mul c
  have hraw : StronglyMeasurable (gaussianLogTruncatedPair η : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ) :=
    stronglyMeasurable_logPhysicalPair.sub (stronglyMeasurable_gaussianLogShortPair η hη hd)
  have hAm : Measurable A := (measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _ hraw).measurable).const_mul β
  have hb (ω : Fin n → EuclideanSpace ℝ ι) : Real.exp (A ω) ≤
      c*(Real.exp (gaussianLogCutoffSourceExponent μ (2*β) η n ω)+
        Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i)))) := by
    have hAlgebra : A ω = X ω+Y ω+β*m/2 := by
      dsimp [A,X,Y,F,m,gaussianLogCutoffSourceExponent]
      ring
    rw [hAlgebra,Real.exp_add,Real.exp_add]
    have hYoung := mul_le_mul_of_nonneg_left (log_exp_product_le_half_sum_doubles (X ω) (Y ω))
      (Real.exp_pos (β*m/2)).le
    rw [htwice,hexpY] at hYoung
    have hstep : Real.exp (X ω)*Real.exp (Y ω)*Real.exp (β*m/2) ≤
        (Real.exp (β*m/2)/2)*(Real.exp (gaussianLogCutoffSourceExponent μ (2*β) η n ω)+
          Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i)))) := by nlinarith only [hYoung]
    exact hstep.trans (mul_le_mul_of_nonneg_right hcη (by positivity))
  have hI : Integrable (fun ω => Real.exp (A ω)) P := by
    apply hmajor.mono' (Real.continuous_exp.comp_aestronglyMeasurable hAm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (Real.exp_pos _).le];exact hb ω)
  refine ⟨hI,?_⟩
  calc
    _ ≤ ∫ ω,c*(Real.exp (gaussianLogCutoffSourceExponent μ (2*β) η n ω)+
        Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i)))) ∂P := integral_mono hI hmajor hb
    _ = c*((∫ ω,Real.exp (gaussianLogCutoffSourceExponent μ (2*β) η n ω) ∂P)+
        ∫ ω,Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i))) ∂P) := by
      rw [integral_const_mul,integral_add hS hY]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hC η hη hη1 n hn).2 (bY.trans bTailη)) hc

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogCutoffCanonical_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianLogCutoffCanonical_uniform_exponential
