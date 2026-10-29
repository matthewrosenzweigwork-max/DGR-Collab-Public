import DGRHS.Attractive.SignedFeatureSourceRate
import DGRHS.Gaussian.GaussianLogInfiniteFeatureGram

/- Actual physical diagonal moment from the SAME constructed feature.
B feature bodies are imported unchanged; original tail properness supplies
the exponential moment. No favorable field/diagonal premise is assumed. -/
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S] {μ : Measure S}
  [IsProbabilityMeasure μ]

lemma feature_diagonal_exponential_of_source_potential
    (D F : S → ℝ) (hD : AEStronglyMeasurable D μ)
    (β A η : ℝ) (hβ : 0≤β) (hη : 0<η)
    (hbound : ∀ᵐ x ∂μ,D x≤A-Real.log η-2*F x)
    (htail : Integrable (fun x => Real.exp (-4*β*F x)) μ) :
    Integrable (fun x => Real.exp (2*β*D x)) μ ∧
    (∫ x,Real.exp (2*β*D x) ∂μ) ≤
      Real.exp (2*β*A)*η^(-2*β)*(∫ x,Real.exp (-4*β*F x) ∂μ) := by
  let C := Real.exp (2*β*A)*η^(-2*β)
  have hC : 0≤C := by dsimp [C];positivity
  have he (x : S) : Real.exp (2*β*(A-Real.log η-2*F x)) =
      C*Real.exp (-4*β*F x) := by
    dsimp [C]
    rw [Real.rpow_def_of_pos hη,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hb : ∀ᵐ x ∂μ,Real.exp (2*β*D x)≤C*Real.exp (-4*β*F x) := by
    filter_upwards [hbound] with x hx
    rw [←he]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (by positivity))
  have hi := htail.const_mul C
  have hiD : Integrable (fun x => Real.exp (2*β*D x)) μ :=
    hi.mono' (Real.continuous_exp.comp_aestronglyMeasurable (hD.const_mul (2*β))) (by
      filter_upwards [hb] with x hx
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx)
  refine ⟨hiD,?_⟩
  calc
    _ ≤ ∫ x,C*Real.exp (-4*β*F x) ∂μ := integral_mono_ae hiD hi hb
    _ = _ := by rw [integral_const_mul]

/- Scalar uniform HS/margin comparison. Uses true physical bounds, not a
desired moment, determinant or rate premise. -/
lemma feature_HS_margin_exponential_uniform
    (β s v H O : ℝ) (hβ : 0≤β) (hs : 0≤s) (hv : v≤O)
    (hH : s≤H) (hmargin : 2*β*O<1) :
    Real.exp ((2*β)^2*s/(2*(1-2*β*v))) ≤
      Real.exp ((2*β)^2*H/(2*(1-2*β*O))) := by
  apply Real.exp_le_exp.mpr
  have hdO : 0<2*(1-2*β*O) := by linarith
  have hden : 2*(1-2*β*O)≤2*(1-2*β*v) := by
    have h := mul_le_mul_of_nonneg_left hv (show 0≤2*β by positivity)
    linarith
  have hdv : 0<2*(1-2*β*v) := lt_of_lt_of_le hdO hden
  have hHnon : 0≤H := hs.trans hH
  calc
    _ ≤ (2*β)^2*H/(2*(1-2*β*v)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH (sq_nonneg _)) hdv.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hdO hden

open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem gaussianLogFeature_diagonal_exponential
    (β η : ℝ) (hβ : 0≤β) (hη : 0<η) (hη1 : η≤1)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp
      (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
    let A := 2*M*((2*Real.pi)^((Fintype.card ι:ℝ)/2)/(Fintype.card ι:ℝ))+
      1/4+(∫ p,logPhysicalPair p ∂μ.prod μ)
    Integrable (fun x=>Real.exp (2*β*‖k x‖^2)) μ ∧
      (∫ x,Real.exp (2*β*‖k x‖^2) ∂μ) ≤
        Real.exp (2*β*A)*η^(-2*β)*
          (∫ x,Real.exp (-4*β*logPhysicalPotential μ x) ∂μ) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  let d := (Fintype.card ι:ℝ)
  let A := 2*M*((2*Real.pi)^(d/2)/d)+(1/4:ℝ)+(∫ p,logPhysicalPair p ∂μ.prod μ)
  have hD : AEStronglyMeasurable (fun x=>‖k x‖^2) μ :=
    ((stronglyMeasurable_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair).norm.pow 2).aestronglyMeasurable
  have hpow : η^d≤1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hη.le hη1 hd.le
  have hcoef : 0≤2*M*((2*Real.pi)^(d/2)/d) := by dsimp [d];positivity
  have hb : ∀ᵐ x ∂μ,‖k x‖^2≤A-Real.log η-2*logPhysicalPotential μ x := by
    apply Filter.Eventually.of_forall
    intro x
    have h := norm_sq_gaussianLogCenteredInfiniteFeature_le_sourcePotential
      η hη hd ρ M hM hρ hpair x
    have hscale := mul_le_mul_of_nonneg_left hpow hcoef
    dsimp [k,A,μ,d]
    dsimp [d] at hscale
    nlinarith
  exact feature_diagonal_exponential_of_source_potential _ _ hD β A η hβ hη hb htail

end DGRHS.Attractive
#check @DGRHS.Attractive.gaussianLogFeature_diagonal_exponential
#print axioms DGRHS.Attractive.gaussianLogFeature_diagonal_exponential
#print axioms DGRHS.Attractive.feature_diagonal_exponential_of_source_potential
#print axioms DGRHS.Attractive.feature_HS_margin_exponential_uniform
