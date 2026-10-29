import DGRHS.Commutator.SourceRieszLocalCenteredCap
import DGRHS.Gaussian.HoeffdingRowL2

/-! Scale-uniform actual mixed and product square estimates and SAME operator
for the local Riesz commutator cutoff. The actual full square-row estimate
requires exactly 2s<d. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma memLp_sourceRieszLocalRawCutoff (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η) (γ σ : ℝ)
    (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (p : ℝ≥0∞) :
    MemLp (sourceRieszLocalRawCutoff s η n γ σ K v) p (μ.prod μ) := by
  have hC := (gaussianRieszSourceCoefficient_pos s hs).le
  apply (memLp_const (3*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)))).of_le
    (stronglyMeasurable_sourceRieszLocalRawCutoff s η n γ σ hs hη hv).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤3*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)))]
  exact sourceRieszLocalRawCutoff_cap s η n hs hη γ σ hγ hσ hv z

lemma sourceRieszLocalRawCutoff_square_row (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : 2*s<(Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (x : E) :
    Integrable (fun y=>(sourceRieszLocalRawCutoff s η n γ σ K v (x,y))^2) (gaussianRieszDensityMeasure ρ) ∧
      (∫ y,(sourceRieszLocalRawCutoff s η n γ σ K v (x,y))^2 ∂gaussianRieszDensityMeasure ρ)≤
        9*γ^2*sourceRieszFullSquareRowControl s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let r := sourceRieszLocalRawCutoff s η n γ σ K v
  let C := 3*γ*(gaussianRieszSourceCoefficient s/s*η^(-s))
  have hC0 := (gaussianRieszSourceCoefficient_pos s hs).le
  have hC : 0≤C := by dsimp [C];positivity
  have hm : StronglyMeasurable (fun y : E=>r (x,y)) := (stronglyMeasurable_sourceRieszLocalRawCutoff s η n γ σ hs hη hv).comp_measurable
    (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun y=>r (x,y)^2) μ := sourceRieszLocal_bounded_integrable μ _ (hm.pow 2) (C^2)
    (sq_nonneg _) (fun y=>by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hb := sourceRieszLocalRawCutoff_cap s η n hs hη γ σ hγ hσ hv (x,y)
      change |r (x,y)|≤C at hb
      have hsq := (sq_le_sq₀ (abs_nonneg (r (x,y))) hC).2 hb
      simpa only [sq_abs] using hsq)
  have hc : 0<Fintype.card ι := by exact_mod_cast (show (0:ℝ)<(Fintype.card ι:ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure;infer_instance
  have hb : ∀ᵐ y ∂μ,r (x,y)^2≤9*γ^2*(gaussianRieszPhysicalPair s (x,y))^2 := by
    filter_upwards [μ.ae_ne x] with y hy
    have hg := (gaussianRieszEuclidean_truncation_bounds s η hs hη (x-y) (sub_ne_zero.mpr hy.symm)).2.1
    have hr := (sourceRieszLocalRawCutoff_bound s η n hs hη γ σ hγ hσ hv (x,y)).trans
      (mul_le_mul_of_nonneg_left hg (by positivity : 0≤3*γ))
    change |r (x,y)|≤3*γ*gaussianRieszPhysicalPair s (x,y) at hr
    have hp : 0≤3*γ*gaussianRieszPhysicalPair s (x,y) := by unfold gaussianRieszPhysicalPair;positivity
    have hsq := (sq_le_sq₀ (abs_nonneg (r (x,y))) hp).2 hr
    nlinarith only [hsq,show |r (x,y)|^2=r (x,y)^2 from sq_abs _]
  have hfull := sourceRieszPhysicalPair_square_row s hs hd ρ M hM hρ x
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y,9*γ^2*(gaussianRieszPhysicalPair s (x,y))^2 ∂μ := integral_mono_ae hi (hfull.1.const_mul _) hb
    _ = 9*γ^2*(∫ y,(gaussianRieszPhysicalPair s (x,y))^2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hfull.2 (by positivity)

lemma sourceRieszLocalRawCutoff_square_pair (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : 2*s<(Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    (∫ p,(sourceRieszLocalRawCutoff s η n γ σ K v p)^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))≤
        9*γ^2*sourceRieszFullSquareRowControl s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hi := (memLp_sourceRieszLocalRawCutoff μ s η n hs hη γ σ hγ hσ hv 2).integrable_sq
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : E,9*γ^2*sourceRieszFullSquareRowControl s M ι ∂μ := integral_mono_ae hi.integral_prod_left
      (integrable_const _) (Filter.Eventually.of_forall (fun x=>(sourceRieszLocalRawCutoff_square_row s η n hs hη hd γ σ hγ hσ hv ρ M hM hρ x).2))
    _ = _ := by simp

lemma sourceRieszLocalCenteredCutoff_square_controls (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : 2*s<(Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y,(sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s η n γ σ K v (x,y))^2 ∂gaussianRieszDensityMeasure ρ)≤
        144*γ^2*sourceRieszFullSquareRowControl s M ι) ∧
    (∫ p,(sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s η n γ σ K v p)^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))≤
        144*γ^2*sourceRieszFullSquareRowControl s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hm := stronglyMeasurable_sourceRieszLocalRawCutoff s η n γ σ hs hη hv
  have h2 := memLp_sourceRieszLocalRawCutoff μ s η n hs hη γ σ hγ hσ hv 2
  constructor
  · have hb := ae_row_sq_hoeffdingCentered_le μ _ hm h2 _
      (Filter.Eventually.of_forall (fun x=>(sourceRieszLocalRawCutoff_square_row s η n hs hη hd γ σ hγ hσ hv ρ M hM hρ x).2))
    filter_upwards [hb] with x hx
    change (∫ y,hoeffdingCentered μ (sourceRieszLocalRawCutoff s η n γ σ K v) (x,y)^2 ∂μ)≤_ at hx ⊢
    nlinarith [hx]
  · have hb := (integral_sq_hoeffdingCentered_le μ _ hm h2).trans
      (mul_le_mul_of_nonneg_left (sourceRieszLocalRawCutoff_square_pair s η n hs hη hd γ σ hγ hσ hv ρ M hM hρ) (by positivity : 0≤(16:ℝ)))
    change (∫ p,hoeffdingCentered μ (sourceRieszLocalRawCutoff s η n γ σ K v) p^2 ∂μ.prod μ)≤_ at hb ⊢
    nlinarith [hb]

lemma norm_sourceRieszLocalCenteredCutoff_operator (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : 2*s<(Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    ‖DGRHS.Kernel.integralOperator (sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s η n γ σ K v)
      (memLp_sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s η n hs hη γ σ hγ hσ hv 2)‖≤
        12*γ*Real.sqrt (sourceRieszFullSquareRowControl s M ι) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := sourceRieszLocalCenteredCutoff μ s η n γ σ K v
  let hW := memLp_sourceRieszLocalCenteredCutoff μ s η n hs hη γ σ hγ hσ hv 2
  have hfull := sourceRieszPhysicalPair_square_row s hs hd ρ M hM hρ (0:E)
  have hC : 0≤sourceRieszFullSquareRowControl s M ι := (integral_nonneg (fun y=>sq_nonneg _)).trans hfull.2
  have hb : ‖hW.toLp W‖^2≤144*γ^2*sourceRieszFullSquareRowControl s M ι := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact (sourceRieszLocalCenteredCutoff_square_controls s η n hs hη hd γ σ hγ hσ hv ρ M hM hρ).2
  have hn : ‖hW.toLp W‖≤12*γ*Real.sqrt (sourceRieszFullSquareRowControl s M ι) := by
    apply (sq_le_sq₀ (norm_nonneg (hW.toLp W)) (by positivity : 0≤12*γ*Real.sqrt (sourceRieszFullSquareRowControl s M ι))).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt hC]
    convert hb using 1 <;> ring
  exact (DGRHS.Kernel.norm_integralOperator_le W hW).trans hn

end DGRHS.Commutator

#check DGRHS.Commutator.memLp_sourceRieszLocalRawCutoff
#print axioms DGRHS.Commutator.memLp_sourceRieszLocalRawCutoff

#check DGRHS.Commutator.sourceRieszLocalRawCutoff_square_row
#print axioms DGRHS.Commutator.sourceRieszLocalRawCutoff_square_row

#check DGRHS.Commutator.sourceRieszLocalRawCutoff_square_pair
#print axioms DGRHS.Commutator.sourceRieszLocalRawCutoff_square_pair

#check DGRHS.Commutator.sourceRieszLocalCenteredCutoff_square_controls
#print axioms DGRHS.Commutator.sourceRieszLocalCenteredCutoff_square_controls

#check DGRHS.Commutator.norm_sourceRieszLocalCenteredCutoff_operator
#print axioms DGRHS.Commutator.norm_sourceRieszLocalCenteredCutoff_operator
