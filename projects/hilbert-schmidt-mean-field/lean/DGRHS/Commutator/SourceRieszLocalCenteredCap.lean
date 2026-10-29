import DGRHS.Commutator.SourceRieszLocalCutoff
import DGRHS.Gaussian.HoeffdingLinearity

/-! Proper pointwise centering and cap of the actual local Riesz cutoff.
All bounds are derived from the proved Gaussian profile; no supplied centered
kernel, numerator, exponential moment, or favorable operator premise. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian

lemma sourceRieszLocal_bounded_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W : X → ℝ)
    (hm : StronglyMeasurable W) (C : ℝ) (hC : 0≤C) (hb : ∀ x, |W x|≤C) :
    Integrable W μ := by
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x=> by simpa only [Real.norm_eq_abs] using hb x)

lemma sourceRieszLocal_bounded_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W : X → ℝ)
    (hm : StronglyMeasurable W) (C : ℝ) (hC : 0≤C) (hb : ∀ x, |W x|≤C) :
    |∫ x,W x ∂μ|≤C := by
  have hi := sourceRieszLocal_bounded_integrable μ W hm C hC hb
  calc
    _ ≤ ∫ x,|W x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm W
    _ ≤ ∫ _ : X,C ∂μ := integral_mono_ae hi.norm (integrable_const _) (Filter.Eventually.of_forall hb)
    _ = _ := by simp

lemma sourceRieszLocal_centered_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W : X×X → ℝ)
    (hm : StronglyMeasurable W) (C : ℝ) (hC : 0≤C) (hb : ∀ p, |W p|≤C) (p : X×X) :
    |hoeffdingCentered μ W p|≤4*C := by
  have hR := sourceRieszLocal_bounded_integral μ (fun y=>W (p.1,y))
    (hm.comp_measurable (measurable_const.prodMk measurable_id)) C hC (fun y=>hb (p.1,y))
  have hL := sourceRieszLocal_bounded_integral μ (fun x=>W (x,p.2))
    (hm.comp_measurable (measurable_id.prodMk measurable_const)) C hC (fun x=>hb (x,p.2))
  have hM := sourceRieszLocal_bounded_integral (μ.prod μ) W hm C hC hb
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change |W p-(∫ y,W (p.1,y) ∂μ)-(∫ x,W (x,p.2) ∂μ)+(∫ z,W z ∂μ.prod μ)|≤_
  have hsub (a b : ℝ) : |a-b|≤|a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  calc
    _ ≤ |W p|+|∫ y,W (p.1,y) ∂μ|+|∫ x,W (x,p.2) ∂μ|+|∫ z,W z ∂μ.prod μ| := by
      calc
        _ ≤ |W p-(∫ y,W (p.1,y) ∂μ)-(∫ x,W (x,p.2) ∂μ)|+|∫ z,W z ∂μ.prod μ| := abs_add_le _ _
        _ ≤ (|W p-(∫ y,W (p.1,y) ∂μ)|+|∫ x,W (x,p.2) ∂μ|)+|∫ z,W z ∂μ.prod μ| := by gcongr;exact hsub _ _
        _ ≤ _ := by gcongr;exact hsub _ _
    _ ≤ _ := by have h0:=hb p;linarith

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma stronglyMeasurable_sourceRieszLocalRawCutoff (s η : ℝ) (n : ℕ) (γ σ : ℝ)
    (hs : 0<s) (hη : 0<η) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    StronglyMeasurable (sourceRieszLocalRawCutoff s η n γ σ K v) := by
  have hg := (stronglyMeasurable_gaussianRieszEuclideanTruncation (ι:=ι) s (2*η) hs (by positivity)).comp_measurable
    (measurable_fst.sub measurable_snd)
  exact (((measurable_sourceRieszLongTransportKernel_all_order s η n hs hη hv).stronglyMeasurable).const_mul _).add (hg.const_mul _)

lemma sourceRieszLocalRawCutoff_symmetric (s η : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0)
    (v : E→E) (x y : E) :
    sourceRieszLocalRawCutoff s η n γ σ K v (x,y)=sourceRieszLocalRawCutoff s η n γ σ K v (y,x) := by
  have hk := sourceRieszLongTransportKernel_all_order_symmetric s η n v (x,y)
  unfold sourceRieszLocalRawCutoff
  simp only [Prod.swap_prod_mk] at hk
  rw [hk]
  simp [gaussianRieszEuclideanTruncation,norm_sub_rev]

lemma sourceRieszLocalRawCutoff_cap (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0} {v : E→E}
    (hv : LipschitzWith K v) (p : E×E) :
    |sourceRieszLocalRawCutoff s η n γ σ K v p|≤
      3*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  apply (sourceRieszLocalRawCutoff_bound s η n hs hη γ σ hγ hσ hv p).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤3*γ)
  have hg := gaussianRieszEuclideanTruncation_nonneg s η hs hη (p.1-p.2)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hg] using
    gaussianRieszEuclideanTruncation_le_diagonal s η hs hη (p.1-p.2)

def sourceRieszLocalCenteredCutoff (μ : Measure E) (s η : ℝ) (n : ℕ) (γ σ : ℝ)
    (K : ℝ≥0) (v : E→E) : E×E→ℝ :=
  hoeffdingCentered μ (sourceRieszLocalRawCutoff s η n γ σ K v)

lemma sourceRieszLocalCenteredCutoff_cap (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η) (γ σ : ℝ)
    (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (p : E×E) :
    |sourceRieszLocalCenteredCutoff μ s η n γ σ K v p|≤
      12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hC := (gaussianRieszSourceCoefficient_pos s hs).le
  have hb := sourceRieszLocal_centered_bound μ _ (stronglyMeasurable_sourceRieszLocalRawCutoff s η n γ σ hs hη hv)
    (3*γ*(gaussianRieszSourceCoefficient s/s*η^(-s))) (by positivity)
    (sourceRieszLocalRawCutoff_cap s η n hs hη γ σ hγ hσ hv) p
  simpa only [sourceRieszLocalCenteredCutoff] using (show |hoeffdingCentered μ (sourceRieszLocalRawCutoff s η n γ σ K v) p|≤12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)) by nlinarith [hb])

lemma stronglyMeasurable_sourceRieszLocalCenteredCutoff (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (γ σ : ℝ) (hs : 0<s) (hη : 0<η)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    StronglyMeasurable (sourceRieszLocalCenteredCutoff μ s η n γ σ K v) :=
  stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_sourceRieszLocalRawCutoff s η n γ σ hs hη hv)

lemma memLp_sourceRieszLocalCenteredCutoff (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η) (γ σ : ℝ)
    (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (p : ℝ≥0∞) :
    MemLp (sourceRieszLocalCenteredCutoff μ s η n γ σ K v) p (μ.prod μ) := by
  have hC := (gaussianRieszSourceCoefficient_pos s hs).le
  apply (memLp_const (12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)))).of_le
    (stronglyMeasurable_sourceRieszLocalCenteredCutoff μ s η n γ σ hs hη hv).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)))]
  exact sourceRieszLocalCenteredCutoff_cap μ s η n hs hη γ σ hγ hσ hv z

lemma sourceRieszLocalCenteredCutoff_symmetric (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0) (v : E→E) (x y : E) :
    sourceRieszLocalCenteredCutoff μ s η n γ σ K v (x,y)=sourceRieszLocalCenteredCutoff μ s η n γ σ K v (y,x) :=
  DGRHS.centeredKernel_symmetric μ _ (sourceRieszLocalRawCutoff_symmetric s η n γ σ K v) x y

lemma sourceRieszLocalCenteredCutoff_canonical (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η) (γ σ : ℝ)
    (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    ∀ᵐ x ∂μ,∫ y,sourceRieszLocalCenteredCutoff μ s η n γ σ K v (x,y) ∂μ=0 := by
  have hC := (gaussianRieszSourceCoefficient_pos s hs).le
  have hi := sourceRieszLocal_bounded_integrable (μ.prod μ) _
    (stronglyMeasurable_sourceRieszLocalRawCutoff s η n γ σ hs hη hv)
    (3*γ*(gaussianRieszSourceCoefficient s/s*η^(-s))) (by positivity)
    (sourceRieszLocalRawCutoff_cap s η n hs hη γ σ hγ hσ hv)
  exact DGRHS.integral_centeredKernel_right μ _ hi

lemma essential_sourceRieszLocalCenteredCutoff_le (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η) (γ σ : ℝ)
    (hγ : 0≤γ) (hσ : |σ|≤1) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    (eLpNormEssSup (sourceRieszLocalCenteredCutoff μ s η n γ σ K v) (μ.prod μ)).toReal≤
      12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hC := (gaussianRieszSourceCoefficient_pos s hs).le
  have hB : 0≤12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by positivity
  have hAE : ∀ᵐ p ∂μ.prod μ, ‖sourceRieszLocalCenteredCutoff μ s η n γ σ K v p‖≤12*γ*(gaussianRieszSourceCoefficient s/s*η^(-s)) := Filter.Eventually.of_forall (fun p=> by
    simpa only [Real.norm_eq_abs] using sourceRieszLocalCenteredCutoff_cap μ s η n hs hη γ σ hγ hσ hv p)
  have h := eLpNormEssSup_le_of_ae_bound hAE
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocal_bounded_integrable
#print axioms DGRHS.Commutator.sourceRieszLocal_bounded_integrable

#check DGRHS.Commutator.sourceRieszLocal_bounded_integral
#print axioms DGRHS.Commutator.sourceRieszLocal_bounded_integral

#check DGRHS.Commutator.sourceRieszLocal_centered_bound
#print axioms DGRHS.Commutator.sourceRieszLocal_centered_bound

#check DGRHS.Commutator.stronglyMeasurable_sourceRieszLocalRawCutoff
#print axioms DGRHS.Commutator.stronglyMeasurable_sourceRieszLocalRawCutoff

#check DGRHS.Commutator.sourceRieszLocalRawCutoff_symmetric
#print axioms DGRHS.Commutator.sourceRieszLocalRawCutoff_symmetric

#check DGRHS.Commutator.sourceRieszLocalRawCutoff_cap
#print axioms DGRHS.Commutator.sourceRieszLocalRawCutoff_cap

#check DGRHS.Commutator.sourceRieszLocalCenteredCutoff
#print axioms DGRHS.Commutator.sourceRieszLocalCenteredCutoff

#check DGRHS.Commutator.sourceRieszLocalCenteredCutoff_cap
#print axioms DGRHS.Commutator.sourceRieszLocalCenteredCutoff_cap

#check DGRHS.Commutator.stronglyMeasurable_sourceRieszLocalCenteredCutoff
#print axioms DGRHS.Commutator.stronglyMeasurable_sourceRieszLocalCenteredCutoff

#check DGRHS.Commutator.memLp_sourceRieszLocalCenteredCutoff
#print axioms DGRHS.Commutator.memLp_sourceRieszLocalCenteredCutoff

#check DGRHS.Commutator.sourceRieszLocalCenteredCutoff_symmetric
#print axioms DGRHS.Commutator.sourceRieszLocalCenteredCutoff_symmetric

#check DGRHS.Commutator.sourceRieszLocalCenteredCutoff_canonical
#print axioms DGRHS.Commutator.sourceRieszLocalCenteredCutoff_canonical

#check DGRHS.Commutator.essential_sourceRieszLocalCenteredCutoff_le
#print axioms DGRHS.Commutator.essential_sourceRieszLocalCenteredCutoff_le
