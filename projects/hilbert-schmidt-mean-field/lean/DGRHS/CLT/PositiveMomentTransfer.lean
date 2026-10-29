/- Changing sample spaces: convergence of positive expectations from actual weak
convergence and a uniform moment of any order strictly greater than one.
No weighted expectation convergence is assumed. Physical exponential moment
hypotheses must be discharged separately before a Gibbs application. -/
import DGRHS.CLT.BoundedLipschitz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT

def positiveClip (R x : ℝ) : ℝ := min (max x 0) R

lemma continuous_positiveClip (R : ℝ) : Continuous (positiveClip R) := by
  unfold positiveClip
  fun_prop

lemma positiveClip_bounds {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 ≤ positiveClip R x ∧ positiveClip R x ≤ R := by
  exact ⟨le_min (le_max_right _ _) hR, min_le_right _ _⟩

lemma positiveClip_le {R x : ℝ} (hx : 0 ≤ x) : positiveClip R x ≤ x := by
  unfold positiveClip
  rw [max_eq_left hx]
  exact min_le_left _ _

lemma positiveClip_error_rpow {R x ε : ℝ} (hR : 0 < R) (hx : 0 ≤ x)
    (hε : 0 < ε) :
    |x-positiveClip R x| ≤ x^(1+ε)/R^ε := by
  unfold positiveClip
  rw [max_eq_left hx, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
  by_cases hxR : x ≤ R
  · rw [min_eq_left hxR, sub_self]
    exact div_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hR.le _)
  · have hRx : R ≤ x := le_of_not_ge hxR
    have hxpos : 0 < x := hR.trans_le hRx
    have hp := Real.rpow_le_rpow hR.le hRx hε.le
    have hpr : 0 < R^ε := Real.rpow_pos_of_pos hR _
    rw [min_eq_right hRx]
    calc
      x-R ≤ x := sub_le_self _ hR.le
      _ ≤ x^(1+ε)/R^ε := by
        apply (le_div_iff₀ hpr).mpr
        rw [Real.rpow_add hxpos, Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hp hx

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma integrable_positiveClip {X : S → ℝ} (hX : AEMeasurable X μ)
    {R : ℝ} (hR : 0 ≤ R) : Integrable (fun x => positiveClip R (X x)) μ := by
  apply Integrable.of_bound
    ((continuous_positiveClip R).measurable.comp_aemeasurable hX).aestronglyMeasurable R
  exact ae_of_all _ fun x => by
    change ‖positiveClip R (X x)‖ ≤ R
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveClip_bounds hR _).1]
    exact (positiveClip_bounds hR _).2

lemma integral_positiveClip_error_le {X : S → ℝ} (hX : Integrable X μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ X x) {R ε C : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hmom : Integrable (fun x => (X x)^(1+ε)) μ)
    (hC : (∫ x, (X x)^(1+ε) ∂μ) ≤ C) :
    dist (∫ x, X x ∂μ) (∫ x, positiveClip R (X x) ∂μ) ≤ C/R^ε := by
  have hc := integrable_positiveClip hX.aemeasurable hR.le
  rw [dist_eq_norm, ← integral_sub hX hc]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ x, ‖X x-positiveClip R (X x)‖ ∂μ) ≤
        ∫ x, (X x)^(1+ε)/R^ε ∂μ := by
      apply integral_mono_ae (hX.sub hc).norm (hmom.div_const _)
      filter_upwards [hpos] with x hx
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using positiveClip_error_rpow hR hx hε
    _ = (∫ x, (X x)^(1+ε) ∂μ)/R^ε := integral_div _ _
    _ ≤ C/R^ε := div_le_div_of_nonneg_right hC (Real.rpow_nonneg hR.le _)

lemma integral_positiveClip_tendsto {Z : S → ℝ} (hZ : Integrable Z μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ Z x) :
    Tendsto (fun m : ℕ => ∫ x, positiveClip ((m:ℝ)+1) (Z x) ∂μ)
      atTop (𝓝 (∫ x, Z x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖Z x‖)
  · exact Eventually.of_forall (fun m =>
      ((continuous_positiveClip ((m:ℝ)+1)).measurable.comp_aemeasurable
        hZ.aemeasurable).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro m
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveClip_bounds (by positivity) _).1,
      Real.norm_eq_abs, abs_of_nonneg hx]
    exact positiveClip_le hx
  · exact hZ.norm
  · filter_upwards [hpos] with x hx
    have ht : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (eventually_ge_atTop (Z x))] with m hm
    simp [positiveClip, max_eq_left hx, min_eq_left hm]

variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μn : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μn n)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma positive_integral_tendsto_of_distribution_moment
    (X : ∀ n, Ω n → ℝ) (Z : Ω' → ℝ)
    (hweak : TendstoInDistribution X atTop Z μn ν)
    (hX : ∀ n, Integrable (X n) (μn n)) (hZ : Integrable Z ν)
    (hpos : ∀ n, ∀ᵐ x ∂μn n, 0 ≤ X n x) (hzpos : ∀ᵐ z ∂ν, 0 ≤ Z z)
    (ε C : ℝ) (hε : 0 < ε)
    (hmom : ∀ n, Integrable (fun x => (X n x)^(1+ε)) (μn n))
    (hC : ∀ n, (∫ x, (X n x)^(1+ε) ∂μn n) ≤ C) :
    Tendsto (fun n => ∫ x, X n x ∂μn n) atTop (𝓝 (∫ z, Z z ∂ν)) := by
  apply tendsto_of_uniform_approximation _
    (fun m n => ∫ x, positiveClip ((m:ℝ)+1) (X n x) ∂μn n)
    (fun m => ∫ z, positiveClip ((m:ℝ)+1) (Z z) ∂ν)
    (fun m => C/((m:ℝ)+1)^ε) _
  · have ht : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hε).comp ht)
  · exact integral_positiveClip_tendsto hZ hzpos
  · intro m
    have hR : 0 ≤ (m:ℝ)+1 := by positivity
    let F : BoundedContinuousFunction ℝ ℝ := ⟨⟨positiveClip ((m:ℝ)+1), continuous_positiveClip _⟩,
      ⟨(m:ℝ)+1, fun x y => by
        have hx := positiveClip_bounds hR x
        have hy := positiveClip_bounds hR y
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith⟩⟩
    exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hweak.forall_aemeasurable hweak.aemeasurable_limit).mp hweak F
  · intro m n
    exact integral_positiveClip_error_le (hX n) (hpos n) (by positivity)
      hε (hmom n) (hC n)

end DGRHS.CLT
#print axioms DGRHS.CLT.positiveClip_error_rpow
#print axioms DGRHS.CLT.integral_positiveClip_error_le
#print axioms DGRHS.CLT.integral_positiveClip_tendsto
#print axioms DGRHS.CLT.positive_integral_tendsto_of_distribution_moment
#check @DGRHS.CLT.positive_integral_tendsto_of_distribution_moment
