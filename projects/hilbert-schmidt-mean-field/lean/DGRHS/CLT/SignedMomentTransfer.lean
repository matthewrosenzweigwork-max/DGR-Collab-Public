/- Changing-domain integral convergence for real variables with an actual
uniform absolute moment of any order strictly greater than one. -/
import DGRHS.CLT.PositiveMomentTransfer
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT

lemma max_zero_le_abs (x : ℝ) : max x 0 ≤ |x| :=
  max_le (le_abs_self _) (abs_nonneg _)

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

lemma integrable_pospart_rpow {X : S → ℝ} (hX : AEMeasurable X μ)
    {p : ℝ} (hp : 0 ≤ p) (hm : Integrable (fun x => |X x|^p) μ) :
    Integrable (fun x => (max (X x) 0)^p) μ := by
  have hc : Continuous (fun t : ℝ => (max t 0)^p) :=
    (Real.continuous_rpow_const hp).comp (continuous_id.max continuous_const)
  apply hm.mono' (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change |(max (X x) 0)^p| ≤ |X x|^p
    rw [abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    exact Real.rpow_le_rpow (le_max_right _ _) (max_zero_le_abs _) hp

lemma integral_pospart_rpow_le {X : S → ℝ} (hX : AEMeasurable X μ)
    {p : ℝ} (hp : 0 ≤ p) (hm : Integrable (fun x => |X x|^p) μ) :
    (∫ x, (max (X x) 0)^p ∂μ) ≤ ∫ x, |X x|^p ∂μ := by
  apply integral_mono (integrable_pospart_rpow hX hp hm) hm
  intro x
  exact Real.rpow_le_rpow (le_max_right _ _) (max_zero_le_abs _) hp

lemma integral_pospart_sub_negpart (ρ : Measure S) (f : S → ℝ)
    (hf : Integrable f ρ) :
    (∫ t, max (f t) 0 ∂ρ)-(∫ t, max (-f t) 0 ∂ρ) = ∫ t, f t ∂ρ := by
  rw [← integral_sub hf.pos_part hf.neg_part]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    change max (f t) 0-max (-f t) 0 = f t
    by_cases ht : 0 ≤ f t
    · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
    · rw [max_eq_right (le_of_not_ge ht), max_eq_left (neg_nonneg.mpr (le_of_not_ge ht))]
      ring

variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μn : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μn n)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma integral_tendsto_of_distribution_absolute_moment
    (X : ∀ n, Ω n → ℝ) (Z : Ω' → ℝ)
    (hweak : TendstoInDistribution X atTop Z μn ν)
    (hX : ∀ n, Integrable (X n) (μn n)) (hZ : Integrable Z ν)
    (p C : ℝ) (hp : 1 < p)
    (hmom : ∀ n, Integrable (fun x => |X n x|^p) (μn n))
    (hC : ∀ n, (∫ x, |X n x|^p ∂μn n) ≤ C) :
    Tendsto (fun n => ∫ x, X n x ∂μn n) atTop (𝓝 (∫ z, Z z ∂ν)) := by
  have hp0 : 0 ≤ p := (lt_trans zero_lt_one hp).le
  have pos : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  have neg : Continuous (fun t : ℝ => max (-t) 0) := continuous_id.neg.max continuous_const
  have hpseq := positive_integral_tendsto_of_distribution_moment
    (fun n x => max (X n x) 0) (fun z => max (Z z) 0)
    (hweak.continuous_comp (g := fun t : ℝ => max t 0) pos)
    (fun n => (hX n).pos_part) hZ.pos_part
    (fun n => ae_of_all _ fun x => le_max_right _ _)
    (ae_of_all _ fun z => le_max_right _ _) (p-1) C (by linarith)
    (fun n => by simpa only [show 1+(p-1)=p by ring] using
      integrable_pospart_rpow (hweak.forall_aemeasurable n) hp0 (hmom n))
    (fun n => by simpa only [show 1+(p-1)=p by ring] using
      (integral_pospart_rpow_le (hweak.forall_aemeasurable n) hp0 (hmom n)).trans (hC n))
  have hnmom : ∀ n, Integrable (fun x => |-X n x|^p) (μn n) := by
    intro n
    simpa only [abs_neg] using hmom n
  have hnseq := positive_integral_tendsto_of_distribution_moment
    (fun n x => max (-X n x) 0) (fun z => max (-Z z) 0)
    (hweak.continuous_comp (g := fun t : ℝ => max (-t) 0) neg)
    (fun n => (hX n).neg_part) hZ.neg_part
    (fun n => ae_of_all _ fun x => le_max_right _ _)
    (ae_of_all _ fun z => le_max_right _ _) (p-1) C (by linarith)
    (fun n => by simpa only [show 1+(p-1)=p by ring, Pi.neg_apply] using
      integrable_pospart_rpow (hweak.forall_aemeasurable n).neg hp0 (hnmom n))
    (fun n => by
      have hb : (∫ x, |-X n x|^p ∂μn n) ≤ C := by
        simpa only [abs_neg] using hC n
      have hh := (integral_pospart_rpow_le (hweak.forall_aemeasurable n).neg hp0 (hnmom n)).trans hb
      simpa only [show 1+(p-1)=p by ring, Pi.neg_apply] using hh)
  simpa only [integral_pospart_sub_negpart _ _ hZ,
    integral_pospart_sub_negpart _ _ (hX _)] using hpseq.sub hnseq

end DGRHS.CLT
#print axioms DGRHS.CLT.integrable_pospart_rpow
#print axioms DGRHS.CLT.integral_pospart_rpow_le
#print axioms DGRHS.CLT.integral_tendsto_of_distribution_absolute_moment
#check @DGRHS.CLT.integral_tendsto_of_distribution_absolute_moment
