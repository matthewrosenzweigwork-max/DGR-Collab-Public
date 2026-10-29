import LeanResearch.PeriodicAttractiveLogGas.Geometry
import LeanResearch.PeriodicAttractiveLogGas.StationaryRankSlope
import LeanResearch.PeriodicAttractiveLogGas.RearrangementRegularity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Actual superlevel distribution of a continuous function on the square torus.
Source: the stationary uniqueness proof, level sets and decreasing rearrangement.
Level sets of positive area are allowed throughout. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace PeriodicAttractiveLogGas.StationaryDistribution

local instance : torusMeasure.IsOpenPosMeasure := by
  unfold torusMeasure
  infer_instance

def minimum (v : Torus → ℝ) : ℝ := sInf (range v)
def maximum (v : Torus → ℝ) : ℝ := sSup (range v)
def rank (v : Torus → ℝ) (t : ℝ) : ℝ := torusMeasure.real {x | t < v x}
def upperRank (v : Torus → ℝ) (t : ℝ) : ℝ := torusMeasure.real {x | t ≤ v x}

theorem minimum_le {v : Torus → ℝ} (hv : Continuous v) (x : Torus) :
    minimum v ≤ v x := csInf_le (isCompact_range hv).bddBelow (mem_range_self x)

theorem le_maximum {v : Torus → ℝ} (hv : Continuous v) (x : Torus) :
    v x ≤ maximum v := le_csSup (isCompact_range hv).bddAbove (mem_range_self x)

theorem minimum_attained {v : Torus → ℝ} (hv : Continuous v) :
    ∃ x, v x = minimum v := (isCompact_range hv).sInf_mem (range_nonempty v)

theorem maximum_attained {v : Torus → ℝ} (hv : Continuous v) :
    ∃ x, v x = maximum v := (isCompact_range hv).sSup_mem (range_nonempty v)

theorem minimum_le_maximum {v : Torus → ℝ} (hv : Continuous v) :
    minimum v ≤ maximum v := (minimum_le hv 0).trans (le_maximum hv 0)

theorem range_eq_interval {v : Torus → ℝ} (hv : Continuous v) :
    range v = Icc (minimum v) (maximum v) := by
  apply Subset.antisymm
  · rintro t ⟨x, rfl⟩
    exact ⟨minimum_le hv x, le_maximum hv x⟩
  · obtain ⟨a, ha⟩ := minimum_attained hv
    obtain ⟨b, hb⟩ := maximum_attained hv
    simpa only [ha, hb] using intermediate_value_univ a b hv

theorem rank_nonneg (v : Torus → ℝ) (t : ℝ) : 0 ≤ rank v t := measureReal_nonneg

theorem rank_le_one (v : Torus → ℝ) (t : ℝ) : rank v t ≤ 1 := by
  simpa only [rank, probReal_univ] using
    (measureReal_mono (μ := torusMeasure) (subset_univ {x | t < v x}))

theorem rank_antitone (v : Torus → ℝ) : Antitone (rank v) := by
  intro a b hab
  exact measureReal_mono (fun _ hx => lt_of_le_of_lt hab hx)

theorem rank_eq_one_below {v : Torus → ℝ} (hv : Continuous v) {t : ℝ}
    (ht : t < minimum v) : rank v t = 1 := by
  have he : {x | t < v x} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ht.trans_le (minimum_le hv x)
  simp [rank, he]

theorem rank_eq_zero_above {v : Torus → ℝ} (hv : Continuous v) {t : ℝ}
    (ht : maximum v ≤ t) : rank v t = 0 := by
  have he : {x | t < v x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge ((le_maximum hv x).trans ht)
  simp [rank, he]

theorem open_band_pos {v : Torus → ℝ} (hv : Continuous v) {a b : ℝ}
    (hab : a < b) (ha : minimum v ≤ a) (hb : b ≤ maximum v) :
    0 < torusMeasure.real {x | a < v x ∧ v x < b} := by
  obtain ⟨t, hat, htb⟩ := exists_between hab
  have ht : t ∈ range v := by
    rw [range_eq_interval hv]
    exact ⟨ha.trans hat.le, htb.le.trans hb⟩
  obtain ⟨x, hx⟩ := ht
  have hopen : IsOpen {x | a < v x ∧ v x < b} :=
    (isOpen_lt continuous_const hv).inter (isOpen_lt hv continuous_const)
  exact ENNReal.toReal_pos (hopen.measure_ne_zero torusMeasure
    ⟨x, by change a < v x ∧ v x < b; rw [hx]; exact ⟨hat, htb⟩⟩)
    (measure_ne_top _ _)

theorem rank_strict_on_range {v : Torus → ℝ} (hv : Continuous v) {a b : ℝ}
    (hab : a < b) (ha : minimum v ≤ a) (hb : b ≤ maximum v) :
    rank v b < rank v a := by
  have hsub : {x | b < v x} ⊆ {x | a < v x} := fun _ hx => hab.trans hx
  have hdiff := measureReal_sdiff (μ := torusMeasure) hsub
    (isOpen_lt continuous_const hv).measurableSet
  have hband := open_band_pos hv hab ha hb
  have hle : torusMeasure.real {x | a < v x ∧ v x < b} ≤
      torusMeasure.real ({x | a < v x} \ {x | b < v x}) := by
    exact measureReal_mono (fun _ hx => ⟨hx.1, not_lt_of_ge hx.2.le⟩)
  rw [hdiff] at hle
  change _ ≤ rank v a - rank v b at hle
  linarith

theorem rank_eq_one_sub_cdf {v : Torus → ℝ} (hv : Continuous v) (t : ℝ) :
    rank v t = 1 - ProbabilityTheory.cdf (torusMeasure.map v) t := by
  have : IsProbabilityMeasure (torusMeasure.map v) :=
    (Measure.isProbabilityMeasure_map_iff hv.measurable.aemeasurable).mpr inferInstance
  rw [ProbabilityTheory.cdf_eq_real, map_measureReal_apply hv.measurable measurableSet_Iic]
  have he : {x | t < v x} = (v ⁻¹' Iic t)ᶜ := by ext x; simp
  rw [rank, he, measureReal_compl (hv.measurable measurableSet_Iic), probReal_univ]

theorem rank_right_continuous {v : Torus → ℝ} (hv : Continuous v) (t : ℝ) :
    ContinuousWithinAt (rank v) (Ici t) t := by
  have he : rank v = fun t => 1 - ProbabilityTheory.cdf (torusMeasure.map v) t :=
    funext (rank_eq_one_sub_cdf hv)
  rw [he]
  exact continuousWithinAt_const.sub ((ProbabilityTheory.cdf (torusMeasure.map v)).right_continuous t)

theorem rank_pos_below_maximum {v : Torus → ℝ} (hv : Continuous v) {t : ℝ}
    (ht : t < maximum v) : 0 < rank v t := by
  obtain ⟨x, hx⟩ := maximum_attained hv
  exact ENNReal.toReal_pos
    ((isOpen_lt continuous_const hv).measure_ne_zero torusMeasure
      ⟨x, by change t < v x; rwa [hx]⟩) (measure_ne_top _ _)

/-- The bounded generalized inverse includes the endpoints and allows atoms. -/
def cut (v : Torus → ℝ) (s : ℝ) : Set ℝ :=
  {t | t ∈ Icc (minimum v) (maximum v) ∧ rank v t ≤ s}

def profile (v : Torus → ℝ) (s : ℝ) : ℝ := sInf (cut v s)

theorem cut_nonempty {v : Torus → ℝ} (hv : Continuous v) {s : ℝ} (hs : 0 ≤ s) :
    (cut v s).Nonempty := by
  refine ⟨maximum v, ⟨⟨minimum_le_maximum hv, le_rfl⟩, ?_⟩⟩
  rw [rank_eq_zero_above hv le_rfl]
  exact hs

theorem cut_bddBelow (v : Torus → ℝ) (s : ℝ) : BddBelow (cut v s) :=
  ⟨minimum v, fun _ ht => ht.1.1⟩

theorem profile_mem_interval {v : Torus → ℝ} (hv : Continuous v) {s : ℝ} (hs : 0 ≤ s) :
    profile v s ∈ Icc (minimum v) (maximum v) := by
  refine ⟨le_csInf (cut_nonempty hv hs) (fun _ ht => ht.1.1), ?_⟩
  exact csInf_le (cut_bddBelow v s)
    ⟨⟨minimum_le_maximum hv, le_rfl⟩, by rw [rank_eq_zero_above hv le_rfl]; exact hs⟩

theorem rank_le_above_profile {v : Torus → ℝ} (hv : Continuous v) {s t : ℝ}
    (hs : 0 ≤ s) (ht : profile v s < t) : rank v t ≤ s := by
  obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt (cut_nonempty hv hs) ht
  exact (rank_antitone v hat.le).trans ha.2

theorem rank_profile_le {v : Torus → ℝ} (hv : Continuous v) {s : ℝ} (hs : 0 ≤ s) :
    rank v (profile v s) ≤ s := by
  apply le_of_tendsto ((rank_right_continuous hv (profile v s)).mono Ioi_subset_Ici_self)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact rank_le_above_profile hv hs ht

theorem profile_le_iff {v : Torus → ℝ} (hv : Continuous v) {s t : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) : profile v s ≤ t ↔ rank v t ≤ s := by
  constructor
  · intro h
    exact (rank_antitone v h).trans (rank_profile_le hv hs)
  · intro h
    by_cases ht : maximum v ≤ t
    · exact (profile_mem_interval hv hs).2.trans ht
    have hmin : minimum v ≤ t := by
      by_contra hh
      have he := rank_eq_one_below hv (lt_of_not_ge hh)
      linarith
    exact csInf_le (cut_bddBelow v s) ⟨⟨hmin, (lt_of_not_ge ht).le⟩, h⟩

theorem lt_profile_iff {v : Torus → ℝ} (hv : Continuous v) {s t : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) : t < profile v s ↔ s < rank v t := by
  simpa only [not_le] using not_congr (profile_le_iff hv hs hs1 (t := t))

theorem profile_antitone {v : Torus → ℝ} (hv : Continuous v) :
    AntitoneOn (profile v) (Icc 0 1) := by
  intro a ha b hb hab
  exact csInf_le_csInf (cut_bddBelow v b) (cut_nonempty hv ha.1)
    (fun _ ht => ⟨ht.1, ht.2.trans hab⟩)

theorem profile_zero {v : Torus → ℝ} (hv : Continuous v) : profile v 0 = maximum v := by
  apply le_antisymm (profile_mem_interval hv le_rfl).2
  by_contra h
  have hp := rank_pos_below_maximum hv (lt_of_not_ge h)
  have hn := rank_profile_le hv (s := 0) le_rfl
  linarith

theorem profile_one {v : Torus → ℝ} (hv : Continuous v) : profile v 1 = minimum v := by
  apply le_antisymm _ (profile_mem_interval hv zero_le_one).1
  exact csInf_le (cut_bddBelow v 1)
    ⟨⟨le_rfl, minimum_le_maximum hv⟩, rank_le_one v (minimum v)⟩

theorem rank_lt_of_profile_lt {v : Torus → ℝ} (hv : Continuous v) {s t : ℝ}
    (hs : 0 ≤ s) (ht : profile v s < t) (htop : t ≤ maximum v) : rank v t < s := by
  obtain ⟨a, hqa, hat⟩ := exists_between ht
  have hm : minimum v ≤ a := (profile_mem_interval hv hs).1.trans hqa.le
  exact (rank_strict_on_range hv hat hm htop).trans_le (rank_le_above_profile hv hs hqa)

/-- Positive measure of every open band prevents jumps of the actual inverse.
No atomlessness of the distribution is assumed. -/
theorem profile_continuousOn {v : Torus → ℝ} (hv : Continuous v) :
    ContinuousOn (profile v) (Icc (0 : ℝ) 1) := by
  intro s hs
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hmin : a < minimum v
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact hmin.trans_le (profile_mem_interval hv hr.1).1
    have hs1 : s < 1 := by
      by_contra hh
      have he : s = 1 := le_antisymm hs.2 (le_of_not_gt hh)
      rw [he, profile_one hv] at ha
      exact hmin ha
    have hsa : s < rank v a := (lt_profile_iff hv hs.1 hs1).mp ha
    have hn : ∀ᶠ r in 𝓝[Icc (0 : ℝ) 1] s, r < rank v a :=
      nhdsWithin_le_nhds (eventually_lt_nhds hsa)
    filter_upwards [self_mem_nhdsWithin, hn] with r hr hra
    exact (lt_profile_iff hv hr.1 (hra.trans_le (rank_le_one v a))).mpr hra
  · intro b hb
    by_cases hmax : maximum v < b
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact (profile_mem_interval hv hr.1).2.trans_lt hmax
    obtain ⟨a, hqa, hab⟩ := exists_between hb
    have hamax : a ≤ maximum v := hab.le.trans (le_of_not_gt hmax)
    have has : rank v a < s := rank_lt_of_profile_lt hv hs.1 hqa hamax
    have hn : ∀ᶠ r in 𝓝[Icc (0 : ℝ) 1] s, rank v a < r :=
      nhdsWithin_le_nhds (eventually_gt_nhds has)
    filter_upwards [self_mem_nhdsWithin, hn] with r _ har
    apply lt_of_le_of_lt _ hab
    exact csInf_le (cut_bddBelow v r)
      ⟨⟨(profile_mem_interval hv hs.1).1.trans hqa.le, hamax⟩, har.le⟩

def rankMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure rankMeasure := by
  constructor
  simp [rankMeasure, Real.volume_Ioo]

theorem profile_aemeasurable {v : Torus → ℝ} (hv : Continuous v) :
    AEMeasurable (profile v) rankMeasure :=
  ((profile_continuousOn hv).mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo

theorem profile_superlevel_set {v : Torus → ℝ} (hv : Continuous v) (t : ℝ) :
    (profile v ⁻¹' Ioi t) ∩ Ioo 0 1 = Ioo 0 (rank v t) := by
  ext s
  constructor
  · rintro ⟨ht, hs⟩
    exact ⟨hs.1, (lt_profile_iff hv hs.1.le hs.2).mp ht⟩
  · rintro ⟨hs, ht⟩
    have hs1 : s < 1 := ht.trans_le (rank_le_one v t)
    exact ⟨(lt_profile_iff hv hs.le hs1).mpr ht, hs, hs1⟩

theorem profile_tail_measure {v : Torus → ℝ} (hv : Continuous v) (t : ℝ) :
    (rankMeasure.map (profile v)) (Ioi t) = (torusMeasure.map v) (Ioi t) := by
  rw [Measure.map_apply_of_aemeasurable (profile_aemeasurable hv) measurableSet_Ioi,
    Measure.map_apply hv.measurable measurableSet_Ioi]
  change (volume.restrict (Ioo (0 : ℝ) 1)) (profile v ⁻¹' Ioi t) = _
  rw [Measure.restrict_apply' measurableSet_Ioo, profile_superlevel_set hv,
    Real.volume_Ioo, sub_zero]
  change ENNReal.ofReal (torusMeasure {x | t < v x}).toReal = _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

theorem profile_distribution {v : Torus → ℝ} (hv : Continuous v) :
    rankMeasure.map (profile v) = torusMeasure.map v := by
  have : IsProbabilityMeasure (rankMeasure.map (profile v)) :=
    (Measure.isProbabilityMeasure_map_iff (profile_aemeasurable hv)).mpr inferInstance
  have : IsProbabilityMeasure (torusMeasure.map v) :=
    (Measure.isProbabilityMeasure_map_iff hv.measurable.aemeasurable).mpr inferInstance
  apply Measure.ext_of_Iic
  intro t
  have he : Iic t = (Ioi t)ᶜ := by ext x; simp
  rw [he, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_univ, measure_univ, profile_tail_measure hv]

/-- Equality of the actual laws transports every Borel real observable. -/
theorem integral_profile {v : Torus → ℝ} (hv : Continuous v) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫ s, F (profile v s) ∂rankMeasure) = ∫ x, F (v x) ∂torusMeasure := by
  rw [← integral_map (profile_aemeasurable hv) hF.aestronglyMeasurable,
    profile_distribution hv, integral_map hv.measurable.aemeasurable hF.aestronglyMeasurable]

theorem integral_exp_profile {v : Torus → ℝ} (hv : Continuous v) :
    (∫ s in (0 : ℝ)..1, Real.exp (profile v s)) = ∫ x, Real.exp (v x) ∂torusMeasure := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  exact integral_profile hv Real.continuous_exp.measurable

/-- The source superlevel mass, with the original torus measure. -/
def superlevelMass (v : Torus → ℝ) (t : ℝ) : ℝ :=
  ∫ x in {x | t < v x}, Real.exp (v x) ∂torusMeasure

theorem superlevelMass_eq_cumulative {v : Torus → ℝ} (hv : Continuous v) (t : ℝ) :
    superlevelMass v t = StationaryCumulative.cumulative (profile v) (rank v t) := by
  classical
  have hobs := integral_profile hv (Real.continuous_exp.measurable.indicator measurableSet_Ioi)
    (F := (Ioi t).indicator Real.exp)
  have hright : (fun x : Torus => (Ioi t).indicator Real.exp (v x)) =
      {x : Torus | t < v x}.indicator (fun x => Real.exp (v x)) := by
    funext x
    by_cases h : t < v x <;> simp [h]
  rw [hright, integral_indicator (isOpen_lt continuous_const hv).measurableSet] at hobs
  have hleft : (fun s => (Ioi t).indicator Real.exp (profile v s)) =ᵐ[rankMeasure]
      (Ioo 0 (rank v t)).indicator (fun s => Real.exp (profile v s)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with s hs
    have he := lt_profile_iff hv hs.1.le hs.2 (t := t)
    by_cases h : t < profile v s
    · have hr : s ∈ Ioo 0 (rank v t) := ⟨hs.1, he.mp h⟩
      simp [h, hr]
    · have hr : s ∉ Ioo 0 (rank v t) := fun hr => h (he.mpr hr.2)
      simp [h, hr]
  rw [integral_congr_ae hleft, integral_indicator measurableSet_Ioo] at hobs
  have hsub : Ioo 0 (rank v t) ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hs => ⟨hs.1, hs.2.trans_le (rank_le_one v t)⟩
  change (∫ s, Real.exp (profile v s)
    ∂(volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioo 0 (rank v t))) = _ at hobs
  rw [Measure.restrict_restrict_of_subset hsub] at hobs
  rw [StationaryCumulative.cumulative, intervalIntegral.integral_of_le (rank_nonneg v t),
    ← restrict_Ioo_eq_restrict_Ioc]
  exact hobs.symm

theorem profile_endpoints_strict {v : Torus → ℝ} (hv : Continuous v)
    (hne : ¬ ∃ c : ℝ, ∀ x, v x = c) : profile v 1 < profile v 0 := by
  rw [profile_one hv, profile_zero hv]
  apply lt_of_le_of_ne (minimum_le_maximum hv)
  intro he
  apply hne
  exact ⟨minimum v, fun x => le_antisymm ((le_maximum hv x).trans he.symm.le) (minimum_le hv x)⟩

/-- Actual inverse continuity and rank order discharge every inverse hypothesis.
Only the geometric regular-value slope estimate and nullity of its exceptional
values remain upstream inputs. -/
theorem profile_lipschitz_of_slope {v : Torus → ℝ} (hv : Continuous v)
    {ε ρ : ℝ} {C : Set ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 2) (hρ : 0 < ρ)
    (hC : volume C = 0)
    (hd : ∀ t ∈ Ioo (minimum v) (maximum v), rank v t ∈ Icc ε (1 - ε) → t ∉ C →
      4 * Real.pi * ε * (1 - ε) / ρ ≤ -deriv (rank v) t) :
    LipschitzOnWith ⟨ρ / (4 * Real.pi * ε * (1 - ε)), by
      have he : 0 < 1 - ε := by linarith
      positivity⟩ (profile v) (Icc ε (1 - ε)) := by
  apply StationaryRankSlope.source_profile_lipschitz hε hεsmall hρ (rank_antitone v) hC
    (fun s hs => profile_mem_interval hv (hε.le.trans hs.1)) ?_ hd
  intro s hs t _
  exact lt_profile_iff hv (hε.le.trans hs.1) (by linarith [hs.2])

theorem profile_ac_of_slope {v : Torus → ℝ} (hv : Continuous v)
    {ρ : ℝ} {C : Set ℝ} (hρ : 0 < ρ) (hC : volume C = 0)
    (hd : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ t ∈ Ioo (minimum v) (maximum v), rank v t ∈ Icc ε (1 - ε) → t ∉ C →
        4 * Real.pi * ε * (1 - ε) / ρ ≤ -deriv (rank v) t) :
    AbsolutelyContinuousOnInterval (profile v) 0 1 := by
  apply RearrangementRegularity.ac_of_antitone_of_central_lipschitz
    (profile_continuousOn hv) (profile_antitone hv)
  intro ε he hes
  exact ⟨_, profile_lipschitz_of_slope hv he hes hρ hC (hd ε he hes)⟩

/-- At continuity values of the distribution, the actual rank and its
generalized inverse are inverse without an omitted atom. -/
theorem rank_profile_eq_of_continuousAt {v : Torus → ℝ} (hv : Continuous v)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hc : ContinuousAt (rank v) (profile v s)) : rank v (profile v s) = s := by
  apply le_antisymm (rank_profile_le hv hs)
  apply ge_of_tendsto (hc.mono_left (show 𝓝[<] (profile v s) ≤ 𝓝 (profile v s) from
    nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ((lt_profile_iff hv hs hs1).mp ht).le

theorem profile_continuousAt {v : Torus → ℝ} (hv : Continuous v)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : ContinuousAt (profile v) s :=
  (profile_continuousOn hv).continuousAt (Icc_mem_nhds hs.1 hs.2)

/-- The derivative formula for the constructed inverse follows from local
continuity of the actual rank and its nonzero derivative at the value. -/
theorem profile_hasDerivAt {v : Torus → ℝ} (hv : Continuous v)
    {s r : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hr : HasDerivAt (rank v) r (profile v s)) (hr0 : r ≠ 0)
    (hcont : ∀ᶠ t in 𝓝 (profile v s), ContinuousAt (rank v) t) :
    HasDerivAt (profile v) r⁻¹ s := by
  have hq := profile_continuousAt hv hs
  apply hr.of_local_left_inverse hq hr0
  filter_upwards [Ioo_mem_nhds hs.1 hs.2, hq hcont] with a ha hc
  exact rank_profile_eq_of_continuousAt hv ha.1.le ha.2 hc

/-- Analytic data for the actual cumulative integral. The geometric slope and
Sard inputs remain explicit; profile existence, endpoint regularity, mass,
nonconstancy and the cumulative identities are conclusions of this construction. -/
theorem cumulative_profile_data {v : Torus → ℝ} (hv : Continuous v)
    (hmass : (∫ x, Real.exp (v x) ∂torusMeasure) = 1)
    (hne : ¬ ∃ c : ℝ, ∀ x, v x = c)
    {ρ : ℝ} {C : Set ℝ} (hρ : 0 < ρ) (hC : volume C = 0)
    (hd : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ t ∈ Ioo (minimum v) (maximum v), rank v t ∈ Icc ε (1 - ε) → t ∉ C →
        4 * Real.pi * ε * (1 - ε) / ρ ≤ -deriv (rank v) t) :
    let q := profile v
    let M := StationaryCumulative.cumulative (StationaryCumulative.extendProfile q)
    AbsolutelyContinuousOnInterval M 0 1 ∧
    AbsolutelyContinuousOnInterval (deriv M) 0 1 ∧
    M 0 = 0 ∧ M 1 = 1 ∧
    (∀ s ∈ Icc (0 : ℝ) 1,
      M s = StationaryCumulative.cumulative q s ∧ deriv M s = Real.exp (q s)) ∧
    ConcaveOn ℝ univ M ∧ (∀ s ∈ Icc (0 : ℝ) 1, s ≤ M s) ∧
    0 < StationaryRearrangement.excessArea M ∧
    (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      deriv (deriv M) s = Real.exp (q s) * deriv q s ∧ 0 ≤ -deriv (deriv M) s) := by
  exact StationaryCumulative.interval_cumulative_data (profile_ac_of_slope hv hρ hC hd)
    (profile_antitone hv) ((integral_exp_profile hv).trans hmass) (profile_endpoints_strict hv hne)

end PeriodicAttractiveLogGas.StationaryDistribution
