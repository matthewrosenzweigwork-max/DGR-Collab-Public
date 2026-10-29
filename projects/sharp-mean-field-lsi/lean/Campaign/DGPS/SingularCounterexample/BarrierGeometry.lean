import DGPS.SingularCounterexample.BarrierKernel
import DGPS.SingularCounterexample.Cutoff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Local geometry of the singular barrier

The reciprocal Poisson denominator has uniformly bounded derivatives on compact parameter
sets away from collision, including the limiting radius `r = 1`. The numerator can therefore
be retained as the exact quadratic-width factor in every derivative order.
-/

open Set Filter Topology
open scoped ContDiff

namespace DGPS.SingularCounterexample

private noncomputable def peakDenominatorLift (p : ℝ × ℝ) : ℝ :=
  1 - 2 * p.1 * Real.cos (2 * Real.pi * p.2) + p.1 ^ 2

private theorem peakDenominatorLift_contDiff : ContDiff ℝ ∞ peakDenominatorLift := by
  unfold peakDenominatorLift
  fun_prop

private noncomputable def peakReciprocalDeriv (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv j (fun t : ℝ => (peakDenominatorLift (p.1, t))⁻¹) p.2

set_option backward.isDefEq.respectTransparency.types false in
private theorem reciprocal_derivative_contDiffAt (j : ℕ) (p : ℝ × ℝ)
    (hp : peakDenominatorLift p ≠ 0) :
    ContDiffAt ℝ ∞ (peakReciprocalDeriv j) p := by
  induction j generalizing p with
  | zero =>
      change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (peakDenominatorLift z)⁻¹) p
      exact peakDenominatorLift_contDiff.contDiffAt.inv hp
  | succ j ih =>
      have hm : ContDiffAt ℝ ∞
          (fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.2)) (p, p.2) :=
        contDiffAt_fst.fst.prodMk contDiffAt_snd
      have hprev := ih p hp
      have hcomp := hprev.comp (p, p.2) hm
      have hd := ContDiffAt.fderiv (m := ∞)
        (f := fun z : ℝ × ℝ => fun t : ℝ => peakReciprocalDeriv j (z.1, t))
        (g := fun z : ℝ × ℝ => z.2) hcomp contDiffAt_snd (by simp)
      have hstep : peakReciprocalDeriv (j + 1) =
          fun z : ℝ × ℝ => (fderiv ℝ
            (fun t : ℝ => peakReciprocalDeriv j (z.1, t)) z.2) 1 := by
        funext z
        simp only [peakReciprocalDeriv, iteratedDeriv_succ]
        rfl
      rw [hstep]
      exact hd.clm_apply
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)) p)

private theorem peakDenominatorLift_pos {r t : ℝ}
    (hr : (1 / 2 : ℝ) ≤ r) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < peakDenominatorLift (r, t) := by
  have hangle0 : 0 < 2 * Real.pi * t := by positivity
  have hangle1 : 2 * Real.pi * t < 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hc : Real.cos (2 * Real.pi * t) < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one _) ?_
    intro h
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hangle1).mp h
    linarith
  have hprod : 0 < 2 * r * (1 - Real.cos (2 * Real.pi * t)) :=
    mul_pos (by linarith) (sub_pos.mpr hc)
  unfold peakDenominatorLift
  dsimp only
  nlinarith [sq_nonneg (1 - r)]

/-- Uniform bounds for every reciprocal-denominator derivative on a compact fundamental
interval, with the radius allowed to reach its singular limit. -/
private theorem reciprocal_derivative_bound (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ t ∈ Icc δ (1 - δ),
      |iteratedDeriv j (fun s : ℝ => (peakDenominatorLift (r, s))⁻¹) t| ≤ C := by
  have hcompact : IsCompact (Icc (1 / 2 : ℝ) 1 ×ˢ Icc δ (1 - δ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ =>
        iteratedDeriv j (fun t : ℝ => (peakDenominatorLift (p.1, t))⁻¹) p.2)
      (Icc (1 / 2 : ℝ) 1 ×ˢ Icc δ (1 - δ)) := by
    intro p hp
    exact (reciprocal_derivative_contDiffAt j p
      (ne_of_gt (peakDenominatorLift_pos hp.1.1
        (lt_of_lt_of_le hδ hp.2.1) (by linarith [hp.2.2])))).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun r hr t ht => ?_⟩
  have hb : |iteratedDeriv j (fun s : ℝ => (peakDenominatorLift (r, s))⁻¹) t| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (r, t) ⟨hr, ht⟩
  exact hb.trans (le_max_left _ _)

/-- Every scalar derivative of a Poisson peak retains the quadratic-width factor uniformly
away from the collision point, for all radii in `[1/2,1]`. -/
theorem poissonPeak_iteratedDeriv_bound (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ t ∈ Icc δ (1 - δ),
      |iteratedDeriv j (fun s : ℝ => poissonPeak r (torusPoint s)) t| ≤
        C * (1 - r) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := reciprocal_derivative_bound j hδ
  refine ⟨C, hC0, fun r hr t ht => ?_⟩
  have hfun : (fun s : ℝ => poissonPeak r (torusPoint s)) =
      fun s : ℝ => (1 - r) ^ 2 * (peakDenominatorLift (r, s))⁻¹ := by
    funext s
    rw [poissonPeak, c1_torusPoint]
    rfl
  rw [hfun, iteratedDeriv_const_mul_field, abs_mul, abs_of_nonneg (sq_nonneg (1 - r))]
  exact (mul_le_mul_of_nonneg_left (hC r hr t ht) (sq_nonneg (1 - r))).trans_eq (by ring)

private theorem torusPoint_zero_geometry : torusPoint 0 = (0 : Circle) := by
  ext i
  simp [torusPoint, torusLift, SharpLSI.liftT]

private theorem torusDist_point_le_abs (t : ℝ) :
    torusDist (torusPoint t) 0 ≤ |t| := by
  have h := torusDist_liftT_le (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ))
  change torusDist (torusPoint t) (torusPoint 0) ≤ _ at h
  rw [torusPoint_zero_geometry] at h
  simpa [Real.sqrt_sq_eq_abs] using h

private theorem torusPoint_sub_one_geometry (t : ℝ) : torusPoint (t - 1) = torusPoint t := by
  have h := Examples.PositiveH1.Nonlinear.lift1_add_one (t - 1)
  change torusPoint (t - 1 + 1) = torusPoint (t - 1) at h
  simpa only [sub_add_cancel] using h.symm

private theorem fundamental_mem_of_distance {δ t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hd : δ ≤ torusDist (torusPoint t) 0) :
    t ∈ Icc δ (1 - δ) := by
  have hleft : δ ≤ t := hd.trans (by
    simpa only [abs_of_nonneg ht.1] using torusDist_point_le_abs t)
  have hright := torusDist_point_le_abs (t - 1)
  rw [torusPoint_sub_one_geometry, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hright
  exact ⟨hleft, by linarith⟩

/-- SLC-B001: every derivative order has a bound depending only on the order and the
positive distance from collision, uniformly in the peak index. Derivatives use the frozen
real lift at the canonical circle representative. -/
theorem poissonPeak_radius_derivative_away_zero (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x : Circle, δ ≤ torusDist x 0 →
      |iteratedDeriv j (fun s : ℝ => poissonPeak (radius n) (torusPoint s))
        (SharpLSI.secT x 0)| ≤ C * width n ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := poissonPeak_iteratedDeriv_bound j hδ
  refine ⟨C, hC0, fun n x hx => ?_⟩
  have ht : SharpLSI.secT x 0 ∈ Ioc (0 : ℝ) 1 := by
    simpa only [SharpLSI.secT, zero_add] using
      ((AddCircle.measurableEquivIoc 1 0) (x 0)).property
  have hp : torusPoint (SharpLSI.secT x 0) = x :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT x)).symm.trans
      (SharpLSI.liftT_secT x)
  have hmem : SharpLSI.secT x 0 ∈ Icc δ (1 - δ) :=
    fundamental_mem_of_distance ⟨ht.1.le, ht.2⟩ (by simpa only [hp] using hx)
  have h := hC (radius n) ⟨radius_ge_half n, (radius_lt_one n).le⟩ _ hmem
  simpa only [radius, sub_sub_cancel] using h

private noncomputable def peakLift (n : ℕ) (t : ℝ) : ℝ :=
  poissonPeak (radius n) (torusPoint t)

private noncomputable def blockLift (n : ℕ) (t : ℝ) : ℝ :=
  barrierBlock n (torusPoint t)

private theorem peakLift_smooth (n : ℕ) : ContDiff ℝ ∞ (peakLift n) := by
  have hp := poissonPeak_smooth_periodic (r := radius n)
    (by linarith [radius_ge_half n]) (radius_lt_one n)
  change ContDiff ℝ ∞ (fun v : Fin 1 → ℝ => poissonPeak (radius n) (torusLift v)) at hp
  change ContDiff ℝ ∞
    (fun t : ℝ => poissonPeak (radius n) (torusLift (fun _ : Fin 1 => t)))
  exact hp.comp (contDiff_pi.2 fun _ => contDiff_id)

private theorem blockLift_smooth (n : ℕ) : ContDiff ℝ ∞ (blockLift n) := by
  have hp := barrierBlock_smooth_periodic n
  change ContDiff ℝ ∞ (fun v : Fin 1 → ℝ => barrierBlock n (torusLift v)) at hp
  change ContDiff ℝ ∞ (fun t : ℝ => barrierBlock n (torusLift (fun _ : Fin 1 => t)))
  exact hp.comp (contDiff_pi.2 fun _ => contDiff_id)

private theorem blockLift_iteratedDeriv (j n : ℕ) (t : ℝ) :
    iteratedDeriv j (blockLift n) t = height n *
      (2 * iteratedDeriv j (peakLift n) t +
        iteratedDeriv j (peakLift n) (t - separation n) +
        iteratedDeriv j (peakLift n) (t + separation n)) := by
  have hfun : blockLift n = fun t : ℝ => height n *
      (2 * peakLift n t + peakLift n (t - separation n) + peakLift n (t + separation n)) := by
    funext t
    have hminus : torusPoint (t - separation n) =
        torusPoint t - torusPoint (separation n) :=
      Examples.PositiveH1.Nonlinear.lift1_sub t (separation n)
    have hplus : torusPoint (t + separation n) =
        torusPoint t + torusPoint (separation n) :=
      Examples.PositiveH1.Nonlinear.lift1_add t (separation n)
    simp only [blockLift, peakLift, barrierBlock, hminus, hplus]
  have hp : ContDiff ℝ (j : ℕ) (peakLift n) := (peakLift_smooth n).of_le (by simp)
  have hm : ContDiff ℝ (j : ℕ) (fun t : ℝ => peakLift n (t - separation n)) :=
    hp.comp (contDiff_id.sub contDiff_const)
  have hplus : ContDiff ℝ (j : ℕ) (fun t : ℝ => peakLift n (t + separation n)) :=
    hp.comp (contDiff_id.add contDiff_const)
  rw [hfun, iteratedDeriv_const_mul_field]
  change height n * iteratedDeriv j
    (((fun s : ℝ => 2 * peakLift n s) + (fun s : ℝ => peakLift n (s - separation n))) +
      (fun s : ℝ => peakLift n (s + separation n))) t = _
  have htwo : ContDiff ℝ (j : ℕ) (fun s : ℝ => 2 * peakLift n s) := contDiff_const.mul hp
  have hadd := iteratedDeriv_add (n := j) (x := t)
    (f := (fun s : ℝ => 2 * peakLift n s) + (fun s : ℝ => peakLift n (s - separation n)))
    (g := fun s : ℝ => peakLift n (s + separation n)) (htwo.add hm).contDiffAt hplus.contDiffAt
  have hadd' := iteratedDeriv_add (n := j) (x := t)
    (f := fun s : ℝ => 2 * peakLift n s) (g := fun s : ℝ => peakLift n (s - separation n))
    htwo.contDiffAt hm.contDiffAt
  rw [hadd, hadd']
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const,
    iteratedDeriv_comp_add_const]

/-- On a fixed compact chart away from collision, every block derivative eventually has
a summable `height * width²` bound, uniform over the entire chart. -/
theorem barrierBlock_derivative_eventually_bound (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc δ (1 - δ),
      |iteratedDeriv j (fun s : ℝ => barrierBlock n (torusPoint s)) t| ≤
        C * (height n * width n ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := poissonPeak_iteratedDeriv_bound j (show 0 < δ / 2 by linarith)
  refine ⟨4 * C, by positivity, ?_⟩
  have ha : ∀ᶠ n in atTop, separation n < δ / 2 :=
    separation_tendsto_zero.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards [ha] with n hn t ht
  have hr : radius n ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨radius_ge_half n, (radius_lt_one n).le⟩
  have hc := hC (radius n) hr t
    (show t ∈ Icc (δ / 2) (1 - δ / 2) from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hm := hC (radius n) hr (t - separation n)
    (show t - separation n ∈ Icc (δ / 2) (1 - δ / 2) from
      ⟨by linarith [ht.1], by linarith [ht.2, separation_pos n]⟩)
  have hp := hC (radius n) hr (t + separation n)
    (show t + separation n ∈ Icc (δ / 2) (1 - δ / 2) from
      ⟨by linarith [ht.1, separation_pos n], by linarith [ht.2]⟩)
  simp only [radius, sub_sub_cancel] at hc hm hp
  change |iteratedDeriv j (blockLift n) t| ≤ _
  rw [blockLift_iteratedDeriv, abs_mul, abs_of_pos (height_pos n)]
  have htri := abs_add_le
    (2 * iteratedDeriv j (peakLift n) t + iteratedDeriv j (peakLift n) (t - separation n))
    (iteratedDeriv j (peakLift n) (t + separation n))
  have htri' := abs_add_le (2 * iteratedDeriv j (peakLift n) t)
    (iteratedDeriv j (peakLift n) (t - separation n))
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at htri'
  have hs : |2 * iteratedDeriv j (peakLift n) t +
        iteratedDeriv j (peakLift n) (t - separation n) +
        iteratedDeriv j (peakLift n) (t + separation n)| ≤ 4 * C * width n ^ 2 := by
    change |iteratedDeriv j (peakLift n) t| ≤ C * width n ^ 2 at hc
    change |iteratedDeriv j (peakLift n) (t - separation n)| ≤ C * width n ^ 2 at hm
    change |iteratedDeriv j (peakLift n) (t + separation n)| ≤ C * width n ^ 2 at hp
    linarith
  exact (mul_le_mul_of_nonneg_left hs (height_pos n).le).trans_eq (by ring)

theorem compact_away_zero_distance (K : Set Circle) (hK : IsCompact K)
    (h0 : (0 : Circle) ∉ K) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ torusDist x 0 := by
  by_cases hne : K.Nonempty
  · have hcont : Continuous (fun x : Circle => torusDist x 0) := by
      simpa only [torusDist_one, Pi.zero_apply, sub_zero] using
        (continuous_apply (0 : Fin 1)).norm
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    have hx0 : x ≠ 0 := by
      intro h
      apply h0
      simpa only [h] using hx
    refine ⟨torusDist x 0,
      (dist_pos.mpr hx0).trans_le (torusDist_comparison x 0).1, fun y hy => hmin hy⟩
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

private theorem canonical_mem_of_distance {δ : ℝ} (x : Circle)
    (hx : δ ≤ torusDist x 0) : SharpLSI.secT x 0 ∈ Icc δ (1 - δ) := by
  have ht : SharpLSI.secT x 0 ∈ Ioc (0 : ℝ) 1 := by
    simpa only [SharpLSI.secT, zero_add] using
      ((AddCircle.measurableEquivIoc 1 0) (x 0)).property
  have hp : torusPoint (SharpLSI.secT x 0) = x :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT x)).symm.trans
      (SharpLSI.liftT_secT x)
  exact fundamental_mem_of_distance ⟨ht.1.le, ht.2⟩ (by simpa only [hp] using hx)

/-- SLC-B002: on every compact circle set avoiding collision, the series of every
derivative order is summable pointwise and converges uniformly. -/
theorem barrierBlock_derivatives_on_compact (j : ℕ) (K : Set Circle) (hK : IsCompact K)
    (h0 : (0 : Circle) ∉ K) :
    (∀ x ∈ K, Summable (fun n : ℕ =>
      iteratedDeriv j (fun s : ℝ => barrierBlock n (torusPoint s)) (SharpLSI.secT x 0))) ∧
    TendstoUniformlyOn
      (fun N x => ∑ n ∈ Finset.range N,
        iteratedDeriv j (fun s : ℝ => barrierBlock n (torusPoint s)) (SharpLSI.secT x 0))
      (fun x => ∑' n : ℕ,
        iteratedDeriv j (fun s : ℝ => barrierBlock n (torusPoint s)) (SharpLSI.secT x 0))
      atTop K := by
  obtain ⟨δ, hδ, hKδ⟩ := compact_away_zero_distance K hK h0
  obtain ⟨C, _, hC⟩ := barrierBlock_derivative_eventually_bound j hδ
  have hbound : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖iteratedDeriv j (fun s : ℝ => barrierBlock n (torusPoint s)) (SharpLSI.secT x 0)‖ ≤
        C * (height n * width n ^ 2) := by
    filter_upwards [hC] with n hn x hx
    simpa only [Real.norm_eq_abs] using
      hn (SharpLSI.secT x 0) (canonical_mem_of_distance x (hKδ x hx))
  have hsum := height_width_sq_summable.mul_left C
  refine ⟨fun x hx => hsum.of_norm_bounded_eventually_nat ?_,
    tendstoUniformlyOn_tsum_nat_eventually hsum hbound⟩
  filter_upwards [hbound] with n hn using hn x hx

private theorem block_derivatives_uniform_on_chart (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun N t => ∑ n ∈ Finset.range N, iteratedDeriv j (blockLift n) t)
      (fun t => ∑' n : ℕ, iteratedDeriv j (blockLift n) t) atTop (Icc δ (1 - δ)) := by
  obtain ⟨C, _, hC⟩ := barrierBlock_derivative_eventually_bound j hδ
  apply tendstoUniformlyOn_tsum_nat_eventually (height_width_sq_summable.mul_left C)
  filter_upwards [hC] with n hn t ht
  change ‖iteratedDeriv j (fun s : ℝ => barrierBlock n (torusPoint s)) t‖ ≤ _
  simpa only [Real.norm_eq_abs] using hn t ht

private noncomputable def blockDerivativeSum (j : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, iteratedDeriv j (blockLift n) t

private theorem blockDerivativeSum_continuousOn (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (blockDerivativeSum j) (Ioo δ (1 - δ)) := by
  have hu := (block_derivatives_uniform_on_chart j hδ).mono Ioo_subset_Icc_self
  apply hu.continuousOn
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun N =>
    (continuous_finsetSum _ fun n _ =>
      (blockLift_smooth n).continuous_iteratedDeriv j (by simp)).continuousOn

private theorem blockDerivativeSum_hasDerivAt (j : ℕ) {δ t : ℝ}
    (hδ : 0 < δ) (ht : t ∈ Ioo δ (1 - δ)) :
    HasDerivAt (blockDerivativeSum j) (blockDerivativeSum (j + 1) t) t := by
  have hu := (block_derivatives_uniform_on_chart (j + 1) hδ).mono Ioo_subset_Icc_self
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hu
  · refine Filter.Eventually.of_forall fun N y _ => ?_
    apply HasDerivAt.fun_sum
    intro n _
    have hd := ((blockLift_smooth n).differentiable_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))).differentiableAt (x := y) |>.hasDerivAt
    simpa only [iteratedDeriv_succ] using hd
  · intro y hy
    exact (block_derivatives_uniform_on_chart j hδ).tendsto_at ⟨hy.1.le, hy.2.le⟩
  · exact ht

private theorem blockDerivativeSum_smooth_on_chart {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ContDiffOn ℝ ∞ (blockDerivativeSum j) (Ioo δ (1 - δ)) := by
  have hfinite : ∀ m : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ (m : ℕ) (blockDerivativeSum k) (Ioo δ (1 - δ)) := by
    intro m
    induction m with
    | zero =>
        intro k
        exact contDiffOn_zero.mpr (blockDerivativeSum_continuousOn k hδ)
    | succ m ih =>
        intro k
        have hc : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (blockDerivativeSum k)
            (Ioo δ (1 - δ)) := by
          apply (contDiffOn_succ_iff_derivWithin (n := (m : ℕ)) isOpen_Ioo.uniqueDiffOn).mpr
          refine ⟨?_, by simp, ?_⟩
          · intro t ht
            exact (blockDerivativeSum_hasDerivAt k hδ ht).differentiableAt.differentiableWithinAt
          · apply (ih (k + 1)).congr
            intro t ht
            exact (blockDerivativeSum_hasDerivAt k hδ ht).hasDerivWithinAt.derivWithin
              (isOpen_Ioo.uniqueDiffOn t ht)
        simpa only [Nat.cast_add, Nat.cast_one] using hc
  exact contDiffOn_infty.mpr fun m => hfinite m j

private theorem torusPoint_ne_zero_of_fundamental {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    torusPoint t ≠ (0 : Circle) := by
  intro h
  have hc : Real.cos (2 * Real.pi * t) = 1 := by rw [← c1_torusPoint, h, c1_zero]
  have hd := peakDenominatorLift_pos (r := 1) (by norm_num) ht0 ht1
  norm_num [peakDenominatorLift, hc] at hd

private theorem barrier_smooth_on_chart {δ : ℝ} (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => barrier (torusPoint t)) (Ioo δ (1 - δ)) := by
  apply (blockDerivativeSum_smooth_on_chart hδ 0).congr
  intro t ht
  have hp := torusPoint_ne_zero_of_fundamental
    (lt_trans hδ ht.1) (by linarith [ht.2])
  change barrier (torusPoint t) = ∑' n : ℕ, iteratedDeriv 0 (blockLift n) t
  simp only [barrier, ite_eq_right hp, iteratedDeriv_zero, blockLift]

private theorem barrier_contDiffAt_fundamental {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ContDiffAt ℝ ∞ (fun s : ℝ => barrier (torusPoint s)) t := by
  let δ := min t (1 - t) / 2
  have hδ : 0 < δ := div_pos (lt_min ht0 (sub_pos.mpr ht1)) (by norm_num)
  have ht : t ∈ Ioo δ (1 - δ) := by
    have hmin := min_le_left t (1 - t)
    have hmin' := min_le_right t (1 - t)
    constructor <;> dsimp [δ] <;> linarith
  exact (barrier_smooth_on_chart hδ).contDiffAt (isOpen_Ioo.mem_nhds ht)

/-- SLC-B003: the barrier is `C∞` off collision, in the periodic real lift at every
noncollision lift point. -/
theorem barrier_smooth_off_collision :
    ContDiffOn ℝ ∞ (fun t : ℝ => barrier (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
  intro t ht
  let u := SharpLSI.secT (torusPoint t) 0
  have hu : u ∈ Ioc (0 : ℝ) 1 := by
    simpa only [u, SharpLSI.secT, zero_add] using
      ((AddCircle.measurableEquivIoc 1 0) ((torusPoint t) 0)).property
  have hup : torusPoint u = torusPoint t :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT (torusPoint t))).symm.trans
      (SharpLSI.liftT_secT (torusPoint t))
  have hu1 : u < 1 := by
    refine lt_of_le_of_ne hu.2 ?_
    intro heq
    have hpoint1 : torusPoint 1 = (0 : Circle) := by
      have h := torusPoint_sub_one_geometry 1
      simpa only [sub_self, torusPoint_zero_geometry] using h.symm
    exact ht (hup.symm.trans (by simpa only [heq] using hpoint1))
  obtain ⟨k, hk⟩ := Examples.PositiveH1.Nonlinear.lift1_eq_iff hup.symm
  have hperiod : Function.Periodic torusPoint 1 := Examples.PositiveH1.Nonlinear.lift1_add_one
  have hshift (s : ℝ) : torusPoint (s - (k : ℝ)) = torusPoint s := by
    simpa only [Int.cast_neg, mul_one, sub_eq_add_neg] using hperiod.int_mul (-k) s
  have hbase := barrier_contDiffAt_fundamental hu.1 hu1
  have hbase' : ContDiffAt ℝ ∞ (fun s : ℝ => barrier (torusPoint s)) (t - (k : ℝ)) := by
    have htk : t - (k : ℝ) = u := by linarith only [hk]
    rw [htk]
    exact hbase
  have hc := hbase'.comp t (contDiffAt_id.sub contDiffAt_const)
  have hfun : (fun s : ℝ => barrier (torusPoint (s - (k : ℝ)))) =
      fun s : ℝ => barrier (torusPoint s) := by
    funext s
    rw [hshift]
  change ContDiffAt ℝ ∞ (fun s : ℝ => barrier (torusPoint (s - (k : ℝ)))) t at hc
  rw [hfun] at hc
  exact hc.contDiffWithinAt

/-- Uniform boundedness of the barrier at every fixed positive distance from collision. -/
theorem barrier_bound_away_zero {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Circle, δ ≤ torusDist x 0 → barrier x ≤ C := by
  let K : Set Circle := {x | δ ≤ torusDist x 0}
  have hdcont : Continuous (fun x : Circle => torusDist x 0) := by
    simpa only [torusDist_one, Pi.zero_apply, sub_zero] using
      (continuous_apply (0 : Fin 1)).norm
  have hK : IsCompact K := (isClosed_le continuous_const hdcont).isCompact
  have h0 : (0 : Circle) ∉ K := by
    intro hx
    change δ ≤ torusDist (0 : Circle) 0 at hx
    have hz : torusDist (0 : Circle) 0 = 0 := by simp [torusDist_one]
    rw [hz] at hx
    linarith
  have hp (x : Circle) : torusPoint (SharpLSI.secT x 0) = x :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT x)).symm.trans
      (SharpLSI.liftT_secT x)
  have hu := (barrierBlock_derivatives_on_compact 0 K hK h0).2
  simp only [iteratedDeriv_zero, hp] at hu
  have hcontinuous : ContinuousOn (fun x => ∑' n : ℕ, barrierBlock n x) K := by
    apply hu.continuousOn
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall fun N =>
      (continuous_finsetSum _ fun n _ =>
        SharpLSI.continuous_of_liftT' (barrierBlock_smooth_periodic n).continuous).continuousOn
  have hbcont : ContinuousOn barrier K := by
    apply hcontinuous.congr
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      apply h0
      simpa only [h] using hx
    simp only [barrier, ite_eq_right hx0]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hbcont
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hbound : |barrier x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
  exact (le_abs_self _).trans (hbound.trans (le_max_left _ _))

private theorem cutoff_derivative_periodic_geometry (n : ℕ) :
    Function.Periodic (deriv (cutoffLine n)) 1 := by
  intro t
  have hfun : (fun s : ℝ => cutoffLine n (s + 1)) = cutoffLine n :=
    funext (cutoffLine_periodic n)
  have h := congrArg (fun f : ℝ → ℝ => iteratedDeriv 1 f) hfun
  rw [iteratedDeriv_comp_add_const] at h
  simpa only [iteratedDeriv_one] using congrFun h t

private theorem cutoff_derivative_zero_geometry (n : ℕ) : deriv (cutoffLine n) 0 = 0 := by
  have hfun : (fun s : ℝ => cutoffLine n (-s)) = cutoffLine n :=
    funext (cutoffLine_even n)
  have h := congrArg (fun f : ℝ → ℝ => deriv f 0) hfun
  rw [deriv_comp_neg] at h
  simp only [neg_zero] at h
  linarith

private theorem barrier_lower_of_peak (n : ℕ) {x : Circle} (hx : x ≠ 0)
    (hpeak : 1 / 65 ≤ poissonPeak (radius n) x ∨
      1 / 65 ≤ poissonPeak (radius n) (x - torusPoint (separation n)) ∨
      1 / 65 ≤ poissonPeak (radius n) (x + torusPoint (separation n))) :
    height n / 65 ≤ barrier x := by
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hc := (poissonPeak_pos hr0 (radius_lt_one n) x).le
  have hm := (poissonPeak_pos hr0 (radius_lt_one n) (x - torusPoint (separation n))).le
  have hp := (poissonPeak_pos hr0 (radius_lt_one n) (x + torusPoint (separation n))).le
  have hs : 1 / 65 ≤ 2 * poissonPeak (radius n) x +
      poissonPeak (radius n) (x - torusPoint (separation n)) +
      poissonPeak (radius n) (x + torusPoint (separation n)) := by
    rcases hpeak with h | h | h <;> linarith
  calc
    height n / 65 = height n * (1 / 65) := by ring
    _ ≤ barrierBlock n x := mul_le_mul_of_nonneg_left hs (height_pos n).le
    _ ≤ barrier x := barrierBlock_le_barrier hx n

private theorem barrier_lower_on_cutoff_derivative_Ioc (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) (hderiv : deriv (cutoffLine n) t ≠ 0) :
    height n / 65 ≤ barrier (torusPoint t) := by
  have ht1 : t < 1 := by
    refine lt_of_le_of_ne ht.2 ?_
    intro heq
    apply hderiv
    have hper : deriv (cutoffLine n) 1 = deriv (cutoffLine n) 0 := by
      simpa only [zero_add] using cutoff_derivative_periodic_geometry n 0
    rw [heq, hper, cutoff_derivative_zero_geometry]
  apply barrier_lower_of_peak n (torusPoint_ne_zero_of_fundamental ht.1 ht1)
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have heps : width n = 1 - radius n := by simp only [radius, sub_sub_cancel]
  have hnear (s : ℝ) (hs : |s| ≤ width n) :
      1 / 65 ≤ poissonPeak (radius n) (torusPoint s) :=
    poissonPeak_near_peak_lower hr0 (radius_lt_one n) heps (torusPoint s)
      ((torusDist_comparison (torusPoint s) 0).1.trans
        ((torusDist_point_le_abs s).trans hs))
  rcases cutoffLine_deriv_support_on_Ioc ht hderiv with h | h | h | h
  · left
    exact hnear t (by simpa only [abs_of_nonneg h.1] using h.2)
  · right
    left
    have hs : torusPoint (t - separation n) =
        torusPoint t - torusPoint (separation n) :=
      Examples.PositiveH1.Nonlinear.lift1_sub t (separation n)
    have hb := hnear (t - separation n) (abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)
    simpa only [hs] using hb
  · right
    right
    have hs : torusPoint (t + separation n - 1) =
        torusPoint t + torusPoint (separation n) :=
      (torusPoint_sub_one_geometry (t + separation n)).trans
        (Examples.PositiveH1.Nonlinear.lift1_add t (separation n))
    have hb := hnear (t + separation n - 1)
      (abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)
    simpa only [hs] using hb
  · left
    have hb := hnear (t - 1)
      (abs_le.mpr ⟨by linarith [h.1], by linarith [h.2, width_pos n]⟩)
    simpa only [torusPoint_sub_one_geometry] using hb

/-- SLC-B011: every real-lift point where the cutoff derivative is nonzero has a
uniform height barrier. Periodic normalization retains the collision representative. -/
theorem barrier_lower_on_cutoff_derivative (n : ℕ) (t : ℝ)
    (hderiv : deriv (cutoffLine n) t ≠ 0) : height n / 65 ≤ barrier (torusPoint t) := by
  let x := torusPoint t
  let u := SharpLSI.secT x 0
  have hu : u ∈ Ioc (0 : ℝ) 1 := by
    simpa only [u, SharpLSI.secT, zero_add] using
      ((AddCircle.measurableEquivIoc 1 0) (x 0)).property
  have hup : torusPoint u = x :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT x)).symm.trans
      (SharpLSI.liftT_secT x)
  obtain ⟨k, hk⟩ := Examples.PositiveH1.Nonlinear.lift1_eq_iff hup.symm
  have hperiod := cutoff_derivative_periodic_geometry n
  have hdt : deriv (cutoffLine n) t = deriv (cutoffLine n) u :=
    (congrArg (deriv (cutoffLine n)) hk).trans
      (by simpa only [mul_one] using hperiod.int_mul k u)
  have hdu : deriv (cutoffLine n) u ≠ 0 := fun hz => hderiv (hdt.trans hz)
  have h := barrier_lower_on_cutoff_derivative_Ioc n hu hdu
  rw [hup] at h
  exact h

private theorem separation_small_geometry (n : ℕ) : separation n ≤ 1 / 10000 := by
  have h := separation_le_ten_neg_four n
  norm_num [Real.rpow_neg, Real.rpow_natCast] at h
  exact h

private theorem dist_point_eq_abs_geometry {t : ℝ} (ht : |t| ≤ 1 / 2) :
    dist (torusPoint t) 0 = |t| := by
  have h := torusDist_liftT_eq (x := fun _ : Fin 1 => t) (y := fun _ : Fin 1 => (0 : ℝ))
    (fun _ => by simpa only [sub_zero] using ht)
  change torusDist (torusPoint t) (torusPoint 0) = _ at h
  rw [torusPoint_zero_geometry] at h
  have heq : torusDist (torusPoint t) 0 = |t| := by simpa [Real.sqrt_sq_eq_abs] using h
  have hcomp := torusDist_comparison (torusPoint t) 0
  exact (le_antisymm hcomp.1 (by simpa using hcomp.2)).trans heq

private theorem valley_lift_noncollision (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (separation n / 3) (2 * separation n / 3)) : torusPoint t ≠ 0 :=
  torusPoint_ne_zero_of_fundamental
    (by linarith [ht.1, separation_pos n])
    (by linarith [ht.2, separation_small_geometry n])

private theorem block_valley_upper_geometry (n j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (separation n / 3) (2 * separation n / 3))
    (hcenter : separation j = separation n ∨ separation j ≤ separation n / 10) :
    barrierBlock j (torusPoint t) ≤ 18 * height j * width j ^ 2 / separation n ^ 2 := by
  let a := separation n
  let b := separation j
  change t ∈ Icc (a / 3) (2 * a / 3) at ht
  change b = a ∨ b ≤ a / 10 at hcenter
  have ha : 0 < a := separation_pos n
  have hb : 0 < b := separation_pos j
  have hasmall : a ≤ 1 / 10000 := separation_small_geometry n
  have hba : b ≤ a := by
    rcases hcenter with h | h
    · exact h.le
    · linarith
  have hsumsmall : t + b ≤ 1 / 2 := by linarith [ht.2]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hr0 : 0 < radius j := by linarith [radius_ge_half j]
  have heps : width j = 1 - radius j := by simp only [radius, sub_sub_cancel]
  have hepshalf : width j ≤ 1 / 2 := by
    have h := radius_ge_half j
    simp only [radius] at h
    linarith
  have hfar (s : ℝ) (hsmall : |s| ≤ 1 / 2) (hd : a / 6 ≤ |s|) :
      poissonPeak (radius j) (torusPoint s) ≤ width j ^ 2 / (8 * (a / 6) ^ 2) :=
    poissonPeak_away_upper hr0 (radius_lt_one j) heps hepshalf (by positivity)
      (torusPoint s) (by rw [dist_point_eq_abs_geometry hsmall]; exact hd)
  have hc := hfar t (by rw [abs_of_nonneg ht0]; linarith)
    (by rw [abs_of_nonneg ht0]; linarith [ht.1])
  have hminusfar : a / 6 ≤ |t - b| := by
    rcases hcenter with h | h
    · rw [h, abs_of_nonpos (by linarith [ht.2] : t - a ≤ 0)]
      linarith [ht.2]
    · rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - b)]
      linarith [ht.1]
  have hm := hfar (t - b) (abs_le.mpr ⟨by linarith, by linarith⟩) hminusfar
  have hp := hfar (t + b) (by rw [abs_of_nonneg (by positivity)]; exact hsumsmall)
    (by rw [abs_of_nonneg (by positivity)]; linarith [ht.1])
  have hminus : torusPoint (t - b) = torusPoint t - torusPoint (separation j) :=
    Examples.PositiveH1.Nonlinear.lift1_sub t (separation j)
  have hplus : torusPoint (t + b) = torusPoint t + torusPoint (separation j) :=
    Examples.PositiveH1.Nonlinear.lift1_add t (separation j)
  rw [hminus] at hm
  rw [hplus] at hp
  have hs : 2 * poissonPeak (radius j) (torusPoint t) +
      poissonPeak (radius j) (torusPoint t - torusPoint (separation j)) +
      poissonPeak (radius j) (torusPoint t + torusPoint (separation j)) ≤
        4 * (width j ^ 2 / (8 * (a / 6) ^ 2)) := by linarith
  calc
    barrierBlock j (torusPoint t) ≤ height j * (4 * (width j ^ 2 / (8 * (a / 6) ^ 2))) :=
      mul_le_mul_of_nonneg_left hs (height_pos j).le
    _ = 18 * height j * width j ^ 2 / separation n ^ 2 := by
      change _ = 18 * height j * width j ^ 2 / a ^ 2
      field_simp [ne_of_gt ha]
      ring

/-- SLC-B012: the block indexed by the valley scale has a quadratic tail cost there. -/
theorem barrierBlock_valley_upper (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (separation n / 3) (2 * separation n / 3)) :
    barrierBlock n (torusPoint t) ≤ 18 * height n * width n ^ 2 / separation n ^ 2 :=
  block_valley_upper_geometry n n ht (Or.inl rfl)

private theorem separation_succ_geometry (n : ℕ) :
    separation (n + 1) = separation n / 10 := by
  simp only [separation]
  rw [show shiftedIndex (n + 1) = shiftedIndex n + 1 by simp [shiftedIndex, Nat.add_assoc],
    pow_succ, mul_inv]
  ring

theorem barrierBlock_later_valley_upper (n j : ℕ) (hj : n < j) {t : ℝ}
    (ht : t ∈ Icc (separation n / 3) (2 * separation n / 3)) :
    barrierBlock j (torusPoint t) ≤ 18 * height j * width j ^ 2 / separation n ^ 2 := by
  have hmono := (strictAnti_nat_of_succ_lt separation_succ_lt).antitone
  apply block_valley_upper_geometry n j ht
  right
  exact (hmono (Nat.succ_le_of_lt hj)).trans_eq (separation_succ_geometry n)

/-- SLC-B013: all later blocks have one common valley distance and a summable tail cost. -/
theorem barrierBlock_valley_tail_upper (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (separation n / 3) (2 * separation n / 3)) :
    (∑' m : ℕ, barrierBlock (m + (n + 1)) (torusPoint t)) ≤
      18 / separation n ^ 2 *
        ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1)) ^ 2 := by
  have hinj : Function.Injective (fun m : ℕ => m + (n + 1)) := fun i j h => Nat.add_right_cancel h
  have hblock := (barrierBlock_summable (valley_lift_noncollision n ht)).comp_injective hinj
  have hmajor := (height_width_sq_summable.comp_injective hinj).mul_left (18 / separation n ^ 2)
  have h := Summable.tsum_le_tsum (f := fun m : ℕ => barrierBlock (m + (n + 1)) (torusPoint t))
    (g := fun m : ℕ => 18 / separation n ^ 2 *
      (height (m + (n + 1)) * width (m + (n + 1)) ^ 2))
    (fun m => by
      have hm := barrierBlock_later_valley_upper n (m + (n + 1)) (by omega) ht
      convert hm using 1
      ring) hblock hmajor
  simpa only [tsum_mul_left] using h

/-- The complete valley cost: earlier heights, the current block tail, and every later tail. -/
noncomputable def valleyCost (n : ℕ) : ℝ :=
  4 * previousHeightSum n + 18 * (height n * width n ^ 2 / separation n ^ 2) +
    18 / separation n ^ 2 *
      ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1)) ^ 2

theorem valleyCost_nonneg (n : ℕ) : 0 ≤ valleyCost n := by
  have hp := previousHeightSum_nonneg n
  have hh := (height_pos n).le
  have ht : 0 ≤ ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1)) ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (height_pos _).le (sq_nonneg _)
  unfold valleyCost
  positivity

/-- The actual barrier obeys the complete cost bound on the favorable plateau. -/
theorem barrier_valley_upper (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (separation n / 3) (2 * separation n / 3)) :
    barrier (torusPoint t) ≤ valleyCost n := by
  have hx := valley_lift_noncollision n ht
  have hsum := (barrierBlock_summable hx).sum_add_tsum_nat_add (n + 1)
  rw [Finset.sum_range_succ] at hsum
  have hseries : barrier (torusPoint t) =
      (∑ j ∈ Finset.range n, barrierBlock j (torusPoint t)) + barrierBlock n (torusPoint t) +
        ∑' m : ℕ, barrierBlock (m + (n + 1)) (torusPoint t) := by
    rw [barrier, ite_eq_right hx]
    exact hsum.symm
  have hearlier : (∑ j ∈ Finset.range n, barrierBlock j (torusPoint t)) ≤
      4 * previousHeightSum n := by
    unfold previousHeightSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => barrierBlock_le_four_height j (torusPoint t)
  have hself := barrierBlock_valley_upper n ht
  have hself' : barrierBlock n (torusPoint t) ≤
      18 * (height n * width n ^ 2 / separation n ^ 2) := by
    convert hself using 1
    ring
  have htail := barrierBlock_valley_tail_upper n ht
  rw [hseries]
  unfold valleyCost
  linarith only [hearlier, hself', htail]

private theorem width_le_separation_sq_geometry (n : ℕ) : width n ≤ separation n ^ 2 := by
  have htwo : 2 ≤ (n + 3).factorial := by
    simpa only [Nat.factorial_two] using Nat.factorial_le (show 2 ≤ n + 3 by omega)
  have hfac : 2 * shiftedIndex n ≤ (shiftedIndex n).factorial := by
    change 2 * (n + 4) ≤ (n + 4).factorial
    have hstep : (n + 4).factorial = (n + 4) * (n + 3).factorial := by
      convert Nat.factorial_succ (n + 3) using 1
    rw [hstep]
    nlinarith [Nat.mul_le_mul_left (n + 4) htwo]
  have hp : (10 : ℝ) ^ (2 * shiftedIndex n) ≤ (10 : ℝ) ^ (shiftedIndex n).factorial := by
    gcongr
    · norm_num
  have hi := (inv_le_inv₀ (by positivity : 0 < (10 : ℝ) ^ (shiftedIndex n).factorial)
    (by positivity : 0 < (10 : ℝ) ^ (2 * shiftedIndex n))).mpr hp
  have heq : (10 : ℝ) ^ (2 * shiftedIndex n) = ((10 : ℝ) ^ shiftedIndex n) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [heq] at hi
  simpa only [width, separation, inv_pow] using hi

private theorem width_antitone_geometry {n j : ℕ} (hj : n ≤ j) : width j ≤ width n := by
  have hfac : (shiftedIndex n).factorial ≤ (shiftedIndex j).factorial :=
    Nat.factorial_le (shiftedIndex_monotone hj)
  have hp : (10 : ℝ) ^ (shiftedIndex n).factorial ≤ (10 : ℝ) ^ (shiftedIndex j).factorial := by
    gcongr
    · norm_num
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hp

private theorem height_ge_one_geometry (n : ℕ) : 1 ≤ height n := by
  have hfac : (1 : ℝ) ≤ ((shiftedIndex n).factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (shiftedIndex n)))
  unfold height
  nlinarith

private theorem valleyCost_ratio_upper (n : ℕ) :
    valleyCost n / height n ≤ 4 * (previousHeightSum n / height n) + 18 * width n +
      18 * ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1)) := by
  let T₁ := ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1))
  let T₂ := ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1)) ^ 2
  have hT₁ : 0 ≤ T₁ := tsum_nonneg fun m =>
    mul_nonneg (height_pos _).le (width_pos _).le
  have hinj : Function.Injective (fun m : ℕ => m + (n + 1)) := fun i j h => Nat.add_right_cancel h
  have hquad := height_width_sq_summable.comp_injective hinj
  have hlin := (height_width_summable.comp_injective hinj).mul_left (separation n ^ 2)
  have htail : T₂ ≤ separation n ^ 2 * T₁ := by
    have h := Summable.tsum_le_tsum
      (f := fun m : ℕ => height (m + (n + 1)) * width (m + (n + 1)) ^ 2)
      (g := fun m : ℕ => separation n ^ 2 *
        (height (m + (n + 1)) * width (m + (n + 1))))
      (fun m => by
        have hw := (width_antitone_geometry (show n ≤ m + (n + 1) by omega)).trans
          (width_le_separation_sq_geometry n)
        have hm := mul_le_mul_of_nonneg_right hw
          (mul_nonneg (height_pos (m + (n + 1))).le (width_pos (m + (n + 1))).le)
        convert hm using 1
        ring) hquad hlin
    simpa only [tsum_mul_left] using h
  have ha2 : 0 < separation n ^ 2 := sq_pos_of_pos (separation_pos n)
  have hself : width n ^ 2 / separation n ^ 2 ≤ width n := by
    apply (div_le_iff₀ ha2).mpr
    have hm := mul_le_mul_of_nonneg_left (width_le_separation_sq_geometry n) (width_pos n).le
    nlinarith
  have htailquot : T₂ / separation n ^ 2 ≤ T₁ := (div_le_iff₀ ha2).mpr (by nlinarith [htail])
  have htaildiv : (T₂ / separation n ^ 2) / height n ≤ T₁ := by
    apply (div_le_iff₀ (height_pos n)).mpr
    have hm := mul_nonneg hT₁ (sub_nonneg.mpr (height_ge_one_geometry n))
    nlinarith
  have heq : valleyCost n / height n =
      4 * (previousHeightSum n / height n) + 18 * (width n ^ 2 / separation n ^ 2) +
        18 * ((T₂ / separation n ^ 2) / height n) := by
    unfold valleyCost
    change (4 * previousHeightSum n + 18 * (height n * width n ^ 2 / separation n ^ 2) +
      18 / separation n ^ 2 * T₂) / height n = _
    field_simp [ne_of_gt (height_pos n), ne_of_gt (separation_pos n)]
  rw [heq]
  change _ ≤ 4 * (previousHeightSum n / height n) + 18 * width n + 18 * T₁
  linarith

/-- SLC-B014: the complete favorable-valley cost is negligible relative to the barrier
height, including both the self-error and the infinite later tail. -/
theorem valleyCost_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => valleyCost n / height n) atTop (𝓝 0) := by
  have htail : Tendsto
      (fun n : ℕ => ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (height_width_rpow_tail_tendsto_zero (α := 1) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun n : ℕ => 4 * (previousHeightSum n / height n) + 18 * width n +
        18 * ∑' m : ℕ, height (m + (n + 1)) * width (m + (n + 1))) atTop (𝓝 0) := by
    simpa using ((previousHeightSum_ratio_tendsto_zero.const_mul 4).add
      (width_tendsto_zero.const_mul 18)).add (htail.const_mul 18)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => div_nonneg (valleyCost_nonneg n) (height_pos n).le) valleyCost_ratio_upper

end DGPS.SingularCounterexample
