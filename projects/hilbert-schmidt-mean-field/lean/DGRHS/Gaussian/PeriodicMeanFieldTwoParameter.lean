import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
Packet P11e, unit 1 (part 2): a two-parameter chain rule.

This is the one-dimensional calculus behind the moving-test step of the proof of Proposition 8.2
(TeX 3922-3924, "for the time-dependent test `f^r` the additional drift ... cancels").  Let
`H r s` be the pairing of the frozen test `f^s` with the law `μ^r`.  Suppose `H · s` is a primitive of
`a · s` (the static weak mean-field equation tested against the `C²` function `f^s`), `H r ·` is a
primitive of `b r ·` (the time derivative of the test integrated against `μ^r`), `b` is jointly continuous
and `a u ·` is uniformly continuous in the frozen test, uniformly in `u` (the `C²` dependence of the
static drift on the test).  Then `r ↦ H r r` has the integrated derivative `a u u + b u u`:
`H t t - H 0 0 = ∫_0^t (a u u + b u u) du`.  The proof is by telescoping on a uniform partition; no
differentiability of `r ↦ a u u` and no Lebesgue differentiation is used, and the integrability of the
diagonal `u ↦ a u u` is obtained as a uniform limit of step functions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace DGRHS.Periodic

/-- The left endpoint of the `k`-th cell of the uniform partition of `[0,t]` into `n` cells. -/
def partitionPoint (t : ℝ) (n k : ℕ) : ℝ := (k : ℝ) * t / (n : ℝ)

lemma partitionPoint_mem (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n) :
    partitionPoint t n k ∈ Icc 0 t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold partitionPoint
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn']
  have : (k : ℝ) ≤ n := by exact_mod_cast hk
  nlinarith

lemma partitionPoint_succ_sub (t : ℝ) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    partitionPoint t n (k + 1) - partitionPoint t n k = t / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold partitionPoint
  push_cast
  field_simp
  ring

lemma partitionPoint_zero (t : ℝ) (n : ℕ) : partitionPoint t n 0 = 0 := by
  simp [partitionPoint]

lemma partitionPoint_last (t : ℝ) (n : ℕ) (hn : 1 ≤ n) : partitionPoint t n n = t := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold partitionPoint
  field_simp

lemma partitionPoint_floor (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : u ∈ Ico 0 t) :
    ∃ k < n, u ∈ Ico (partitionPoint t n k) (partitionPoint t n (k + 1)) ∧
      ∀ j, u ∈ Ico (partitionPoint t n j) (partitionPoint t n (j + 1)) → j = k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set w : ℝ := u * n / t with hw
  have hw0 : 0 ≤ w := by
    have := hu.1
    positivity
  have hwn : w < n := by
    rw [hw, div_lt_iff₀ ht]
    nlinarith [hu.2]
  refine ⟨⌊w⌋₊, ?_, ?_, ?_⟩
  · have := Nat.floor_lt hw0 |>.mpr (by exact_mod_cast hwn)
    exact this
  · have h1 := Nat.floor_le hw0
    have h2 := Nat.lt_floor_add_one w
    unfold partitionPoint
    constructor
    · rw [div_le_iff₀ hn']
      have : (⌊w⌋₊ : ℝ) * t ≤ w * t := mul_le_mul_of_nonneg_right h1 ht.le
      have e : w * t = u * n := by rw [hw]; field_simp
      nlinarith
    · rw [lt_div_iff₀ hn']
      have : w * t < ((⌊w⌋₊ : ℝ) + 1) * t := mul_lt_mul_of_pos_right h2 ht
      have e : w * t = u * n := by rw [hw]; field_simp
      push_cast
      nlinarith
  · intro j hj
    have hj1 : (j : ℝ) * t / n ≤ u := hj.1
    have hj2 : u < ((j + 1 : ℕ) : ℝ) * t / n := hj.2
    rw [div_le_iff₀ hn'] at hj1
    rw [lt_div_iff₀ hn'] at hj2
    push_cast at hj2
    have e : w * t = u * n := by rw [hw]; field_simp
    have a1 : (j : ℝ) ≤ w := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have a2 : w < (j : ℝ) + 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact ((Nat.floor_eq_iff hw0).mpr ⟨a1, a2⟩).symm

/-- Integrability of the diagonal as a uniform limit of step functions. -/
lemma diagonal_intervalIntegrable (t : ℝ) (ht : 0 ≤ t) (a : ℝ → ℝ → ℝ) (A : ℝ)
    (ha_int : ∀ s ∈ Icc 0 t, IntervalIntegrable (fun u => a u s) volume 0 t)
    (haA : ∀ u ∈ Icc 0 t, ∀ s ∈ Icc 0 t, |a u s| ≤ A)
    (hauc : ∀ ε > 0, ∃ η > 0, ∀ u ∈ Icc 0 t, ∀ s ∈ Icc 0 t, ∀ s' ∈ Icc 0 t, |s - s'| < η →
      |a u s - a u s'| ≤ ε) :
    IntervalIntegrable (fun u => a u u) volume 0 t := by
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    exact IntervalIntegrable.refl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  set μ0 : Measure ℝ := volume.restrict (Ioc 0 t) with hμ0
  let φ : ℕ → ℝ → ℝ := fun n u => ∑ k ∈ Finset.range n,
    (Ico (partitionPoint t n k) (partitionPoint t n (k + 1))).indicator
      (fun u => a u (partitionPoint t n k)) u
  have hφm : ∀ n, AEStronglyMeasurable (φ n) μ0 := by
    intro n
    refine Finset.aestronglyMeasurable_fun_sum _ (fun k hk => ?_)
    by_cases hn : 1 ≤ n
    · have hkn : k ≤ n := (Finset.mem_range.mp hk).le
      have hs := partitionPoint_mem t ht n hn k hkn
      exact ((ha_int _ hs).1.aestronglyMeasurable).indicator measurableSet_Ico
    · have : n = 0 := by omega
      subst this
      simp at hk
  have hlim : ∀ᵐ u ∂μ0, Tendsto (fun n => φ n u) atTop (𝓝 (a u u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with u hu hne
    have huI : u ∈ Ico 0 t := ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩
    have huc : u ∈ Icc 0 t := ⟨huI.1, huI.2.le⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨η, hη, hηa⟩ := hauc (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (t / η)
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hNn : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hsmall : t / n < η := by
      rw [div_lt_iff₀ hnpos]
      have h1 : t < N * η := by
        have := (div_lt_iff₀ hη).mp hN
        linarith
      nlinarith
    obtain ⟨k, hkn, hk, huniq⟩ := partitionPoint_floor t htpos n hn1 u huI
    have hφ : φ n u = a u (partitionPoint t n k) := by
      simp only [φ]
      rw [Finset.sum_eq_single k]
      · simp [indicator_of_mem hk]
      · intro j _ hjk
        have : u ∉ Ico (partitionPoint t n j) (partitionPoint t n (j + 1)) := fun hj =>
          hjk (huniq j hj)
        simp [indicator_of_notMem this]
      · intro hk'
        exact absurd (Finset.mem_range.mpr hkn) hk'
    rw [hφ, Real.dist_eq]
    have hrk := partitionPoint_mem t ht n hn1 k hkn.le
    have hdiff : |partitionPoint t n k - u| < η := by
      have h1 := partitionPoint_succ_sub t n hn1 k
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hk.1)]
      linarith [hk.2]
    have := hηa u huc _ hrk u huc hdiff
    linarith
  have hmeas : AEStronglyMeasurable (fun u => a u u) μ0 :=
    aestronglyMeasurable_of_tendsto_ae atTop hφm hlim
  refine Integrable.mono' (integrable_const A) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs]
  exact haA u ⟨hu.1.le, hu.2⟩ u ⟨hu.1.le, hu.2⟩

/-- **Two-parameter chain rule.** -/
theorem two_parameter_chain_rule (t : ℝ) (ht : 0 ≤ t) (H a b : ℝ → ℝ → ℝ) (A : ℝ)
    (ha_int : ∀ s ∈ Icc 0 t, IntervalIntegrable (fun u => a u s) volume 0 t)
    (hHr : ∀ s ∈ Icc 0 t, ∀ r ∈ Icc 0 t, ∀ r' ∈ Icc 0 t, H r s - H r' s = ∫ u in r'..r, a u s)
    (hb : ContinuousOn (fun p : ℝ × ℝ => b p.1 p.2) (Icc 0 t ×ˢ Icc 0 t))
    (hHs : ∀ r ∈ Icc 0 t, ∀ s ∈ Icc 0 t, ∀ s' ∈ Icc 0 t, H r s - H r s' = ∫ v in s'..s, b r v)
    (haA : ∀ u ∈ Icc 0 t, ∀ s ∈ Icc 0 t, |a u s| ≤ A)
    (hauc : ∀ ε > 0, ∃ η > 0, ∀ u ∈ Icc 0 t, ∀ s ∈ Icc 0 t, ∀ s' ∈ Icc 0 t, |s - s'| < η →
      |a u s - a u s'| ≤ ε) :
    IntervalIntegrable (fun u => a u u + b u u) volume 0 t ∧
      H t t - H 0 0 = ∫ u in 0..t, (a u u + b u u) := by
  have hdiag := diagonal_intervalIntegrable t ht a A ha_int haA hauc
  have hbdiag : ContinuousOn (fun u => b u u) (Icc 0 t) :=
    hb.comp (continuous_id.prodMk continuous_id).continuousOn (fun u hu => ⟨hu, hu⟩)
  have hbdiagI : IntervalIntegrable (fun u => b u u) volume 0 t :=
    ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le ht])
  have hI : IntervalIntegrable (fun u => a u u + b u u) volume 0 t := hdiag.add hbdiagI
  refine ⟨hI, ?_⟩
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    simp
  -- uniform continuity of `b` on the compact square
  have hbuc : UniformContinuousOn (fun p : ℝ × ℝ => b p.1 p.2) (Icc 0 t ×ˢ Icc 0 t) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hb
  set D : ℝ := (H t t - H 0 0) - ∫ u in 0..t, (a u u + b u u) with hD
  have key : ∀ ε > 0, |D| ≤ 2 * t * ε := by
    intro ε hε
    obtain ⟨ηa, hηa, hauc'⟩ := hauc ε hε
    obtain ⟨ηb, hηb, hbuc'⟩ := Metric.uniformContinuousOn_iff.mp hbuc ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (t / min ηa ηb)
    have hmin : 0 < min ηa ηb := lt_min hηa hηb
    have hnpos : (0 : ℝ) < n := lt_trans (by positivity) hn
    have hn1 : 1 ≤ n := by exact_mod_cast hnpos
    have hh : t / n < min ηa ηb := by
      rw [div_lt_iff₀ hnpos]
      have := (div_lt_iff₀ hmin).mp hn
      linarith
    set r : ℕ → ℝ := partitionPoint t n with hr
    have hrI : ∀ k ≤ n, r k ∈ Icc 0 t := fun k hk => partitionPoint_mem t ht n hn1 k hk
    have hstep : ∀ k, r (k + 1) - r k = t / n := fun k => partitionPoint_succ_sub t n hn1 k
    have hrmono : ∀ k, r k ≤ r (k + 1) := fun k => by
      have := hstep k
      have : 0 ≤ t / (n : ℝ) := by positivity
      linarith
    -- telescoping
    have htel : H t t - H 0 0 = ∑ k ∈ Finset.range n, (H (r (k + 1)) (r (k + 1)) - H (r k) (r k)) := by
      rw [Finset.sum_range_sub (fun k => H (r k) (r k)) n]
      have e0 : r 0 = 0 := partitionPoint_zero t n
      have e1 : r n = t := partitionPoint_last t n hn1
      rw [e0, e1]
    -- cell decomposition
    have hcell : ∀ k < n, H (r (k + 1)) (r (k + 1)) - H (r k) (r k) =
        (∫ v in r k..r (k + 1), b (r (k + 1)) v) + ∫ u in r k..r (k + 1), a u (r k) := by
      intro k hk
      have h1 := hrI k hk.le
      have h2 := hrI (k + 1) hk
      have e1 := hHs (r (k + 1)) h2 (r (k + 1)) h2 (r k) h1
      have e2 := hHr (r k) h1 (r (k + 1)) h2 (r k) h1
      linarith
    -- integrability on cells
    have hcellsub : ∀ k < n, ∀ g : ℝ → ℝ, IntervalIntegrable g volume 0 t →
        IntervalIntegrable g volume (r k) (r (k + 1)) := by
      intro k hk g hg
      have h1 := hrI k hk.le
      have h2 := hrI (k + 1) hk
      refine hg.mono_set ?_
      rw [uIcc_of_le ht, uIcc_of_le (hrmono k)]
      exact Icc_subset_Icc h1.1 h2.2
    have hbI : ∀ k < n, IntervalIntegrable (fun v => b (r (k + 1)) v) volume 0 t := by
      intro k hk
      have h2 := hrI (k + 1) hk
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht]
      exact hb.comp (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨h2, hv⟩)
    have hcellerr : ∀ k < n, |(H (r (k + 1)) (r (k + 1)) - H (r k) (r k)) -
        ∫ u in r k..r (k + 1), (a u u + b u u)| ≤ (t / n) * (2 * ε) := by
      intro k hk
      have h1 := hrI k hk.le
      have h2 := hrI (k + 1) hk
      have hmem : ∀ v ∈ Icc (r k) (r (k + 1)), v ∈ Icc 0 t := fun v hv =>
        ⟨h1.1.trans hv.1, hv.2.trans h2.2⟩
      have hsplit : (∫ u in r k..r (k + 1), (a u u + b u u)) =
          (∫ u in r k..r (k + 1), a u u) + ∫ u in r k..r (k + 1), b u u := by
        refine intervalIntegral.integral_add (hcellsub k hk _ hdiag) (hcellsub k hk _ hbdiagI)
      have hA : IntervalIntegrable (fun u => a u (r k)) volume (r k) (r (k + 1)) :=
        hcellsub k hk _ (ha_int _ h1)
      have hB : IntervalIntegrable (fun v => b (r (k + 1)) v) volume (r k) (r (k + 1)) :=
        hcellsub k hk _ (hbI k hk)
      have hdA : IntervalIntegrable (fun u => a u u) volume (r k) (r (k + 1)) :=
        hcellsub k hk _ hdiag
      have hdB : IntervalIntegrable (fun u => b u u) volume (r k) (r (k + 1)) :=
        hcellsub k hk _ hbdiagI
      rw [hcell k hk, hsplit]
      have hsub : ((∫ v in r k..r (k + 1), b (r (k + 1)) v) + ∫ u in r k..r (k + 1), a u (r k)) -
          ((∫ u in r k..r (k + 1), a u u) + ∫ u in r k..r (k + 1), b u u) =
          (∫ u in r k..r (k + 1), (a u (r k) - a u u)) +
            ∫ v in r k..r (k + 1), (b (r (k + 1)) v - b v v) := by
        rw [intervalIntegral.integral_sub hA hdA, intervalIntegral.integral_sub hB hdB]
        ring
      rw [hsub]
      have hlen : |r (k + 1) - r k| = t / n := by
        rw [abs_of_nonneg (by linarith [hrmono k])]; exact hstep k
      have hIa : ‖∫ u in r k..r (k + 1), (a u (r k) - a u u)‖ ≤ ε * |r (k + 1) - r k| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => ?_)
        rw [uIoc_of_le (hrmono k)] at hu
        have hu' : u ∈ Icc (r k) (r (k + 1)) := ⟨hu.1.le, hu.2⟩
        rw [Real.norm_eq_abs]
        have := hauc' u (hmem u hu') (r k) h1 u (hmem u hu') (by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hu'.1)]
          have := hstep k
          have hlt : t / n < ηa := lt_of_lt_of_le hh (min_le_left _ _)
          linarith [hu'.2])
        exact this
      have hIb : ‖∫ v in r k..r (k + 1), (b (r (k + 1)) v - b v v)‖ ≤ ε * |r (k + 1) - r k| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun v hv => ?_)
        rw [uIoc_of_le (hrmono k)] at hv
        have hv' : v ∈ Icc (r k) (r (k + 1)) := ⟨hv.1.le, hv.2⟩
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        have hlt : t / n < ηb := lt_of_lt_of_le hh (min_le_right _ _)
        have := hbuc' (r (k + 1), v) ⟨h2, hmem v hv'⟩ (v, v) ⟨hmem v hv', hmem v hv'⟩ (by
          rw [Prod.dist_eq]
          simp only [Real.dist_eq, sub_self, abs_zero]
          rw [max_lt_iff]
          refine ⟨?_, hηb⟩
          rw [abs_of_nonneg (by linarith [hv'.2])]
          have := hstep k
          linarith [hv'.1])
        exact this.le
      rw [Real.norm_eq_abs] at hIa hIb
      calc _ ≤ |∫ u in r k..r (k + 1), (a u (r k) - a u u)| +
            |∫ v in r k..r (k + 1), (b (r (k + 1)) v - b v v)| := abs_add_le _ _
        _ ≤ ε * |r (k + 1) - r k| + ε * |r (k + 1) - r k| := add_le_add hIa hIb
        _ = (t / n) * (2 * ε) := by rw [hlen]; ring
    have hcellI : ∀ k < n, IntervalIntegrable (fun u => a u u + b u u) volume (r k) (r (k + 1)) :=
      fun k hk => hcellsub k hk _ hI
    have hsum : ∑ k ∈ Finset.range n, ∫ u in r k..r (k + 1), (a u u + b u u) =
        ∫ u in r 0..r n, (a u u + b u u) :=
      intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hcellI k hk)
    have e0 : r 0 = 0 := partitionPoint_zero t n
    have e1 : r n = t := partitionPoint_last t n hn1
    rw [e0, e1] at hsum
    have hDsum : D = ∑ k ∈ Finset.range n, ((H (r (k + 1)) (r (k + 1)) - H (r k) (r k)) -
        ∫ u in r k..r (k + 1), (a u u + b u u)) := by
      rw [Finset.sum_sub_distrib, hsum, ← htel]
    rw [hDsum]
    calc _ ≤ ∑ k ∈ Finset.range n, |(H (r (k + 1)) (r (k + 1)) - H (r k) (r k)) -
          ∫ u in r k..r (k + 1), (a u u + b u u)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, (t / n) * (2 * ε) :=
          Finset.sum_le_sum fun k hk => hcellerr k (Finset.mem_range.mp hk)
      _ = 2 * t * ε := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hD0 : D = 0 := by
    by_contra hne
    have hpos : 0 < |D| := abs_pos.mpr hne
    have := key (|D| / (4 * t)) (by positivity)
    have h2 : 2 * t * (|D| / (4 * t)) = |D| / 2 := by field_simp; ring
    rw [h2] at this
    linarith
  linarith

end DGRHS.Periodic
