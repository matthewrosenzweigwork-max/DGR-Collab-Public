import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! Monotone rank variation and the generalized-inverse estimate in the
supplied stationary proof. The rank need not be absolutely continuous or
continuous: jumps and singular variation are retained. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace PeriodicAttractiveLogGas.StationaryRankSlope

/-- Monotone variation dominates the actual derivative integral. There is
no absolute-continuity hypothesis on the rank function. -/
theorem antitone_derivative_integral {rank : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : AntitoneOn rank (Icc a b)) :
    IntervalIntegrable (fun t ↦ -deriv rank t) volume a b ∧
      (∫ t in a..b, -deriv rank t) ≤ rank a - rank b := by
  have hm : MonotoneOn (-rank) (uIcc a b) := by
    simpa only [uIcc_of_le hab, Pi.neg_apply] using! hr.neg
  have hd : 0 ≤ rank a - rank b :=
    sub_nonneg.mpr (hr ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have hi := hm.intervalIntegrable_deriv
  have hb := hm.intervalIntegral_deriv_mem_uIcc
  have hb' : (∫ t in a..b, -deriv rank t) ∈ Icc 0 (rank a - rank b) := by
    simpa only [deriv.neg', Pi.neg_apply, neg_sub_neg, uIcc_of_le hd] using! hb
  exact ⟨by simpa only [deriv.neg'] using! hi, hb'.2⟩

/-- A lower bound on minus the derivative forces at least that much rank
decrease, even when further variation is singular. -/
theorem rank_drop_ge_of_ae_deriv_le {rank : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hr : AntitoneOn rank (Icc a b))
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), deriv rank t ≤ -c) :
    c * (b - a) ≤ rank a - rank b := by
  obtain ⟨hi, hb⟩ := antitone_derivative_integral hab hr
  have hd' : ∀ᵐ t ∂volume.restrict (Icc a b), c ≤ -deriv rank t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hd] with t ht
    linarith
  have hc := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const (c := c)) hi hd'
  have hh := hc.trans hb
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh

/-- Critical values may be removed before integrating the slope bound.
Only their Lebesgue nullity is used, not continuity or AC of the rank. -/
theorem rank_drop_ge_off_null {rank : ℝ → ℝ} {a b c : ℝ} {C : Set ℝ}
    (hab : a ≤ b) (hr : AntitoneOn rank (Icc a b)) (hC : volume C = 0)
    (hd : ∀ t ∈ Ioo a b, t ∉ C → deriv rank t ≤ -c) :
    c * (b - a) ≤ rank a - rank b := by
  have hnull : ∀ᵐ t : ℝ ∂volume, t ∉ C := by
    apply ae_iff.mpr
    rw [show {t : ℝ | ¬t ∉ C} = C by ext t; simp]
    exact hC
  apply rank_drop_ge_of_ae_deriv_le hab hr
  filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem measurableSet_Ioo] with t ht hi
  exact hd t hi ht

/-- Literal cross-order relations already force the inverse profile to
be antitone. No continuity of the rank or inverse is required. -/
theorem profile_antitone_of_rank_order {rank q : ℝ → ℝ} {lo hi : ℝ} {S : Set ℝ}
    (hval : ∀ s ∈ S, q s ∈ Icc lo hi)
    (hl : ∀ s ∈ S, ∀ t ∈ Ioo lo hi, t < q s → s ≤ rank t)
    (hu : ∀ s ∈ S, ∀ t ∈ Ioo lo hi, q s < t → rank t ≤ s) :
    AntitoneOn q S := by
  intro x hx y hy hxy
  by_contra hn
  have hq : q x < q y := lt_of_not_ge hn
  obtain ⟨t, hxt, hty⟩ := exists_between hq
  have ht : t ∈ Ioo lo hi :=
    ⟨lt_of_le_of_lt (hval x hx).1 hxt, lt_of_lt_of_le hty (hval y hy).2⟩
  have hyx : y ≤ x := (hl y hy t ht hty).trans (hu x hx t ht hxt)
  have he : x = y := le_antisymm hxy hyx
  simp only [he, lt_self_iff_false] at hq

/-- For two central ranks, integrate only over values strictly between
their profile values. This omits endpoint atoms. Dense order then reaches
the endpoint gap without assuming one-sided continuity of the rank. -/
theorem profile_gap_le {rank q : ℝ → ℝ} {lo hi ε c : ℝ} {C : Set ℝ}
    (hc : 0 < c) (hr : Antitone rank) (hC : volume C = 0)
    (hval : ∀ s ∈ Icc ε (1 - ε), q s ∈ Icc lo hi)
    (hl : ∀ s ∈ Icc ε (1 - ε), ∀ t ∈ Ioo lo hi, t < q s → s ≤ rank t)
    (hu : ∀ s ∈ Icc ε (1 - ε), ∀ t ∈ Ioo lo hi, q s < t → rank t ≤ s)
    (hd : ∀ t ∈ Ioo lo hi, rank t ∈ Icc ε (1 - ε) → t ∉ C → deriv rank t ≤ -c)
    {x y : ℝ} (hx : x ∈ Icc ε (1 - ε)) (hy : y ∈ Icc ε (1 - ε)) (hxy : x ≤ y) :
    q x - q y ≤ (y - x) / c := by
  by_contra hn
  have hn' : (y - x) / c < q x - q y := lt_of_not_ge hn
  have hnonneg : 0 ≤ (y - x) / c := div_nonneg (sub_nonneg.mpr hxy) hc.le
  obtain ⟨a, hya, ha⟩ := exists_between (show q y < q x - (y - x) / c by linarith)
  obtain ⟨b, hab', hbx⟩ := exists_between (show a + (y - x) / c < q x by linarith)
  have hab : a < b := by linarith
  have haI : a ∈ Ioo lo hi :=
    ⟨lt_of_le_of_lt (hval y hy).1 hya,
      lt_of_lt_of_le (hab.trans hbx) (hval x hx).2⟩
  have hbI : b ∈ Ioo lo hi :=
    ⟨lt_of_le_of_lt (hval y hy).1 (hya.trans hab),
      lt_of_lt_of_le hbx (hval x hx).2⟩
  have hdrop : c * (b - a) ≤ rank a - rank b := by
    apply rank_drop_ge_off_null hab.le (hr.antitoneOn (s := Icc a b)) hC
    intro t ht htc
    have htI : t ∈ Ioo lo hi :=
      ⟨haI.1.trans ht.1, ht.2.trans hbI.2⟩
    have htr : rank t ∈ Icc ε (1 - ε) :=
      ⟨hx.1.trans (hl x hx t htI (ht.2.trans hbx)),
        (hu y hy t htI (hya.trans ht.1)).trans hy.2⟩
    exact hd t htI htr htc
  have hupper : rank a - rank b ≤ y - x := by
    have hyb := hu y hy a haI hya
    have hxb := hl x hx b hbI hbx
    linarith
  have hstrict : y - x < (b - a) * c :=
    (div_lt_iff₀ hc).mp (show (y - x) / c < b - a by linarith)
  nlinarith

/-- The actual inverse Lipschitz estimate follows from pointwise rank
order, a null exceptional value set, and the regular-value slope bound. -/
theorem profile_lipschitz {rank q : ℝ → ℝ} {lo hi ε c : ℝ} {C : Set ℝ}
    (hc : 0 < c) (hr : Antitone rank) (hC : volume C = 0)
    (hval : ∀ s ∈ Icc ε (1 - ε), q s ∈ Icc lo hi)
    (hl : ∀ s ∈ Icc ε (1 - ε), ∀ t ∈ Ioo lo hi, t < q s → s ≤ rank t)
    (hu : ∀ s ∈ Icc ε (1 - ε), ∀ t ∈ Ioo lo hi, q s < t → rank t ≤ s)
    (hd : ∀ t ∈ Ioo lo hi, rank t ∈ Icc ε (1 - ε) → t ∉ C → deriv rank t ≤ -c) :
    LipschitzOnWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ q (Icc ε (1 - ε)) := by
  have hq := profile_antitone_of_rank_order hval hl hu
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change |q x - q y| ≤ c⁻¹ * |x - y|
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr (hq hx hy hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hh := profile_gap_le hc hr hC hval hl hu hd hx hy hxy
    simpa only [neg_sub, div_eq_mul_inv, mul_comm] using hh
  · rw [abs_of_nonpos (sub_nonpos.mpr (hq hy hx hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx), neg_sub]
    have hh := profile_gap_le hc hr hC hval hl hu hd hy hx hyx
    simpa only [div_eq_mul_inv, mul_comm] using hh

/-- The strict rank/profile equivalence used by a generalized inverse
implies both cross-order relations, including the direction that omits an
atom at a profile endpoint. -/
theorem profile_lipschitz_of_rank_iff {rank q : ℝ → ℝ} {lo hi ε c : ℝ} {C : Set ℝ}
    (hc : 0 < c) (hr : Antitone rank) (hC : volume C = 0)
    (hval : ∀ s ∈ Icc ε (1 - ε), q s ∈ Icc lo hi)
    (horder : ∀ s ∈ Icc ε (1 - ε), ∀ t ∈ Ioo lo hi, t < q s ↔ s < rank t)
    (hd : ∀ t ∈ Ioo lo hi, rank t ∈ Icc ε (1 - ε) → t ∉ C → deriv rank t ≤ -c) :
    LipschitzOnWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ q (Icc ε (1 - ε)) := by
  apply profile_lipschitz hc hr hC hval ?_ ?_ hd
  · intro s hs t ht hts
    exact ((horder s hs t ht).mp hts).le
  · intro s hs t ht hst
    by_contra hn
    have hts := (horder s hs t ht).mpr (lt_of_not_ge hn)
    linarith

/-- The literal source constant after the positive-coupling level-set
slope bound. Nullity of the critical values and that geometric bound remain
explicit upstream inputs; the inverse estimate is proved here. -/
theorem source_profile_lipschitz {rank q : ℝ → ℝ} {lo hi ε ρ : ℝ} {C : Set ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 2) (hρ : 0 < ρ)
    (hr : Antitone rank) (hC : volume C = 0)
    (hval : ∀ s ∈ Icc ε (1 - ε), q s ∈ Icc lo hi)
    (horder : ∀ s ∈ Icc ε (1 - ε), ∀ t ∈ Ioo lo hi, t < q s ↔ s < rank t)
    (hd : ∀ t ∈ Ioo lo hi, rank t ∈ Icc ε (1 - ε) → t ∉ C →
      4 * Real.pi * ε * (1 - ε) / ρ ≤ -deriv rank t) :
    LipschitzOnWith ⟨ρ / (4 * Real.pi * ε * (1 - ε)), by
      have h : 0 < 1 - ε := by linarith
      positivity⟩ q (Icc ε (1 - ε)) := by
  have he : 0 < 1 - ε := by linarith
  have hc : 0 < 4 * Real.pi * ε * (1 - ε) / ρ := by positivity
  have hder : ∀ t ∈ Ioo lo hi, rank t ∈ Icc ε (1 - ε) → t ∉ C →
      deriv rank t ≤ -(4 * Real.pi * ε * (1 - ε) / ρ) := by
    intro t ht hrank htc
    have hh := hd t ht hrank htc
    linarith
  have hh := profile_lipschitz_of_rank_iff hc hr hC hval horder hder
  simpa only [inv_div] using hh

end PeriodicAttractiveLogGas.StationaryRankSlope
