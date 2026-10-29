import LeanResearch.PeriodicAttractiveLogGas.StationaryEssentialBoundary

/-! Coordinate widths of closed planar lifts. The two complementary arcs
show that every coordinate width is at most half the physical length.
This permits choosing coordinate cuts missing the whole boundary when
its total perimeter is less than two. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace PeriodicAttractiveLogGas.ClosedLoopWidths
open StationaryCurveIntegrals

theorem norm_sub_le_arc {γ γ' : ℝ → PlanarSpace}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Continuous γ')
    {a b : ℝ} (hab : a ≤ b) :
    ‖γ b - γ a‖ ≤ ∫ x in a..b, ‖γ' x‖ := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hγ x) (hγ'.intervalIntegrable a b)]
  exact intervalIntegral.norm_integral_le_integral_norm hab

theorem norm_sub_le_half_length_ordered {γ γ' : ℝ → PlanarSpace} {P s t : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Continuous γ')
    (hclosed : γ P = γ 0) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ P) :
    2 * ‖γ t - γ s‖ ≤ ∫ x in (0 : ℝ)..P, ‖γ' x‖ := by
  have ha := norm_sub_le_arc hγ hγ' hst
  have hb := norm_sub_le_arc hγ hγ' hs
  have hc := norm_sub_le_arc hγ hγ' ht
  have hd : ‖γ t - γ s‖ ≤ ‖γ P - γ t‖ + ‖γ s - γ 0‖ := by
    have hh := norm_add_le (γ t - γ P) (γ 0 - γ s)
    rw [hclosed, sub_add_sub_cancel, norm_sub_rev (γ t) (γ 0), norm_sub_rev (γ 0) (γ s)] at hh
    simpa only [hclosed] using hh
  have hsplit : (∫ x in (0 : ℝ)..s, ‖γ' x‖) + (∫ x in s..t, ‖γ' x‖) +
      (∫ x in t..P, ‖γ' x‖) = ∫ x in (0 : ℝ)..P, ‖γ' x‖ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hγ'.norm.intervalIntegrable 0 s)
      (hγ'.norm.intervalIntegrable s t),
      intervalIntegral.integral_add_adjacent_intervals (hγ'.norm.intervalIntegrable 0 t)
      (hγ'.norm.intervalIntegrable t P)]
  linarith only [ha, hb, hc, hd, hsplit]

theorem norm_sub_le_half_length {γ γ' : ℝ → PlanarSpace} {P s t : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Continuous γ')
    (hclosed : γ P = γ 0) (hs : s ∈ Icc 0 P) (ht : t ∈ Icc 0 P) :
    2 * ‖γ t - γ s‖ ≤ ∫ x in (0 : ℝ)..P, ‖γ' x‖ := by
  rcases le_total s t with hst | hts
  · exact norm_sub_le_half_length_ordered hγ hγ' hclosed hs.1 hst ht.2
  · simpa only [norm_sub_rev (γ s) (γ t)] using
      norm_sub_le_half_length_ordered hγ hγ' hclosed ht.1 hts hs.2

/-- The extremal coordinate values bound the full periodic curve, not
merely one chosen half-open traversal. -/
theorem exists_coordinate_interval {γ γ' : ℝ → PlanarSpace} {P : ℝ}
    (hP : 0 < P) (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Continuous γ')
    (hp : Function.Periodic γ P) (j : Fin 2) :
    ∃ a b : ℝ, a ≤ b ∧ (∀ s : ℝ, γ s j ∈ Icc a b) ∧
      2 * (b - a) ≤ ∫ s in (0 : ℝ)..P, ‖γ' s‖ := by
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun s ↦ (hγ s).continuousAt
  have hc : Continuous (fun s ↦ γ s j) := (EuclideanSpace.proj j).continuous.comp hcont
  have hne : (Icc (0 : ℝ) P).Nonempty := ⟨0, le_rfl, hP.le⟩
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc.continuousOn
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc.continuousOn
  refine ⟨γ s j, γ t j, hmin ht, ?_, ?_⟩
  · intro r
    have hr : γ r ∈ γ '' Ico 0 P := by
      rw [← periodic_range_eq_image hP hp]
      exact ⟨r, rfl⟩
    obtain ⟨u, hu, heu⟩ := hr
    rw [← heu]
    exact ⟨hmin (Ico_subset_Icc_self hu), hmax (Ico_subset_Icc_self hu)⟩
  · have hd := norm_sub_le_half_length hγ hγ' hp.eq hs ht
    have hcoord : γ t j - γ s j ≤ ‖γ t - γ s‖ := by
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (γ t - γ s) j)
    linarith only [hd, hcoord]

end PeriodicAttractiveLogGas.ClosedLoopWidths
