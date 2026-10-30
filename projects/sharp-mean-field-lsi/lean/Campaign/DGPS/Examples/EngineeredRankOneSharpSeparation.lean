import DGPS.Examples.EngineeredRankOneSpeciesLimit
import DGPS.Examples.EngineeredRankOneScalarScale

/-!
# Exact fixed-coupling engineered scalar/species separation

Every field belongs to the prescribed domain `h ≥ 2`, and all real rates carry
pointwise finiteness proofs. Positivity and the uniform scalar scale are asserted
on one common tail. The ratio limit follows from the actual species limit and
the actual linear scalar lower bound.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models

private theorem field_val_tendsto :
    Tendsto (fun h : Set.Ici (2 : ℝ) => (h : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  refine eventually_atTop.2 ⟨⟨max 2 b, show (2 : ℝ) ≤ max 2 b from le_max_left _ _⟩,
    fun h hh => ?_⟩
  exact (le_max_right _ _).trans hh

/-- T10 for the exact prescribed potentials and coupling one. No sharp-LSI or
scalar-scale estimate is an assumption. -/
theorem unbounded_scalar_species_separation :
    ∃ hs : ∀ h : Set.Ici (2 : ℝ),
        FiniteRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)),
    ∃ hm : ∀ h : Set.Ici (2 : ℝ),
        FiniteRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)),
      let rs := fun h : Set.Ici (2 : ℝ) =>
        realRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hs h)
      let rm := fun h : Set.Ici (2 : ℝ) =>
        realRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hm h)
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ h0 : ℝ, 2 ≤ h0 ∧
        ∀ h : Set.Ici (2 : ℝ), h0 ≤ h.1 →
          0 < rm h ∧ 0 < rs h ∧ c * DGPS.a0 * h.1 ≤ rs h ∧ rs h ≤ C * DGPS.a0 * h.1) ∧
      Tendsto (fun h => rm h / DGPS.a0) atTop (𝓝 1) ∧
      Tendsto (fun h => rs h / rm h) atTop atTop := by
  let hs : ∀ h : Set.Ici (2 : ℝ),
      FiniteRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) :=
    fun h => DGPS.Examples.engineered_scalar_rate_finite h.1 h.2
  obtain ⟨hm, hlimit⟩ := species_rate_limit
  let rs := fun h : Set.Ici (2 : ℝ) =>
    realRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hs h)
  let rm := fun h : Set.Ici (2 : ℝ) =>
    realRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hm h)
  change Tendsto (fun h => rm h / DGPS.a0) atTop (𝓝 1) at hlimit
  obtain ⟨c, C, hS, hc, hC, hhS, hbound⟩ := DGPS.Examples.engineered_scalar_linear_growth
  have hreal (h : Set.Ici (2 : ℝ)) (hSh : hS ≤ h.1) :
      c * DGPS.a0 * h.1 ≤ rs h ∧ rs h ≤ C * DGPS.a0 * h.1 := by
    obtain ⟨hlow, hupp⟩ := hbound h.1 h.2 hSh
    have hh0 : 0 ≤ h.1 := (by norm_num : (0 : ℝ) ≤ 2).trans h.2
    constructor
    · have hrealLow := ENNReal.toReal_mono (hs h) hlow
      rw [ENNReal.toReal_ofReal
        (mul_nonneg (mul_nonneg hc.le DGPS.a0_pos.le) hh0)] at hrealLow
      exact hrealLow
    · have hrealUpp := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupp
      rw [ENNReal.toReal_ofReal
        (mul_nonneg (mul_nonneg hC.le DGPS.a0_pos.le) hh0)] at hrealUpp
      exact hrealUpp
  have hpos : ∀ᶠ h in atTop, 0 < rm h := by
    filter_upwards [hlimit.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with h hh
    simpa only [zero_mul] using (lt_div_iff₀ DGPS.a0_pos).mp hh
  have hupp : ∀ᶠ h in atTop, rm h ≤ 2 * DGPS.a0 := by
    filter_upwards [hlimit.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with h hh
    exact ((div_lt_iff₀ DGPS.a0_pos).mp hh).le
  have htail : ∀ᶠ h : Set.Ici (2 : ℝ) in atTop,
      hS ≤ h.1 ∧ 0 < rm h ∧ rm h ≤ 2 * DGPS.a0 := by
    filter_upwards [field_val_tendsto.eventually (eventually_ge_atTop hS), hpos, hupp]
      with h hSh hp hu
    exact ⟨hSh, hp, hu⟩
  have hscale : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ h0 : ℝ, 2 ≤ h0 ∧
      ∀ h : Set.Ici (2 : ℝ), h0 ≤ h.1 →
        0 < rm h ∧ 0 < rs h ∧ c * DGPS.a0 * h.1 ≤ rs h ∧ rs h ≤ C * DGPS.a0 * h.1 := by
    obtain ⟨H, hH⟩ := eventually_atTop.1 htail
    refine ⟨c, C, hc, hC, H.1, H.2, fun h hh => ?_⟩
    obtain ⟨hSh, hp, -⟩ := hH h hh
    obtain ⟨hl, hu⟩ := hreal h hSh
    have hh0 : 0 < h.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) h.2
    exact ⟨hp, (mul_pos (mul_pos hc DGPS.a0_pos) hh0).trans_le hl, hl, hu⟩
  have hcompare : ∀ᶠ h : Set.Ici (2 : ℝ) in atTop, (c / 2) * h.1 ≤ rs h / rm h := by
    filter_upwards [htail] with h hh
    obtain ⟨hSh, hp, hu⟩ := hh
    have hl := (hreal h hSh).1
    have hh0 : 0 ≤ h.1 := (by norm_num : (0 : ℝ) ≤ 2).trans h.2
    apply (le_div_iff₀ hp).2
    calc (c / 2 * h.1) * rm h ≤ (c / 2 * h.1) * (2 * DGPS.a0) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = c * DGPS.a0 * h.1 := by ring
      _ ≤ rs h := hl
  have hlinear : Tendsto (fun h : Set.Ici (2 : ℝ) => (c / 2) * h.1) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos hc) field_val_tendsto
  have hratio : Tendsto (fun h => rs h / rm h) atTop atTop :=
    tendsto_atTop_mono' atTop hcompare hlinear
  exact ⟨hs, hm, hscale, hlimit, hratio⟩

/-- The scalar rate has uniform positive linear scale on the fixed field family. -/
theorem scalar_rate_theta_h :
    ∃ hs : ∀ h : Set.Ici (2 : ℝ),
        FiniteRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)),
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ h0 : ℝ, 2 ≤ h0 ∧
        ∀ h : Set.Ici (2 : ℝ), h0 ≤ h.1 →
          c * DGPS.a0 * h.1 ≤
              realRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hs h) ∧
          realRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hs h) ≤
            C * DGPS.a0 * h.1 := by
  obtain ⟨hs, hm, hscale, -, -⟩ := unbounded_scalar_species_separation
  obtain ⟨c, C, hc, hC, h0, hh0, htail⟩ := hscale
  exact ⟨hs, c, C, hc, hC, h0, hh0, fun h hh => (htail h hh).2.2⟩

/-- The scalar/species ratio diverges, with the denominator proved positive on a tail. -/
theorem scalar_species_ratio_tends_atTop :
    ∃ hs : ∀ h : Set.Ici (2 : ℝ),
        FiniteRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)),
    ∃ hm : ∀ h : Set.Ici (2 : ℝ),
        FiniteRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)),
      (∀ᶠ h : Set.Ici (2 : ℝ) in atTop,
        0 < realRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hm h)) ∧
      Tendsto (fun h : Set.Ici (2 : ℝ) =>
        realRate (scalarRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hs h) /
          realRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) (hm h))
        atTop atTop := by
  obtain ⟨hs, hm, hscale, -, hratio⟩ := unbounded_scalar_species_separation
  obtain ⟨c, C, hc, hC, h0, hh0, htail⟩ := hscale
  refine ⟨hs, hm, ?_, hratio⟩
  filter_upwards [field_val_tendsto.eventually (eventually_ge_atTop h0)] with h hh
  exact (htail h hh).1

end DGPS.Examples.EngineeredRankOne
