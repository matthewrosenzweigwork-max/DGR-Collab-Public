import DGPS.Examples.PolynomialOriginCapture
import DGPS.Examples.PolynomialScalarSineUpper

/-! Original sqrt-H1 capture for every actual polynomial scalar minimizer
sequence as the field tends to zero. All quotient upper bounds are derived
from the actual sine-tilt producer before invoking origin capture. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- Every actual original-domain minimizer sequence has a strictly increasing
subsequence converging to Haar in the original sqrt-H1 norm. No information,
quotient bound, nearness, compactness or limiting-gap premise is supplied. -/
theorem polynomial_scalarMinimizer_origin_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n =>
      (eLpNorm (fun x => (ρ (φ n)).sqrt x - 1) 2 (haar 1)).toReal +
        (eLpNorm (weakGradient (ρ (φ n)).sqrt (ρ (φ n)).sqrt_mem) 2 (haar 1)).toReal) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hu⟩ := polynomial_scalarRate_eventual_upper 1 (by norm_num)
  have hs : ∀ᶠ n in atTop, |h n| < δ := by
    have ht : Tendsto (fun n => |h n|) atTop (𝓝 0) := by simpa using hh.abs
    exact ht.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hs
  let hs := fun n => h (n + N)
  let bs := fun n => b (n + N)
  let τ := fun n => ρ (n + N)
  have hhs : Tendsto hs atTop (𝓝 0) := hh.comp (tendsto_add_atTop_nat N)
  have hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n) ≤
      ENNReal.ofReal (a0 + 1) := by
    intro n
    change scalarQuotient (canonical_elementary_polynomial_model (h (n + N))) (b (n + N)) (ρ (n + N)) ≤ _
    rw [hmin (n + N)]
    exact hu _ (hN (n + N) (by omega)) _
  have hnear : ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
      scalarQuotient (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n) ≤ ENNReal.ofReal (a0 + t) := by
    intro t ht
    obtain ⟨δt, hδt, hut⟩ := polynomial_scalarRate_eventual_upper t ht
    have habs : Tendsto (fun n => |hs n|) atTop (𝓝 0) := by simpa using hhs.abs
    filter_upwards [habs.eventually (gt_mem_nhds hδt)] with n hn
    change scalarQuotient (canonical_elementary_polynomial_model (h (n + N))) (b (n + N)) (ρ (n + N)) ≤ _
    rw [hmin (n + N)]
    exact hut _ hn _
  obtain ⟨φ, hφ, hcapture⟩ := polynomial_scalar_origin_capture hs hhs bs (a0 + 1)
    (by unfold a0; positivity) τ (fun n => hG (n + N)) hQ hnear
  exact ⟨fun n => φ n + N, fun i j hij => Nat.add_lt_add_right (hφ hij) N, hcapture⟩

end DGPS.Examples.PolynomialSpecies
