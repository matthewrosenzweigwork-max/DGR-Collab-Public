import DGPS.Examples.PolynomialSpeciesOptimizerAssembly

noncomputable section
open Filter Topology
namespace DGPS.Examples.PolynomialSpecies

/-- An open neighborhood of the full zero-field slice contains a uniform
small-field tube above every compact coefficient set. -/
theorem compact_zero_slice_tube
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {O : Set (ℝ × X)} (hO : IsOpen O) (hzero : ∀ x ∈ K, (0, x) ∈ O) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → ∀ x ∈ K, (h, x) ∈ O := by
  by_contra hno
  push_neg at hno
  have hex : ∀ n : ℕ, ∃ h : ℝ, |h| < 1 / ((n : ℝ) + 1) ∧
      ∃ x ∈ K, (h, x) ∉ O := by
    intro n
    exact hno (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hh x hx hnot using hex
  have hh0 : Tendsto h atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => by simpa only [dist_zero_right, Real.norm_eq_abs] using (hh n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨x₀, hx₀, φ, hφ, hconv⟩ := hK.tendsto_subseq hx
  have ht := (hh0.comp hφ.tendsto_atTop).prodMk_nhds hconv
  have he := ht.eventually (hO.mem_nhds (hzero x₀ hx₀))
  obtain ⟨n, hn⟩ := he.exists
  exact hnot (φ n) hn

end DGPS.Examples.PolynomialSpecies
