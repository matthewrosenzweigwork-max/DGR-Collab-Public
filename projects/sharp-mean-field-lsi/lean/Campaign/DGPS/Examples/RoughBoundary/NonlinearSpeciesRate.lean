import DGPS.Examples.RoughBoundary.NonlinearRate
import DGPS.Examples.RoughBoundary.NonlinearSpecies
import DGPS.Variational.SpeciesInclusion

/-!
# Exact arbitrary finite species rate (RUF036)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 5, (5.3).

For the rough product model `W_{L,ε}` (`ε ≠ 0`, `L > 0`) with the exact free-energy decomposition
(RUF027) and every weak-drift provider `b`, the multi-species rate is `r_ms = a0 = 4π²`, with no
bound on the species count `q` and no lower bound on the weights `θ_s`: every finite family with
positive gap has quotient `≥ a0` (infinite dissipation if the barycenter mean is nonzero; if it is
zero, `∑ θ_s I_s ≥ 2 a0 ∑ θ_s H_s` by the sharp circle LSI species by species, zero-entropy
species included), and the single-species family attains the scalar rate `a0` (RUF033).

Design choices (R5 notes).
* Hypotheses are those of RUF033/RUF035: `ε ≠ 0`, `L > 0` arbitrary and
  `FreeEnergyDecomposition L ε`. The statement is for each such `(L, ε)` (hence for every
  nonzero-amplitude member of the RUF026 family); each family `F` is handled individually, so
  sequences `q → ∞` or `θ_min → 0` are covered one family at a time.
* The conclusion is the equality `speciesRate = ofReal (4π²)`; the at-most-`k` rates are also
  `≥ a0` and the `k = 1` one equals `a0`.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace DGPS.Examples.RoughBoundary.Nonlinear

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.FreeEnergy (FreeEnergyDecomposition)

/-- Every finite species family with positive gap has quotient at least `a0`. -/
lemma ofReal_a0_le_speciesQuotient {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (hdec : FreeEnergyDecomposition L ε) (b : AbsoluteDrift (modelData hL ε))
    (F : SpeciesFamily 1) (hG : 0 < speciesGap (modelData hL ε) F) :
    ENNReal.ofReal (4 * π ^ 2) ≤ speciesQuotient (modelData hL ε) b F := by
  obtain ⟨hiff, hzero⟩ :=
    finite_species_dissipation_exactly_means_zero_barycenter_mean hL hε hdec b F
  by_cases hM : ∑ s, F.weight s • featureMean L ε (F.density s) = 0
  · obtain ⟨hD, hgap⟩ := hzero hM
    unfold speciesQuotient
    set g : ℝ := (speciesGap (modelData hL ε) F : ℝ) with hg
    have hgpos : 0 < g := by exact_mod_cast hG
    have hgE : (speciesGap (modelData hL ε) F : ℝ≥0∞) = ENNReal.ofReal g := by
      rw [hg, ENNReal.ofReal_coe_nnreal]
    have hlsi : ∀ s, 2 * (4 * π ^ 2) *
        (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1)) (haar 1)).toReal ≤
        4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1 := fun s => by
      have h := (haar_circle_lsi (F.density s)).2.2
      rw [circleEntropy_eq_relativeEntropy] at h
      exact h
    have hsum : 2 * (4 * π ^ 2) * g ≤
        ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1) := by
      rw [hgap, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have := mul_le_mul_of_nonneg_left (hlsi s) (F.weight_nonneg s)
      linarith
    have h2g : (2 : ℝ≥0∞) * ENNReal.ofReal g = ENNReal.ofReal (2 * g) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [hD, hgE, h2g,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hgpos)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have htop : speciesDissipation (modelData hL ε) b F = ⊤ := by
      by_contra hne
      exact hM (hiff.1 (lt_top_iff_ne_top.2 hne))
    unfold speciesQuotient
    rw [htop]
    have : (2 * (speciesGap (modelData hL ε) F : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
    rw [ENNReal.top_div_of_ne_top this]
    exact le_top

/-- **RUF036.** For the rough product model `W_{L,ε}` (`ε ≠ 0`) with the exact free-energy
decomposition and every weak-drift provider `b`, the multi-species rate equals `a0 = 4π²`,
for arbitrary finite species families (any count `q`, no lower bound on the weights). -/
theorem exact_arbitrary_finite_species_rate {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (hdec : FreeEnergyDecomposition L ε) (b : AbsoluteDrift (modelData hL ε)) :
    speciesRate (modelData hL ε) b = ENNReal.ofReal (4 * π ^ 2) ∧
    (∀ F : SpeciesFamily 1, 0 < speciesGap (modelData hL ε) F →
      ENNReal.ofReal (4 * π ^ 2) ≤ speciesQuotient (modelData hL ε) b F) ∧
    (∀ k : ℕ, 1 ≤ k → speciesRateAtMost (modelData hL ε) b k = ENNReal.ofReal (4 * π ^ 2)) := by
  have hscalar := (exact_scalar_rate_of_the_rough_example hL hε hdec b).1
  have hq := fun F hG => ofReal_a0_le_speciesQuotient hL hε hdec b F hG
  have hlow : ENNReal.ofReal (4 * π ^ 2) ≤ speciesRate (modelData hL ε) b :=
    le_iInf fun F => hq F.1 F.2
  have hup : speciesRate (modelData hL ε) b ≤ ENNReal.ofReal (4 * π ^ 2) :=
    hscalar ▸ speciesRate_le_scalarRate _ b
  refine ⟨le_antisymm hup hlow, hq, fun k hk => ?_⟩
  refine le_antisymm ?_ ?_
  · rw [← hscalar]
    refine le_iInf fun ρ => ?_
    have hG1 : 0 < speciesGap (modelData hL ε) (SpeciesFamily.single ρ.1) := by
      rw [speciesGap_single]; exact ρ.2
    calc speciesRateAtMost (modelData hL ε) b k ≤
          speciesQuotient (modelData hL ε) b (SpeciesFamily.single ρ.1) :=
          speciesRateAtMost_le _ b k _ (by simpa [SpeciesFamily.single] using hk) hG1
      _ = scalarQuotient (modelData hL ε) b ρ.1 := speciesQuotient_single _ b ρ.1
  · exact hlow.trans (speciesRate_le_speciesRateAtMost _ b k)

end DGPS.Examples.RoughBoundary.Nonlinear
