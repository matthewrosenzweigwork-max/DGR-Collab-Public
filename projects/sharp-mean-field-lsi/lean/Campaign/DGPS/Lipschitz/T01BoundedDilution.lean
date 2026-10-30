import DGPS.Lipschitz.T01SpeciesReferenceQuotient
import DGPS.Lipschitz.T01DilutionComplement

/-!
# Quantitative bounded-test dilution at a Lipschitz minimizing reference
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The exact binary family gives the ordinary test quotient with an error linear in the
small species weight. The reference density is only positive Lipschitz. -/
theorem t01_bounded_dilution_estimate (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    {g : Torus d → ℝ} (hg : g ∈ WeightedH1 (frozenGibbs A μ)) {M a H ε : ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hgM : ∀ x, |g x| ≤ M) (ha : 0 < a)
    (hZ : a * ∫ x, g x ^ 2 ∂(frozenGibbs A μ).measure = 1)
    (hH : homogeneousEntropy (frozenGibbs A μ).measure (fun x => g x ^ 2) = ENNReal.ofReal H)
    (hH0 : 0 < H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hεM : ε * a * M ^ 2 ≤ 1 / 2) :
    speciesRate A b ≤ ENNReal.ofReal
      (2 * (∫ x, ‖weightedGradient (frozenGibbs A μ) g hg x‖ ^ 2 ∂(frozenGibbs A μ).measure) / H +
        16 * ε * a * M ^ 2 *
          (∫ x, ‖weightedGradient (frozenGibbs A μ) g hg x‖ ^ 2 ∂(frozenGibbs A μ).measure) / H) := by
  let P := frozenGibbs A μ
  let G := weightedGradient P g hg
  let E := ∫ x, ‖G x‖ ^ 2 ∂P.measure
  have hE : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hgW : IsWeakGradient g G :=
    (isWeightedWeakGradient_iff P).mp (isWeightedWeakGradient_weightedGradient P hg)
  let u : Torus d → ℝ := fun x => Real.sqrt a * g x
  have huW : IsWeakGradient u (fun x => Real.sqrt a • G x) := hgW.smul (Real.sqrt a)
  have hu : u ∈ WeightedH1 P := (mem_weightedH1_iff P).mpr ⟨_, huW⟩
  have hu0 : ∀ x, 0 ≤ u x := fun x => mul_nonneg (Real.sqrt_nonneg _) (hg0 x)
  have husq : ∀ x, u x ^ 2 = a * g x ^ 2 := by
    intro x
    change (Real.sqrt a * g x) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt ha.le]
  have hu1 : ∫ x, u x ^ 2 ∂P.measure = 1 := by
    simp_rw [husq]
    rw [integral_const_mul]
    exact hZ
  have huEnt : homogeneousEntropy P.measure (fun x => u x ^ 2) =
      ENNReal.ofReal a * ENNReal.ofReal H := by
    simp_rw [husq]
    rw [FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent
      ((isWeightedWeakGradient_weightedGradient P hg).memLp.integrable_sq.const_mul a),
      SharpLSI.ent_const_mul P.measure
        (isWeightedWeakGradient_weightedGradient P hg).memLp.integrable_sq ha.le,
      ← FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent
        (isWeightedWeakGradient_weightedGradient P hg).memLp.integrable_sq,
      hH]
  have huE : ∫ x, ‖weightedGradient P u hu x‖ ^ 2 ∂P.measure = a * E := by
    have hae : weightedGradient P u hu =ᵐ[P.measure] (fun x => Real.sqrt a • G x) :=
      P.measure_ac_haar.ae_le (weightedGradient_ae_eq P hu huW)
    rw [integral_congr_ae (hae.mono fun x hx => by rw [hx])]
    have hn : ∀ x, ‖Real.sqrt a • G x‖ ^ 2 = a * ‖G x‖ ^ 2 := by
      intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, Real.sq_sqrt ha.le]
    simp_rw [hn]
    exact integral_const_mul _ _
  let v := t01DilutionComplement ε a g
  have hv : v ∈ WeightedH1 P :=
    t01DilutionComplement_mem P hg hgM hε0.le hε1 ha.le hεM
  have hv0 : ∀ x, 0 ≤ v x := t01DilutionComplement_nonneg ε a g
  have hv1 : ∫ x, v x ^ 2 ∂P.measure = 1 :=
    t01DilutionComplement_mass P hg hgM hε0.le hε1 ha.le hεM hZ
  have hmix : ∀ x, ε * u x ^ 2 + (1 - ε) * v x ^ 2 = 1 := by
    intro x
    rw [husq, t01DilutionComplement_sq g hgM hε0.le hε1 ha.le hεM]
    ring
  have hrate := t01_relative_pair_rate_bound A hLip b hμ u v hu hv hu0 hv0 hu1 hv1
    ε hε0 (by linarith) hmix (by rw [huEnt]; positivity)
  refine hrate.trans ?_
  apply SharpLSI.FL.quot_arith (M := M) hε0 (by linarith) ha hE hH0
  · rw [huE]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  · apply ENNReal.ofReal_le_ofReal
    have hb := t01DilutionComplement_energy_bound P hg hgM hε0.le hε1 ha.le hεM hv
    change _ ≤ 8 * ε ^ 2 * a ^ 2 * M ^ 2 * E at hb
    nlinarith
  · exact huEnt

/-- Letting the species weight vanish gives the exact bounded relative-test upper bound. -/
theorem t01_speciesRate_le_bounded_test (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    {g : Torus d → ℝ} (hg : g ∈ WeightedH1 (frozenGibbs A μ)) {M a H : ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hgM : ∀ x, |g x| ≤ M) (ha : 0 < a)
    (hZ : a * ∫ x, g x ^ 2 ∂(frozenGibbs A μ).measure = 1)
    (hH : homogeneousEntropy (frozenGibbs A μ).measure (fun x => g x ^ 2) = ENNReal.ofReal H)
    (hH0 : 0 < H) :
    speciesRate A b ≤ ENNReal.ofReal
      (2 * (∫ x, ‖weightedGradient (frozenGibbs A μ) g hg x‖ ^ 2 ∂(frozenGibbs A μ).measure) / H) := by
  let E := ∫ x, ‖weightedGradient (frozenGibbs A μ) g hg x‖ ^ 2 ∂(frozenGibbs A μ).measure
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * E / H + 16 * ε * a * M ^ 2 * E / H))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2 * E / H))) := by
    have hc : Continuous (fun ε : ℝ => 2 * E / H + 16 * ε * a * M ^ 2 * E / H) := by fun_prop
    simpa only [Function.comp_def, zero_mul, mul_zero, zero_div, add_zero] using
      ((ENNReal.continuous_ofReal.comp hc).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  refine ge_of_tendsto hlim ?_
  have hehalf : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 2 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_id.tendsto (0 : ℝ)).eventually_lt_const (by norm_num))
  have heM : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * a * M ^ 2 < 1 / 2 :=
    eventually_nhdsWithin_of_eventually_nhds
      (((by fun_prop : Continuous fun ε : ℝ => ε * a * M ^ 2).tendsto 0).eventually_lt_const
        (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hehalf, heM] with ε hε0 hε1 hεM
  exact t01_bounded_dilution_estimate A hLip b hμ hg hg0 hgM ha hZ hH hH0 hε0 hε1.le hεM.le

end DGPS.Lipschitz
