import DGPS.Examples.RoughBoundary.NonlinearDissipation
import DGPS.Model.SpeciesRate
import DGPS.Variational.ScoreDecomposition

/-!
# Finite species dissipation exactly means zero barycenter mean (RUF035)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 5, (5.1)-(5.2).

For the rough product model `W_{L,ε}(x,y) = κ (1 - U(x)·U(y))` with `ε ≠ 0`, every finite species
family `F` of absolute-admissible densities `ρ_s = u_s²` with positive weights `θ_s`, and every
weak-drift provider `b`: put `M_s = ∫ U ρ_s dm` and `M̄ = ∑ θ_s M_s`. The common score is
`S_s = 2 u_s' - κ u_s M̄·U'`, and `D_θ = ∑ θ_s ‖S_s‖₂² < ∞` iff `M̄ = 0`. On that class
`D_θ = ∑ θ_s I_s` with `I_s = 4 ∫ |u_s'|²` and (under the exact free-energy decomposition of RUF027)
`G_θ = ∑ θ_s H(ρ_s m | m)`.

Design choices (R5 notes).
* `ε ≠ 0` is assumed (needed for the directional roughness of RUF007); `L > 0` is arbitrary.
* The identification of `G_θ` uses `FreeEnergyDecomposition L ε` (RUF027) as hypothesis, as in RUF032.
* Individual means `M_s` are not assumed to vanish; the barycenter mean is the explicit sum
  `∑ θ_s • featureMean L ε ρ_s`, which equals the feature mean of the barycenter density.
* The gap identity is stated in `ℝ` (`speciesGap` is `ℝ≥0`, entropies are finite for absolute
  admissible densities, so `toReal` loses nothing). Nonnegativity of the gap is built into
  `speciesGap : ℝ≥0` (DEF013/DEF014).
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Real

namespace DGPS.Examples.RoughBoundary.Nonlinear

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.FreeEnergy (FreeEnergyDecomposition)

/-- The score `2 u' - κ u (M·U')` for a prescribed (common) mean vector `M`. -/
noncomputable def commonScore (L ε : ℝ) (M : EuclideanSpace ℝ (Fin 2)) (u : Torus 1 → ℝ)
    (g : Torus 1 → Tangent 1) : Torus 1 → ℝ :=
  fun x => 2 * g x 0 - kappa * u x * inner ℝ M (Uprime L ε x)

lemma memLp_commonScore {L : ℝ} (hL : 0 < L) (ε : ℝ) (M : EuclideanSpace ℝ (Fin 2))
    {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (hg : IsWeakGradient u g) {p : ℝ} (hp : 1 ≤ p)
    (hp2 : p < 2) :
    MemLp (commonScore L ε M u g) (ENNReal.ofReal p) (haar 1) := by
  have hc := memLp_forceCoeff hL ε M hp hp2
  obtain ⟨B, hB0, hB⟩ := exists_ae_bound_one hg
  have h1 : MemLp (fun x => g x 0) (ENNReal.ofReal p) (haar 1) :=
    (memLp_coord_of_memLp hg.memLp_grad 0).mono_exponent
      (by simpa using (ENNReal.ofReal_le_ofReal hp2.le : ENNReal.ofReal p ≤ ENNReal.ofReal 2))
  have h2 : MemLp (fun x => u x * -(kappa * inner ℝ M (Uprime L ε x)))
      (ENNReal.ofReal p) (haar 1) := by
    refine MemLp.mono (hc.const_mul B)
      (hg.memLp.aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_
    filter_upwards [hB] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB0]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have e : commonScore L ε M u g = fun x => 2 * g x 0 +
      u x * -(kappa * inner ℝ M (Uprime L ε x)) := by
    funext x; simp only [commonScore]; ring
  rw [e]
  exact (h1.const_mul 2).add h2

/-- A finite `L²` energy of a common score forces the common mean to vanish. -/
lemma commonMean_eq_zero_of_finite {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (M : EuclideanSpace ℝ (Fin 2)) (ρ : AbsoluteDensity 1)
    (hD : ∫⁻ x, ‖commonScore L ε M ρ.sqrt (weakGradient ρ.sqrt ρ.sqrt_mem) x‖ₑ ^ 2 ∂haar 1 < ⊤) :
    M = 0 := by
  by_contra hM
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  set g := weakGradient ρ.sqrt ρ.sqrt_mem with hg
  have hS : MemLp (commonScore L ε M ρ.sqrt g) 2 (haar 1) := by
    refine memLp_two_of_lintegral_lt_top ?_ hD
    have := memLp_commonScore hL ε M hw (p := 1) le_rfl one_lt_two
    exact this.aestronglyMeasurable
  have hg0 : MemLp (fun x => g x 0) 2 (haar 1) := memLp_coord_of_memLp hw.memLp_grad 0
  have hK : MemLp (fun x => kappa * (ρ.sqrt x * inner ℝ M (Uprime L ε x))) 2
      (haar 1) := by
    have e : (fun x => kappa * (ρ.sqrt x * inner ℝ M (Uprime L ε x))) =
        (fun x => 2 * g x 0) - commonScore L ε M ρ.sqrt g := by
      funext x; simp only [Pi.sub_apply, commonScore]; ring
    rw [e]
    exact (hg0.const_mul 2).sub hS
  obtain ⟨w, hwc, hwae, -, -⟩ := exists_continuous_rep_one hw
  have hmass : ∫ x, w x ^ 2 ∂haar 1 = 1 := by
    exact (integral_congr_ae (hwae.mono fun x hx => by simp [hx])).trans ρ.mass_one
  refine false_of_finite_weighted_directional hL hε hwc hmass hM ?_
  have hk0 : kappa ≠ 0 := by unfold kappa; norm_num
  have hlt := lintegral_lt_top_of_memLp_two hK
  have h1 : ∫⁻ x, ‖w x * inner ℝ M (Uprime L ε x)‖ₑ ^ 2 ∂haar 1 =
      ‖kappa⁻¹‖ₑ ^ 2 * ∫⁻ x, ‖kappa * (ρ.sqrt x *
        inner ℝ M (Uprime L ε x))‖ₑ ^ 2 ∂haar 1 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
    refine lintegral_congr_ae (hwae.mono fun x hx => ?_)
    simp only
    rw [← hx, ← mul_pow, ← enorm_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
  rw [h1]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) hlt

/-- The feature mean of the barycenter is the weighted sum of the species feature means. -/
lemma featureMean_barycenter {L : ℝ} (hL : 0 < L) (ε : ℝ) (F : SpeciesFamily 1) :
    featureMean L ε (barycenter F) =
      ∑ s, F.weight s • featureMean L ε (F.density s) := by
  unfold featureMean
  have e : ∀ y, (barycenter F).density y • Ufeat L ε y =
      ∑ s, F.weight s • ((F.density s).density y • Ufeat L ε y) := by
    intro y
    rw [SpeciesFamily.barycenter_density_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul]
    rfl
  simp_rw [e]
  have hi : ∀ s ∈ (Finset.univ : Finset (Fin F.count)), Integrable
      (fun y => F.weight s • ((F.density s).density y • Ufeat L ε y)) (haar 1) :=
    fun s _ => (integrable_density_smul_Ufeat hL ε (F.density s)).smul (F.weight s)
  rw [integral_finsetSum _ hi]
  exact Finset.sum_congr rfl fun s _ => integral_smul _ _

/-- The species dissipation as a weighted sum of `L²` energies of the common scores. -/
lemma speciesDissipation_eq {L : ℝ} (hL : 0 < L) (ε : ℝ) (b : AbsoluteDrift (modelData hL ε))
    (F : SpeciesFamily 1) :
    speciesDissipation (modelData hL ε) b F =
      ∑ s, ENNReal.ofReal (F.weight s) *
        ∫⁻ x, ‖commonScore L ε (∑ t, F.weight t • featureMean L ε (F.density t))
          (F.density s).sqrt (F.sqrtGradient s) x‖ₑ ^ 2 ∂haar 1 := by
  unfold speciesDissipation
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  have hF := force_ae_eq hL ε b (barycenter F)
  rw [featureMean_barycenter hL ε F] at hF
  refine lintegral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [enorm_sq_eq_ofReal, norm_tangent_one]
  congr 2
  simp only [commonScore, hx, forceVec]
  simp
  ring

/-- Under the exact decomposition and zero barycenter mean, `G_θ = ∑ θ_s H(ρ_s m | m)`. -/
lemma speciesGap_eq_of_zero {L : ℝ} (hL : 0 < L) {ε : ℝ} (hdec : FreeEnergyDecomposition L ε)
    (F : SpeciesFamily 1) (hM : ∑ s, F.weight s • featureMean L ε (F.density s) = 0) :
    (speciesGap (modelData hL ε) F : ℝ) =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
        (haar 1)).toReal := by
  have hb : featureMean L ε (barycenter F) = 0 := by
    rw [featureMean_barycenter hL ε F]; exact hM
  have h1 := scalarGap_eq_of_zero hL hdec (barycenter F) hb
  have h2 : (scalarGap (modelData hL ε) (barycenter F) : ℝ) =
      (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus 1))
        (haar 1)).toReal := by
    have := congrArg ENNReal.toReal h1
    simpa using this
  have hfin := (absoluteDensity_entropy_finite (barycenter F)).2.2.1
  have hE : densityFreeEnergy (modelData hL ε) (barycenter F) =
      (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus 1))
        (haar 1)).toReal +
        potentialEnergy (modelData hL ε) (densityMeasure (barycenter F)) +
        (1 / 2 : ℝ) * interactionEnergy (modelData hL ε)
          (densityMeasure (barycenter F)) := by
    have h := coe_densityFreeEnergy (modelData hL ε) (barycenter F)
    rw [freeEnergy_eq_real _ _ hfin] at h
    exact EReal.coe_eq_coe_iff.mp h
  have h3 := speciesGap_eq (modelData hL ε) F
  rw [coe_scalarGap, hE] at h2
  linarith

/-- **RUF035.** For every finite species family of absolute-admissible densities with positive
weights (any `q ≥ 1`, any weights) and every weak-drift provider `b`, the species dissipation
`D_θ = ∑ θ_s ‖S_s‖₂²` with common score `S_s = 2 u_s' - κ u_s M̄·U'` is finite iff the barycenter
mean `M̄ = ∑ θ_s M_s` vanishes (the individual `M_s` need not). On that class
`D_θ = ∑ θ_s I_s`, `I_s = 4 ∫ |u_s'|²`, and `G_θ = ∑ θ_s H(ρ_s m | m)`. -/
theorem finite_species_dissipation_exactly_means_zero_barycenter_mean {L : ℝ} (hL : 0 < L)
    {ε : ℝ} (hε : ε ≠ 0) (hdec : FreeEnergyDecomposition L ε)
    (b : AbsoluteDrift (modelData hL ε)) (F : SpeciesFamily 1) :
    (speciesDissipation (modelData hL ε) b F < ⊤ ↔
      ∑ s, F.weight s • featureMean L ε (F.density s) = 0) ∧
    (∑ s, F.weight s • featureMean L ε (F.density s) = 0 →
      speciesDissipation (modelData hL ε) b F =
          ENNReal.ofReal (∑ s, F.weight s *
            (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)) ∧
        (speciesGap (modelData hL ε) F : ℝ) =
          ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
            (haar 1)).toReal) := by
  set M := ∑ s, F.weight s • featureMean L ε (F.density s) with hMdef
  have hsum := speciesDissipation_eq hL ε b F
  rw [← hMdef] at hsum
  have hzero : M = 0 → speciesDissipation (modelData hL ε) b F =
      ENNReal.ofReal (∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)) := by
    intro hM0
    rw [hsum, ENNReal.ofReal_sum_of_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _))]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hw := F.isWeakGradient_sqrtGradient s
    have hint : Integrable (fun x => ‖F.sqrtGradient s x‖ ^ 2) (haar 1) :=
      hw.memLp_grad.norm.integrable_sq
    rw [ENNReal.ofReal_mul (F.weight_nonneg s), ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal (hint.const_mul 4)
        (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [enorm_sq_eq_ofReal]
    congr 1
    simp only [commonScore, hM0, inner_zero_left, mul_zero, sub_zero]
    have := norm_tangent_one (F.sqrtGradient s x)
    rw [this]
    ring
  have hiff : speciesDissipation (modelData hL ε) b F < ⊤ ↔ M = 0 := by
    refine ⟨fun h => ?_, fun hM0 => by rw [hzero hM0]; exact ENNReal.ofReal_lt_top⟩
    let s0 : Fin F.count := ⟨0, F.count.pos⟩
    rw [hsum] at h
    have h0 := ENNReal.sum_lt_top.1 h s0 (Finset.mem_univ _)
    have h1 : ∫⁻ x, ‖commonScore L ε M (F.density s0).sqrt (F.sqrtGradient s0) x‖ₑ ^ 2 ∂haar 1
        < ⊤ := by
      by_contra hcon
      have htop : ∫⁻ x, ‖commonScore L ε M (F.density s0).sqrt (F.sqrtGradient s0) x‖ₑ ^ 2
          ∂haar 1 = ⊤ := not_lt_top_iff.1 hcon
      rw [htop, ENNReal.mul_top] at h0
      · exact lt_irrefl _ h0
      · simpa using F.weight_pos s0
    exact commonMean_eq_zero_of_finite hL hε M (F.density s0) h1
  exact ⟨hiff, fun hM0 => ⟨hzero hM0, speciesGap_eq_of_zero hL hdec F hM0⟩⟩

end DGPS.Examples.RoughBoundary.Nonlinear
