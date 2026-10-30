import DGPS.Lipschitz.T01GroundStateSobolev
import DGPS.Lipschitz.T01ParticleReferenceBridge
import FullLabeledLSI.Paper.Prop23ReplaceB

/-!
# Actual ground-state energy replacement

Minkowski compares the shifted reference energies for two actual weak potentials. The root is
the canonical current Gibbs/reference transform; no legacy equilibrium hypothesis is imported.
The force difference is integrated under the actual particle law.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL

private theorem actual_ref_grad_measurable {d N : ℕ} (P : BoundedPositiveReference d)
    {μ : ProbabilityMeasure (Torus d)} (hP : P.measure = (μ : Measure (Torus d)))
    {u : Config N d → ℝ} (hu : HasWeakGrad (u ∘ unflat)) (i : Fin N) (k : Fin d) :
    AEStronglyMeasurable (fun X => weakGradC u X i k)
      (QN (μ : Measure (Torus d)) N) := by
  have hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal P.upper • haar d := by
    rw [← hP]
    exact P.measure_le_smul_haar
  have hm := ((isWeakGrad_weakGrad hu).aestronglyMeasurable_grad (i, k)).mono_ac
    (Spectral.ac_map_flat hup)
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d))
      (QN (μ : Measure (Torus d)) N) ((QN (μ : Measure (Torus d)) N).map flat) :=
    ⟨measurable_flat, rfl⟩
  exact hm.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving

private theorem actual_root_shEn_rpow_half_le_aux {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleH1 A N) {B : ℝ} (hB : ∀ᵐ X ∂particleLaw A N, |f X| ≤ B)
    {U₁ U₂ D : Config N d → ℝ} (h₁ : HasWeakGrad (U₁ ∘ unflat))
    (h₂ : HasWeakGrad (U₂ ∘ unflat))
    (hDq : ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, ∀ i k,
      weakGradC D X i k ^ 2 = (weakGradC U₁ X i k - weakGradC U₂ X i k) ^ 2) :
    (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U₁) ^ (1 / 2 : ℝ) ≤
      (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U₂) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (B / 2) *
          (∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂particleLaw A N) ^ (1 / 2 : ℝ) := by
  have hB0 : 0 ≤ B := by
    obtain ⟨X, hX⟩ := hB.exists
    exact (abs_nonneg _).trans hX
  obtain ⟨gΨ, hgΨ⟩ := centeredParticleRoot_memH1 A hA μ N f
  have hΨmem := (legacy_particle_reference_form (frozenGibbs A μ) hgΨ).1
  rw [hfix] at hΨmem
  have hΨ : HasWeakGrad (centeredParticleRoot A μ N f ∘ unflat) := hΨmem.1
  set Ψ := centeredParticleRoot A μ N f with hΨdef
  have mΨ : AEStronglyMeasurable Ψ (QN (μ : Measure (Torus d)) N) :=
    SharpLSI.FL.Spectral.memLp_of_H1 hΨmem |>.aestronglyMeasurable
  have hmain : (shEn (μ : Measure (Torus d)) Ψ U₁) =
      ∫⁻ X, ENNReal.ofReal (∑ i, ∑ k,
        ((weakGradC Ψ X i k + 1 / 2 * Ψ X * weakGradC U₂ X i k) +
          (1 / 2 * Ψ X * (weakGradC U₁ X i k - weakGradC U₂ X i k))) ^ 2) ∂QN (μ : Measure (Torus d)) N := by
    unfold shEn
    refine lintegral_congr fun X => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring
  have mink := lintegral_minkowski_dsum (ν := QN (μ : Measure (Torus d)) N)
    (fun X i k => weakGradC Ψ X i k + 1 / 2 * Ψ X * weakGradC U₂ X i k)
    (fun X i k => 1 / 2 * Ψ X * (weakGradC U₁ X i k - weakGradC U₂ X i k))
    (fun i k => (actual_ref_grad_measurable (frozenGibbs A μ) hfix hΨ i k).add
      ((mΨ.const_mul (1 / 2)).mul (actual_ref_grad_measurable (frozenGibbs A μ) hfix h₂ i k)))
    (fun i k => (mΨ.const_mul (1 / 2)).mul
      ((actual_ref_grad_measurable (frozenGibbs A μ) hfix h₁ i k).sub (actual_ref_grad_measurable (frozenGibbs A μ) hfix h₂ i k)))
  rw [hmain]
  refine mink.trans (add_le_add (le_of_eq rfl) ?_)
  -- the `b`-term
  have h1 : ∫⁻ X, ENNReal.ofReal (∑ i, ∑ k,
        (1 / 2 * Ψ X * (weakGradC U₁ X i k - weakGradC U₂ X i k)) ^ 2) ∂QN (μ : Measure (Torus d)) N =
      ∫⁻ X, ENNReal.ofReal (centeredParticleDensity A μ N X) *
        ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂QN (μ : Measure (Torus d)) N := by
    refine lintegral_congr_ae ?_
    filter_upwards [hDq] with X hX
    have hg : gradSqC D X = ∑ i, ∑ k, (weakGradC U₁ X i k - weakGradC U₂ X i k) ^ 2 := by
      unfold gradSqC
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hX i k
    have hΨ2 : Ψ X ^ 2 = f X ^ 2 * (centeredParticleDensity A μ N X) := by
      simpa only [hΨdef, mul_comm] using centeredParticleRoot_sq A μ N f X
    rw [← ENNReal.ofReal_mul (centeredParticleDensity_pos A μ N X).le,
      sum_half_mul_sq_loc, hg, hΨ2]
    congr 1; ring
  have h3 : ∫⁻ X, ENNReal.ofReal (centeredParticleDensity A μ N X) *
        ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂QN (μ : Measure (Torus d)) N =
      ∫⁻ X, ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂particleLaw A N :=
    (lintegral_particleLaw_eq_centered A μ hfix N
      (fun X => ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X))).symm
  have h4 : ∫⁻ X, ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂particleLaw A N ≤
      ENNReal.ofReal ((B / 2) ^ 2) * ∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂particleLaw A N := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hB.mono fun X hX => ?_)
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hg0 : 0 ≤ gradSqC D X :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hf2 : f X ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hX 2
    have : 1 / 4 * f X ^ 2 ≤ (B / 2) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hg0
  rw [h1, h3]
  calc (∫⁻ X, ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂particleLaw A N) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((B / 2) ^ 2) * ∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂particleLaw A N) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h4 (by norm_num)
    _ = ENNReal.ofReal (B / 2) * (∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂particleLaw A N) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
          ← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith)]


private theorem actual_ref_weakGradC_sub {d : ℕ} (P : BoundedPositiveReference d)
    {μ : ProbabilityMeasure (Torus d)} (hP : P.measure = (μ : Measure (Torus d))) {N : ℕ}
    {U₁ U₂ : Config N d → ℝ} (h₁ : HasWeakGrad (U₁ ∘ unflat))
    (h₂ : HasWeakGrad (U₂ ∘ unflat)) :
    ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, ∀ i k,
      weakGradC (fun Y => U₁ Y - U₂ Y) X i k = weakGradC U₁ X i k - weakGradC U₂ X i k := by
  have hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal P.upper • haar d := by
    rw [← hP]
    exact P.measure_le_smul_haar
  have hD := isWeakGrad_sub_loc (isWeakGrad_weakGrad h₁) (isWeakGrad_weakGrad h₂)
  have hh := (Spectral.ac_map_flat (N := N) hup).ae_le (weakGrad_ae_eq hD)
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d))
      (QN (μ : Measure (Torus d)) N) ((QN (μ : Measure (Torus d)) N).map flat) :=
    ⟨measurable_flat, rfl⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae hh] with X hX
  intro i k
  exact congrFun hX (i, k)

/-- The exact current root obeys the two-sided shifted-energy square-root comparison. -/
theorem actual_root_shEn_rpow_half_le {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleH1 A N) {B : ℝ} (hB : ∀ᵐ X ∂particleLaw A N, |f X| ≤ B)
    {U₁ U₂ : Config N d → ℝ} (h₁ : HasWeakGrad (U₁ ∘ unflat))
    (h₂ : HasWeakGrad (U₂ ∘ unflat)) :
    (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U₁) ^ (1 / 2 : ℝ) ≤
      (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U₂) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (B / 2) * (∫⁻ X, ENNReal.ofReal
          (gradSqC (fun Y => U₁ Y - U₂ Y) X) ∂particleLaw A N) ^ (1 / 2 : ℝ) ∧
    (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U₂) ^ (1 / 2 : ℝ) ≤
      (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U₁) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (B / 2) * (∫⁻ X, ENNReal.ofReal
          (gradSqC (fun Y => U₁ Y - U₂ Y) X) ∂particleLaw A N) ^ (1 / 2 : ℝ) := by
  have hsub := actual_ref_weakGradC_sub (frozenGibbs A μ) hfix h₁ h₂
  refine ⟨actual_root_shEn_rpow_half_le_aux A hA μ hfix N f hB h₁ h₂ ?_,
    actual_root_shEn_rpow_half_le_aux A hA μ hfix N f hB h₂ h₁ ?_⟩
  · filter_upwards [hsub] with X hX i k
    rw [hX i k]
  · filter_upwards [hsub] with X hX i k
    rw [hX i k]
    ring

/-- The legacy shifted form at the actual centered potential is the actual particle energy. -/
theorem actual_root_shEn_eq_particleEnergy {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleH1 A N) :
    shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f)
      (centeredParticlePotential A μ N) = ENNReal.ofReal (particleEnergy A N f) := by
  obtain ⟨gU, hU, hgU⟩ := centeredParticlePotential_has_bounded_weakGradient A hA μ N
  have hR := centeredParticleRootGradient_isWeakGradient A μ N f hU hgU
  have haU := (legacy_particle_reference_form (frozenGibbs A μ) hU).2.1
  have haR := (legacy_particle_reference_form (frozenGibbs A μ) hR).2.1
  rw [hfix] at haU haR
  rw [centeredParticleRoot_energy_identity A μ hfix N f gU]
  unfold shEn
  refine lintegral_congr_ae ?_
  filter_upwards [haU, haR] with X hXU hXR
  congr 1
  simp only [hXU, hXR, particleTangentNormSq_eq, Pi.add_apply, Pi.smul_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

/-- A small actual Gibbs force error uniformly controls the shifted-energy replacement error.
The threshold is chosen before particle number and the bounded Sobolev observable. -/
theorem actual_root_energy_replacement_threshold {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (B M : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (N : ℕ+) (f : ParticleH1 A N) (U_R : Config N d → ℝ),
        HasWeakGrad (U_R ∘ unflat) → (∀ᵐ X ∂particleLaw A N, |f X| ≤ B) →
        particleEnergy A N f ≤ M →
        (∫⁻ X, ENNReal.ofReal (gradSqC
          (fun Y => centeredParticlePotential A μ N Y - U_R Y) X) ∂particleLaw A N) ≤
            ENNReal.ofReal η →
        |particleEnergy A N f -
          (shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) U_R).toReal| ≤ ε := by
  intro ε hε
  set s : ℝ := Real.sqrt (max M 0) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set β : ℝ := max (B / 2) 0 with hβ
  have hβ0 : 0 ≤ β := le_max_right _ _
  set δ₀ : ℝ := min 1 (ε / (2 * s + 1)) with hδ₀
  have h2s : 0 < 2 * s + 1 := by linarith
  have hδ0 : 0 < δ₀ := lt_min one_pos (div_pos hε h2s)
  have hδε : δ₀ * (2 * s + δ₀) ≤ ε := by
    calc δ₀ * (2 * s + δ₀) ≤ δ₀ * (2 * s + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [min_le_left 1 (ε / (2 * s + 1))]) hδ0.le
      _ ≤ ε / (2 * s + 1) * (2 * s + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) h2s.le
      _ = ε := div_mul_cancel₀ _ h2s.ne'
  set η : ℝ := (δ₀ / (β + 1)) ^ 2 with hη
  have hη0 : 0 < η := by positivity
  refine ⟨η, hη0, fun N f U_R hUR hB hE hI => ?_⟩
  obtain ⟨gU, hU, -⟩ := centeredParticlePotential_has_bounded_weakGradient A hA μ N
  have h₁ : HasWeakGrad (centeredParticlePotential A μ N ∘ unflat) :=
    ⟨_, legacy_isWeakGrad_of_particle hU⟩
  obtain ⟨hA1, hA2⟩ := actual_root_shEn_rpow_half_le A hA μ hfix N f hB h₁ hUR
  have hM : shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f)
      (centeredParticlePotential A μ N) ≤ ENNReal.ofReal M := by
    rw [actual_root_shEn_eq_particleEnergy A hA μ hfix N f]
    exact ENNReal.ofReal_le_ofReal hE
  set x₁ := shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) (centeredParticlePotential A μ N) with hx₁
  set x₂ := shEn (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) (U_R) with hx₂
  set I := ∫⁻ X, ENNReal.ofReal (gradSqC (fun Y => centeredParticlePotential A μ N Y - U_R Y) X)
    ∂particleLaw A N with hIdef
  have hδE : ENNReal.ofReal (B / 2) * I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal δ₀ := by
    have hI' : I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (δ₀ / (β + 1)) := by
      calc I ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal η) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hI (by norm_num)
        _ = ENNReal.ofReal (δ₀ / (β + 1)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hη0.le (by norm_num), ← Real.sqrt_eq_rpow, hη,
              Real.sqrt_sq (by positivity)]
    calc ENNReal.ofReal (B / 2) * I ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal β * ENNReal.ofReal (δ₀ / (β + 1)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hI'
      _ = ENNReal.ofReal (β * (δ₀ / (β + 1))) := (ENNReal.ofReal_mul hβ0).symm
      _ ≤ ENNReal.ofReal δ₀ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith
  have hx₁top : x₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM
  have hA1' : x₁ ^ (1 / 2 : ℝ) ≤ x₂ ^ (1 / 2 : ℝ) + ENNReal.ofReal δ₀ := hA1.trans (add_le_add le_rfl hδE)
  have hA2' : x₂ ^ (1 / 2 : ℝ) ≤ x₁ ^ (1 / 2 : ℝ) + ENNReal.ofReal δ₀ := hA2.trans (add_le_add le_rfl hδE)
  have hx₂top : x₂ ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at hA2'
    have : x₁ ^ (1 / 2 : ℝ) + ENNReal.ofReal δ₀ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) hx₁top, ENNReal.ofReal_ne_top⟩
    exact this (top_le_iff.1 hA2')
  have r1 := toReal_rpow_half_le_loc hδ0.le hA1' hx₂top
  have r2 := toReal_rpow_half_le_loc hδ0.le hA2' hx₁top
  have hx₁le : x₁.toReal ≤ max M 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM
    rwa [ENNReal.toReal_ofReal'] at this
  have hrs : Real.sqrt x₁.toReal ≤ s := Real.sqrt_le_sqrt hx₁le
  have key := real_sq_diff_loc (Real.sqrt_nonneg x₁.toReal) (Real.sqrt_nonneg x₂.toReal) hrs hδ0.le
    r2 r1 hδε
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg] at key
  simpa only [hx₁, hx₂, actual_root_shEn_eq_particleEnergy A hA μ hfix N f,
    ENNReal.toReal_ofReal (particleEnergy_nonneg f)] using key


end DGPS.Lipschitz
