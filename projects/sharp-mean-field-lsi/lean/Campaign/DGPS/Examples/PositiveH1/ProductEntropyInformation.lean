import Mathlib
import DGPS.Examples.PositiveH1.UpperRecovery
import DGPS.Examples.PositiveH1.Harmonic

/-!
# H1041: exact entropy and information of the first-harmonic product state

For `0 < |t| ≤ 1/2` and `ν_N = ρ_t^{⊗N}` the root `f_{Nt} = √(dν_N/dP_N)` is a symmetric `H¹(P_N)`
test function with `Ent(f²) = N H_t + κ A / 2 + log K_N ≥ N H_t > 0` and
`4 E_N(f) = N I_t + κ² (N - 1) J_t / N`, `0 ≤ J_t ≤ (1 + |t|) ‖R′‖₂²`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace DGPS.Examples.PositiveH1.Recovery
open DGPS DGPS.Particle DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
  DGPS.Examples.PositiveH1.Nonlinear DGPS.Examples.PositiveH1.Model
  DGPS.Analysis.CircleMoments

theorem pei_pairMeas_zero {t : ℝ} (ht : |t| < 1) :
    pairMeas (firstHarmonicDensity t ht) (firstHarmonicDensity t ht) = 0 := by
  unfold pairMeas
  rw [integral_R_sub]
  have : ∀ n : ℕ, a n * ‖measureFourier
      (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1)) n‖ ^ 2 = 0 := by
    intro n
    rw [h1011_measureFourier, firstHarmonicDensity_density ht]
    by_cases hn : 2 ≤ n
    · rw [Harmonic.coeff_freq_firstHarmonic t hn]; simp
    · rw [a_zero_of_lt (by omega)]; simp
  simp [this]

theorem pei_label_eq (κ : ℝ) (N : ℕ+) (ρ : AbsoluteDensity 1) {B : ℝ}
    (hB : ∀ᵐ y ∂haar 1, ρ.density y ≤ B) (hconv : ∀ y, conv dR ρ.density y = 0) (i : Fin N) :
    ∫ x, (score ρ (x i) + κ / (N : ℝ) * ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2
        ∂labeledProduct (fun _ : Fin N => ρ) =
      ∫ y, ρ.density y * score ρ y ^ 2 ∂haar 1 +
      (κ / (N : ℝ)) ^ 2 * (((N : ℝ) - 1) *
        ∫ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 ∂haar 1) := by
  set c : ℝ := κ / (N : ℝ) with hc
  set μ : Fin N → Measure (Torus 1) := fun _ => (densityMeasure ρ : Measure (Torus 1)) with hμ
  have hν : labeledProduct (fun _ : Fin N => ρ) = Measure.pi μ := rfl
  set F : (Fin N → Torus 1) → ℝ := fun x => (score ρ (x i) + c *
        ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2 with hF
  have hFint : Integrable F (Measure.pi μ) := by
    rw [← hν]; exact cfv_integrable_F κ N (fun _ => ρ) i
  have hmap := cfv_map_update μ i
  have hFmap : Integrable F (((μ i).prod (Measure.pi μ)).map
      (fun p : Torus 1 × (Fin N → Torus 1) => Function.update p.2 i p.1)) := by
    rw [hmap]; exact hFint
  have hint2 : Integrable (fun p : Torus 1 × (Fin N → Torus 1) => F (Function.update p.2 i p.1))
      ((μ i).prod (Measure.pi μ)) :=
    (integrable_map_measure hFmap.aestronglyMeasurable (cfv_measurable_upd i).aemeasurable).1 hFmap
  have hLHS : ∫ x, F x ∂Measure.pi μ =
      ∫ t, ∫ x, F (Function.update x i t) ∂Measure.pi μ ∂μ i := by
    conv_lhs => rw [← hmap]
    rw [integral_map (cfv_measurable_upd i).aemeasurable (by rw [hmap]; exact hFint.1),
      integral_prod _ hint2]
  set a : Torus 1 → ℝ := score ρ with ha
  set W : Torus 1 → ℝ := fun t => c * ∑ j ∈ Finset.univ.erase i, conv dR ρ.density t with hW
  have hWc : Continuous W :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_driftField ρ)
  set A : Torus 1 → ℝ := fun t => (a t + W t) ^ 2 with hA
  set V : Torus 1 → ℝ := fun t => c ^ 2 * ∑ j ∈ Finset.univ.erase i,
      Var[fun y => dR (t - y); μ j] with hV
  have hT : ∀ t, ∫ x, F (Function.update x i t) ∂Measure.pi μ = A t + V t := by
    intro t
    have h1 : ∀ x : Fin N → Torus 1, F (Function.update x i t) =
        (a t + c * ∑ j ∈ Finset.univ.erase i, dR (t - x j)) ^ 2 := by
      intro x
      simp only [hF, ha, Function.update_self]
      congr 3
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.mem_erase.1 hj).1]
    simp_rw [h1]
    rw [cfv_fixed μ i (fun y => dR (t - y)) (fun j => cfv_memLp_dR_sub ρ hB t) (a t) c]
    simp only [hA, hW, hV, hμ, cfv_mean]
  have hAint : Integrable A (μ i) := by
    have := cfv_main_integrable ρ hWc
    rw [← cfv_integrable_densityMeasure_iff] at this
    exact this
  have hTint : Integrable (fun t => ∫ x, F (Function.update x i t) ∂Measure.pi μ) (μ i) :=
    hint2.integral_prod_left
  have hVint : Integrable V (μ i) := by
    have := hTint.sub hAint
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, hT]; ring
  have hsplit : ∫ x, F x ∂Measure.pi μ = ∫ t, A t ∂μ i + ∫ t, V t ∂μ i := by
    rw [hLHS]
    simp_rw [hT]
    exact integral_add hAint hVint
  -- evaluate the two pieces
  have hMA : ∫ t, A t ∂μ i = ∫ y, ρ.density y * score ρ y ^ 2 ∂haar 1 := by
    have h := integral_densityMeasure ρ A
    refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
    simp [hA, hW, ha, hconv]
  have hvar : ∀ t, Var[fun y => dR (t - y); (densityMeasure ρ : Measure (Torus 1))] =
      ∫ y, ρ.density y * dR (t - y) ^ 2 ∂haar 1 := by
    intro t
    rw [variance_eq_sub (cfv_memLp_dR_sub ρ hB t)]
    have e : ((densityMeasure ρ : Measure (Torus 1))[(fun y => dR (t - y)) ^ 2]) =
        ∫ y, dR (t - y) ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := by
      simp only [Pi.pow_apply]
    have e0 : ((densityMeasure ρ : Measure (Torus 1))[fun y => dR (t - y)]) = 0 := by
      show ∫ y, dR (t - y) ∂(densityMeasure ρ : Measure (Torus 1)) = 0
      rw [cfv_mean, hconv]
    rw [e, e0, integral_densityMeasure]
    simp
  have hcard : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    have : 1 ≤ (N : ℕ) := N.pos
    simp [Nat.cast_sub this]
  have hVform : ∀ t, V t = c ^ 2 * (((N : ℝ) - 1) * ∫ y, ρ.density y * dR (t - y) ^ 2 ∂haar 1) := by
    intro t
    simp only [hV, hμ, hvar, Finset.sum_const, nsmul_eq_mul, hcard]
  have hMV : ∫ t, V t ∂μ i = c ^ 2 * (((N : ℝ) - 1) *
      ∫ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 ∂haar 1) := by
    have h := integral_densityMeasure ρ V
    have h2 : ∀ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 =
        ρ.density x * ∫ y, ρ.density y * dR (x - y) ^ 2 ∂haar 1 := by
      intro x
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
    simp_rw [h2]
    rw [show (∫ t, V t ∂μ i) = ∫ t, V t ∂(densityMeasure ρ : Measure (Torus 1)) from rfl, h]
    simp_rw [hVform]
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  show ∫ x, F x ∂Measure.pi μ = _
  rw [hsplit, hMA, hMV]


theorem pei_fisher {t : ℝ} (ht : |t| < 1) :
    ∫ y, (firstHarmonicDensity t ht).density y * score (firstHarmonicDensity t ht) y ^ 2
      ∂haar 1 = firstHarmonicFisher t := by
  rw [firstHarmonicFisher_of_lt ht, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [cfv_main_ae (firstHarmonicDensity t ht) (fun _ => 0)] with y hy
  have hn : ‖weakGradient (firstHarmonicDensity t ht).sqrt
      (firstHarmonicDensity t ht).sqrt_mem y‖ ^ 2 =
      (weakGradient (firstHarmonicDensity t ht).sqrt (firstHarmonicDensity t ht).sqrt_mem y 0) ^ 2 := by
    rw [tangent_norm_sq]; simp
  simp only [add_zero, mul_zero] at hy
  rw [hy, hn]
  ring

theorem pei_J_nonneg (ρ : AbsoluteDensity 1) :
    0 ≤ ∫ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 ∂haar 1 :=
  integral_nonneg fun x => integral_nonneg fun y =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (ρ.density_nonneg x) (ρ.density_nonneg y))

theorem pei_J_le (ρ : AbsoluteDensity 1) {B : ℝ} (hB : ∀ᵐ y ∂haar 1, ρ.density y ≤ B) :
    ∫ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 ∂haar 1 ≤
      B * ∫ y, dR y ^ 2 ∂haar 1 := by
  have hinner : ∀ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 ≤
      ρ.density x * (B * ∫ y, dR y ^ 2 ∂haar 1) := by
    intro x
    have h2 : Integrable (fun y => dR (x - y) ^ 2) (haar 1) :=
      (memLp_sub_left memLp_dR x).integrable_sq
    have e : ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 =
        ρ.density x * ∫ y, ρ.density y * dR (x - y) ^ 2 ∂haar 1 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (ρ.density_nonneg x)
    calc ∫ y, ρ.density y * dR (x - y) ^ 2 ∂haar 1 ≤ ∫ y, B * dR (x - y) ^ 2 ∂haar 1 := by
          refine integral_mono_ae (cfv_integrable_rho_mul ρ hB x) (h2.const_mul B) ?_
          filter_upwards [hB] with y hy
          exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)
      _ = B * ∫ y, dR y ^ 2 ∂haar 1 := by rw [integral_const_mul, integral_sq_sub_left]
  calc ∫ x, ∫ y, dR (x - y) ^ 2 * (ρ.density x * ρ.density y) ∂haar 1 ∂haar 1
      ≤ ∫ x, ρ.density x * (B * ∫ y, dR y ^ 2 ∂haar 1) ∂haar 1 :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => integral_nonneg fun y =>
            mul_nonneg (sq_nonneg _) (mul_nonneg (ρ.density_nonneg x) (ρ.density_nonneg y)))
          (ρ.integrable_density.mul_const _) (Filter.Eventually.of_forall hinner)
    _ = B * ∫ y, dR y ^ 2 ∂haar 1 := by
        rw [integral_mul_const, ρ.integral_density, one_mul]


/-- `J_t = ∬ |R′(x - y)|² ρ_t(x) ρ_t(y) dm dm`. -/
noncomputable def firstHarmonicForceMoment (t : ℝ) : ℝ :=
  ∫ x, ∫ y, dR (x - y) ^ 2 * (firstHarmonic t x * firstHarmonic t y) ∂haar 1 ∂haar 1

theorem pei_density_le {t : ℝ} (ht : |t| < 1) :
    ∀ᵐ y ∂haar 1, (firstHarmonicDensity t ht).density y ≤ 1 + |t| := by
  refine Filter.Eventually.of_forall fun y => ?_
  have key : ∀ c : ℝ, |c| ≤ 1 → t * c ≤ |t| := fun c hc =>
    calc t * c ≤ |t * c| := le_abs_self _
      _ = |t| * |c| := abs_mul _ _
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = |t| := mul_one _
  rw [firstHarmonicDensity_density ht]
  unfold firstHarmonic
  exact add_le_add_right (key _ (abs_cosMode_le y)) 1

/-- **H1041.** For `0 < |t| ≤ 1/2` and `ν_N = ρ_t^{⊗N}`, the root `f_{Nt} = √(dν_N/dP_N)` is a
symmetric `H¹(P_N)` test function with exact entropy `N H_t + κ A / 2 + log K_N ≥ N H_t > 0` and
exact energy `4 E_N(f_{Nt}) = N I_t + κ² (N - 1) J_t / N`, where
`0 ≤ J_t ≤ (1 + |t|) ‖R′‖₂²`. -/
theorem exact_first_harmonic_product_entropy_and_information (κ : ℝ) (N : ℕ+) {t : ℝ}
    (ht : |t| < 1) (ht0 : t ≠ 0) (hle : |t| ≤ 1 / 2) :
    ∃ h : MemParticleH1 (kernelData κ) N
        (root κ (fun _ : Fin N => firstHarmonicDensity t ht)),
      IsSymmetricParticleTest
        (⟨root κ (fun _ : Fin N => firstHarmonicDensity t ht), h⟩ : ParticleH1 (kernelData κ) N) ∧
      ∫ x, root κ (fun _ : Fin N => firstHarmonicDensity t ht) x ^ 2
        ∂particleLaw (kernelData κ) N = 1 ∧
      labeledProduct (fun _ : Fin N => firstHarmonicDensity t ht) =
        (particleLaw (kernelData κ) N).withDensity
          (fun x => ENNReal.ofReal (root κ (fun _ : Fin N => firstHarmonicDensity t ht) x ^ 2)) ∧
      (fun x => root κ (fun _ : Fin N => firstHarmonicDensity t ht) x ^ 2) =ᵐ[particleLaw (kernelData κ) N]
        (fun x => ((labeledProduct (fun _ : Fin N => firstHarmonicDensity t ht)).rnDeriv
          (particleLaw (kernelData κ) N) x).toReal) ∧
      particleEntropy (kernelData κ) N
          ⟨root κ (fun _ : Fin N => firstHarmonicDensity t ht), h⟩ =
        ENNReal.ofReal ((N : ℝ) * firstHarmonicEntropy t + κ * A / 2 + Real.log (K κ N)) ∧
      (N : ℝ) * firstHarmonicEntropy t ≤
        (N : ℝ) * firstHarmonicEntropy t + κ * A / 2 + Real.log (K κ N) ∧
      0 < (N : ℝ) * firstHarmonicEntropy t ∧
      4 * particleEnergy (kernelData κ) N
          ⟨root κ (fun _ : Fin N => firstHarmonicDensity t ht), h⟩ =
        (N : ℝ) * firstHarmonicFisher t +
          κ ^ 2 * ((N : ℝ) - 1) * firstHarmonicForceMoment t / (N : ℝ) ∧
      0 ≤ firstHarmonicForceMoment t ∧
      firstHarmonicForceMoment t ≤ (1 + |t|) * ∫ y, dR y ^ 2 ∂haar 1 := by
  obtain ⟨-, C, -, hH, -⟩ := Harmonic.first_harmonic_recovery_and_normalized_taylor_bounds
  obtain ⟨-, -, -, -, -, hconv', -, hpos, hne, -, -⟩ := hH t ht ht0 hle
  obtain ⟨hmem, hmass, hν, hrn, -, -, hen⟩ :=
    rough_product_admissibility κ N (fun _ : Fin N => firstHarmonicDensity t ht)
  have hconv : ∀ y, conv dR (firstHarmonicDensity t ht).density y = 0 := by
    intro y; rw [firstHarmonicDensity_density ht]; exact hconv' y
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 N.ne_zero
  have hHent : entropyOf (firstHarmonicDensity t ht) = firstHarmonicEntropy t := by
    rw [firstHarmonicEntropy_of_lt ht]; rfl
  have hJeq : firstHarmonicForceMoment t =
      ∫ x, ∫ y, dR (x - y) ^ 2 * ((firstHarmonicDensity t ht).density x *
        (firstHarmonicDensity t ht).density y) ∂haar 1 ∂haar 1 := by
    simp only [firstHarmonicForceMoment, firstHarmonicDensity_density ht]
  obtain ⟨hfin, hex⟩ := labeled_entropy_exact κ (N := N) (fun _ : Fin N => firstHarmonicDensity t ht)
  have hsum : ∑ i : Fin N, ∑ j : Fin N,
      (if i = j then A else pairMeas (firstHarmonicDensity t ht) (firstHarmonicDensity t ht)) =
        (N : ℝ) * A := by
    rw [pei_pairMeas_zero ht]
    simp
  have hval : (relativeEntropy (labeledProduct (fun _ : Fin N => firstHarmonicDensity t ht))
      (particleLaw (kernelData κ) N)).toReal =
      (N : ℝ) * firstHarmonicEntropy t + κ * A / 2 + Real.log (K κ N) := by
    rw [hex, integral_U_labeled, hsum, hHent]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  refine ⟨hmem, isSymmetric_root κ N _ (fun _ _ => rfl) hmem, hmass, hν, hrn, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [particleEntropy_root κ N _ hmem, ← ENNReal.ofReal_toReal hfin, hval]
  · have h1 : -(κ * A / 2) ≤ Real.log (K κ N) := by
      rw [Real.le_log_iff_exp_le (K_pos κ N)]
      exact exp_le_K κ N
    linarith
  · rw [← hHent]
    unfold entropyOf
    have := ENNReal.toReal_pos hpos.ne' hne
    positivity
  · rw [hen hmem, Finset.sum_congr rfl fun i _ =>
      pei_label_eq κ N (firstHarmonicDensity t ht) (pei_density_le ht) hconv i, pei_fisher ht,
      ← hJeq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [hJeq]; exact pei_J_nonneg _
  · rw [hJeq]; exact pei_J_le _ (pei_density_le ht)

end DGPS.Examples.PositiveH1.Recovery
