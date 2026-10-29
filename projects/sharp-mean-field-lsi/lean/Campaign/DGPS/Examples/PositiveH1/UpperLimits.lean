import Mathlib
import DGPS.Examples.PositiveH1.ProductEntropyInformation
import DGPS.Examples.PositiveH1.UpperRecovery
import DGPS.Examples.PositiveH1.Harmonic
import DGPS.Particle.Rates

/-!
# H1042: both particle upper limits

For the fixed rough kernel `positiveH1` (`κ = 1/100`),
`limsup_N r_N^all ≤ limsup_N r_N^sym ≤ a₀`.

The first-harmonic product states `f_{Nt}` (H1041) are symmetric competitors with
`2 E_N / Ent ≤ (N I_t + κ² J_t) / (2 N H_t)`; letting `N → ∞` at fixed `t` gives
`limsup r_N^sym ≤ I_t / (2 H_t)`, and only then `t → 0` (H1013) gives `a₀`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.PositiveH1.Recovery
open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.Particle DGPS.Analysis.CircleMoments

/-- Fixed `t`: `limsup_N r_N^sym ≤ I_t / (2 H_t)` for the kernel `κ ≥ 0`. -/
theorem sym_limsup_le_fixed_t {κ : ℝ} {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0)
    (hle : |t| ≤ 1 / 2) :
    limsup (fun N : ℕ+ => particleRateSym (kernelData κ) N) atTop ≤
      ENNReal.ofReal (firstHarmonicFisher t / (2 * firstHarmonicEntropy t)) := by
  set J : ℝ := firstHarmonicForceMoment t with hJ
  set I : ℝ := firstHarmonicFisher t with hI
  set H : ℝ := firstHarmonicEntropy t with hH
  set u : ℕ+ → ℝ := fun N => (I + κ ^ 2 * J / (N : ℝ)) / (2 * H) with hu
  have hHpos : 0 < H := by
    obtain ⟨-, -, -, -, -, -, -, hpos, -⟩ :=
      exact_first_harmonic_product_entropy_and_information κ 1 ht ht0 hle
    simpa [hH] using hpos
  have hlim : Tendsto u atTop (𝓝 (I / (2 * H))) := by
    have h1 : Tendsto (fun N : ℕ+ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      (tendsto_one_div_atTop_nhds_zero_nat).comp tendsto_PNat_val_atTop_atTop
    have h2 : Tendsto (fun N : ℕ+ => (I + κ ^ 2 * J * (1 / (N : ℝ))) / (2 * H)) atTop
        (𝓝 ((I + κ ^ 2 * J * 0) / (2 * H))) :=
      ((h1.const_mul (κ ^ 2 * J)).const_add I).div_const _
    simp only [mul_zero, add_zero] at h2
    refine h2.congr fun N => ?_
    simp only [hu]; ring_nf
  have hbound : ∀ N : ℕ+, particleRateSym (kernelData κ) N ≤ ENNReal.ofReal (u N) := by
    intro N
    obtain ⟨hmem, hsym, -, -, -, hent, hge, hpos, h4E, hJ0, -⟩ :=
      exact_first_harmonic_product_entropy_and_information κ N ht ht0 hle
    set f : ParticleH1 (kernelData κ) N :=
      ⟨root κ (fun _ : Fin N => firstHarmonicDensity t ht), hmem⟩ with hf
    set E' : ℝ := (N : ℝ) * H + κ * A / 2 + Real.log (K κ N) with hE'
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 N.pos
    have hNH : 0 < (N : ℝ) * H := mul_pos hNpos hHpos
    have hE'pos : 0 < E' := lt_of_lt_of_le hNH hge
    have hent' : particleEntropy (kernelData κ) N f = ENNReal.ofReal E' := hent
    have hfpos : 0 < particleEntropy (kernelData κ) N f := by
      rw [hent']; exact ENNReal.ofReal_pos.2 hE'pos
    refine (particleRateSym_le_quotient (kernelData κ) N f hsym hfpos).trans ?_
    unfold particleQuotient
    rw [hent', ← ENNReal.ofReal_div_of_pos hE'pos]
    refine ENNReal.ofReal_le_ofReal ?_
    have hEn : 0 ≤ particleEnergy (kernelData κ) N f := particleEnergy_nonneg f
    have hc : κ ^ 2 * ((N : ℝ) - 1) * J / (N : ℝ) ≤ κ ^ 2 * J := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
      rw [div_le_iff₀ hNpos]
      have : 0 ≤ κ ^ 2 * J := mul_nonneg (sq_nonneg _) hJ0
      nlinarith
    calc 2 * particleEnergy (kernelData κ) N f / E'
        ≤ 2 * particleEnergy (kernelData κ) N f / ((N : ℝ) * H) :=
          div_le_div_of_nonneg_left (by positivity) hNH hge
      _ ≤ (I + κ ^ 2 * J / (N : ℝ)) / (2 * H) := by
          rw [div_le_div_iff₀ hNH (by positivity)]
          have h4 : 4 * particleEnergy (kernelData κ) N f =
              (N : ℝ) * I + κ ^ 2 * ((N : ℝ) - 1) * J / (N : ℝ) := h4E
          have : (I + κ ^ 2 * J / (N : ℝ)) * ((N : ℝ) * H) =
              ((N : ℝ) * I + κ ^ 2 * J) * H := by field_simp
          rw [this]
          have hH0 := hHpos.le
          nlinarith
  calc limsup (fun N : ℕ+ => particleRateSym (kernelData κ) N) atTop
      ≤ limsup (fun N : ℕ+ => ENNReal.ofReal (u N)) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound)
    _ = ENNReal.ofReal (I / (2 * H)) :=
        ((ENNReal.tendsto_ofReal hlim)).limsup_eq

/-- `limsup_N r_N^sym ≤ a₀` for the kernel `κ`: the limit `t → 0` after `N → ∞`. -/
theorem sym_limsup_le_a0 (κ : ℝ) :
    limsup (fun N : ℕ+ => particleRateSym (kernelData κ) N) atTop ≤ ENNReal.ofReal a0 := by
  obtain ⟨-, -, -, -, hlim⟩ := Harmonic.first_harmonic_recovery_and_normalized_taylor_bounds
  have hlim' := ENNReal.tendsto_ofReal hlim
  refine ge_of_tendsto hlim' ?_
  have h1 : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| < 1 / 2 := by
    have : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 / 2 := by
      have hc : Continuous fun t : ℝ => |t| := continuous_abs
      exact hc.continuousAt.eventually_lt continuousAt_const (by norm_num)
    exact eventually_nhdsWithin_of_eventually_nhds this
  filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht0
  exact sym_limsup_le_fixed_t (by linarith) ht0 ht1.le

/-- **H1042.** For the fixed rough kernel `positiveH1`,
`limsup_N r_N^all ≤ limsup_N r_N^sym ≤ a₀`. -/
theorem both_particle_upper_limits :
    limsup (fun N : ℕ+ => particleRateAll positiveH1 N) atTop ≤
        limsup (fun N : ℕ+ => particleRateSym positiveH1 N) atTop ∧
      limsup (fun N : ℕ+ => particleRateSym positiveH1 N) atTop ≤ ENNReal.ofReal a0 := by
  refine ⟨limsup_le_limsup (Eventually.of_forall fun N => particleRateAll_le_sym positiveH1 N), ?_⟩
  rw [← kernelData_kappa_eq]
  exact sym_limsup_le_a0 kappa

end DGPS.Examples.PositiveH1.Recovery
