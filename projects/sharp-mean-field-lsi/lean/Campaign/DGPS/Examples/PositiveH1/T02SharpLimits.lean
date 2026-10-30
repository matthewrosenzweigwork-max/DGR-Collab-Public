import DGPS.Lipschitz.SharpLimits
import DGPS.Examples.PositiveH1.Regularity
import DGPS.Examples.PositiveH1.NonlinearRates
import DGPS.Examples.PositiveH1.TransferDirichlet
import DGPS.Examples.PositiveH1.UpperLimits
import DGPS.Lipschitz.T01BoundedComparisonUniformity
import DGPS.Lipschitz.T01UniformParticleDefective

/-! Fixed-cutoff T01 specialization and the full-domain transfer for the single rough H1 model.
Every cutoff is chosen before its particle threshold; the rough interaction never depends on N.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.PositiveH1

open DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Transfer

/-- Every finite Fourier cutoff satisfies the direct Euclidean Lipschitz hypothesis. -/
theorem positiveH1Cutoff_lipschitz (M : ℕ) : LipschitzData (positiveH1Cutoff M) := by
  have hs : IsSmoothPeriodic (pairFun (positiveH1Cutoff M).W) := by
    rw [pairFun_cutoff]
    exact (diffKernel_aux kappa (RM M 0) (isSmoothPeriodic_RM M)).1
  obtain ⟨L, _, hL⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hs
  refine ⟨⟨0, fun x y => by simp [positiveH1Cutoff]⟩, L, fun x y x' y' => ?_⟩
  have h := hL ![x 0, y 0] ![x' 0, y' 0]
  rw [Regularity.torusDist_two] at h
  have he : ∀ z : Torus 1, (fun _ : Fin 1 => z 0) = z := fun z => funext fun i => by
    rw [Subsingleton.elim i 0]
  simpa [pairFun, he] using h

/-- T01 applies separately to each fixed cutoff, with both exact limits a0. -/
theorem positive_h1_fixed_cutoff_rates (M : ℕ) (hM : 2 ≤ M) :
    Tendsto (fun N : ℕ+ => particleRateAll (positiveH1Cutoff M) N) atTop
      (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2))) ∧
    Tendsto (fun N : ℕ+ => particleRateSym (positiveH1Cutoff M) N) atTop
      (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2))) := by
  let hLip := positiveH1Cutoff_lipschitz M
  have hrate := Nonlinear.exact_nonlinear_rates_for_rough_and_every_fixed_smooth_cutoff.2 M hM
    (lipschitz_absoluteDrift (positiveH1Cutoff M) hLip)
  exact ⟨by simpa only [hrate.2] using
    DGPS.Lipschitz.sharp_limits_all 1 (by decide) (positiveH1Cutoff M) hLip,
    by simpa only [hrate.1] using
      DGPS.Lipschitz.sharp_limits_sym 1 (by decide) (positiveH1Cutoff M) hLip⟩

/-- For fixed M and positive s<a0, one threshold controls every full cutoff H1 test. -/
theorem positive_h1_fixed_cutoff_eventual_lsi (M : ℕ) (hM : 2 ≤ M)
    {s : ℝ} (hs : 0 < s) (hsa : s < 4 * Real.pi ^ 2) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 (positiveH1Cutoff M) N,
      particleEntropy (positiveH1Cutoff M) N f ≤
        ENNReal.ofReal ((2 / s) * particleEnergy (positiveH1Cutoff M) N f) := by
  let hLip := positiveH1Cutoff_lipschitz M
  have hrate := (Nonlinear.exact_nonlinear_rates_for_rough_and_every_fixed_smooth_cutoff.2 M hM
    (lipschitz_absoluteDrift (positiveH1Cutoff M) hLip)).2
  have hlt : ENNReal.ofReal s < speciesRate (positiveH1Cutoff M)
      (lipschitz_absoluteDrift (positiveH1Cutoff M) hLip) := by
    rw [hrate]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hsa
  obtain ⟨N0, hN0⟩ := DGPS.Lipschitz.eventual_lsi_all 1 (by decide) (positiveH1Cutoff M)
    hLip s hs hlt
  exact eventually_atTop.mpr ⟨N0, hN0⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Memorandum (7.5): a fixed smooth cutoff transfers its exact LSI to every rough H1 test. -/
theorem positive_h1_fixed_cutoff_transfer (M : ℕ) (hM : 2 ≤ M)
    {s η : ℝ} (hs : 0 < s) (hsa : s < 4 * Real.pi ^ 2) (hη : 0 < η) :
    let δ := ((2 / s) * (1 + η⁻¹) / 4 + 1) * h1033_eps M
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      particleEntropy (kernelData (1 / 100)) N f ≤
        ENNReal.ofReal (((2 / s) * (1 + η) + δ) * particleEnergy (kernelData (1 / 100)) N f +
          δ * ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
  dsimp only
  filter_upwards [positive_h1_fixed_cutoff_eventual_lsi M hM hs hsa] with N hN f
  obtain ⟨hg, _, _, hEg⟩ := full_domain_dirichlet_transfer N M hM f
  let g : ParticleH1 (positiveH1Cutoff M) N := ⟨fun X => f X * hNM N M X, hg⟩
  obtain ⟨hg', _, hfFin, _, hEnt, hlog⟩ := full_domain_entropy_change_of_density N M f
  change (particleEntropy (kernelData (1 / 100)) N f).toReal =
    (particleEntropy (positiveH1Cutoff M) N g).toReal +
      (∫ X, f X ^ 2 * tailT (1 / 100) N M X ∂particleLaw (kernelData (1 / 100)) N) +
      Real.log (K (1 / 100) N / KM N M) *
        (∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) at hEnt
  have hmass : 0 ≤ ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N :=
    integral_nonneg fun X => sq_nonneg _
  have hgs : (particleEntropy (positiveH1Cutoff M) N g).toReal ≤
      (2 / s) * particleEnergy (positiveH1Cutoff M) N g := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN g)
    exact hh.trans_eq (ENNReal.toReal_ofReal
      (mul_nonneg (div_nonneg (by norm_num) hs.le) (particleEnergy_nonneg g)))
  have htail := (common_vanishing_tail_coefficient.2 N M hM f).1
  have hreal : (particleEntropy (kernelData (1 / 100)) N f).toReal ≤
      (((2 / s) * (1 + η) + ((2 / s) * (1 + η⁻¹) / 4 + 1) * h1033_eps M) *
        particleEnergy (kernelData (1 / 100)) N f +
      (((2 / s) * (1 + η⁻¹) / 4 + 1) * h1033_eps M) *
        ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
    calc
      _ ≤ (2 / s) * particleEnergy (positiveH1Cutoff M) N g +
          h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
            ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
        rw [hEnt]
        exact (add_le_add (add_le_add hgs htail)
          (mul_nonpos_of_nonpos_of_nonneg hlog hmass)).trans_eq (by ring)
      _ ≤ (2 / s) * ((1 + η) * particleEnergy (kernelData (1 / 100)) N f +
          (1 + η⁻¹) * (h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
            ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) / 4)) +
          h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
            ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) :=
        add_le_add (mul_le_mul_of_nonneg_left (hEg η hη)
          (by positivity : 0 ≤ (2 / s))) le_rfl
      _ = _ := by ring
  rw [← ENNReal.ofReal_toReal hfFin]
  exact ENNReal.ofReal_le_ofReal hreal

set_option backward.isDefEq.respectTransparency.types false in
/-- Memorandum (7.6), uniformly on every full rough particle H1 domain. -/
theorem positive_h1_vanishing_defect (ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      particleEntropy (kernelData (1 / 100)) N f ≤ ENNReal.ofReal
        (((2 / (4 * Real.pi ^ 2)) + ζ) * particleEnergy (kernelData (1 / 100)) N f +
          ζ * ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
  let a : ℝ := 4 * Real.pi ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  let t : ℝ := min 1 (ζ * a / 16)
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htζ : t ≤ ζ * a / 16 := min_le_right _ _
  let s : ℝ := a / (1 + t)
  have hs : 0 < s := div_pos ha (by positivity)
  have hsa : s < a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith [mul_pos ha ht])
  have heq : (2 / s) * (1 + t) = 2 / a + (4 * t + 2 * t ^ 2) / a := by
    dsimp [s]
    field_simp [ha.ne', (by positivity : (1 + t) ≠ 0)]
    ring
  have hsur : (4 * t + 2 * t ^ 2) / a < ζ / 2 := by
    apply (div_lt_iff₀ ha).mpr
    have htt : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
    nlinarith [mul_pos hζ ha]
  have hbase : (2 / s) * (1 + t) < 2 / a + ζ / 2 := by rw [heq]; linarith
  let δ : ℕ → ℝ := fun M => ((2 / s) * (1 + t⁻¹) / 4 + 1) * h1033_eps M
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using common_vanishing_tail_coefficient.1.const_mul
      ((2 / s) * (1 + t⁻¹) / 4 + 1)
  obtain ⟨M, hM, hδM⟩ := ((eventually_ge_atTop 2).and
    (hδ.eventually (gt_mem_nhds (half_pos hζ)))).exists
  have hβ : (2 / s) * (1 + t) + δ M ≤ 2 / a + ζ := by linarith
  have hδζ : δ M ≤ ζ := by linarith
  have htransfer := positive_h1_fixed_cutoff_transfer M hM hs hsa ht
  filter_upwards [htransfer] with N hN f
  refine (hN f).trans (ENNReal.ofReal_le_ofReal ?_)
  exact add_le_add
    (mul_le_mul_of_nonneg_right hβ (particleEnergy_nonneg f))
    (mul_le_mul_of_nonneg_right hδζ (integral_nonneg fun X => sq_nonneg _))

/-- Vanishing full-domain defects give the exact bounded comparison at a0 for the rough model. -/
theorem positive_h1_bounded_comparison :
    ∀ B E0 ε : ℝ, 0 < B → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 (kernelData (1 / 100)) N,
        (∀ X, |f X| ≤ B) → particleEnergy (kernelData (1 / 100)) N f ≤ E0 →
        ENNReal.ofReal ((4 * Real.pi ^ 2) / 2) * particleEntropy (kernelData (1 / 100)) N f ≤
          ENNReal.ofReal (particleEnergy (kernelData (1 / 100)) N f + ε) := by
  intro B E0 ε hB hE0 hε
  let a : ℝ := 4 * Real.pi ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  let ζ : ℝ := ε / (a * (E0 + B ^ 2 + 1))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  filter_upwards [positive_h1_vanishing_defect ζ hζ] with N hN f hbf hEf
  have hmass : (∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) ≤ B ^ 2 := by
    calc
      (∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) ≤
          ∫ _X, B ^ 2 ∂particleLaw (kernelData (1 / 100)) N := by
        exact integral_mono_of_nonneg (Eventually.of_forall fun X => sq_nonneg _)
          (integrable_const _) (Eventually.of_forall fun X => by
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f X)) (hbf X) 2)
      _ = _ := by simp
  have hmul := mul_le_mul_of_nonneg_left (hN f)
    (by positivity : 0 ≤ ENNReal.ofReal (a / 2))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a / 2)] at hmul
  refine hmul.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsmall : a / 2 * ζ * (E0 + B ^ 2) ≤ ε := by
    have hp : 0 < E0 + B ^ 2 + 1 := by positivity
    have heq : a / 2 * ζ * (E0 + B ^ 2) =
        (ε / 2) * ((E0 + B ^ 2) / (E0 + B ^ 2 + 1)) := by
      dsimp only [ζ]
      field_simp [ha.ne', hp.ne']
    rw [heq]
    have hratio : (E0 + B ^ 2) / (E0 + B ^ 2 + 1) ≤ 1 :=
      (div_le_iff₀ hp).mpr (by linarith)
    calc _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ ε := by linarith

  calc a / 2 * ((2 / a + ζ) * particleEnergy (kernelData (1 / 100)) N f +
      ζ * ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) =
        particleEnergy (kernelData (1 / 100)) N f + a / 2 * ζ *
          (particleEnergy (kernelData (1 / 100)) N f +
            ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by field_simp [ha.ne']; ring
    _ ≤ particleEnergy (kernelData (1 / 100)) N f + a / 2 * ζ * (E0 + B ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hEf hmass) (by positivity))
    _ ≤ _ := add_le_add le_rfl hsmall

set_option backward.isDefEq.respectTransparency.types false in
/-- The full rough particle Poincare lower bounds follow from the actual vanishing defects. -/
theorem positive_h1_eventual_poincare {ρ : ℝ} (hρ : ρ < 4 * Real.pi ^ 2) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      ρ * ((∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) -
        (∫ X, f X ∂particleLaw (kernelData (1 / 100)) N) ^ 2) ≤
          particleEnergy (kernelData (1 / 100)) N f := by
  let η : ℝ := 2 / (4 * Real.pi ^ 2) + 1
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (positive_h1_vanishing_defect 1 one_pos)
  have htail : ∃ n0 : ℕ, ∃ B : ℝ, ∀ N : ℕ+, n0 ≤ N →
      ∀ f : ParticleH1 (kernelData (1 / 100)) N, True →
        particleEntropy (kernelData (1 / 100)) N f ≤
          ENNReal.ofReal (η * particleEnergy (kernelData (1 / 100)) N f) +
          ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2)
            ∂particleLaw (kernelData (1 / 100)) N := by
    refine ⟨N0, 1, fun N hN f _ => ?_⟩
    have h := hN0 N hN f
    have hm : ENNReal.ofReal (∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) =
        ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw (kernelData (1 / 100)) N :=
      ofReal_integral_eq_lintegral_ofReal
        (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
        (Eventually.of_forall fun X => sq_nonneg _)
    simp only [one_mul] at h
    change particleEntropy (kernelData (1 / 100)) N f ≤ ENNReal.ofReal
      (η * particleEnergy (kernelData (1 / 100)) N f +
        ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) at h
    rw [ENNReal.ofReal_add (mul_nonneg hη.le (particleEnergy_nonneg f))
      (integral_nonneg fun X => sq_nonneg _), hm] at h
    simpa only [ENNReal.ofReal_one, one_mul] using h
  obtain ⟨C, hC, hdef⟩ := DGPS.Lipschitz.particle_defective_uniform_of_eventual
    (kernelData (1 / 100)) hη (fun _ _ => True) htail
  have hmerged : ∀ N : ℕ+, ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      particleEntropy (kernelData (1 / 100)) N f ≤ ENNReal.ofReal
        (η * particleEnergy (kernelData (1 / 100)) N f +
          C * ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
    intro N f
    have h := hdef N f trivial
    have hm : (∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw (kernelData (1 / 100)) N) =
        ENNReal.ofReal (∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) :=
      (ofReal_integral_eq_lintegral_ofReal
        (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
        (Eventually.of_forall fun X => sq_nonneg _)).symm
    rw [hm, ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_add (mul_nonneg hη.le (particleEnergy_nonneg f))
        (mul_nonneg hC (integral_nonneg fun X => sq_nonneg _))] at h
    exact h
  exact DGPS.Lipschitz.eventual_particle_poincare_of_bounded_comparison (kernelData (1 / 100))
    (by positivity) positive_h1_bounded_comparison ⟨η, C, hmerged⟩ hρ

set_option backward.isDefEq.respectTransparency.types false in
/-- Every strict positive subrate is an eventual exact LSI on the original full rough domain. -/
theorem positive_h1_eventual_exact_lsi {r : ℝ} (hr : 0 < r) (hra : r < 4 * Real.pi ^ 2) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 positiveH1 N,
      particleEntropy positiveH1 N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy positiveH1 N f) := by
  let a : ℝ := 4 * Real.pi ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  let R : ℝ := (r + a) / 2
  have hrR : r < R := by dsimp [R, a]; linarith
  have hRa : R < a := by dsimp [R, a]; linarith
  have hR : 0 < R := hr.trans hrR
  let ζ : ℝ := 2 * (a - R) / (a * R)
  have hζ : 0 < ζ := by
    exact div_pos (mul_pos two_pos (sub_pos.mpr hRa)) (mul_pos ha hR)
  have hc : 2 / a + ζ = 2 / R := by
    dsimp [ζ]
    field_simp [ha.ne', hR.ne']
    ring
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (positive_h1_vanishing_defect ζ hζ)
  have htail : ∀ N ≥ N0, ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      particleEntropy (kernelData (1 / 100)) N f ≤ ENNReal.ofReal
        (2 * particleEnergy (kernelData (1 / 100)) N f / R +
          ζ * ∫ X, f X ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
    intro N hN f
    have h := hN0 N hN f
    change _ ≤ ENNReal.ofReal ((2 / a + ζ) * particleEnergy (kernelData (1 / 100)) N f + _) at h
    rw [hc] at h
    convert h using 1 <;> congr 1 <;> ring
  have hLSI := DGPS.Lipschitz.eventual_particle_lsi_after_concrete_tightening
    (kernelData (1 / 100)) hR N0 ζ htail
    ⟨a, hRa.le, positive_h1_bounded_comparison⟩
    (fun ρ hρ => positive_h1_eventual_poincare (hρ.trans hRa)) hr hrR
  have hmodel : kernelData (1 / 100) = positiveH1 := by
    simpa only [kappa] using Recovery.kernelData_kappa_eq
  exact Eq.mp (congrArg (fun A : InteractionData 1 =>
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f)) hmodel) hLSI

end DGPS.Examples.PositiveH1
