import DGPS.Examples.AttractiveXYTiltEX024
import DGPS.Examples.CriticalRecoveryBridgesEX021
import DGPS.Examples.CriticalRecoveryAsymptoticsEX021
import DGPS.Examples.EngineeredRankOneRates
import DGPS.Circle.BesselConcavity
import DGPS.Circle.BesselMonotonicity
import DGPS.Variational.SpeciesInclusion

/-!
# Explicit remote stationary obstruction (EX025)

For the attractive XY model at `κ = 4`, `h = 1/2`, the scalar equation `4 g(s) - s = 1/2`
(with `g = besselRatio`) has a root `s₁ ∈ (0,1)` and a root `s₂ ∈ (1,4)`. Their remote states
`q_{-s}` are smooth, positive, zero-dissipation states of positive gap, so both nonlinear rates
vanish and the zero rate is attained at positive gap by one species. The unique global
equilibrium satisfies the EX024 Hessian bound `H ≥ Id/9` (since `h + κ = 9/2`) and the Gaussian
bound with constant `4π² e⁻⁹ / 9`.
-/

open MeasureTheory

namespace DGPS.Examples.AttractiveXYTiltRemoteEX025

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Examples.ThreeSpeciesCircle hiding besselI
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity
open DGPS.Examples.CriticalRecoveryBridgesEX021 DGPS.Examples.CriticalRecoveryAsymptoticsEX021

/-- The auxiliary function whose zeros are the remote roots `4 g(s) - s = 1/2`. -/
noncomputable def remoteF_EX025 (s : ℝ) : ℝ := 4 * besselRatio s - s - 1 / 2

theorem remoteF_continuous_EX025 : Continuous remoteF_EX025 := by
  unfold remoteF_EX025
  exact ((continuous_const.mul DGPS.Circle.BesselConcavity.continuous_besselRatio).sub
    continuous_id).sub continuous_const

theorem remoteF_zero_EX025 : remoteF_EX025 0 = -(1 / 2) := by
  unfold remoteF_EX025
  rw [DGPS.Circle.BesselConcavity.ratio_zero]
  norm_num

theorem remoteF_one_pos_EX025 : 0 < remoteF_EX025 1 := by
  unfold remoteF_EX025
  have := DGPS.Circle.BesselConcavity.four_ratio_one_sub_gt
  linarith

theorem remoteF_four_neg_EX025 : remoteF_EX025 4 < 0 := by
  unfold remoteF_EX025
  have := DGPS.Circle.BesselMonotonicity.besselRatio_lt_one 4
  linarith

/-- Two remote roots of `4 g(s) - s = 1/2`: one in `(0,1)` and one in `(1,4)`. -/
theorem remote_roots_exist_EX025 :
    ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 1 < s₂ ∧ s₂ < 4 ∧
      4 * besselRatio s₁ - s₁ = 1 / 2 ∧ 4 * besselRatio s₂ - s₂ = 1 / 2 := by
  have hc := remoteF_continuous_EX025
  obtain ⟨s₁, hs₁, hz₁⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (remoteF_EX025 0) (remoteF_EX025 1) from
      ⟨by rw [remoteF_zero_EX025]; norm_num, remoteF_one_pos_EX025⟩)
  obtain ⟨s₂, hs₂, hz₂⟩ := intermediate_value_Ioo' (by norm_num : (1 : ℝ) ≤ 4) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (remoteF_EX025 4) (remoteF_EX025 1) from
      ⟨remoteF_four_neg_EX025, remoteF_one_pos_EX025⟩)
  unfold remoteF_EX025 at hz₁ hz₂
  exact ⟨s₁, s₂, hs₁.1, hs₁.2, hs₂.1, hs₂.2, by linarith, by linarith⟩

theorem exists_positive_remote_root_EX025 :
    ∃ s : ℝ, 0 < s ∧ 4 * besselRatio s - s = 1 / 2 := by
  obtain ⟨s₁, -, h1, -, -, -, h3, -⟩ := remote_roots_exist_EX025
  exact ⟨s₁, h1, h3⟩

/-- The remote root equation at `t = -s`, using oddness of `besselRatio`. -/
theorem remote_root_iff_EX025 {s : ℝ} :
    -s = 4 * besselRatio (-s) + 1 / 2 ↔ 4 * besselRatio s - s = 1 / 2 := by
  rw [DGPS.Circle.BesselMoments.besselRatio_neg]
  constructor <;> intro h <;> linarith

/-- The von Mises trial law is the tilted law `xyLaw_EX023 t`. -/
theorem density_identity_EX025 (t : ℝ) :
    (DGPS.densityMeasure (vonMisesAbsoluteDensityEX021 t) : Measure (DGPS.Torus 1)) =
      (xyLaw_EX023 t : Measure (DGPS.Torus 1)) := by
  rw [law_density_EX023, DGPS.densityMeasure_coe]
  congr 1
  funext x
  congr 1
  show vonMisesRootEX021 t x ^ 2 = _
  rw [vonMisesRoot_sqEX021, vonMisesTorusDensity_exp_EX021, div_eq_inv_mul]

theorem densityMeasure_eq_EX025 (t : ℝ) :
    DGPS.densityMeasure (vonMisesAbsoluteDensityEX021 t) = xyLaw_EX023 t := by
  apply ProbabilityMeasure.toMeasure_injective
  exact density_identity_EX025 t

theorem vonMises_density_pos_EX025 (t : ℝ) (x : DGPS.Torus 1) :
    0 < (vonMisesAbsoluteDensityEX021 t).density x := by
  show 0 < vonMisesRootEX021 t x ^ 2
  unfold vonMisesRootEX021
  exact pow_pos (mul_pos (inv_pos.2 (Real.sqrt_pos.2
    (DGPS.Circle.BesselMoments.besselI_zero_pos t))) (Real.exp_pos _)) 2

theorem vonMises_density_smooth_EX025 (t : ℝ) :
    DGPS.IsSmoothPeriodic (vonMisesAbsoluteDensityEX021 t).density := by
  have h := vonMisesRoot_smoothEX021 t
  unfold DGPS.IsSmoothPeriodic at h ⊢
  exact h.pow 2

/-- Zero dissipation of the remote state, through the frozen-law identity. -/
theorem remote_dissipation_zero_EX025 {s : ℝ} (hs : 4 * besselRatio s - s = 1 / 2) :
    DGPS.scalarDissipation (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2))
      (vonMisesAbsoluteDensityEX021 (-s)) = 0 := by
  have hfz := DGPS.Examples.AttractiveXYTiltEX024.xyFrozen_measure_EX024 (-s)
  have key := DGPS.Examples.EngineeredRankOneRates.fisher_self (xyFrozen (-s) 0)
  rw [hfz] at key
  have hF : xyFrozenLaw 4 (1 / 2) (xyLaw_EX023 (-s) : Measure (DGPS.Torus 1)) =
      xyFrozen (-s) 0 := by
    show xyFrozen (1 / 2 + 4 * xyZ1 (xyLaw_EX023 (-s) : Measure (DGPS.Torus 1)))
      (4 * xyZ2 (xyLaw_EX023 (-s) : Measure (DGPS.Torus 1))) = xyFrozen (-s) 0
    rw [law_cos_EX023, law_sin_EX023, mul_zero, DGPS.Circle.BesselMoments.besselRatio_neg]
    congr 1
    linarith
  rw [scalarDissipation_attractiveXY, density_identity_EX025 (-s), hF]
  exact key

/-- Positive gap of the remote state, from the strict energy comparison. -/
theorem remote_gap_pos_EX025 {s : ℝ} (hs0 : 0 < s) :
    0 < DGPS.scalarGap (attractiveXY 4 (1 / 2)) (vonMisesAbsoluteDensityEX021 (-s)) := by
  have hlt : DGPS.freeEnergyMinimum (attractiveXY 4 (1 / 2)) <
      DGPS.freeEnergy (attractiveXY 4 (1 / 2))
        (DGPS.densityMeasure (vonMisesAbsoluteDensityEX021 (-s))) := by
    rw [densityMeasure_eq_EX025 (-s)]
    calc DGPS.freeEnergyMinimum (attractiveXY 4 (1 / 2))
        ≤ DGPS.freeEnergy (attractiveXY 4 (1 / 2)) (xyLaw_EX023 s) :=
          iInf_le (fun μ : ProbabilityMeasure (DGPS.Torus 1) =>
            DGPS.freeEnergy (attractiveXY 4 (1 / 2)) μ) (xyLaw_EX023 s)
      _ < DGPS.freeEnergy (attractiveXY 4 (1 / 2)) (xyLaw_EX023 (-s)) :=
          negative_energy_strict_EX023 (κ := 4) (h := 1 / 2) (by norm_num) hs0
  rw [DGPS.scalarGap_pos_iff]
  rw [← DGPS.coe_freeEnergyMinimumReal, ← DGPS.coe_densityFreeEnergy] at hlt
  exact EReal.coe_lt_coe_iff.mp hlt

theorem scalarRate_zero_EX025 :
    DGPS.scalarRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 := by
  obtain ⟨s, hs0, hs⟩ := exists_positive_remote_root_EX025
  have hq : DGPS.scalarQuotient (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2))
      (vonMisesAbsoluteDensityEX021 (-s)) = 0 := by
    unfold DGPS.scalarQuotient
    rw [remote_dissipation_zero_EX025 hs, ENNReal.zero_div]
  exact le_antisymm
    ((DGPS.scalarRate_le_quotient (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2))
      (vonMisesAbsoluteDensityEX021 (-s)) (remote_gap_pos_EX025 hs0)).trans hq.le)
    zero_le

theorem speciesRate_zero_EX025 :
    DGPS.speciesRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 :=
  le_antisymm
    ((DGPS.speciesRate_le_scalarRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2))).trans
      scalarRate_zero_EX025.le)
    zero_le

theorem species_attained_EX025 :
    ∃ ρ : DGPS.AbsoluteDensity 1,
      0 < DGPS.speciesGap (attractiveXY 4 (1 / 2)) (DGPS.SpeciesFamily.single ρ) ∧
      DGPS.speciesQuotient (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2))
        (DGPS.SpeciesFamily.single ρ) = 0 := by
  obtain ⟨s, hs0, hs⟩ := exists_positive_remote_root_EX025
  refine ⟨vonMisesAbsoluteDensityEX021 (-s), ?_, ?_⟩
  · rw [DGPS.speciesGap_single]
    exact remote_gap_pos_EX025 hs0
  · rw [DGPS.speciesQuotient_single]
    unfold DGPS.scalarQuotient
    rw [remote_dissipation_zero_EX025 hs, ENNReal.zero_div]

theorem gauss_const_EX025 :
    4 * Real.pi ^ 2 * ((1 / 2 : ℝ) / (1 / 2 + 4)) * Real.exp (-(2 * (1 / 2 + 4))) =
      4 * Real.pi ^ 2 * Real.exp (-9) / 9 := by
  have h1 : (1 / 2 : ℝ) / (1 / 2 + 4) = 1 / 9 := by norm_num
  have h2 : -(2 * ((1 / 2 : ℝ) + 4)) = -9 := by norm_num
  rw [h1, h2]
  ring

/-- The unique global equilibrium at `κ = 4`, `h = 1/2`: the positive root `t` with `1/2 < t < 9/2`,
its law is the unique free-energy minimizer, and its density Hessian and Gaussian rate obey the
explicit bounds. -/
theorem equilibrium_EX025 :
    ∃ t : ℝ, 0 < t ∧ t = 4 * besselRatio t + 1 / 2 ∧
      IsCircleDistributionalStationary (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) ∧
      (∀ ν : ProbabilityMeasure (Torus 1),
        freeEnergy (attractiveXY 4 (1 / 2)) ν = freeEnergyMinimum (attractiveXY 4 (1 / 2)) ↔
          ν = xyLaw_EX023 t) ∧
      1 / 2 < t ∧ t < 9 / 2 ∧
      (∀ f : centeredL2 (xyLaw_EX023 t),
        1 / 9 * ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) f)) ∧
      (∀ hH : IsCoerciveDensityHessian (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t),
        ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-9) / 9) ≤
          gaussianRate (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) hH) := by
  obtain ⟨-, -, t, ht, he, -, -, -, hbs, hmin, -⟩ :=
    DGPS.Examples.tilted_stationary_scalar_root_and_global_minimizer (κ := 4) (h := 1 / 2)
      (by norm_num) (by norm_num)
  obtain ⟨hb1, hb2⟩ := hbs (by norm_num)
  obtain ⟨-, -, hlow, -, -, hG, -⟩ :=
    DGPS.Examples.tilted_centered_hessian_and_local_gaussian_bound (κ := 4) (h := 1 / 2) (t := t)
      (by norm_num) (by norm_num) ht he
  have hcoef : (1 / 9 : ℝ) ≤ 1 / 2 / t := by
    rw [le_div_iff₀ ht]
    linarith
  have hGauss : ∀ hH : IsCoerciveDensityHessian (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t),
      ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-9) / 9) ≤
        gaussianRate (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) hH := by
    intro hH
    rw [← gauss_const_EX025]
    exact (hG hH).2.2
  exact ⟨t, ht, he, root_stationary_EX023 (κ := 4) (h := 1 / 2) he, hmin, hb1, by linarith,
    fun f => le_trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖f‖)) (hlow f), hGauss⟩

end DGPS.Examples.AttractiveXYTiltRemoteEX025

namespace DGPS.Examples

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Examples.ThreeSpeciesCircle hiding besselI
open DGPS.Circle.BesselMoments
open DGPS.Examples.CriticalRecoveryBridgesEX021
open DGPS.Examples.AttractiveXYTiltRemoteEX025

/-- EX025. For the attractive XY model at `κ = 4`, `h = 1/2`:
(i) there are roots `s₁ ∈ (0,1)` and `s₂ ∈ (1,4)` of `4 g(s) - s = 1/2`;
(ii) each positive root gives a smooth positive density `ρ` whose law is `q_{-s}`, which is
stationary, has zero scalar dissipation and positive scalar gap;
(iii) the unique global equilibrium has `H ≥ Id/9` and Gaussian rate at least `4π² e⁻⁹ / 9`;
(iv) the scalar and species rates both vanish;
(v) one species at positive gap attains the zero species quotient. -/
theorem explicit_remote_stationary_obstruction :
    (∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 1 < s₂ ∧ s₂ < 4 ∧
      4 * besselRatio s₁ - s₁ = 1 / 2 ∧ 4 * besselRatio s₂ - s₂ = 1 / 2) ∧
    (∀ s : ℝ, 0 < s → 4 * besselRatio s - s = 1 / 2 →
      ∃ ρ : DGPS.AbsoluteDensity 1,
        DGPS.densityMeasure ρ = xyLaw_EX023 (-s) ∧
        (∀ x, 0 < ρ.density x) ∧
        DGPS.IsSmoothPeriodic ρ.density ∧
        IsCircleDistributionalStationary (attractiveXY 4 (1 / 2)) (xyLaw_EX023 (-s)) ∧
        DGPS.scalarDissipation (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) ρ = 0 ∧
        0 < DGPS.scalarGap (attractiveXY 4 (1 / 2)) ρ) ∧
    (∃ t : ℝ, 0 < t ∧ t = 4 * besselRatio t + 1 / 2 ∧
      IsCircleDistributionalStationary (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) ∧
      (∀ ν : ProbabilityMeasure (Torus 1),
        freeEnergy (attractiveXY 4 (1 / 2)) ν = freeEnergyMinimum (attractiveXY 4 (1 / 2)) ↔
          ν = xyLaw_EX023 t) ∧
      1 / 2 < t ∧ t < 9 / 2 ∧
      (∀ f : centeredL2 (xyLaw_EX023 t),
        1 / 9 * ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) f)) ∧
      (∀ hH : IsCoerciveDensityHessian (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t),
        ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-9) / 9) ≤
          gaussianRate (attractiveXY 4 (1 / 2)) (xyLaw_EX023 t) hH)) ∧
    (DGPS.scalarRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 ∧
      DGPS.speciesRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0) ∧
    (∃ ρ : DGPS.AbsoluteDensity 1,
      0 < DGPS.speciesGap (attractiveXY 4 (1 / 2)) (DGPS.SpeciesFamily.single ρ) ∧
      DGPS.speciesQuotient (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2))
        (DGPS.SpeciesFamily.single ρ) = 0) := by
  refine ⟨remote_roots_exist_EX025, ?_, equilibrium_EX025,
    ⟨scalarRate_zero_EX025, speciesRate_zero_EX025⟩, species_attained_EX025⟩
  intro s hs0 hs
  exact ⟨vonMisesAbsoluteDensityEX021 (-s), densityMeasure_eq_EX025 (-s),
    fun x => vonMises_density_pos_EX025 (-s) x, vonMises_density_smooth_EX025 (-s),
    root_stationary_EX023 (κ := 4) (h := 1 / 2) (remote_root_iff_EX025.mpr hs),
    remote_dissipation_zero_EX025 hs, remote_gap_pos_EX025 hs0⟩

end DGPS.Examples
