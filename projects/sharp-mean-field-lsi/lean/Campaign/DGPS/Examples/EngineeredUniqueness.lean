import DGPS.Examples.EngineeredRankOneGap
import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel

/-!
# EX034: engineered uniqueness and Hessian

For every fixed `h ≥ 2`, the engineered rank-one model `DGPS.Models.engineeredModel h hh`
(`q = q_h ∘ angEquiv`, `φ = E_h ∘ angEquiv`, `η = 1`) satisfies:

* the free energy is strictly convex along mixtures of distinct finite-entropy probabilities;
* `μ_h` (the engineered reference) is the unique equilibrium, i.e. the unique probability with
  `F(ν) = F_*`;
* `μ_h` is the only distributionally stationary probability on the circle;
* the centered density Hessian at `μ_h` is `Id + E_h ⊗ E_h`, hence `≥ Id`.

The structure is proved for an arbitrary `RankOneModel` (`η ≥ 0`), via the exact identity
`F(ν) = H(ν | q) + (η/2) (∫ φ dν)²` and `F_* = 0`, and then specialised to the engineered model.
-/

open MeasureTheory InformationTheory
open DGPS DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.EngineeredUniqueness

section General

variable (M : RankOneModel)

theorem rankOne_ref_isProb : IsProbabilityMeasure M.ref.measure :=
  circ_isProb_withDensity (haar 1) (q := M.q) (fun x => (M.q_pos x).le)
    (integrable_of_continuous_torus M.q_cont) M.q_mass

/-- The reference `q m` of a rank-one model as a bundled probability measure. -/
noncomputable def rankOneRef : ProbabilityMeasure (Torus 1) :=
  ⟨M.ref.measure, rankOne_ref_isProb M⟩

theorem coe_rankOneRef :
    ((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) = M.ref.measure := rfl

theorem integral_ref (g : Torus 1 → ℝ) :
    ∫ x, g x ∂M.ref.measure = ∫ x, M.q x * g x ∂haar 1 :=
  circ_withDensity_integral (haar 1) M.q_cont.measurable (fun x => (M.q_pos x).le) g

theorem integral_φ_ref : ∫ x, M.φ x ∂M.ref.measure = 0 := by
  rw [integral_ref]
  rw [← M.φ_centered]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-! ### Exact free energy and equilibrium -/

theorem freeEnergy_eq_ref (ν : ProbabilityMeasure (Torus 1))
    (hH : relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≠ ⊤) :
    freeEnergy M.data ν = (((relativeEntropy (ν : Measure (Torus 1)) M.ref.measure).toReal +
      M.η / 2 * (∫ x, M.φ x ∂(ν : Measure (Torus 1))) ^ 2 : ℝ) : EReal) := by
  rw [freeEnergy_eq_real _ _ hH, EReal.coe_eq_coe_iff]
  linarith [(M.free_energy_identity ν hH).2]

theorem freeEnergyMinimum_eq_zero : freeEnergyMinimum M.data = ((0 : ℝ) : EReal) := by
  rw [← coe_freeEnergyMinimumReal, M.freeEnergyMinimumReal_eq_zero]

theorem entropy_ref_haar_ne_top : relativeEntropy M.ref.measure (haar 1) ≠ ⊤ := by
  have := (absoluteDensity_entropy_finite M.absQ).2.2.1
  rwa [M.densityMeasure_absQ] at this

theorem rankOne_equilibrium_iff (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy M.data ν = freeEnergyMinimum M.data ↔ ν = rankOneRef M := by
  have := rankOne_ref_isProb M
  rw [freeEnergyMinimum_eq_zero M]
  constructor
  · intro hF
    have hH : relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≠ ⊤ :=
      (finiteFreeEnergy_iff M.data ν).1 ⟨0, hF⟩
    rw [freeEnergy_eq_ref M ν hH, EReal.coe_eq_coe_iff] at hF
    have hne := (M.free_energy_identity ν hH).1
    have h1 : 0 ≤ (relativeEntropy (ν : Measure (Torus 1)) M.ref.measure).toReal :=
      ENNReal.toReal_nonneg
    have h2 : 0 ≤ M.η / 2 * (∫ x, M.φ x ∂(ν : Measure (Torus 1))) ^ 2 :=
      mul_nonneg (by linarith [M.η_nonneg]) (sq_nonneg _)
    have h3 : (relativeEntropy (ν : Measure (Torus 1)) M.ref.measure).toReal = 0 := by linarith
    have h4 : relativeEntropy (ν : Measure (Torus 1)) M.ref.measure = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h | h
      · exact h
      · exact absurd h hne
    rw [DGPS.Analysis.relativeEntropy_eq_klDiv, klDiv_eq_zero_iff] at h4
    exact ProbabilityMeasure.toMeasure_injective h4
  · rintro rfl
    have hH : relativeEntropy ((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
        (haar 1) ≠ ⊤ := entropy_ref_haar_ne_top M
    rw [freeEnergy_eq_ref M _ hH, coe_rankOneRef, integral_φ_ref]
    have h0 : relativeEntropy M.ref.measure M.ref.measure = 0 := by
      rw [DGPS.Analysis.relativeEntropy_eq_klDiv]; exact klDiv_self _
    rw [h0]
    simp

/-! ### Stationarity -/

/-- The potential `-log q + s φ`. -/
noncomputable def driftPotRO (s : ℝ) : Torus 1 → ℝ := fun y => -Real.log (M.q y) + s * M.φ y

theorem smooth_driftPotRO (s : ℝ) : IsSmoothPeriodic (driftPotRO M s) := by
  have hl := M.log_smooth
  have hp := M.φ_smooth
  unfold IsSmoothPeriodic at *
  unfold driftPotRO
  exact hl.neg.add (contDiff_const.mul hp)

theorem rankOne_drift_eq (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (x : Torus 1) :
    coordPartial 0 M.data.V x + ∫ y, coordPartial 0 (fun x' => M.data.W x' y) x ∂ν
      = coordPartial 0 (driftPotRO M (M.η * ∫ z, M.φ z ∂ν)) x := by
  have hφ := M.φ_smooth
  have hφφ : IsSmoothPeriodic (fun y => M.φ y * M.φ y) := hφ.mul hφ
  have hlog := M.log_smooth
  have hV : coordPartial 0 M.data.V x = -coordPartial 0 (fun y => Real.log (M.q y)) x
      + M.η / 2 * (M.φ x * coordPartial 0 M.φ x + coordPartial 0 M.φ x * M.φ x) := by
    have e : M.data.V = fun y => (-1) * Real.log (M.q y) + (M.η / 2) * (M.φ y * M.φ y) + 0 := by
      funext y
      show -Real.log (M.q y) + M.η / 2 * M.φ y ^ 2 = _
      ring
    rw [e, RankOneModel.coordPartial_lin hlog hφφ (-1) (M.η / 2) 0 x, DGPS.coordPartial_mul hφ hφ 0 x]
    ring
  have hW : ∀ y, coordPartial 0 (fun x' => M.data.W x' y) x
      = M.η * (M.φ y * coordPartial 0 M.φ x
        - (M.φ x * coordPartial 0 M.φ x + coordPartial 0 M.φ x * M.φ x) / 2) := by
    intro y
    have e : (fun x' => M.data.W x' y) = fun x' =>
        (M.η * M.φ y) * M.φ x' + (-(M.η / 2)) * (M.φ x' * M.φ x') + (-(M.η * M.φ y ^ 2 / 2)) := by
      funext x'
      show M.η * (M.φ x' * M.φ y - M.φ x' ^ 2 / 2 - M.φ y ^ 2 / 2) = _
      ring
    rw [e, RankOneModel.coordPartial_lin hφ hφφ (M.η * M.φ y) (-(M.η / 2)) _ x,
      DGPS.coordPartial_mul hφ hφ 0 x]
    ring
  have hφi : Integrable M.φ ν :=
    M.φ_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint : ∫ y, coordPartial 0 (fun x' => M.data.W x' y) x ∂ν
      = M.η * ((∫ z, M.φ z ∂ν) * coordPartial 0 M.φ x
        - (M.φ x * coordPartial 0 M.φ x + coordPartial 0 M.φ x * M.φ x) / 2) := by
    simp_rw [hW]
    rw [integral_const_mul, integral_sub (hφi.mul_const _) (integrable_const _),
      integral_mul_const, integral_const]
    simp
  have hU := RankOneModel.coordPartial_lin hlog hφ (-1) (M.η * ∫ z, M.φ z ∂ν) 0 x
  have eU : driftPotRO M (M.η * ∫ z, M.φ z ∂ν)
      = fun y => (-1) * Real.log (M.q y) + (M.η * ∫ z, M.φ z ∂ν) * M.φ y + 0 := by
    funext y; simp [driftPotRO]
  rw [hV, hint, eU, hU]
  ring

theorem rankOne_stationary_iff (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary M.data ν ↔
      (ν : Measure (Torus 1)) =
        gibbsMeasure (driftPotRO M (M.η * ∫ z, M.φ z ∂(ν : Measure (Torus 1)))) := by
  have hsm := smooth_driftPotRO M (M.η * ∫ z, M.φ z ∂(ν : Measure (Torus 1)))
  have key : ∀ φ : Torus 1 → ℝ,
      ∫ x, (coordPartial 0 (coordPartial 0 φ) x -
      (coordPartial 0 M.data.V x + ∫ y, coordPartial 0 (fun x' => M.data.W x' y) x
        ∂(ν : Measure (Torus 1))) * coordPartial 0 φ x) ∂(ν : Measure (Torus 1))
      = ∫ x, (coordPartial 0 (coordPartial 0 φ) x
        - coordPartial 0 (driftPotRO M (M.η * ∫ z, M.φ z ∂(ν : Measure (Torus 1)))) x
          * coordPartial 0 φ x) ∂(ν : Measure (Torus 1)) := by
    intro φ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [rankOne_drift_eq M (ν : Measure (Torus 1)) x]
  constructor
  · intro hs
    exact eq_gibbs_of_stationary hsm fun φ hφ => by rw [← key]; exact hs φ hφ
  · intro heq φ hφ
    rw [key]
    have := gibbs_stationary hsm hφ
    rwa [← heq] at this

theorem gibbsDensity_rankOne (s : ℝ) (x : Torus 1) :
    gibbsDensity (driftPotRO M s) x
      = M.q x * Real.exp (-(s * M.φ x)) / gibbsZ (driftPotRO M s) := by
  unfold gibbsDensity driftPotRO
  have : Real.exp (-(-Real.log (M.q x) + s * M.φ x)) = M.q x * Real.exp (-(s * M.φ x)) := by
    rw [neg_add, neg_neg, Real.exp_add, Real.exp_log (M.q_pos x)]
  rw [this]

theorem gibbsZ_rankOne_zero : gibbsZ (driftPotRO M 0) = 1 := by
  unfold gibbsZ
  have : (fun x => Real.exp (-driftPotRO M 0 x)) = M.q := by
    funext x; simp [driftPotRO, Real.exp_log (M.q_pos x)]
  rw [this]; exact M.q_mass

theorem gibbsMeasure_rankOne_zero : gibbsMeasure (driftPotRO M 0) = M.ref.measure := by
  unfold gibbsMeasure
  show _ = (haar 1).withDensity fun x => ENNReal.ofReal (M.q x)
  congr 1
  funext x
  congr 1
  rw [gibbsDensity_rankOne, gibbsZ_rankOne_zero]
  simp

theorem exp_mul_le (u : ℝ) : u * Real.exp (-u) ≤ u := by
  rcases le_total 0 u with hu | hu
  · have := Real.exp_le_one_iff.2 (neg_nonpos.2 hu)
    exact mul_le_of_le_one_right hu this
  · have h1 : 1 ≤ Real.exp (-u) := Real.one_le_exp (neg_nonneg.2 hu)
    nlinarith [mul_nonneg (neg_nonneg.2 hu) (sub_nonneg.2 h1)]

theorem rankOne_uniq (ν : ProbabilityMeasure (Torus 1))
    (hfix : (ν : Measure (Torus 1)) =
      gibbsMeasure (driftPotRO M (M.η * ∫ z, M.φ z ∂(ν : Measure (Torus 1))))) :
    ν = rankOneRef M := by
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ z, M.φ z ∂(ν : Measure (Torus 1)) := ⟨_, rfl⟩
  rw [← hm] at hfix
  obtain ⟨s, hs⟩ : ∃ s, s = M.η * m := ⟨_, rfl⟩
  rw [← hs] at hfix
  have hU := smooth_driftPotRO M s
  have hZ := gibbsZ_pos hU
  have hmint : m = ∫ x, gibbsDensity (driftPotRO M s) x * M.φ x ∂haar 1 := by
    rw [hm, hfix, integral_gibbsMeasure_eq hU]
  have hE : m * gibbsZ (driftPotRO M s) = ∫ x, M.q x * Real.exp (-(s * M.φ x)) * M.φ x ∂haar 1 := by
    rw [hmint, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gibbsDensity_rankOne]
    field_simp
  have hle : s * ∫ x, M.q x * Real.exp (-(s * M.φ x)) * M.φ x ∂haar 1 ≤ 0 := by
    have c1 : Continuous fun x => M.q x * Real.exp (-(s * M.φ x)) * M.φ x := by
      have := M.q_cont; have := M.φ_cont; fun_prop
    have c2 : Continuous fun x => M.q x * M.φ x := by
      have := M.q_cont; have := M.φ_cont; fun_prop
    have hq0 : ∫ x, M.q x * M.φ x ∂haar 1 = 0 := by
      rw [← M.φ_centered]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [← integral_const_mul]
    calc ∫ x, s * (M.q x * Real.exp (-(s * M.φ x)) * M.φ x) ∂haar 1
        ≤ ∫ x, s * (M.q x * M.φ x) ∂haar 1 := by
          refine integral_mono (integrable_of_continuous_torus (continuous_const.mul c1))
            (integrable_of_continuous_torus (continuous_const.mul c2)) fun x => ?_
          have hq := (M.q_pos x).le
          calc s * (M.q x * Real.exp (-(s * M.φ x)) * M.φ x)
              = M.q x * ((s * M.φ x) * Real.exp (-(s * M.φ x))) := by ring
            _ ≤ M.q x * (s * M.φ x) := mul_le_mul_of_nonneg_left (exp_mul_le _) hq
            _ = s * (M.q x * M.φ x) := by ring
      _ = 0 := by rw [integral_const_mul, hq0, mul_zero]
  have h2 : M.η * m ^ 2 * gibbsZ (driftPotRO M s) ≤ 0 := by
    have : s * (m * gibbsZ (driftPotRO M s)) = M.η * m ^ 2 * gibbsZ (driftPotRO M s) := by
      rw [hs]; ring
    rw [← this, hE]; exact hle
  have h3 : M.η * m ^ 2 ≤ 0 := by
    by_contra hpos
    replace hpos := not_le.1 hpos
    nlinarith [mul_pos hpos hZ]
  have h4 : s = 0 := by
    have h5 : M.η * m ^ 2 = 0 := le_antisymm h3 (mul_nonneg M.η_nonneg (sq_nonneg _))
    have h6 : s ^ 2 = 0 := by
      calc s ^ 2 = M.η * (M.η * m ^ 2) := by rw [hs]; ring
        _ = 0 := by rw [h5, mul_zero]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h6
  apply ProbabilityMeasure.toMeasure_injective
  rw [hfix, h4, gibbsMeasure_rankOne_zero]
  rfl

theorem rankOne_stationary_ref : IsCircleDistributionalStationary M.data (rankOneRef M) := by
  rw [rankOne_stationary_iff, coe_rankOneRef, integral_φ_ref, mul_zero, gibbsMeasure_rankOne_zero]

theorem rankOne_stationary_iff_ref (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary M.data ν ↔ ν = rankOneRef M := by
  constructor
  · intro hs
    exact rankOne_uniq M ν ((rankOne_stationary_iff M ν).1 hs)
  · rintro rfl
    exact rankOne_stationary_ref M

/-! ### Strict convexity -/

theorem pot_half_inter (ν : ProbabilityMeasure (Torus 1)) :
    potentialEnergy M.data ν + (1 / 2 : ℝ) * interactionEnergy M.data ν =
      -∫ x, Real.log (M.q x) ∂(ν : Measure (Torus 1)) +
        M.η / 2 * (∫ x, M.φ x ∂(ν : Measure (Torus 1))) ^ 2 := by
  rw [M.potentialEnergy_eq, M.interactionEnergy_eq]; ring

theorem rankOne_strictConvexity : CircleStrictMixtureConvexFreeEnergy M.data := by
  intro ν₀ ν₁ hne hf0 hf1 t ht0 ht1
  have H0 := (finiteFreeEnergy_iff _ _).1 hf0
  have H1 := (finiteFreeEnergy_iff _ _).1 hf1
  have h0 := ac_of_entropy_ne_top H0
  have h1 := ac_of_entropy_ne_top H1
  obtain ⟨Hm, hbound⟩ := mix_relEntropy_bound t ht0.le ht1.le ν₀ ν₁ H0 H1
  have hT := dens_L1_pos ν₀ ν₁ h0 h1 hne
  set T := ∫ x, |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1
    with hTdef
  have hfe0 : freeEnergyValue M.data ν₀ hf0 =
      (relativeEntropy (ν₀ : Measure (Torus 1)) (haar 1)).toReal +
        (-∫ x, Real.log (M.q x) ∂(ν₀ : Measure (Torus 1)) +
          M.η / 2 * (∫ x, M.φ x ∂(ν₀ : Measure (Torus 1))) ^ 2) := by
    unfold freeEnergyValue; rw [freeEnergy_eq_real _ _ H0, EReal.toReal_coe, add_assoc, pot_half_inter]
  have hfe1 : freeEnergyValue M.data ν₁ hf1 =
      (relativeEntropy (ν₁ : Measure (Torus 1)) (haar 1)).toReal +
        (-∫ x, Real.log (M.q x) ∂(ν₁ : Measure (Torus 1)) +
          M.η / 2 * (∫ x, M.φ x ∂(ν₁ : Measure (Torus 1))) ^ 2) := by
    unfold freeEnergyValue; rw [freeEnergy_eq_real _ _ H1, EReal.toReal_coe, add_assoc, pot_half_inter]
  rw [freeEnergy_eq_real _ _ Hm, EReal.coe_lt_coe_iff, hfe0, hfe1]
  have hpm := pot_half_inter M (circMix t ht0.le ht1.le ν₀ ν₁)
  have ml := integral_circMix t ht0.le ht1.le ν₀ ν₁ M.log_smooth.continuous_torus
  have mφ := integral_circMix t ht0.le ht1.le ν₀ ν₁ M.φ_cont
  rw [ml, mφ] at hpm
  have htt : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have hT2 : 0 < t * (1 - t) * T ^ 2 := mul_pos htt (pow_pos hT 2)
  have hq : M.η / 2 * ((1 - t) * (∫ x, M.φ x ∂(ν₀ : Measure (Torus 1)))
        + t * ∫ x, M.φ x ∂(ν₁ : Measure (Torus 1))) ^ 2
      ≤ (1 - t) * (M.η / 2 * (∫ x, M.φ x ∂(ν₀ : Measure (Torus 1))) ^ 2)
        + t * (M.η / 2 * (∫ x, M.φ x ∂(ν₁ : Measure (Torus 1))) ^ 2) := by
    have := mul_nonneg (mul_nonneg (by linarith [M.η_nonneg] : (0 : ℝ) ≤ M.η / 2) htt.le)
      (sq_nonneg ((∫ x, M.φ x ∂(ν₀ : Measure (Torus 1))) - ∫ x, M.φ x ∂(ν₁ : Measure (Torus 1))))
    nlinarith [this]
  nlinarith [hbound, hq, hT2, hpm]

end General

/-! ### Hessian -/

section Hessian

variable (M : RankOneModel)

theorem rankOne_centeredKernel (x y : Torus 1) :
    centeredKernel M.data (rankOneRef M) x y = M.η * (M.φ x * M.φ y) := by
  have hm : ∫ z, M.φ z ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) = 0 :=
    integral_φ_ref M
  have hconv : ∀ x, interactionConvolution M.data (rankOneRef M) x =
      M.η * ((∫ z, M.φ z ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
        * M.φ x - (∫ z, M.φ z ^ 2 ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) :
          Measure (Torus 1))) / 2 - M.φ x ^ 2 / 2) := by
    intro x
    unfold interactionConvolution
    calc ∫ z, M.data.W x z ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
        = ∫ z, M.W z x ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun z => M.data.W_symm x z)
      _ = _ := M.inner_W _ x
  have hmean : meanInteraction M.data (rankOneRef M) =
      M.η * ((∫ z, M.φ z ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) ^ 2 -
        ∫ z, M.φ z ^ 2 ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) :=
    M.interactionEnergy_eq (rankOneRef M)
  have hW : M.data.W x y = M.η * (M.φ x * M.φ y - M.φ x ^ 2 / 2 - M.φ y ^ 2 / 2) := rfl
  unfold centeredKernel
  rw [hconv x, hconv y, hmean, hW, hm]
  ring

/-- The vector `φ` as an element of the centered `L²(μ_M)`. -/
noncomputable def rankOneE : centeredL2 (rankOneRef M) :=
  ⟨lpOf (rankOneRef M) M.φ M.φ_cont, by
    rw [mem_centeredL2]
    rw [integral_congr_ae (lpOf_ae _ _ _)]
    exact integral_φ_ref M⟩

theorem rankOneE_ae : ((rankOneE M : centeredL2 (rankOneRef M)) :
    Lp ℝ 2 ((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
      =ᵐ[((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))] M.φ :=
  lpOf_ae _ _ _

theorem inner_rankOneE (f : centeredL2 (rankOneRef M)) :
    inner ℝ (rankOneE M) f = ∫ x, M.φ x * (f : Lp ℝ 2 ((rankOneRef M :
      ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) x
        ∂((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) :=
  inner_lpOf _ M.φ_cont _

theorem rankOne_hessian_bilinear (f g : centeredL2 (rankOneRef M)) :
    inner ℝ g (densityHessian M.data (rankOneRef M) f) =
      inner ℝ g f + M.η * (inner ℝ (rankOneE M) f * inner ℝ (rankOneE M) g) := by
  have h1 : inner ℝ g (densityHessian M.data (rankOneRef M) f)
      = inner ℝ g f + inner ℝ g (centeredInteraction M.data (rankOneRef M) f) := by
    rw [← inner_add_right]; rfl
  have h2 : inner ℝ g (centeredInteraction M.data (rankOneRef M) f)
      = inner ℝ (g : Lp ℝ 2 ((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
        (kernelOp M.data (rankOneRef M)
          (f : Lp ℝ 2 ((rankOneRef M : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))) := rfl
  rw [h1, h2, inner_kernelOp]
  congr 1
  set f' : Torus 1 → ℝ := ⇑(f : Lp ℝ 2 ((rankOneRef M : ProbabilityMeasure (Torus 1)) :
    Measure (Torus 1))) with hf'
  set g' : Torus 1 → ℝ := ⇑(g : Lp ℝ 2 ((rankOneRef M : ProbabilityMeasure (Torus 1)) :
    Measure (Torus 1))) with hg'
  have e : ∀ p : Torus 1 × Torus 1, centeredKernel M.data (rankOneRef M) p.1 p.2 *
      (g' p.1 * f' p.2) = M.η * ((M.φ p.1 * g' p.1) * (M.φ p.2 * f' p.2)) := by
    intro p; rw [rankOne_centeredKernel]; ring
  rw [integral_congr_ae (ae_of_all _ e), integral_const_mul,
    integral_prod_mul (fun x => M.φ x * g' x) (fun x => M.φ x * f' x),
    inner_rankOneE, inner_rankOneE]
  ring

theorem rankOne_hessian_apply (f : centeredL2 (rankOneRef M)) :
    densityHessian M.data (rankOneRef M) f
      = f + (M.η * inner ℝ (rankOneE M) f) • rankOneE M := by
  refine ext_inner_left ℝ fun g => ?_
  have hs : inner ℝ g ((M.η * inner ℝ (rankOneE M) f) • rankOneE M)
      = (M.η * inner ℝ (rankOneE M) f) * inner ℝ g (rankOneE M) :=
    real_inner_smul_right (F := centeredL2 (rankOneRef M)) g (rankOneE M) _
  rw [rankOne_hessian_bilinear, inner_add_right, hs, real_inner_comm g (rankOneE M)]
  ring

theorem rankOne_hessian_quadratic (f : centeredL2 (rankOneRef M)) :
    inner ℝ f (densityHessian M.data (rankOneRef M) f)
      = ‖f‖ ^ 2 + M.η * (inner ℝ (rankOneE M) f) ^ 2 := by
  rw [rankOne_hessian_bilinear, real_inner_self_eq_norm_sq]; ring

theorem rankOne_hessian_ge (f : centeredL2 (rankOneRef M)) :
    ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian M.data (rankOneRef M) f) := by
  rw [rankOne_hessian_quadratic]
  nlinarith [mul_nonneg M.η_nonneg (sq_nonneg (inner ℝ (rankOneE M) f))]

theorem rankOne_coercive : IsCoerciveDensityHessian M.data (rankOneRef M) :=
  ⟨1, one_pos, fun f => by rw [one_mul]; exact rankOne_hessian_ge M f⟩

end Hessian

/-! ### The engineered model -/

section Engineered

open DGPS.Models DGPS.Examples.EngineeredRankOne

/-- The engineered reference `μ_h` as a bundled probability measure. -/
noncomputable def engineeredProb (h : ℝ) (hh : 2 ≤ h) : ProbabilityMeasure (Torus 1) :=
  rankOneRef (engineeredModel h hh)

theorem coe_engineeredProb (h : ℝ) (hh : 2 ≤ h) :
    ((engineeredProb h hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
      = engineeredReference h :=
  engineeredModel_ref_measure h hh

/-- The vector `E_h = E_h ∘ angEquiv` in the centered `L²(μ_h)`. -/
noncomputable def engineeredE (h : ℝ) (hh : 2 ≤ h) : centeredL2 (engineeredProb h hh) :=
  rankOneE (engineeredModel h hh)

end Engineered

end DGPS.Examples.EngineeredUniqueness

namespace DGPS.Examples

open DGPS.Models DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredUniqueness

/-- **EX034.** For every `h ≥ 2`, the engineered model has strictly convex free energy along
distinct finite-entropy mixtures, `μ_h` is its unique equilibrium and its only distributionally
stationary probability, and the centered Hessian at `μ_h` is `Id + E_h ⊗ E_h ≥ Id`. -/
theorem engineered_uniqueness_and_hessian (h : ℝ) (hh : 2 ≤ h) :
    ((engineeredProb h hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
        = engineeredReference h ∧
    CircleStrictMixtureConvexFreeEnergy (engineeredModel h hh).data ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      freeEnergy (engineeredModel h hh).data ν = freeEnergyMinimum (engineeredModel h hh).data
        ↔ ν = engineeredProb h hh) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      IsCircleDistributionalStationary (engineeredModel h hh).data ν ↔ ν = engineeredProb h hh) ∧
    (((engineeredE h hh : centeredL2 (engineeredProb h hh)) :
        Lp ℝ 2 ((engineeredProb h hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
      =ᵐ[((engineeredProb h hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))]
        (engineeredModel h hh).φ) ∧
    (∀ f : centeredL2 (engineeredProb h hh),
      densityHessian (engineeredModel h hh).data (engineeredProb h hh) f
        = f + inner ℝ (engineeredE h hh) f • engineeredE h hh) ∧
    (∀ f : centeredL2 (engineeredProb h hh),
      inner ℝ f (densityHessian (engineeredModel h hh).data (engineeredProb h hh) f)
        = ‖f‖ ^ 2 + (inner ℝ (engineeredE h hh) f) ^ 2) ∧
    (∀ f : centeredL2 (engineeredProb h hh),
      ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (engineeredModel h hh).data (engineeredProb h hh) f)) ∧
    IsCoerciveDensityHessian (engineeredModel h hh).data (engineeredProb h hh) := by
  have hη : (engineeredModel h hh).η = 1 := rfl
  refine ⟨coe_engineeredProb h hh, rankOne_strictConvexity _, rankOne_equilibrium_iff _,
    rankOne_stationary_iff_ref _, rankOneE_ae _, ?_, ?_, rankOne_hessian_ge _, rankOne_coercive _⟩
  · intro f
    have := rankOne_hessian_apply (engineeredModel h hh) f
    rw [hη, one_mul] at this
    exact this
  · intro f
    have := rankOne_hessian_quadratic (engineeredModel h hh) f
    rw [hη, one_mul] at this
    exact this

end DGPS.Examples
