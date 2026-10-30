import DGPS.Examples.EngineeredRankOneRates
import DGPS.Lipschitz.Representatives
import DGPS.Analysis.WeakConvolution
import DGPS.Foundations.WeakContractions

/-!
# The exact engineered model and its normalized rank-one representation

The normalized one-body potential differs from the prescribed one by `log Zh`.
The constant is retained through the actual free-energy minimum. The canonical
exact-model drift has the identical force to a genuine normalized-model drift.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models DGPS.PositiveRankOne

private theorem pair_torusDist (p q : Torus 2) :
    torusDist p q = Real.sqrt
      (torusDist (fun _ : Fin 1 => p 0) (fun _ : Fin 1 => q 0) ^ 2 +
        torusDist (fun _ : Fin 1 => p 1) (fun _ : Fin 1 => q 1) ^ 2) := by
  unfold torusDist SharpLSI.flatDist
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_two]

private theorem rankOne_lipschitz (M : RankOneModel) : LipschitzData M.data := by
  have hV : IsSmoothPeriodic M.data.V :=
    M.log_smooth.neg.add ((M.φ_smooth.pow 2).const_smul (M.η / 2))
  have hp (i : Fin 2) : IsSmoothPeriodic (fun p : Torus 2 => M.φ (fun _ : Fin 1 => p i)) := by
    have hc : ContDiff ℝ ∞ (fun v : Fin 2 → ℝ => fun _ : Fin 1 => v i) := by fun_prop
    exact M.φ_smooth.comp hc
  have hW : IsSmoothPeriodic (fun p : Torus 2 =>
      M.data.W (fun _ : Fin 1 => p 0) (fun _ : Fin 1 => p 1)) :=
    ((((hp 0).mul (hp 1)).sub (((hp 0).pow 2).div_const 2)).sub
      (((hp 1).pow 2).div_const 2)).const_smul M.η
  obtain ⟨LV, -, hLV⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hV
  obtain ⟨LW, -, hLW⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hW
  refine ⟨⟨LV, hLV⟩, LW, fun x y x' y' => ?_⟩
  have h := hLW ![x 0, y 0] ![x' 0, y' 0]
  rw [pair_torusDist] at h
  have he : ∀ z : Torus 1, (fun _ : Fin 1 => z 0) = z := fun z => funext fun i => by
    rw [Subsingleton.elim i 0]
  simpa [he] using h

/-- The actual normalized data are Lipschitz; this is proved from their smooth fields. -/
theorem normalizedLipschitz (h : ℝ) (hh : 2 ≤ h) :
    LipschitzData (engineeredModel h hh).data := rankOne_lipschitz _

/-- A genuine drift on every absolute competitor of the normalized model. -/
noncomputable def normalizedDrift (h : ℝ) (hh : 2 ≤ h) :
    AbsoluteDrift (engineeredModel h hh).data :=
  lipschitz_absoluteDrift _ (normalizedLipschitz h hh)

/-- The one-body normalization constant is explicit; the potentials are not identified. -/
theorem normalized_potential_shift (h : ℝ) (hh : 2 ≤ h) (x : Torus 1) :
    (engineeredModel h hh).data.V x = (engineeredRankOne h hh).V x + Real.log (Zh h) := by
  change -Real.log (qAng h (DGPS.Circle.AngularNormalization.angEquiv x)) +
      1 / 2 * Eang h (DGPS.Circle.AngularNormalization.angEquiv x) ^ 2 =
    Vang h (DGPS.Circle.AngularNormalization.angEquiv x) + Real.log (Zh h)
  rw [log_qAng h (by linarith)]
  unfold Vang logq
  ring

/-- The zero-diagonal interaction kernel is exactly the prescribed kernel. -/
theorem normalized_kernel_eq (h : ℝ) (hh : 2 ≤ h) (x y : Torus 1) :
    (engineeredModel h hh).data.W x y = (engineeredRankOne h hh).W x y := by
  change 1 * (Eang h _ * Eang h _ - Eang h _ ^ 2 / 2 - Eang h _ ^ 2 / 2) =
    -(Eang h _ - Eang h _) ^ 2 / 2
  ring

private theorem weakGradientLp_add_constant {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hw : IsWeakGradientLp 1 u g) (c : ℝ) : IsWeakGradientLp 1 (fun x => u x + c) g := by
  refine ⟨hw.memLp.add (memLp_const _), hw.memLp_grad, fun φ hφ j => ?_⟩
  have hi : Integrable (fun x => u x * coordPartial j φ x) (haar 1) :=
    hw.memLp.integrable_mul (hφ.memLp_top_coordPartial j)
  have hc : Integrable (fun x : Torus 1 => c * coordPartial j φ x) (haar 1) :=
    ((hφ.memLp_top_coordPartial j).integrable le_top).const_mul c
  have hz := (isWeakGradient_const (d := 1) c).ibp φ hφ j
  simp only [PiLp.zero_apply, zero_mul, integral_zero, neg_zero] at hz
  simp_rw [add_mul]
  rw [integral_add hi hc, hw.ibp φ hφ j, hz, add_zero]

private noncomputable def constantPotentialDrift (A B : InteractionData 1) (c : ℝ)
    (hV : ∀ x, A.V x = B.V x + c) (hW : ∀ x y, A.W x y = B.W x y)
    (b : AbsoluteDrift A) : AbsoluteDrift B where
  force := b.force
  measurable_force := b.measurable_force
  weak_gradient ρ := by
    have hp : interactionPotential B ρ = fun x => interactionPotential A ρ x + -c := by
      funext x
      unfold interactionPotential
      simp_rw [hV, hW]
      ring
    rw [hp]
    exact weakGradientLp_add_constant (b.weak_gradient ρ) (-c)

private theorem potential_energy_shift (A B : InteractionData 1) (c : ℝ)
    (hV : ∀ x, A.V x = B.V x + c) (ν : ProbabilityMeasure (Torus 1)) :
    potentialEnergy A ν = potentialEnergy B ν + c := by
  unfold potentialEnergy
  simp_rw [hV]
  rw [integral_add (B.V_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp

private theorem interaction_energy_eq (A B : InteractionData 1)
    (hW : ∀ x y, A.W x y = B.W x y) (ν : ProbabilityMeasure (Torus 1)) :
    interactionEnergy A ν = interactionEnergy B ν := by
  unfold interactionEnergy
  exact integral_congr_ae (Eventually.of_forall fun p => hW p.1 p.2)

private theorem freeEnergy_shift (A B : InteractionData 1) (c : ℝ)
    (hV : ∀ x, A.V x = B.V x + c) (hW : ∀ x y, A.W x y = B.W x y)
    (ν : ProbabilityMeasure (Torus 1)) : freeEnergy A ν = freeEnergy B ν + (c : EReal) := by
  by_cases hH : relativeEntropy (ν : Measure (Torus 1)) (haar 1) = ⊤
  · simp only [freeEnergy, hH, EReal.coe_ennreal_top, EReal.top_add_coe]
  · rw [freeEnergy_eq_real A ν hH, freeEnergy_eq_real B ν hH,
      potential_energy_shift A B c hV, interaction_energy_eq A B hW, ← EReal.coe_add]
    congr 1
    ring

private theorem minimum_real_shift (A B : InteractionData 1) (c : ℝ)
    (hV : ∀ x, A.V x = B.V x + c) (hW : ∀ x y, A.W x y = B.W x y) :
    freeEnergyMinimumReal A = freeEnergyMinimumReal B + c := by
  obtain ⟨ν, hν⟩ := freeEnergy_minimum_exists B
  obtain ⟨μ, hμ⟩ := freeEnergy_minimum_exists A
  have hu : freeEnergyMinimum A ≤ freeEnergyMinimum B + (c : EReal) := by
    calc _ ≤ freeEnergy A ν := iInf_le _ _
      _ = _ := by rw [freeEnergy_shift A B c hV hW, hν]
  have hl : freeEnergyMinimum B + (c : EReal) ≤ freeEnergyMinimum A := by
    rw [← hμ, freeEnergy_shift A B c hV hW]
    have hbase : freeEnergyMinimum B ≤ freeEnergy B μ := iInf_le _ _
    calc freeEnergyMinimum B + (c : EReal) = (c : EReal) + freeEnergyMinimum B := add_comm _ _
      _ ≤ (c : EReal) + freeEnergy B μ := add_le_add_right hbase _
      _ = freeEnergy B μ + (c : EReal) := add_comm _ _
  apply EReal.coe_injective
  rw [EReal.coe_add, coe_freeEnergyMinimumReal A, coe_freeEnergyMinimumReal B]
  exact le_antisymm hu hl

private theorem speciesGap_constant_shift (A B : InteractionData 1) (c : ℝ)
    (hV : ∀ x, A.V x = B.V x + c) (hW : ∀ x y, A.W x y = B.W x y)
    (F : SpeciesFamily 1) : speciesGap A F = speciesGap B F := by
  apply NNReal.coe_injective
  simp only [coe_speciesGap, speciesRawGap]
  rw [potential_energy_shift A B c hV, interaction_energy_eq A B hW,
    minimum_real_shift A B c hV hW]
  ring

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Models

/-- The actual absolute drift of the exact fixed-coupling engineered potentials. -/
noncomputable def engineeredRankOneDrift (h : ℝ) (hh : 2 ≤ h) :
    AbsoluteDrift (engineeredRankOne h hh) :=
  DGPS.Examples.EngineeredRankOne.constantPotentialDrift
    (engineeredModel h hh).data (engineeredRankOne h hh)
    (Real.log (DGPS.Examples.EngineeredRankOne.Zh h))
    (DGPS.Examples.EngineeredRankOne.normalized_potential_shift h hh)
    (DGPS.Examples.EngineeredRankOne.normalized_kernel_eq h hh)
    (DGPS.Examples.EngineeredRankOne.normalizedDrift h hh)

end DGPS.Models

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models

/-- Gauge cancellation preserves every full finite-family gap. -/
theorem normalized_speciesGap (h : ℝ) (hh : 2 ≤ h) (F : SpeciesFamily 1) :
    speciesGap (engineeredModel h hh).data F = speciesGap (engineeredRankOne h hh) F :=
  speciesGap_constant_shift _ _ _ (normalized_potential_shift h hh) (normalized_kernel_eq h hh) F

/-- Gauge cancellation preserves every absolute scalar gap. -/
theorem normalized_scalarGap (h : ℝ) (hh : 2 ≤ h) (ρ : AbsoluteDensity 1) :
    scalarGap (engineeredModel h hh).data ρ = scalarGap (engineeredRankOne h hh) ρ := by
  simpa only [speciesGap_single] using normalized_speciesGap h hh (SpeciesFamily.single ρ)

/-- The canonical exact and normalized drifts have identical forces and dissipations. -/
theorem normalized_scalarDissipation (h : ℝ) (hh : 2 ≤ h) (ρ : AbsoluteDensity 1) :
    scalarDissipation (engineeredModel h hh).data (normalizedDrift h hh) ρ =
      scalarDissipation (engineeredRankOne h hh) (engineeredRankOneDrift h hh) ρ := rfl

theorem normalized_speciesDissipation (h : ℝ) (hh : 2 ≤ h) (F : SpeciesFamily 1) :
    speciesDissipation (engineeredModel h hh).data (normalizedDrift h hh) F =
      speciesDissipation (engineeredRankOne h hh) (engineeredRankOneDrift h hh) F := rfl

/-- Scalar rates on the actual absolute domain are unchanged by the proved gauge. -/
theorem normalized_scalarRate (h : ℝ) (hh : 2 ≤ h) :
    scalarRate (engineeredModel h hh).data (normalizedDrift h hh) =
      scalarRate (engineeredRankOne h hh) (engineeredRankOneDrift h hh) := by
  have hq (ρ : AbsoluteDensity 1) :
      scalarQuotient (engineeredModel h hh).data (normalizedDrift h hh) ρ =
        scalarQuotient (engineeredRankOne h hh) (engineeredRankOneDrift h hh) ρ := by
    simp only [scalarQuotient, normalized_scalarGap, normalized_scalarDissipation]
  apply le_antisymm
  · refine le_iInf fun ρ => ?_
    have hp : 0 < scalarGap (engineeredModel h hh).data ρ.1 := by
      rw [normalized_scalarGap]
      exact ρ.2
    exact (scalarRate_le_quotient _ _ ρ.1 hp).trans_eq (hq ρ.1)
  · refine le_iInf fun ρ => ?_
    have hp : 0 < scalarGap (engineeredRankOne h hh) ρ.1 := by
      rw [← normalized_scalarGap]
      exact ρ.2
    exact (scalarRate_le_quotient _ _ ρ.1 hp).trans_eq (hq ρ.1).symm

/-- Full finite-species rates are unchanged by the proved gauge. -/
theorem normalized_speciesRate (h : ℝ) (hh : 2 ≤ h) :
    speciesRate (engineeredModel h hh).data (normalizedDrift h hh) =
      speciesRate (engineeredRankOne h hh) (engineeredRankOneDrift h hh) := by
  have hq (F : SpeciesFamily 1) :
      speciesQuotient (engineeredModel h hh).data (normalizedDrift h hh) F =
        speciesQuotient (engineeredRankOne h hh) (engineeredRankOneDrift h hh) F := by
    simp only [speciesQuotient, normalized_speciesGap, normalized_speciesDissipation]
  apply le_antisymm
  · refine le_iInf fun F => ?_
    have hp : 0 < speciesGap (engineeredModel h hh).data F.1 := by
      rw [normalized_speciesGap]
      exact F.2
    exact (speciesRate_le _ _ F.1 hp).trans_eq (hq F.1)
  · refine le_iInf fun F => ?_
    have hp : 0 < speciesGap (engineeredRankOne h hh) F.1 := by
      rw [← normalized_speciesGap]
      exact F.2
    exact (speciesRate_le _ _ F.1 hp).trans_eq (hq F.1).symm

end DGPS.Examples.EngineeredRankOne
