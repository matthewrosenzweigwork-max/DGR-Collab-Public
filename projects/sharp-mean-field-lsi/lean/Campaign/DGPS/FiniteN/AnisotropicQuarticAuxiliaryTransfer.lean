import DGPS.FiniteN.AnisotropicQuarticSmoothClosure
import DGPS.FiniteN.AnisotropicQuarticHubbard

/-! Exact physical-field auxiliary law and its actual smooth-test Poincare estimate.
The measure and energy transports adapt ScalarFoldFIN060F/G to two physical coordinates. -/

open MeasureTheory ProbabilityTheory Set Matrix
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.AuxiliaryTransfer
open DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.ScalarFoldFIN060
open scoped ContDiff ENNReal

namespace DGPS.FiniteN

private theorem quartic_map_density_toLp (G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (s : Set (EuclideanSpace ℝ (Fin 2))) (hs : MeasurableSet s) :
    ((volume : Measure (Fin 2 → ℝ)).withDensity (fun w => G (WithLp.toLp 2 w))).map
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) s =
      (volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity G s := by
  have hT := PiLp.volume_preserving_toLp (Fin 2)
  have hemb := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding
  rw [Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable hs),
    withDensity_apply _ hs]
  exact hT.setLIntegral_comp_preimage_emb hemb G s

/-- Exact normalized auxiliary-law transport, with the original physical field coordinates. -/
theorem quartic_auxLaw_map (N : ℕ+) :
    (auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
      (DGPS.haar 1) N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) =
        imsEta (N : ℝ) quarticPsi_FIN066 := by
  let G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-((N : ℝ) * quarticPsi_FIN066 z)))
  let ν : Measure (EuclideanSpace ℝ (Fin 2)) := volume.withDensity G
  have hvec : ∀ w : Fin 2 → ℝ, WithLp.toLp 2 w = !₂[w 0, w 1] := by
    intro w
    ext i
    fin_cases i <;> rfl
  have hF : (fun w : Fin 2 → ℝ => ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD quarticHubbardField
        (DGPS.haar 1) w))) = fun w => G (WithLp.toLp 2 w) := by
    funext w
    dsimp only [G]
    rw [quartic_hubbard_aux_potential, hvec w, neg_mul]
  have hmap : ((volume : Measure (Fin 2 → ℝ)).withDensity (fun w =>
      ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential quarticHubbardU quarticHubbardFeature
        quarticHubbardD quarticHubbardField (DGPS.haar 1) w)))).map
          (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = ν := by
    refine Measure.ext fun s hs => ?_
    rw [hF]
    exact quartic_map_density_toLp G s hs
  have hmass : ν univ = auxMass quarticHubbardD quarticHubbardField quarticHubbardU
      quarticHubbardFeature (DGPS.haar 1) N := by
    rw [← hmap, Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable
      MeasurableSet.univ, preimage_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    rfl
  have hint : (∫⁻ z : EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (Real.exp (-((N : ℝ) * quarticPsi_FIN066 z)))) = ν univ := by
    rw [show ν = volume.withDensity G from rfl, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  unfold auxLaw imsEta
  rw [Measure.map_smul, hmap, hint, hmass]
  exact (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable

private theorem quartic_fderiv_ofLp {g : (Fin 2 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (x v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => g (WithLp.ofLp y)) x v =
      fderiv ℝ g (WithLp.ofLp x) (WithLp.ofLp v) := by
  have h := ((hg.differentiable (by simp)) (WithLp.ofLp x)).hasFDerivAt.comp x
    (PiLp.hasFDerivAt_ofLp 2 x)
  change (fderiv ℝ (g ∘ WithLp.ofLp) x) v = _
  rw [h.fderiv]
  rfl

/-- Exact Euclidean energy in the two physical field coordinates. -/
theorem quartic_auxiliary_energy_coordinates {g : (Fin 2 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => g (WithLp.ofLp y)) x‖ ^ 2 =
      ∑ j : Fin 2, (fderiv ℝ g (WithLp.ofLp x) (Pi.single j 1)) ^ 2 := by
  rw [groundState_norm_sq_eq_sum_basis]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [quartic_fderiv_ofLp hg]
  congr 2
  ext i
  simp [EuclideanSpace.basisFun_apply, Pi.single_apply]

/-- Actual Hubbard auxiliary Poincare bound in the exact bounded-smooth class needed
by the Hamiltonian-level full particle transfer, with all constants fixed before N. -/
theorem quartic_auxiliary_poincare :
    ∃ a : ℝ, 0 < a ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℕ+, N0 ≤ (N : ℝ) →
      PoincareAt (auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
        (DGPS.haar 1) N) AuxSmoothFIN060 auxGradSq (a * Real.sqrt (N : ℝ))⁻¹ := by
  obtain ⟨a, ha, N0, hN0, hbound⟩ := quartic_auxiliary_bounded_smooth_poincare
  refine ⟨a, ha, N0, hN0, fun N hN => ?_⟩
  let μ := auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
    (DGPS.haar 1) N
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_auxLaw quartic_hubbard_hyp
    quartic_hubbard_D_posDef quarticHubbardField N
  let e := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  let η := imsEta (N : ℝ) quarticPsi_FIN066
  have hmap : μ.map e = η := quartic_auxLaw_map N
  haveI : IsProbabilityMeasure η := quartic_imsEta_probability (N : ℝ) (by positivity)
  rintro g ⟨hg, ⟨B, hBg⟩, B', hB'g⟩
  let G : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => g (WithLp.ofLp x)
  have hGs : ContDiff ℝ ∞ G := hg.comp PiLp.contDiff_ofLp
  have hGB : ∀ x, |G x| ≤ B := fun x => hBg _
  have hderiv : ∀ x, ‖fderiv ℝ G x‖ ^ 2 ≤ B' := fun x => by
    rw [show G = fun x => g (WithLp.ofLp x) from rfl, quartic_auxiliary_energy_coordinates hg]
    exact hB'g _
  have hderiv' : ∀ x, ‖fderiv ℝ G x‖ ≤ B' + 1 := fun x => by
    have h := hderiv x
    nlinarith [sq_nonneg (‖fderiv ℝ G x‖ - 1)]
  have hmain := hbound (N : ℝ) hN G hGs ⟨B, hGB⟩ ⟨B' + 1, hderiv'⟩
  have hlam : 0 < a * Real.sqrt (N : ℝ) := mul_pos ha (Real.sqrt_pos.mpr (by positivity))
  have hmem : MemLp g 2 μ := MemLp.of_bound hg.continuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hBg w)
  have hGe : G ∘ e = g := rfl
  have hvar : variance g μ = ∫ x, (G x - ∫ y, G y ∂η) ^ 2 ∂η := by
    rw [← hGe, ← variance_map_equiv G e, hmap,
      variance_eq_integral hGs.continuous.aemeasurable]
  have hgrad : ∫⁻ w, auxGradSq g w ∂μ = ENNReal.ofReal (∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂η) := by
    have hcont : Continuous (fun x => ‖fderiv ℝ G x‖ ^ 2) :=
      ((hGs.continuous_fderiv (by simp)).norm).pow 2
    have hint : Integrable (fun x => ‖fderiv ℝ G x‖ ^ 2) η :=
      Integrable.of_bound hcont.aestronglyMeasurable B' (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hderiv x)
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _),
      ← hmap, lintegral_map_equiv]
    refine lintegral_congr fun w => ?_
    unfold auxGradSq
    rw [← quartic_auxiliary_energy_coordinates hg]
    rfl
  show evariance g μ ≤ ENNReal.ofReal (a * Real.sqrt (N : ℝ))⁻¹ * ∫⁻ w, auxGradSq g w ∂μ
  rw [← hmem.ofReal_variance_eq, hvar, hgrad, ← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ hlam]
  linarith only [hmain]

end DGPS.FiniteN
