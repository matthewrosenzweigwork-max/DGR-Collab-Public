import SharpSymmetricLSI.Paper.CosineD1
import SharpSymmetricLSI.Paper.CosineMeanField
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# The `d`-dimensional cosine model (2): free energy, `F_*` and the gap

With `Q_k(μ) = (∫ cos 2πxₖ dμ)² + (∫ sin 2πxₖ dμ)²` (`cosDQ`, the first mode of the `k`-th
marginal), `W_κ(μ,μ) = κ ∑ₖ (Q_k(μ) - 1)` (`interE_cosWd`), `F_* = -dκ/2` (`Fstar_cosWd`) and
`G(μ) = H(μ|m) + (κ/2) ∑ₖ Q_k(μ)` (`gap_cosWd`).
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ}

theorem measurable_cosDproj (k : Fin d) : Measurable (cosDproj k) :=
  (continuous_cosDproj k).measurable

/-- The `k`-th marginal of `m` is the Haar measure of the circle. -/
theorem map_cosDproj_haar (k : Fin d) : (haar d).map (cosDproj k) = haar 1 := by
  have e : cosDproj k = (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm ∘
      fun x : Torus d => x k := by
    funext x i; rfl
  rw [e, ← Measure.map_map (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm.measurable
    (measurable_pi_apply k)]
  have h1 : (haar d).map (fun x : Torus d => x k) = (volume : Measure UnitAddCircle) :=
    (measurePreserving_eval (fun _ : Fin d => (volume : Measure UnitAddCircle)) k).map_eq
  rw [h1]
  exact (volume_preserving_funUnique (Fin 1) UnitAddCircle).symm.map_eq

theorem integral_cosDproj_haar (k : Fin d) {F : Torus 1 → ℝ} (hF : Continuous F) :
    ∫ x, F (cosDproj k x) ∂haar d = ∫ y, F y ∂haar 1 := by
  rw [← map_cosDproj_haar k, integral_map (measurable_cosDproj k).aemeasurable
    hF.aestronglyMeasurable]

/-- `Q_k(μ)`. -/
noncomputable def cosDQ (k : Fin d) (μ : Measure (Torus d)) : ℝ :=
  (∫ x, gCos (cosDproj k x) ∂μ) ^ 2 + (∫ x, sCos (cosDproj k x) ∂μ) ^ 2

theorem cosDQ_nonneg (k : Fin d) (μ : Measure (Torus d)) : 0 ≤ cosDQ k μ := by
  unfold cosDQ; positivity

theorem cosDQ_eq_firstModeM (k : Fin d) (μ : Measure (Torus d)) :
    cosDQ k μ = firstModeM (μ.map (cosDproj k)) := by
  unfold cosDQ firstModeM
  rw [integral_map (measurable_cosDproj k).aemeasurable continuous_gCos.aestronglyMeasurable,
    integral_map (measurable_cosDproj k).aemeasurable continuous_sCos.aestronglyMeasurable]

theorem cosDQ_haar (k : Fin d) : cosDQ k (haar d) = 0 := by
  rw [cosDQ_eq_firstModeM, map_cosDproj_haar, firstModeM_haar]

/-- `∫ W_κ(z, w) dν(z) = κ (A cos 2πw + B sin 2πw - 1)` on the circle. -/
theorem integral_cosW_left (κ : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (w : Torus 1) :
    ∫ z, cosW κ z w ∂ν =
      κ * ((∫ z, gCos z ∂ν) * gCos w + (∫ z, sCos z ∂ν) * sCos w - 1) := by
  unfold cosW
  simp_rw [gCos_sub]
  have ic : Integrable gCos ν := integrable_bdd continuous_gCos
  have is : Integrable sCos ν := integrable_bdd continuous_sCos
  rw [integral_const_mul, integral_sub (f := fun x => gCos x * gCos w + sCos x * sCos w)
    (g := fun _ => (1 : ℝ)) ((ic.mul_const _).add (is.mul_const _)) (integrable_const _),
    integral_add (f := fun x => gCos x * gCos w) (g := fun x => sCos x * sCos w)
      (ic.mul_const _) (is.mul_const _), integral_mul_const, integral_mul_const]
  simp

theorem continuous_integral_cosW_left (κ : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    Continuous fun w => ∫ z, cosW κ z w ∂ν := by
  simp_rw [integral_cosW_left]
  exact continuous_const.mul (((continuous_const.mul continuous_gCos).add
    (continuous_const.mul continuous_sCos)).sub continuous_const)

theorem cosD_continuous_cosW_left (κ : ℝ) (w : Torus 1) : Continuous fun z => cosW κ z w := by
  unfold cosW
  exact continuous_const.mul ((continuous_gCos.comp (continuous_id.sub continuous_const)).sub
    continuous_const)

theorem integrable_torusD {μ : Measure (Torus d)} [IsFiniteMeasure μ] {F : Torus d → ℝ}
    (hF : Continuous F) : Integrable F μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable _

/-- `W_κ(μ,μ) = κ ∑ₖ (Q_k(μ) - 1)`. -/
theorem interE_cosWd (κ : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    interE (cosWd κ) μ μ = ∑ k, κ * (cosDQ k μ - 1) := by
  have hν : ∀ k : Fin d, IsProbabilityMeasure (μ.map (cosDproj k)) := fun k =>
    inferInstance
  have hin : ∀ (k : Fin d) (y : Torus d), ∫ x, cosW κ (cosDproj k x) (cosDproj k y) ∂μ =
      ∫ z, cosW κ z (cosDproj k y) ∂(μ.map (cosDproj k)) := fun k y => by
    rw [integral_map (measurable_cosDproj k).aemeasurable
      ((cosD_continuous_cosW_left κ (cosDproj k y))).aestronglyMeasurable]
  unfold interE
  simp_rw [cosWd_eq_sum]
  have h1 : ∀ y, ∫ x, ∑ k, cosW κ (cosDproj k x) (cosDproj k y) ∂μ =
      ∑ k, ∫ z, cosW κ z (cosDproj k y) ∂(μ.map (cosDproj k)) := fun y => by
    rw [integral_finsetSum (f := fun k x => cosW κ (cosDproj k x) (cosDproj k y)) _
      fun k _ => integrable_torusD
      ((cosD_continuous_cosW_left κ (cosDproj k y)).comp (continuous_cosDproj k))]
    exact Finset.sum_congr rfl fun k _ => hin k y
  simp_rw [h1]
  rw [integral_finsetSum (f := fun k y => ∫ z, cosW κ z (cosDproj k y) ∂(μ.map (cosDproj k))) _
    fun k _ => integrable_torusD
    ((continuous_integral_cosW_left κ _).comp (continuous_cosDproj k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_map (μ := μ) (measurable_cosDproj k).aemeasurable
    (continuous_integral_cosW_left κ _).aestronglyMeasurable (f := fun w =>
      ∫ z, cosW κ z w ∂(μ.map (cosDproj k))), cosDQ_eq_firstModeM, ← interE_cos]
  rfl

theorem sum_cosW_terms (κ : ℝ) (μ : Measure (Torus d)) :
    ∑ k, κ * (cosDQ k μ - 1) = κ * ∑ k, cosDQ k μ - d * κ := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp; ring

theorem freeEnergy_cosWd (κ : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    freeEnergy (fun _ => 0) (cosWd κ) μ = ((klDiv μ (haar d) : ℝ≥0∞) : EReal) +
      (((κ * ∑ k, cosDQ k μ - d * κ) / 2 : ℝ) : EReal) := by
  unfold freeEnergy
  rw [interE_cosWd, sum_cosW_terms]
  simp [potE]

theorem freeEnergy_cosWd_haar (κ : ℝ) :
    freeEnergy (fun _ => 0) (cosWd κ) (haar d) = ((-(d * κ) / 2 : ℝ) : EReal) := by
  rw [freeEnergy_cosWd, klDiv_self]
  simp only [cosDQ_haar, Finset.sum_const_zero, mul_zero, EReal.coe_ennreal_zero, zero_add]
  congr 1; ring

/-- `F_* = -dκ/2`. -/
theorem Fstar_cosWd {κ : ℝ} (hκ : 0 < κ) :
    Fstar (d := d) (fun _ => 0) (cosWd κ) = ((-(d * κ) / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · exact (iInf_le (fun ρ : ProbabilityMeasure (Torus d) =>
      freeEnergy (fun _ => 0) (cosWd κ) (ρ : Measure (Torus d)))
      ⟨haar d, inferInstance⟩).trans (freeEnergy_cosWd_haar (d := d) κ).le
  · refine le_iInf fun μ => ?_
    rw [freeEnergy_cosWd]
    have hQ : 0 ≤ ∑ k, cosDQ k (μ : Measure (Torus d)) :=
      Finset.sum_nonneg fun k _ => cosDQ_nonneg k _
    calc ((-(d * κ) / 2 : ℝ) : EReal)
        ≤ (((κ * ∑ k, cosDQ k (μ : Measure (Torus d)) - d * κ) / 2 : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by nlinarith)
      _ = 0 + (((κ * ∑ k, cosDQ k (μ : Measure (Torus d)) - d * κ) / 2 : ℝ) : EReal) :=
          (zero_add _).symm
      _ ≤ _ := add_le_add (EReal.coe_ennreal_nonneg _) le_rfl

/-- `G(μ) = H(μ|m) + (κ/2) ∑ₖ Q_k(μ)`. -/
theorem gap_cosWd {κ : ℝ} (hκ : 0 < κ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    gap (fun _ => 0) (cosWd κ) μ =
      ((klDiv μ (haar d) : ℝ≥0∞) : EReal) + ((κ / 2 * ∑ k, cosDQ k μ : ℝ) : EReal) := by
  unfold gap
  rw [freeEnergy_cosWd, Fstar_cosWd hκ]
  by_cases hK : klDiv μ (haar d) = ⊤
  · rw [hK, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.top_sub_coe, EReal.top_add_coe]
  · rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1; ring

end SharpLSI
