import LeanResearch.PeriodicAttractiveLogGas.MovingPoleCharts
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Source-only continuation of source Lemma 3.5. The actual limiting Green
weights retain the checked uniform three-halves bounds. Their normalizers
have a positive lower bound, including at coincident source positions. All
vector normalization below uses raw restricted Haar measure exactly.

The log/quotient expressions identified below are candidate weak fields;
this file does not infer a weak chain rule merely from those identities.
The remaining weak chain and Lipschitz-representative passage is recorded
in the accompanying development note. No evaluation was run by the author. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.MovingPoleCalculus

open MovingPoleIntegrability MovingPoleWeakLimit MovingPoleNumerators MovingPoleCharts
open GreenPointWeights MeshCells MeshAdjacentCells LabelOccupations ConditionalParameters

variable {ι : Type*} [Fintype ι]

/-- The lower-bound constant comes from the proved actual Green kernel. -/
def greenLowerConstant : ℝ :=
  Classical.choose exists_regularGreenRepresentative_lower_bound

theorem greenLowerConstant_pos : 0 < greenLowerConstant :=
  (Classical.choose_spec exists_regularGreenRepresentative_lower_bound).1

theorem green_lower_bound (z : Torus) : -greenLowerConstant ≤ regularGreenRepresentative z :=
  (Classical.choose_spec exists_regularGreenRepresentative_lower_bound).2 z

def normalizerLower (β₀ : ℝ) : ℝ := Real.exp (-greenLowerConstant * β₀)

theorem normalizerLower_pos (β₀ : ℝ) : 0 < normalizerLower β₀ := Real.exp_pos _

theorem torusWeight_lower (y : ι → Torus) (w : ι → ℝ) {β₀ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, w i ≤ β₀) (z : Torus) :
    normalizerLower β₀ ≤ torusWeight y w z := by
  apply Real.exp_le_exp.mpr
  calc
    -greenLowerConstant * β₀ ≤ -greenLowerConstant * (∑ i, w i) :=
      mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr greenLowerConstant_pos.le)
    _ = ∑ i, w i * (-greenLowerConstant) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ ∑ i, w i * regularGreenRepresentative (z - y i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (green_lower_bound _) (hw i)

theorem regularizedTorusWeight_lower (y : ι → Torus) (w : ι → ℝ) {β₀ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, w i ≤ β₀)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    normalizerLower β₀ ≤ regularizedTorusWeight y w ε hε z := by
  apply Real.exp_le_exp.mpr
  calc
    -greenLowerConstant * β₀ ≤ -greenLowerConstant * (∑ i, w i) :=
      mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr greenLowerConstant_pos.le)
    _ = ∑ i, w i * (-greenLowerConstant) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ ∑ i, w i * regularizedGreen ε hε (z - y i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
        (regularizedGreen_lower_bound green_lower_bound ε hε hs _) (hw i)

theorem normalizer_lower {μ : Measure Torus} [IsProbabilityMeasure μ]
    (y : ι → Torus) (w : ι → ℝ) {β₀ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, w i ≤ β₀) (hi : Integrable (torusWeight y w) μ) :
    normalizerLower β₀ ≤ ∫ z, torusWeight y w z ∂μ := by
  have h := integral_mono_ae (integrable_const (normalizerLower β₀)) hi
    (ae_of_all _ (torusWeight_lower y w hw ht))
  simpa only [integral_const, probReal_univ, one_smul] using h

section LimitNorms

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} {p : ℝ≥0∞}

/-- Fatou's inequality is applied to finite extended norms before any
real-valued norm is used. In particular the real norm cannot hide infinity. -/
theorem memLp_limit_of_uniform_norm {u : ℕ → A → E} {v : A → E} {B : ℝ}
    (hB : 0 ≤ B) (hu : ∀ n, MemLp (u n) p μ)
    (hb : ∀ n, lpNorm (u n) p μ ≤ B) (hv : AEStronglyMeasurable v μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (v x))) :
    MemLp v p μ ∧ lpNorm v p μ ≤ B := by
  have he : eLpNorm v p μ ≤ ENNReal.ofReal B := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
      (Eventually.of_forall fun n ↦ ?_) (fun n ↦ (hu n).aestronglyMeasurable) hv ht
    rw [← ofReal_lpNorm (hu n)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  refine ⟨memLp_iff.mpr (lt_of_le_of_lt he ENNReal.ofReal_lt_top), ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal hB] using hr

theorem integral_norm_le_lpNorm [IsProbabilityMeasure μ] {f : A → E}
    (hp : 1 ≤ p) (hf : MemLp f p μ) : (∫ x, ‖f x‖ ∂μ) ≤ lpNorm f p μ := by
  rw [← lpNorm_one_eq_integral_norm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp)

end LimitNorms

theorem measurable_sourceGradient (y : ι → Torus) (w : ι → ℝ) (j : ι) :
    Measurable (sourceGradient y w j) := by
  exact ((measurable_torusWeight y w).const_mul (-w j)).smul
    (measurable_greenGradient.comp (measurable_id.sub measurable_const))

/-- The same uniform bounds as for the regularizations hold for the actual
singular weight and its proposed ordinary physical source-gradient field.
The pole positions may coincide, lie on boundaries, or be deleted by a zero
coefficient. No pointwise common dominator is a premise. -/
theorem capped_limiting_mesh_bounds (K : KernelBounds) {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J hJ a b
    let y : I → Torus := fun i ↦ X i
    let v : I → ℝ := fun i ↦ w i
    MemLp (torusWeight y v) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
      lpNorm (torusWeight y v) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
        weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant ∧
      ∀ j, MemLp (sourceGradient y v j) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
        lpNorm (sourceGradient y v j) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
          sourceNormBound K β₀ J (nearRadius β₀ C₁) := by
  let μ := patchMeasure J hJ a b
  let y : I → Torus := fun i ↦ X i
  let v : I → ℝ := fun i ↦ w i
  have hJ₂ : 2 ≤ J := by omega
  have hac := patchMeasure_absolutelyContinuous hJ hJ₂ a b
  have hcoll : ∀ᵐ z ∂μ, ∀ i : I, z - y i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact ((torusMeasure.ae_ne (y i)).filter_mono hac.ae_le).mono fun z hz ↦ sub_ne_zero.mpr hz
  have hb (n : ℕ) := capped_mesh_bounds K hJ hN hβ hβ₀ hC₀ hmesh η hη I X hX w hw₀ hw a b
    (approximationScale n) (approximationScale_pos n) (approximationScale_small n)
  obtain ⟨hW, hWb⟩ := memLp_limit_of_uniform_norm
    (mul_nonneg (weightConstant_pos K β₀ J (nearRadius β₀ C₁)).le normConstant_nonneg)
    (fun n ↦ (hb n).1) (fun n ↦ (hb n).2.1)
    (measurable_torusWeight y v).aestronglyMeasurable
    (hcoll.mono fun z hz ↦ tendsto_weight approximationScale_pos approximationScale_small
      approximationScale_tendsto y v z hz)
  refine ⟨hW, hWb, fun j ↦ ?_⟩
  exact memLp_limit_of_uniform_norm
    (sourceNormBound_nonneg K (hβ.trans hβ₀) (by positivity) (by positivity))
    (fun n ↦ ((hb n).2.2 j).1) (fun n ↦ ((hb n).2.2 j).2)
    (measurable_sourceGradient y v j).aestronglyMeasurable
    (hcoll.mono fun z hz ↦ tendsto_sourceGradient approximationScale_pos approximationScale_small
      approximationScale_tendsto y v j z hz)

theorem capped_normalizer_bounds (K : KernelBounds) {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J hJ a b
    let W := torusWeight (fun i : I ↦ X i) (fun i : I ↦ w i)
    Integrable W μ ∧ normalizerLower β₀ ≤ (∫ z, W z ∂μ) ∧
      (∫ z, W z ∂μ) ≤ weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant := by
  let := patchMeasure_probability J hJ a b
  have h := capped_limiting_mesh_bounds K hJ hN hβ hβ₀ hC₀ hmesh η hη I X hX w hw₀ hw a b
  have hi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) h.1
  have ht : ∑ i : I, w i ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le hN hβ hβ₀ I hw
  refine ⟨hi, normalizer_lower _ _ (fun i ↦ hw₀ i i.property) ht hi, ?_⟩
  have hn := (integral_norm_le_lpNorm (by norm_num) h.1).trans h.2.1
  simpa only [Real.norm_eq_abs, abs_of_pos (torusWeight_pos _ _ _)] using hn

section RawHaar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- The vector version of the exact raw-Haar scaling identity. No scalar
component, norm comparison, or ambient-dimensional Jacobian is substituted. -/
theorem integral_raw_eq_patchArea_smul {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (H : Torus → V)
    (hH : AEStronglyMeasurable H (patchMeasure J hJ a b)) :
    (∫ z in patchDomain J hJ a b, H z ∂torusMeasure) =
      patchArea J b • (∫ Z, H (meshChart J a Z) ∂patchReference b) := by
  have hm := measurePreserving_patch J hJ a b
  have he : (∫ Z, H (meshChart J a Z) ∂patchReference b) =
      ∫ z, H z ∂patchMeasure J hJ a b := by
    rw [← hm.map_eq] at hH ⊢
    exact (integral_map hm.aemeasurable hH).symm
  rw [patchMeasure_eq_normalized hJ hJ₂ a b, integral_smul_measure] at he
  rw [he, patchArea, smul_smul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr
    ⟨patchNormalization_ne_zero hJ b, patchNormalization_ne_top J b⟩), one_smul]

omit [CompleteSpace V] in
theorem integral_raw_eq_patchArea_smul_patch {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (H : Torus → V) :
    (∫ z in patchDomain J hJ a b, H z ∂torusMeasure) =
      patchArea J b • (∫ z, H z ∂patchMeasure J hJ a b) := by
  rw [patchMeasure_eq_normalized hJ hJ₂ a b, integral_smul_measure, patchArea,
    smul_smul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨patchNormalization_ne_zero hJ b, patchNormalization_ne_top J b⟩), one_smul]

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem integrable_raw_iff_reference {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (H : Torus → V)
    (hH : AEStronglyMeasurable H (patchMeasure J hJ a b)) :
    Integrable H (torusMeasure.restrict (patchDomain J hJ a b)) ↔
      Integrable (fun Z ↦ H (meshChart J a Z)) (patchReference b) := by
  have hi := (measurePreserving_patch J hJ a b).integrable_comp hH
  rw [patchMeasure_eq_normalized hJ hJ₂ a b] at hi
  rw [integrable_smul_measure (patchNormalization_ne_zero hJ b)
    (patchNormalization_ne_top J b)] at hi
  exact hi.symm

end RawHaar

section PointLaws

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem pointLaw_integrable_iff {μ : Measure Torus} (y : ι → Torus) (w : ι → ℝ)
    (hz : 0 < ∫ z, torusWeight y w z ∂μ) (H : Torus → V) :
    Integrable H (pointLaw μ y w) ↔
      Integrable (fun z ↦ pointDensity μ y w z • H z) μ := by
  have hp (z : Torus) : 0 ≤ pointDensity μ y w z :=
    div_nonneg (torusWeight_pos y w z).le hz.le
  rw [pointLaw, integrable_withDensity_iff_integrable_smul₀'
    (measurable_pointDensity μ y w).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp _)]

omit [CompleteSpace V] in
theorem pointLaw_integral {μ : Measure Torus} (y : ι → Torus) (w : ι → ℝ)
    (hz : 0 < ∫ z, torusWeight y w z ∂μ) (H : Torus → V) :
    (∫ z, H z ∂pointLaw μ y w) =
      (∫ z, torusWeight y w z ∂μ)⁻¹ • (∫ z, torusWeight y w z • H z ∂μ) := by
  have hp (z : Torus) : 0 ≤ pointDensity μ y w z :=
    div_nonneg (torusWeight_pos y w z).le hz.le
  rw [pointLaw, integral_withDensity_eq_integral_toReal_smul₀
    (measurable_pointDensity μ y w).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp _)]
  simp only [pointDensity]
  simp_rw [div_eq_mul_inv, mul_comm _ (∫ z, torusWeight y w z ∂μ)⁻¹, mul_smul]
  exact integral_smul _ _

end PointLaws

/-- Normalizing the same actual weight cancels a positive finite scalar in
the reference measure. This identifies the patch-probability construction
with the manuscript's raw restricted-Haar conditional law. -/
theorem pointLaw_smul_measure (μ : Measure Torus) (y : ι → Torus) (w : ι → ℝ)
    (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hc_top : c ≠ (∞ : ℝ≥0∞)) :
    pointLaw (c • μ) y w = pointLaw μ y w := by
  have hd (z : Torus) : pointDensity (c • μ) y w z = c.toReal⁻¹ * pointDensity μ y w z := by
    rw [pointDensity, integral_smul_measure, smul_eq_mul, pointDensity]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hi : ENNReal.ofReal (c.toReal⁻¹) = c⁻¹ := by
    rw [← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hc₀)]
  have he : (fun z ↦ ENNReal.ofReal (pointDensity (c • μ) y w z)) =
      c⁻¹ • (fun z ↦ ENNReal.ofReal (pointDensity μ y w z)) := by
    funext z
    rw [hd, ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg), hi]
    rfl
  rw [pointLaw, he, withDensity_smul_measure,
    withDensity_smul c⁻¹ (measurable_pointDensity μ y w).ennreal_ofReal,
    smul_smul, ENNReal.mul_inv_cancel hc₀ hc_top, one_smul]
  rfl

theorem pointLaw_patch_eq_raw {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (y : ι → Torus) (w : ι → ℝ) :
    pointLaw (patchMeasure J hJ a b) y w =
      pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) y w := by
  rw [patchMeasure_eq_normalized hJ hJ₂ a b]
  exact pointLaw_smul_measure _ y w _ (patchNormalization_ne_zero hJ b)
    (patchNormalization_ne_top J b)

theorem memLp_greenGradient_patch {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (y : Torus) :
    MemLp (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal (4 / 3 : ℝ))
      (patchMeasure J hJ a b) := by
  have h := (memLp_greenGradient (4 / 3 : ℝ) (by norm_num) (by norm_num)).comp_measurePreserving
    (measurePreserving_sub_right torusMeasure y)
  rw [patchMeasure_eq_normalized hJ hJ₂ a b]
  exact (h.restrict _).smul_measure (patchNormalization_ne_top J b)

/-- Unweighted Green-gradient integrability under the actual point law is
proved even when its source coefficient is zero. It is not inferred by
dividing the integrable weighted source derivative by that coefficient. -/
theorem integrable_greenGradient_pointLaw {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (y : ι → Torus) (w : ι → ℝ)
    (hz : 0 < ∫ z, torusWeight y w z ∂patchMeasure J hJ a b)
    (hp : MemLp (pointDensity (patchMeasure J hJ a b) y w) 4 (patchMeasure J hJ a b))
    (Y : Torus) :
    Integrable (fun z ↦ greenGradient (z - Y)) (pointLaw (patchMeasure J hJ a b) y w) := by
  have hc : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by constructor <;> norm_num
  let : ENNReal.HolderTriple 4 (ENNReal.ofReal (4 / 3 : ℝ)) 1 := by
    simpa only [ENNReal.ofReal_ofNat] using hc.ennrealOfReal
  rw [pointLaw_integrable_iff y w hz]
  exact memLp_one_iff_integrable.mp (hp.smul (memLp_greenGradient_patch hJ hJ₂ a b Y))

theorem capped_greenGradient_pointLaw {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (Y : Torus) :
    Integrable (fun z ↦ greenGradient (z - Y))
      (pointLaw (patchMeasure J hJ a b) (fun i : I ↦ X i) (fun i : I ↦ w i)) := by
  have h := CappedPointWeights.capped_pointWeight_bounds hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁
    hmesh η hη I X hX w hw₀ hw a b
  exact integrable_greenGradient_pointLaw hJ (by omega) a b _ _ h.2.1 h.2.2.2.1 Y

theorem capped_raw_normalizer_bounds (K : KernelBounds) {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    let W := torusWeight (fun i : I ↦ X i) (fun i : I ↦ w i)
    Integrable W (torusMeasure.restrict (patchDomain J hJ a b)) ∧
      0 < patchArea J b * normalizerLower β₀ ∧
      patchArea J b * normalizerLower β₀ ≤ (∫ z in patchDomain J hJ a b, W z ∂torusMeasure) ∧
      (∫ z in patchDomain J hJ a b, W z ∂torusMeasure) ≤
        patchArea J b * (weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant) := by
  have h := capped_normalizer_bounds K hJ hN hβ hβ₀ hC₀ hmesh η hη I X hX w hw₀ hw a b
  have hJ₂ : 2 ≤ J := by omega
  have hi := h.1
  rw [patchMeasure_eq_normalized hJ hJ₂ a b,
    integrable_smul_measure (patchNormalization_ne_zero hJ b) (patchNormalization_ne_top J b)] at hi
  refine ⟨hi, mul_pos (patchArea_pos hJ b) (normalizerLower_pos β₀), ?_, ?_⟩
  · rw [integral_raw_eq_patchArea_smul_patch hJ hJ₂ a b, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left h.2.1 (patchArea_pos hJ b).le
  · rw [integral_raw_eq_patchArea_smul_patch hJ hJ₂ a b, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left h.2.2 (patchArea_pos hJ b).le

section LocalFactors

/-- Ordinary Riesz gradient in the physical source coordinates, with the
torus integration coordinate held fixed. Behavior off the chart is unrestricted. -/
def torusFactorGradient (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι) (z : Torus) :
    SourceSpace ι := (InnerProductSpace.toDual ℝ (SourceSpace ι)).symm
      (fderiv ℝ (fun Y ↦ F Y z) X)

theorem torusFactorGradient_comp {J : ℕ} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    {X : SourceSpace ι} (hX : X ∈ S) {Z : PlanarSpace} (hZ : Z ∈ patchClosed b) :
    torusFactorGradient F X (meshChart J a Z) = factorGradient (torusFactor F J a) (X, Z) := by
  symm
  exact factorGradient_eq_riesz_fibre ((hf.contDiffAt ⟨hX, hZ⟩).differentiableAt one_ne_zero)

theorem continuousOn_torusFactor_comp {J : ℕ} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    {X : SourceSpace ι} (hX : X ∈ S) :
    ContinuousOn (fun Z ↦ F X (meshChart J a Z)) (patchClosed b) := by
  exact hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hZ ↦ ⟨hX, hZ⟩)

theorem continuousOn_torusFactorGradient_comp {J : ℕ} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    {X : SourceSpace ι} (hX : X ∈ S) :
    ContinuousOn (fun Z ↦ torusFactorGradient F X (meshChart J a Z)) (patchClosed b) := by
  have hc := hf.continuousOn_factorGradient.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ hZ ↦ ⟨hX, hZ⟩)
  exact hc.congr (fun _ hZ ↦ torusFactorGradient_comp hf hX hZ)

/-- This discharges the earlier local raw-factor measurability obligation
from the genuine local C1 hypothesis, rather than adding a global hypothesis. -/
theorem measurable_local_factors {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    {X : SourceSpace ι} (hX : X ∈ S) :
    AEStronglyMeasurable (F X) (patchMeasure J hJ a b) ∧
      AEStronglyMeasurable (torusFactorGradient F X) (patchMeasure J hJ a b) :=
  ⟨aestronglyMeasurable_patch_of_comp hJ a b (continuousOn_torusFactor_comp hf hX),
    aestronglyMeasurable_patch_of_comp hJ a b (continuousOn_torusFactorGradient_comp hf hX)⟩

/-- Both finite bounds are uniform over the whole fixed closed source chart. -/
theorem local_factors_uniformly_bounded {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    {S : Set (SourceSpace ι)} (hS : IsCompact S) {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ X ∈ S, ∀ z ∈ closure (patchDomain J hJ a b),
      |F X z| ≤ A ∧ ‖torusFactorGradient F X z‖ ≤ D := by
  obtain ⟨A, hA, hbA⟩ := ((hS.prod (isCompact_patchClosed b)).image_of_continuousOn
    hf.continuousOn).isBounded.exists_pos_norm_le
  obtain ⟨D, hD, hbD⟩ := ((hS.prod (isCompact_patchClosed b)).image_of_continuousOn
    hf.continuousOn_factorGradient).isBounded.exists_pos_norm_le
  refine ⟨A, D, hA, hD, ?_⟩
  intro X hX z hz
  rw [closure_patchDomain hJ] at hz
  obtain ⟨Z, hZ, rfl⟩ := hz
  constructor
  · exact hbA _ (mem_image_of_mem (torusFactor F J a) (show (X, Z) ∈ S ×ˢ patchClosed b from ⟨hX, hZ⟩))
  · rw [torusFactorGradient_comp hf hX hZ]
    exact hbD _ (mem_image_of_mem _ ⟨hX, hZ⟩)

def torusProductGradient (w : ι → ℝ) (F : SourceSpace ι → Torus → ℝ)
    (X : SourceSpace ι) (z : Torus) : SourceSpace ι :=
  torusWeight (sources X) w z • torusFactorGradient F X z +
    fullGradient (fun j ↦ F X z • sourceGradient (sources X) w j z)

theorem torusProductGradient_comp {J : ℕ} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) (w : ι → ℝ)
    {X : SourceSpace ι} (hX : X ∈ S) {Z : PlanarSpace} (hZ : Z ∈ patchClosed b) :
    torusProductGradient w F X (meshChart J a Z) =
      productGradient w J a (torusFactor F J a) (X, Z) := by
  simp only [torusProductGradient, torusFactorGradient_comp hf hX hZ,
    productGradient, weight, gradient, torusFactor]

theorem measurable_torusProductGradient {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) (w : ι → ℝ)
    {X : SourceSpace ι} (hX : X ∈ S) :
    AEStronglyMeasurable (torusProductGradient w F X) (patchMeasure J hJ a b) := by
  obtain ⟨hF, hD⟩ := measurable_local_factors hJ a b hf hX
  apply ((measurable_torusWeight (sources X) w).aestronglyMeasurable.smul hD).add
  unfold fullGradient
  apply Finset.aestronglyMeasurable_fun_sum
  intro j _
  exact (sourceProjection j).adjoint.continuous.comp_aestronglyMeasurable
    (hF.smul (measurable_sourceGradient (sources X) w j).aestronglyMeasurable)

def rawNumeratorGradient (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι) : SourceSpace ι :=
  ∫ z in patchDomain J hJ a b, torusProductGradient w F X z ∂torusMeasure

/-- Exact equality of the entire physical raw-Haar numerator field and the
reference field already occurring in the checked weak identity. -/
theorem rawNumeratorGradient_eq_scaled {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) {S : Set (SourceSpace ι)}
    {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) (w : ι → ℝ)
    {X : SourceSpace ι} (hX : X ∈ S) :
    rawNumeratorGradient w J hJ a b F X =
      patchArea J b • numeratorGradient w J a b (torusFactor F J a) X := by
  rw [rawNumeratorGradient, integral_raw_eq_patchArea_smul hJ hJ₂ a b _
    (measurable_torusProductGradient hJ a b hf w hX)]
  congr 1
  exact integral_congr_ae ((ae_mem_patchClosed b).mono fun Z hZ ↦
    torusProductGradient_comp hf w hX hZ)

theorem rawNumerator_eq_scaled_local {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) {S : Set (SourceSpace ι)}
    {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) (w : ι → ℝ)
    {X : SourceSpace ι} (hX : X ∈ S) :
    rawNumerator w J hJ a b F X =
      patchArea J b * numerator w J a b (torusFactor F J a) X :=
  rawNumerator_eq_scaled w hJ hJ₂ a b F X (measurable_local_factors hJ a b hf hX).1

theorem capped_raw_fibres_integrable (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (X : SourceSpace I) (hXS : X ∈ S)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) :
    Integrable (fun z ↦ torusWeight (sources X) (fun i : I ↦ w i) z * F X z)
      (torusMeasure.restrict (patchDomain J hJ a b)) ∧
      Integrable (torusProductGradient (fun i : I ↦ w i) F X)
        (torusMeasure.restrict (patchDomain J hJ a b)) := by
  have hJ₂ : 2 ≤ J := by omega
  obtain ⟨hi, hgi⟩ := capped_fixed_productFibre_integrable K hJ hN hβ hβ₀ hC₀ hmesh I S X hXS
    η hη hX w hw₀ hw a b hf
  refine ⟨integrable_rawFibre_of_reference _ hJ hJ₂ a b F X
    (measurable_local_factors hJ a b hf hXS).1 hi, ?_⟩
  apply (integrable_raw_iff_reference hJ hJ₂ a b _
    (measurable_torusProductGradient hJ a b hf _ hXS)).mpr
  exact hgi.congr ((ae_mem_patchClosed b).mono fun Z hZ ↦
    (torusProductGradient_comp hf _ hXS hZ).symm)

end LocalFactors

section Covariance

variable {μ : Measure Torus}

/-- Componentwise covariance with an actual physical vector field. -/
def vectorCovariance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (ν : Measure Torus) (f : Torus → ℝ) (G : Torus → V) : V :=
  (∫ z, f z • G z ∂ν) - (∫ z, f z ∂ν) • (∫ z, G z ∂ν)

theorem normalized_sourceGradient_eq (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (hz : 0 < ∫ z, torusWeight y w z ∂μ) :
    (∫ z, torusWeight y w z ∂μ)⁻¹ • (∫ z, sourceGradient y w j z ∂μ) =
      (-w j) • (∫ z, greenGradient (z - y j) ∂pointLaw μ y w) := by
  rw [pointLaw_integral y w hz]
  simp_rw [sourceGradient, mul_smul]
  rw [integral_smul, smul_smul, smul_smul, mul_comm]

theorem normalized_factor_sourceGradient_eq (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (hz : 0 < ∫ z, torusWeight y w z ∂μ) (f : Torus → ℝ) :
    (∫ z, torusWeight y w z ∂μ)⁻¹ • (∫ z, f z • sourceGradient y w j z ∂μ) =
      (-w j) • (∫ z, f z • greenGradient (z - y j) ∂pointLaw μ y w) := by
  have he : (fun z ↦ f z • sourceGradient y w j z) =
      (fun z ↦ (-w j) • (torusWeight y w z • (f z • greenGradient (z - y j)))) := by
    funext z
    simp only [sourceGradient, smul_smul]
    congr 1
    ring
  rw [he, integral_smul, pointLaw_integral y w hz, smul_smul, smul_smul, mul_comm]

theorem normalized_factor_eq_mean (y : ι → Torus) (w : ι → ℝ)
    (hz : 0 < ∫ z, torusWeight y w z ∂μ) (f : Torus → ℝ) :
    (∫ z, torusWeight y w z * f z ∂μ) / (∫ z, torusWeight y w z ∂μ) =
      ∫ z, f z ∂pointLaw μ y w := by
  rw [pointLaw_integral y w hz]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- An algebraic identification of the proposed source quotient field with
the physical covariance expression. This is not a weak quotient theorem.
Its integrals are proved integrable at the capped local endpoint below. -/
theorem source_quotient_field_eq_covariance (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (hz : 0 < ∫ z, torusWeight y w z ∂μ) (f : Torus → ℝ) (A : Torus → PlanarSpace) :
    (∫ z, torusWeight y w z ∂μ)⁻¹ •
        ((∫ z, torusWeight y w z • A z ∂μ) + (∫ z, f z • sourceGradient y w j z ∂μ)) -
      ((∫ z, torusWeight y w z * f z ∂μ) / (∫ z, torusWeight y w z ∂μ) ^ 2) •
        (∫ z, sourceGradient y w j z ∂μ) =
      (∫ z, A z ∂pointLaw μ y w) -
        w j • vectorCovariance (pointLaw μ y w) f (fun z ↦ greenGradient (z - y j)) := by
  have he : (∫ z, torusWeight y w z * f z ∂μ) / (∫ z, torusWeight y w z ∂μ) ^ 2 =
      ((∫ z, torusWeight y w z * f z ∂μ) / (∫ z, torusWeight y w z ∂μ)) *
        (∫ z, torusWeight y w z ∂μ)⁻¹ := by
    field_simp [hz.ne']
  rw [he, mul_smul, smul_add, ← pointLaw_integral y w hz A,
    normalized_factor_sourceGradient_eq y w j hz f,
    normalized_sourceGradient_eq y w j hz, normalized_factor_eq_mean y w hz f]
  rw [vectorCovariance, smul_sub]
  simp only [neg_smul, smul_neg, smul_smul, mul_comm]
  abel

theorem local_covariance_integrable {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) {S : Set (SourceSpace ι)} (hS : IsCompact S)
    {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    (X : SourceSpace ι) (hXS : X ∈ S) (ν : Measure Torus) [IsProbabilityMeasure ν]
    (hac : ν ≪ patchMeasure J hJ a b)
    (hG : ∀ Y : Torus, Integrable (fun z ↦ greenGradient (z - Y)) ν) :
    Integrable (F X) ν ∧ Integrable (torusFactorGradient F X) ν ∧
      ∀ Y : Torus, Integrable (fun z ↦ greenGradient (z - Y)) ν ∧
        Integrable (fun z ↦ F X z • greenGradient (z - Y)) ν := by
  obtain ⟨A, D, hA, hD, hbnd⟩ := local_factors_uniformly_bounded hJ a b hS hf
  obtain ⟨hFm, hDm⟩ := measurable_local_factors hJ a b hf hXS
  have hFν : AEStronglyMeasurable (F X) ν := AEStronglyMeasurable.mono_ac hac hFm
  have hDν : AEStronglyMeasurable (torusFactorGradient F X) ν :=
    AEStronglyMeasurable.mono_ac hac hDm
  have hν : ∀ᵐ z ∂ν, z ∈ closure (patchDomain J hJ a b) :=
    (ae_mem_closure_patch hJ a b).filter_mono hac.ae_le
  have hbF : ∀ᵐ z ∂ν, ‖F X z‖ ≤ A := hν.mono fun z hz ↦ (hbnd X hXS z hz).1
  have hbD : ∀ᵐ z ∂ν, ‖torusFactorGradient F X z‖ ≤ D :=
    hν.mono fun z hz ↦ (hbnd X hXS z hz).2
  refine ⟨Integrable.of_bound hFν A hbF, Integrable.of_bound hDν D hbD, ?_⟩
  intro Y
  exact ⟨hG Y, (hG Y).bdd_smul A hFν hbF⟩

/-- All physical right-hand-side terms are integrable for every fixed capped
placement, including coincident sources and a deleted coefficient. The
factor and its derivative are required only near the closed product chart. -/
theorem capped_local_covariance_integrable {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) {S : Set (SourceSpace I)} (hS : IsCompact S)
    (X : SourceSpace I) (hXS : X ∈ S) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) :
    let ν := pointLaw (patchMeasure J hJ a b) (sources X) (fun i : I ↦ w i)
    Integrable (F X) ν ∧ Integrable (torusFactorGradient F X) ν ∧
      ∀ Y : Torus, Integrable (fun z ↦ greenGradient (z - Y)) ν ∧
        Integrable (fun z ↦ F X z • greenGradient (z - Y)) ν := by
  have hb := CappedPointWeights.capped_pointWeight_bounds hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁
    hmesh η hη I (extendedSources I X) hX w hw₀ hw a b
  simp only [extendedSources_subtype] at hb
  let ν := pointLaw (patchMeasure J hJ a b) (sources X) (fun i : I ↦ w i)
  change Integrable (F X) ν ∧ Integrable (torusFactorGradient F X) ν ∧
    ∀ Y : Torus, Integrable (fun z ↦ greenGradient (z - Y)) ν ∧
      Integrable (fun z ↦ F X z • greenGradient (z - Y)) ν
  let : IsProbabilityMeasure ν := hb.2.2.1
  have hac : ν ≪ patchMeasure J hJ a b := withDensity_absolutelyContinuous _ _
  apply local_covariance_integrable hJ a b hS hf X hXS ν hac
  exact fun Y ↦ integrable_greenGradient_pointLaw hJ (by omega) a b (sources X)
    (fun i : I ↦ w i) hb.2.1 hb.2.2.2.1 Y

end Covariance

section UniformNumerators

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure A}

omit [CompleteSpace E] in
theorem norm_integral_smul_bounded {W : A → ℝ} {G : A → E} {D : ℝ}
    (hW : Integrable W μ) (hb : ∀ᵐ z ∂μ, ‖G z‖ ≤ D) :
    ‖∫ z, W z • G z ∂μ‖ ≤ D * ∫ z, ‖W z‖ ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hW.norm.const_mul D)
  filter_upwards [hb] with z hz
  rw [norm_smul, mul_comm D]
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

omit [CompleteSpace E] in
theorem norm_integral_bounded_smul {f : A → ℝ} {G : A → E} {C : ℝ}
    (hG : Integrable G μ) (hb : ∀ᵐ z ∂μ, ‖f z‖ ≤ C) :
    ‖∫ z, f z • G z ∂μ‖ ≤ C * ∫ z, ‖G z‖ ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hG.norm.const_mul C)
  filter_upwards [hb] with z hz
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

theorem integrable_fullGradient {G : ι → A → PlanarSpace} (hG : ∀ j, Integrable (G j) μ) :
    Integrable (fun z ↦ fullGradient (fun j ↦ G j z)) μ := by
  apply integrable_finsetSum Finset.univ
  intro j _
  exact (sourceProjection j).adjoint.integrable_comp (hG j)

theorem integral_fullGradient {G : ι → A → PlanarSpace} (hG : ∀ j, Integrable (G j) μ) :
    (∫ z, fullGradient (fun j ↦ G j z) ∂μ) = fullGradient (fun j ↦ ∫ z, G j z ∂μ) := by
  unfold fullGradient
  rw [integral_finsetSum Finset.univ
    (fun j _ ↦ (sourceProjection j).adjoint.integrable_comp (hG j))]
  exact Finset.sum_congr rfl fun j _ ↦ (sourceProjection j).adjoint.integral_comp_comm (hG j)

theorem norm_fullGradient_le (G : ι → PlanarSpace) :
    ‖fullGradient G‖ ≤ ∑ j, ‖(sourceProjection j).adjoint‖ * ‖G j‖ := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun j _ ↦ (sourceProjection j).adjoint.le_opNorm (G j)

end UniformNumerators

/-- An explicit bound for the actual integrated whole source-gradient field.
All factors and moments used here are finite; the capped theorem below
supplies these hypotheses for the genuine weight and local ordinary gradient. -/
theorem integral_torusProductGradient_bound {μ : Measure Torus}
    (w : ι → ℝ) (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι)
    {A D CW CG : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hW : Integrable (torusWeight (sources X) w) μ)
    (hG : ∀ j, Integrable (sourceGradient (sources X) w j) μ)
    (hFm : AEStronglyMeasurable (F X) μ) (hDm : AEStronglyMeasurable (torusFactorGradient F X) μ)
    (hbF : ∀ᵐ z ∂μ, ‖F X z‖ ≤ A) (hbD : ∀ᵐ z ∂μ, ‖torusFactorGradient F X z‖ ≤ D)
    (hWb : (∫ z, ‖torusWeight (sources X) w z‖ ∂μ) ≤ CW)
    (hGb : ∀ j, (∫ z, ‖sourceGradient (sources X) w j z‖ ∂μ) ≤ CG) :
    Integrable (torusProductGradient w F X) μ ∧
      ‖∫ z, torusProductGradient w F X z ∂μ‖ ≤
        D * CW + ∑ j : ι, ‖(sourceProjection j).adjoint‖ * (A * CG) := by
  have hFG (j : ι) : Integrable (fun z ↦ F X z • sourceGradient (sources X) w j z) μ :=
    (hG j).bdd_smul A hFm hbF
  have hWD : Integrable (fun z ↦ torusWeight (sources X) w z • torusFactorGradient F X z) μ :=
    hW.smul_bdd D hDm hbD
  refine ⟨hWD.add (integrable_fullGradient hFG), ?_⟩
  change ‖∫ z, torusWeight (sources X) w z • torusFactorGradient F X z +
    fullGradient (fun j ↦ F X z • sourceGradient (sources X) w j z) ∂μ‖ ≤ _
  rw [integral_add hWD (integrable_fullGradient hFG), integral_fullGradient hFG]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_integral_smul_bounded hW hbD).trans (mul_le_mul_of_nonneg_left hWb hD)
  · apply (norm_fullGradient_le _).trans
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_integral_bounded_smul (hG j) hbF).trans (mul_le_mul_of_nonneg_left (hGb j) hA)

/-- At fixed N and J, the numerator, raw normalizer and its full physical
weak numerator field have bounds uniform over every point of the compact
source chart. The labels may switch between two prescribed endpoint cells.
The conclusion uses the literal raw-Haar normalization. -/
theorem capped_uniform_raw_bounds (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S)
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ X ∈ S,
      patchArea J b * normalizerLower β₀ ≤ rawNumerator (fun i : I ↦ w i) J hJ a b (fun _ _ ↦ 1) X ∧
      |rawNumerator (fun i : I ↦ w i) J hJ a b F X| ≤
        patchArea J b * (A * (weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant)) ∧
      ‖rawNumeratorGradient (fun i : I ↦ w i) J hJ a b F X‖ ≤
        patchArea J b * (D * (weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant) +
          ∑ j : I, ‖(sourceProjection j).adjoint‖ * (A * sourceNormBound K β₀ J (nearRadius β₀ C₁))) := by
  obtain ⟨A, D, hA, hD, hbound⟩ := local_factors_uniformly_bounded hJ a b hS hf
  refine ⟨A, D, hA, hD, ?_⟩
  intro X hXS
  let μ := patchMeasure J hJ a b
  let : IsProbabilityMeasure μ := patchMeasure_probability J hJ a b
  have hJ₂ : 2 ≤ J := by omega
  have hm := capped_limiting_mesh_bounds K hJ hN hβ hβ₀ hC₀ hmesh (η X) (hη X hXS)
    I (extendedSources I X) (hX X hXS) w hw₀ hw a b
  simp only [extendedSources_subtype] at hm
  have hW := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) hm.1
  have hG (j : I) := MemLp.integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (hm.2.2 j).1
  have hWb := (integral_norm_le_lpNorm (by norm_num) hm.1).trans hm.2.1
  have hGb (j : I) := (integral_norm_le_lpNorm (by norm_num) (hm.2.2 j).1).trans (hm.2.2 j).2
  obtain ⟨hFm, hDm⟩ := measurable_local_factors hJ a b hf hXS
  have hbF : ∀ᵐ z ∂μ, ‖F X z‖ ≤ A :=
    (ae_mem_closure_patch hJ a b).mono fun z hz ↦ (hbound X hXS z hz).1
  have hbD : ∀ᵐ z ∂μ, ‖torusFactorGradient F X z‖ ≤ D :=
    (ae_mem_closure_patch hJ a b).mono fun z hz ↦ (hbound X hXS z hz).2
  have hr := capped_raw_normalizer_bounds K hJ hN hβ hβ₀ hC₀ hmesh (η X) (hη X hXS)
    I (extendedSources I X) (hX X hXS) w hw₀ hw a b
  simp only [extendedSources_subtype] at hr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rawNumerator, mul_one] using hr.2.2.1
  · change ‖∫ z in patchDomain J hJ a b,
      torusWeight (sources X) (fun i : I ↦ w i) z • F X z ∂torusMeasure‖ ≤ _
    rw [integral_raw_eq_patchArea_smul_patch hJ hJ₂ a b, norm_smul,
      Real.norm_eq_abs, abs_of_pos (patchArea_pos hJ b)]
    exact mul_le_mul_of_nonneg_left ((norm_integral_smul_bounded hW hbF).trans
      (mul_le_mul_of_nonneg_left hWb hA.le)) (patchArea_pos hJ b).le
  · rw [rawNumeratorGradient, integral_raw_eq_patchArea_smul_patch hJ hJ₂ a b,
      norm_smul, Real.norm_eq_abs, abs_of_pos (patchArea_pos hJ b)]
    exact mul_le_mul_of_nonneg_left
      (integral_torusProductGradient_bound _ F X hA.le hD.le hW hG hFm hDm hbF hbD hWb hGb).2
      (patchArea_pos hJ b).le

/-- The unnormalized weak derivative with the actual full raw-Haar field,
on physical Euclidean source Lebesgue measure. -/
structure RawNumeratorWeakDerivative (w : ι → ℝ) (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) (S : Set (SourceSpace ι))
    (F : SourceSpace ι → Torus → ℝ) : Prop where
  value_integrable : Integrable (rawNumerator w J hJ a b F) (volume.restrict S)
  gradient_integrable : Integrable (rawNumeratorGradient w J hJ a b F) (volume.restrict S)
  weak_identity : ∀ ψ : SourceSpace ι → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
    ∀ v : SourceSpace ι,
    (∫ X in S, rawNumerator w J hJ a b F X * fderiv ℝ ψ X v) =
      -(∫ X in S, inner ℝ (rawNumeratorGradient w J hJ a b F X) v * ψ X)

/-- Transport of the checked reference weak identity. Local factor
measurability and equality of the entire vector field are proved above. -/
theorem rawWeakDerivative_of_reference (w : ι → ℝ) {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) {S : Set (SourceSpace ι)} (hS : MeasurableSet S)
    {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    (hN : NumeratorWeakDerivative w J a b S 1 (torusFactor F J a)) :
    RawNumeratorWeakDerivative w J hJ a b S F := by
  have hFm : ∀ᵐ X ∂(volume : Measure (SourceSpace ι)).restrict S,
      AEStronglyMeasurable (F X) (patchMeasure J hJ a b) :=
    (ae_restrict_mem hS).mono fun X hX ↦ (measurable_local_factors hJ a b hf hX).1
  have h := raw_numerator_weak_identity w hJ hJ₂ a b S 1 F
    (by simpa only [one_smul] using hFm) hN
  simp only [one_smul] at h
  have he : rawNumeratorGradient w J hJ a b F =ᵐ[(volume : Measure (SourceSpace ι)).restrict S]
      fun X ↦ patchArea J b • numeratorGradient w J a b (torusFactor F J a) X :=
    (ae_restrict_mem hS).mono fun X hX ↦ rawNumeratorGradient_eq_scaled hJ hJ₂ a b hf w hX
  refine ⟨h.1, h.2.1.congr he.symm, ?_⟩
  intro ψ hψ hc hψS v
  rw [h.2.2.2 ψ hψ hc hψS v]
  congr 1
  exact integral_congr_ae (he.mono fun X hX ↦ by
    dsimp only at hX ⊢
    rw [hX])

/-- Fully instantiated cell-source chart. A factor may be arbitrary away
from the required neighborhood of the product of closed coordinate domains. -/
theorem cellChart_raw_numerator (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart (cellChart I η) (patchClosed b) (torusFactor F J a)) :
    RawNumeratorWeakDerivative (fun i : I ↦ w i) J hJ a b (cellChart I η) F := by
  apply rawWeakDerivative_of_reference _ hJ (by omega) a b
    (isCompact_closedChart J (fun i : I ↦ η i) (fun _ ↦ Patch.cell)).measurableSet hf
  exact cellChart_numerator K hJ hN hβ hβ₀ hC₀ hmesh I η hη w hw₀ hw a b hf

/-- Fully instantiated chart with one adjacent source block, including
either orientation and wrap, using the two genuine endpoint occupation caps. -/
theorem adjacentChart_raw_numerator (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N) (k : Fin N) (d : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁) (Function.update η k (nextCell J hJ (η k) d)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart (adjacentChart I η k d) (patchClosed b) (torusFactor F J a)) :
    RawNumeratorWeakDerivative (fun i : I ↦ w i) J hJ a b (adjacentChart I η k d) F := by
  apply rawWeakDerivative_of_reference _ hJ (by omega) a b
    (isCompact_closedChart J (fun i : I ↦ η i) (adjacentShapes I k d)).measurableSet hf
  exact adjacentChart_numerator K hJ hN hβ hβ₀ hC₀ hmesh I η k d hη₀ hη₁ w hw₀ hw a b hf

/-- Once an almost-everywhere identity is established in physical chart
coordinates, every actual density with respect to that chart inherits it.
This transfer neither establishes an identity nor constructs its Lipschitz
representative. No assertion about collision capacity enters the argument. -/
theorem ae_weighted_chart {S : Set (SourceSpace ι)} {P : SourceSpace ι → Prop}
    (h : ∀ᵐ X ∂(volume : Measure (SourceSpace ι)).restrict S, P X)
    (ρ : SourceSpace ι → ℝ) :
    ∀ᵐ X ∂((volume : Measure (SourceSpace ι)).restrict S).withDensity
      (fun X ↦ ENNReal.ofReal (ρ X)), P X :=
  h.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

end PeriodicAttractiveLogGas.MovingPoleCalculus
