import LeanResearch.PeriodicAttractiveLogGas.MeshAdjacentCells
import LeanResearch.PeriodicAttractiveLogGas.GreenFarOscillation
import LeanResearch.PeriodicAttractiveLogGas.GreenPointRescaling
import LeanResearch.PeriodicAttractiveLogGas.ConditionalParameters
import LeanResearch.PeriodicAttractiveLogGas.MeshNearbyGeometry

/-! Assembly of the actual finite Green point-weight law on a mesh cell or
either orientation of an adjacent-cell union. Geometric classification uses
prescribed source indices, including closed-cell boundary placements. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.GreenPointWeights

open MeshCells MeshAdjacentCells GreenFarOscillation GreenPointRescaling PointWeightDensity

inductive Patch where
  | cell
  | edge (j : Fin 2)

def patchClosed : Patch → Set PlanarSpace
  | .cell => closedUnitSquare
  | .edge j => closedEdgeRectangle j

def patchReference : Patch → Measure PlanarSpace
  | .cell => squareLebesgue
  | .edge j => edgeLebesgue j

def patchMeasure (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Patch → Measure Torus
  | .cell => meshCellMeasure J hJ a
  | .edge j => edgeCellMeasure J hJ a j

instance patchReference_probability (b : Patch) : IsProbabilityMeasure (patchReference b) := by
  cases b with
  | cell => exact isProbabilityMeasure_squareLebesgue
  | edge j => exact isProbabilityMeasure_edgeLebesgue j

theorem patchMeasure_probability (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    IsProbabilityMeasure (patchMeasure J hJ a b) := by
  cases b with
  | cell => exact isProbabilityMeasure_meshCellMeasure J hJ a
  | edge j => exact isProbabilityMeasure_edgeCellMeasure J hJ a j

theorem patchReference_le_volume (b : Patch) : patchReference b ≤ volume := by
  cases b with
  | cell => exact SingularRectangleMoments.squareLebesgue_le_volume
  | edge j =>
    change (2 : ℝ≥0∞)⁻¹ • volume.restrict (edgeRectangle j) ≤ volume
    calc
      _ ≤ (1 : ℝ≥0∞) • volume.restrict (edgeRectangle j) := by
        gcongr
        norm_num
      _ ≤ volume := by simpa only [one_smul] using
        (Measure.restrict_le_self (μ := (volume : Measure PlanarSpace)) (s := edgeRectangle j))

theorem ae_mem_patchClosed (b : Patch) : ∀ᵐ Z ∂patchReference b, Z ∈ patchClosed b := by
  cases b with
  | cell => exact ae_restrict_mem measurableSet_closedUnitSquare
  | edge j =>
    exact (ae_mem_openEdgeRectangle j).mono fun Z hZ k hk ↦
      ⟨(hZ k hk).1.le, (hZ k hk).2.le⟩

theorem measurePreserving_patch (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    MeasurePreserving (meshChart J a) (patchReference b) (patchMeasure J hJ a b) := by
  cases b with
  | cell => exact measurePreserving_meshChart J hJ a
  | edge j => exact measurePreserving_meshChart_edgeRectangle J hJ a j

theorem zero_mem_patchClosed (b : Patch) : (0 : PlanarSpace) ∈ patchClosed b := by
  cases b with
  | cell => intro k hk; exact ⟨le_rfl, zero_le_one⟩
  | edge j => intro k hk; exact ⟨le_rfl, (edgeWidth_pos j k).le⟩

theorem convex_patchClosed (b : Patch) : Convex ℝ (patchClosed b) := by
  cases b with
  | cell => exact convex_closed .square
  | edge j =>
    intro Z hZ W hW s t hs ht hst k hk
    change 0 ≤ s * Z k + t * W k ∧ s * Z k + t * W k ≤ edgeWidth j k
    have hz := hZ k hk
    have hw := hW k hk
    refine ⟨add_nonneg (mul_nonneg hs hz.1) (mul_nonneg ht hw.1), ?_⟩
    calc
      _ ≤ s * edgeWidth j k + t * edgeWidth j k :=
        add_le_add (mul_le_mul_of_nonneg_left hz.2 hs) (mul_le_mul_of_nonneg_left hw.2 ht)
      _ = edgeWidth j k := by rw [← add_mul, hst, one_mul]

theorem norm_sub_patch_le_sqrt_five (b : Patch) {Z W : PlanarSpace}
    (hZ : Z ∈ patchClosed b) (hW : W ∈ patchClosed b) : ‖Z - W‖ ≤ Real.sqrt 5 := by
  cases b with
  | cell => exact norm_sub_le_sqrt_five .square hZ hW
  | edge j =>
    have hb (k : Fin 2) : |Z k - W k| ≤ edgeWidth j k := by
      apply abs_le.mpr
      constructor <;> linarith [(hZ k (mem_univ k)).1, (hZ k (mem_univ k)).2,
        (hW k (mem_univ k)).1, (hW k (mem_univ k)).2]
    have h0 := pow_le_pow_left₀ (abs_nonneg _) (hb 0) 2
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hb 1) 2
    simp only [sq_abs] at h0 h1
    have hd : edgeWidth j 0 ^ 2 + edgeWidth j 1 ^ 2 = 5 := by
      fin_cases j <;> norm_num [edgeWidth]
    have hn : ‖Z - W‖ ^ 2 ≤ 5 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      change (Z 0 - W 0) ^ 2 + (Z 1 - W 1) ^ 2 ≤ 5
      linarith
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hn

variable {ι : Type*} [Fintype ι]

theorem measurable_referencePotential (a : PlanarSpace) (J : ℝ) (y : ι → Torus) (w : ι → ℝ) :
    Measurable (referencePotential a J y w) := by
  apply Finset.measurable_sum
  intro i _
  apply Measurable.const_mul
  apply regularGreenRepresentative_measurable.comp
  have hq : Continuous torusQuotient := by unfold torusQuotient; fun_prop
  exact ((hq.comp (RectangleDilation.continuous_affine a J)).sub continuous_const).measurable

theorem far_oscillation (b : Patch) (a : PlanarSpace) {J R C₁ β₀ : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hkernel : KernelGradientBound C₁)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i ≤ β₀)
    (hsep : ∀ Z ∈ patchClosed b, ∀ i,
      R / J ≤ torusEuclideanNorm (torusQuotient (RectangleDilation.affine a J Z) - y i))
    {Z W : PlanarSpace} (hZ : Z ∈ patchClosed b) (hW : W ∈ patchClosed b) :
    |referencePotential a J y w Z - referencePotential a J y w W| ≤ Real.sqrt 5 * β₀ * C₁ / R := by
  have h := (convex_patchClosed b).norm_image_sub_le_of_norm_fderiv_le
    (fun X hX ↦ differentiableAt_referencePotential_of_separated a hJ hR y w (hsep X hX))
    (fun X hX ↦ norm_fderiv_referencePotential_le a hJ hR hC₁ hkernel
      y w hw hweight (hsep X hX)) hW hZ
  rw [Real.norm_eq_abs] at h
  have hβ : 0 ≤ β₀ := (Finset.sum_nonneg fun i _ ↦ hw i).trans hweight
  calc
    _ ≤ (β₀ * C₁ / R) * ‖Z - W‖ := h
    _ ≤ (β₀ * C₁ / R) * Real.sqrt 5 :=
      mul_le_mul_of_nonneg_left (norm_sub_patch_le_sqrt_five b hZ hW) (by positivity)
    _ = _ := by ring

open MeshNearbyGeometry ConditionalParameters

def nearby (J : ℕ) (hJ : 0 < J) (R : ℕ) (a : MeshIndex J) : Patch → Finset (MeshIndex J)
  | .cell => nearbyCells R a
  | .edge j => nearbyEdgeCells J hJ R a j

theorem card_nearby_le (J : ℕ) (hJ : 0 < J) (R : ℕ) (a : MeshIndex J) (b : Patch) :
    (nearby J hJ R a b).card ≤ (2 * R + 2) ^ 2 := by
  cases b with
  | cell => exact card_nearbyCells_le J hJ R a
  | edge j => exact card_nearbyEdgeCells_le J hJ R a j

theorem nearby_lift {J R : ℕ} (hJ : 0 < J) (a c : MeshIndex J) (b : Patch)
    (hc : c ∈ nearby J hJ R a b) {y : Torus} (hy : y ∈ closure (meshCell J hJ c)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ patchClosed b, ‖Z - Y‖ ≤ distanceBound R := by
  cases b with
  | cell =>
    obtain ⟨Y, hY, hb⟩ := exists_compatible_cell_lift hJ a c hc hy
    exact ⟨Y, hY, fun Z hZ ↦ norm_sub_le_nearReferenceRadius (hb Z hZ)⟩
  | edge j =>
    obtain ⟨Y, hY, hb⟩ := exists_compatible_edge_lift hJ a c j hc hy
    exact ⟨Y, hY, fun Z hZ ↦ norm_sub_le_nearReferenceRadius (hb Z hZ)⟩

theorem far_gap {J R : ℕ} (hJ : 0 < J) (a c : MeshIndex J) (b : Patch)
    (hc : c ∉ nearby J hJ R a b) {Z : PlanarSpace} (hZ : Z ∈ patchClosed b)
    {y : Torus} (hy : y ∈ closure (meshCell J hJ c)) :
    (R : ℝ) / J ≤ torusEuclideanNorm (meshChart J a Z - y) := by
  cases b with
  | cell => exact far_cell_reference_gap hJ a c hc hZ hy
  | edge j => exact far_edge_reference_gap hJ a c j hc hZ hy

def meshTranslation (J : ℕ) (a : MeshIndex J) : PlanarSpace := (J : ℝ)⁻¹ • meshIndexVector a

theorem meshChart_eq_chart (J : ℕ) (a : MeshIndex J) :
    meshChart J a = chart (meshTranslation J a) J := by
  funext Z
  simp only [meshChart, chart, meshAffine_eq_dilation, meshTranslation]

def torusWeight (y : ι → Torus) (w : ι → ℝ) (z : Torus) : ℝ :=
  Real.exp (∑ i, w i * regularGreenRepresentative (z - y i))

theorem measurable_torusWeight (y : ι → Torus) (w : ι → ℝ) : Measurable (torusWeight y w) := by
  apply Real.continuous_exp.measurable.comp
  exact Finset.measurable_sum _ fun i _ ↦
    (regularGreenRepresentative_measurable.comp (measurable_id.sub measurable_const)).const_mul (w i)

theorem torusWeight_pos (y : ι → Torus) (w : ι → ℝ) (z : Torus) : 0 < torusWeight y w z :=
  Real.exp_pos _

/-- The actual finite source family is split by its prescribed indices.
All geometric and oscillation inputs to the analytic normalization are proved. -/
theorem reference_pointWeight_bounds {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a : MeshIndex J) (b : Patch)
    (y : ι → Torus) (labels : ι → MeshIndex J)
    (hy : ∀ i, y i ∈ closure (meshCell J hJ (labels i))) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {β₀ C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : KernelGradientBound C₁) (htotal : ∑ i, w i ≤ β₀)
    (hnear : ∑ i : {i // labels i ∈ nearby J hJ R a b}, w i ≤ 1 / 4) :
    let μ := patchReference b
    let G := fun Z ↦ torusWeight y w (meshChart J a Z)
    Integrable G μ ∧ 0 < (∫ Z, G Z ∂μ) ∧
      IsProbabilityMeasure (μ.withDensity (fun Z ↦ ENNReal.ofReal (normalizedDensity μ G Z))) ∧
      MemLp (normalizedDensity μ G) 4 μ ∧
      (∀ᵐ Z ∂μ, sourceLowerConstant (distanceBound R) (oscillationBound β₀ C₁ R) C₀ ≤
        normalizedDensity μ G Z) ∧
      lpNorm (normalizedDensity μ G) 4 μ ≤
        sourceNormConstant (distanceBound R) (oscillationBound β₀ C₁ R) C₀ := by
  classical
  let P : ι → Prop := fun i ↦ labels i ∈ nearby J hJ R a b
  let Near := {i // P i}
  let Far := {i // ¬P i}
  have hlift (i : Near) : ∃ Y : PlanarSpace, meshChart J a Y = y i ∧
      ∀ Z ∈ patchClosed b, ‖Z - Y‖ ≤ distanceBound R :=
    nearby_lift hJ a (labels i) b i.property (hy i)
  choose Y hY hd using hlift
  let A := meshTranslation J a
  let F := referencePotential A J (fun i : Far ↦ y i) (fun i : Far ↦ w i)
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hwfar : ∑ i : Far, w i ≤ β₀ := by
    have he := Fintype.sum_subtype_add_sum_subtype P w
    have hn : 0 ≤ ∑ i : Near, w i := Finset.sum_nonneg fun i _ ↦ hw i
    change (∑ i : Near, w i) + (∑ i : Far, w i) = ∑ i, w i at he
    linarith
  have hsep : ∀ Z ∈ patchClosed b, ∀ i : Far,
      (R : ℝ) / J ≤ torusEuclideanNorm (torusQuotient (RectangleDilation.affine A J Z) - y i) := by
    intro Z hZ i
    have h := far_gap hJ a (labels i) b i.property hZ (hy i)
    simpa only [meshChart_eq_chart, chart, A] using h
  have hfosc : ∀ᵐ Z ∂patchReference b, |F Z - F 0| ≤ oscillationBound β₀ C₁ R := by
    filter_upwards [ae_mem_patchClosed b] with Z hZ
    exact far_oscillation b A hj hr hC₁ hk₁ (fun i : Far ↦ y i) (fun i : Far ↦ w i)
      (fun i ↦ hw i) hwfar hsep hZ (zero_mem_patchClosed b)
  have hd' : ∀ᵐ Z ∂patchReference b, ∀ i : Near, ‖Z - Y i‖ ≤ distanceBound R := by
    filter_upwards [ae_mem_patchClosed b] with Z hZ
    exact fun i ↦ hd i Z hZ
  have h := greenWeight_normalized_bounds (patchReference_le_volume b) A Y (fun i : Near ↦ w i)
    (fun i ↦ hw i) hnear hC₀ hj (distanceBound_one_le hR) (distanceBound_lt_half hR hmesh)
    hk₀ hd' (measurable_referencePotential A J _ _) 0 hfosc
  have he : greenWeight A J Y (fun i : Near ↦ w i) F =
      (fun Z ↦ torusWeight y w (meshChart J a Z)) := by
    funext Z
    have hYi (i : Near) : chart A J (Y i) = y i := by
      simpa only [meshChart_eq_chart, A] using hY i
    have hch : torusQuotient (RectangleDilation.affine A J Z) = meshChart J a Z :=
      (congrFun (meshChart_eq_chart J a) Z).symm
    simp only [greenWeight, hYi]
    simp only [torusWeight, F, referencePotential, referenceSource, chart, hch]
    congr 1
    rw [add_comm]
    exact Fintype.sum_subtype_add_sum_subtype P (fun i ↦ w i * regularGreenRepresentative (meshChart J a Z - y i))
  dsimp only [F] at he
  simpa only [he] using h

/-- The source density with its actual finite-domain normalizer. -/
def pointDensity (μ : Measure Torus) (y : ι → Torus) (w : ι → ℝ) (z : Torus) : ℝ :=
  torusWeight y w z / ∫ u, torusWeight y w u ∂μ

def pointLaw (μ : Measure Torus) (y : ι → Torus) (w : ι → ℝ) : Measure Torus :=
  μ.withDensity (fun z ↦ ENNReal.ofReal (pointDensity μ y w z))

theorem measurable_pointDensity (μ : Measure Torus) (y : ι → Torus) (w : ι → ℝ) :
    Measurable (pointDensity μ y w) := (measurable_torusWeight y w).div_const _

theorem pointLaw_probability {μ : Measure Torus} {y : ι → Torus} {w : ι → ℝ}
    (hi : Integrable (torusWeight y w) μ) (hz : 0 < ∫ z, torusWeight y w z ∂μ) :
    IsProbabilityMeasure (pointLaw μ y w) := by
  have hp : Integrable (pointDensity μ y w) μ := hi.div_const _
  have hpos : ∀ z, 0 ≤ pointDensity μ y w z := fun z ↦ div_nonneg (torusWeight_pos y w z).le hz.le
  have hmass : (∫ z, pointDensity μ y w z ∂μ) = 1 := by
    unfold pointDensity
    rw [integral_div, div_self hz.ne']
  constructor
  rw [pointLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall hpos), hmass, ENNReal.ofReal_one]

/-- Source Lemma 3.3's actual normalized law and exact density constants.
Every source retains its prescribed closed-cell index, with no separation or
noncoincidence assumption. The functional inequalities are supplied separately
by the local torus density-estimate theorem. -/
theorem pointWeight_bounds {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a : MeshIndex J) (b : Patch)
    (y : ι → Torus) (labels : ι → MeshIndex J)
    (hy : ∀ i, y i ∈ closure (meshCell J hJ (labels i))) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {β₀ C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : KernelGradientBound C₁) (htotal : ∑ i, w i ≤ β₀)
    (hnear : ∑ i : {i // labels i ∈ nearby J hJ R a b}, w i ≤ 1 / 4) :
    let μ := patchMeasure J hJ a b
    Integrable (torusWeight y w) μ ∧ 0 < (∫ z, torusWeight y w z ∂μ) ∧
      IsProbabilityMeasure (pointLaw μ y w) ∧
      MemLp (pointDensity μ y w) 4 μ ∧
      (∀ᵐ z ∂μ, sourceLowerConstant (distanceBound R) (oscillationBound β₀ C₁ R) C₀ ≤ pointDensity μ y w z) ∧
      lpNorm (pointDensity μ y w) 4 μ ≤ sourceNormConstant (distanceBound R) (oscillationBound β₀ C₁ R) C₀ := by
  classical
  let μ := patchReference b
  let ν := patchMeasure J hJ a b
  have hmp : MeasurePreserving (meshChart J a) μ ν := measurePreserving_patch J hJ a b
  have hm := measurable_torusWeight y w
  have h := reference_pointWeight_bounds hJ hR hmesh a b y labels hy w hw hC₀ hC₁ hk₀ hk₁ htotal hnear
  have hi : Integrable (torusWeight y w) ν :=
    (hmp.integrable_comp hm.aestronglyMeasurable).mp h.1
  have heint : (∫ Z, torusWeight y w (meshChart J a Z) ∂μ) = ∫ z, torusWeight y w z ∂ν := by
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable hm.aestronglyMeasurable).symm
  have hz : 0 < ∫ z, torusWeight y w z ∂ν := by
    rw [← heint]
    exact h.2.1
  have he : normalizedDensity μ (fun Z ↦ torusWeight y w (meshChart J a Z)) =
      (pointDensity ν y w) ∘ meshChart J a := by
    funext Z
    simp only [normalizedDensity, pointDensity, Function.comp_def, heint]
  have hpm : AEStronglyMeasurable (pointDensity ν y w) ν :=
    (measurable_pointDensity ν y w).aestronglyMeasurable
  have help := eLpNorm_comp_measurePreserving (p := 4) hpm hmp
  have hpref : MemLp ((pointDensity ν y w) ∘ meshChart J a) 4 μ := by
    rw [← he]
    exact h.2.2.2.1
  have hp : MemLp (pointDensity ν y w) 4 ν := by
    rw [memLp_iff, ← help]
    exact hpref.eLpNorm_lt_top
  refine ⟨hi, hz, pointLaw_probability hi hz, hp, ?_, ?_⟩
  · have hlo := h.2.2.2.2.1
    change ∀ᵐ Z ∂μ, _ ≤ normalizedDensity μ _ Z at hlo
    rw [he] at hlo
    have hmap := (ae_map_iff hmp.aemeasurable
      (measurableSet_le measurable_const (measurable_pointDensity ν y w))).mpr hlo
    simpa only [hmp.map_eq] using hmap
  · change (eLpNorm _ 4 ν).toReal ≤ _
    rw [← help, ← he]
    exact h.2.2.2.2.2

end PeriodicAttractiveLogGas.GreenPointWeights
