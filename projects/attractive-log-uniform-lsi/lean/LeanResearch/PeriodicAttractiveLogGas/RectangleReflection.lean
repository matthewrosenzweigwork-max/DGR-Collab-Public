import LeanResearch.PeriodicAttractiveLogGas.TorusDistance
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Source Lemma 3.1 (`lem:rectangle-sobolev`), lines 409--417:
the actual even-reflection geometry and its Lebesgue normalization.

The circle fold is `t ↦ 2 * ‖t‖`. Its image distribution is ordinary
Lebesgue measure on `[0,1]`, of total mass one. The square fold uses the
physical Euclidean norm and has ordinary derivative twice a coordinate
reflection away from its seams. The final square statements apply to an
arbitrary function Lipschitz on the closed square; its values outside that
square are immaterial. No Sobolev inequality is assumed or proved here.

The direct fold is the source even reflection and rescaling. Semantic review
and protected verification are recorded separately from development checks.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PeriodicAttractiveLogGas

/-- The fold corresponding to even reflection followed by period-two
rescaling. The circle has period one. -/
def circleFold (t : UnitAddCircle) : ℝ := 2 * ‖t‖

theorem continuous_circleFold : Continuous circleFold :=
  continuous_const.mul continuous_norm

theorem circleFold_mem_unitInterval (t : UnitAddCircle) : circleFold t ∈ Icc (0 : ℝ) 1 := by
  have ht := AddCircle.norm_le_half_period (1 : ℝ) (x := t) (by norm_num)
  constructor
  · exact mul_nonneg (by norm_num) (norm_nonneg t)
  · dsimp [circleFold]
    norm_num at ht
    linarith

/-- Exact distribution preservation, including the interval endpoints.
The proof compares finite measures on all left-closed distribution sets,
using the actual circle-ball Haar measure, rather than a formal Jacobian. -/
theorem measurePreserving_circleFold :
    MeasurePreserving circleFold AddCircle.haarAddCircle
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  refine ⟨continuous_circleFold.measurable, ?_⟩
  apply Measure.ext_of_Iic
  intro r
  have hp : circleFold ⁻¹' Iic r = Metric.closedBall (0 : UnitAddCircle) (r / 2) := by
    ext t
    simp only [mem_preimage, mem_Iic, circleFold, Metric.mem_closedBall, dist_zero_right]
    constructor <;> intro h <;> linarith
  have hi : Iic r ∩ Icc (0 : ℝ) 1 = Icc 0 (min 1 r) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [Measure.map_apply continuous_circleFold.measurable measurableSet_Iic,
    hp, ← unitCircle_volume_eq_haar, AddCircle.volume_closedBall,
    Measure.restrict_apply measurableSet_Iic, hi, Real.volume_Icc]
  congr 1
  rw [sub_zero]
  congr 1
  ring

theorem ae_circleFold_mem_openUnitInterval :
    ∀ᵐ t ∂AddCircle.haarAddCircle, circleFold t ∈ Ioo (0 : ℝ) 1 := by
  apply measurePreserving_circleFold.quasiMeasurePreserving.ae
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0),
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 1)] with t ht h0 h1
  exact ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩

def closedUnitSquare : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin 2 ↦ Icc (0 : ℝ) 1)

def openUnitSquare : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin 2 ↦ Ioo (0 : ℝ) 1)

def squareLebesgue : Measure PlanarSpace := volume.restrict closedUnitSquare

theorem measurableSet_closedUnitSquare : MeasurableSet closedUnitSquare :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem measurableSet_openUnitSquare : MeasurableSet openUnitSquare :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem closedUnitSquare_mem_nhds {x : PlanarSpace} (hx : x ∈ openUnitSquare) :
    closedUnitSquare ∈ 𝓝 x :=
  (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.preimage_mem_nhds
    (set_pi_mem_nhds Set.finite_univ fun j _ ↦
      Icc_mem_nhds (hx j (mem_univ j)).1 (hx j (mem_univ j)).2)

/-- The square-valued even reflection of the unit torus. -/
def squareReflection (z : Torus) : PlanarSpace :=
  WithLp.toLp 2 (fun j : Fin 2 ↦ circleFold (z j))

@[simp] theorem squareReflection_apply (z : Torus) (j : Fin 2) :
    squareReflection z j = circleFold (z j) := rfl

theorem continuous_squareReflection : Continuous squareReflection :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    (continuous_pi fun j ↦ continuous_circleFold.comp (continuous_apply j))

theorem squareReflection_mem_closedUnitSquare (z : Torus) :
    squareReflection z ∈ closedUnitSquare := by
  intro j _
  exact circleFold_mem_unitInterval (z j)

theorem continuous_reflectedSquare {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    Continuous (fun z : Torus ↦ u (squareReflection z)) :=
  hu.continuousOn.comp_continuous continuous_squareReflection
    squareReflection_mem_closedUnitSquare

theorem measurePreserving_squareReflection :
    MeasurePreserving squareReflection torusMeasure squareLebesgue := by
  have hp := measurePreserving_pi
    (fun _ : Fin 2 ↦ AddCircle.haarAddCircle)
    (fun _ : Fin 2 ↦ volume.restrict (Icc (0 : ℝ) 1))
    (fun _ ↦ measurePreserving_circleFold)
  have he := (PiLp.volume_preserving_toLp (Fin 2)).restrict_preimage
    (s := closedUnitSquare) measurableSet_closedUnitSquare
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → PlanarSpace) ⁻¹' closedUnitSquare =
      Set.pi Set.univ (fun _ : Fin 2 ↦ Icc (0 : ℝ) 1) := by
    ext x
    rfl
  rw [hpre, show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ ↦ volume) from rfl,
    Measure.restrict_pi_pi] at he
  exact he.comp hp

theorem squareLebesgue_univ : squareLebesgue Set.univ = 1 := by
  rw [← measurePreserving_squareReflection.map_eq,
    Measure.map_apply continuous_squareReflection.measurable MeasurableSet.univ]
  simp

instance isProbabilityMeasure_squareLebesgue : IsProbabilityMeasure squareLebesgue :=
  ⟨squareLebesgue_univ⟩

theorem volume_closedUnitSquare : volume closedUnitSquare = 1 := by
  simpa [squareLebesgue] using squareLebesgue_univ

theorem integral_squareReflection {f : PlanarSpace → ℝ} (hf : Integrable f squareLebesgue) :
    ∫ z, f (squareReflection z) ∂torusMeasure = ∫ x, f x ∂squareLebesgue := by
  have hm := measurePreserving_squareReflection
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    (by simpa only [hm.map_eq] using hf.aestronglyMeasurable)).symm

theorem ae_squareReflection_mem_openUnitSquare :
    ∀ᵐ z ∂torusMeasure, squareReflection z ∈ openUnitSquare := by
  have hj (j : Fin 2) : ∀ᵐ z ∂torusMeasure, circleFold (z j) ∈ Ioo (0 : ℝ) 1 :=
    (measurePreserving_eval (fun _ : Fin 2 ↦ AddCircle.haarAddCircle) j).quasiMeasurePreserving.ae ae_circleFold_mem_openUnitInterval
  filter_upwards [ae_all_iff.mpr hj] with z hz
  exact fun j _ ↦ hz j

theorem ae_mem_openUnitSquare : ∀ᵐ x ∂squareLebesgue, x ∈ openUnitSquare := by
  rw [← measurePreserving_squareReflection.map_eq]
  exact (ae_map_iff measurePreserving_squareReflection.aemeasurable
    measurableSet_openUnitSquare).mpr ae_squareReflection_mem_openUnitSquare

/-- The fold has Lipschitz constant two in the physical Euclidean norm. -/
theorem lipschitzWith_squareReflection_lift :
    LipschitzWith 2 (fun x : PlanarSpace ↦ squareReflection (torusQuotient x)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have hc (j : Fin 2) :
      |circleFold (torusQuotient x j) - circleFold (torusQuotient y j)| ≤
        2 * |x j - y j| := by
    have hquot : ‖torusQuotient x j - torusQuotient y j‖ ≤ |x j - y j| := by
      change ‖((x j - y j : ℝ) : UnitAddCircle)‖ ≤ |x j - y j|
      have h : ‖((x j - y j : ℝ) : UnitAddCircle)‖ ≤ ‖x j - y j‖ :=
        QuotientAddGroup.norm_mk_le_norm
      simpa only [Real.norm_eq_abs] using h
    calc
      _ = 2 * |‖torusQuotient x j‖ - ‖torusQuotient y j‖| := by
        dsimp only [circleFold]
        rw [← mul_sub, abs_mul]
        norm_num
      _ ≤ 2 * ‖torusQuotient x j - torusQuotient y j‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hquot (by norm_num)
  have hs : ‖squareReflection (torusQuotient x) - squareReflection (torusQuotient y)‖ ^ 2 ≤
      (2 * ‖x - y‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change (circleFold (torusQuotient x j) - circleFold (torusQuotient y j)) ^ 2 ≤
      (2 : ℝ) ^ 2 * (x j - y j) ^ 2
    simpa only [mul_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
  change ‖squareReflection (torusQuotient x) - squareReflection (torusQuotient y)‖ ≤
    2 * ‖x - y‖
  nlinarith [norm_nonneg (squareReflection (torusQuotient x) -
    squareReflection (torusQuotient y)), norm_nonneg (x - y)]

theorem lipschitzWith_reflectedSquare_lift {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    LipschitzWith (2 * K) (fun x : PlanarSpace ↦ u (squareReflection (torusQuotient x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ (K : ℝ) * dist (squareReflection (torusQuotient x))
        (squareReflection (torusQuotient y)) :=
      hu.dist_le_mul _ (squareReflection_mem_closedUnitSquare _) _
        (squareReflection_mem_closedUnitSquare _)
    _ ≤ (K : ℝ) * (2 * dist x y) :=
      mul_le_mul_of_nonneg_left (lipschitzWith_squareReflection_lift.dist_le_mul x y)
        K.coe_nonneg
    _ = _ := by push_cast; ring

/-- Coordinate signs act by an actual Euclidean linear isometry. -/
def squareCoordinateReflection (x : PlanarSpace) : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j : Fin 2 ↦
    if x j < 0 then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
    else LinearIsometryEquiv.refl ℝ ℝ

@[simp] theorem squareCoordinateReflection_apply (x y : PlanarSpace) (j : Fin 2) :
    squareCoordinateReflection x y j = if x j < 0 then -(y j) else y j := by
  by_cases hj : x j < 0 <;> simp [squareCoordinateReflection, hj]

/-- At a lift whose coordinates avoid zero and both half-period endpoints,
the ordinary derivative is exactly twice the coordinate reflection. -/
theorem hasFDerivAt_squareReflection_lift {x : PlanarSpace}
    (hx : ∀ j : Fin 2, 0 < |x j| ∧ |x j| < (1 / 2 : ℝ)) :
    HasFDerivAt (fun y ↦ squareReflection (torusQuotient y))
      ((2 : ℝ) • (squareCoordinateReflection x).toLinearIsometry.toContinuousLinearMap) x := by
  have hj (j : Fin 2) : ∀ᶠ y : PlanarSpace in 𝓝 x,
      circleFold (torusQuotient y j) = 2 * (if x j < 0 then -(y j) else y j) := by
    have hs : ∀ᶠ y : PlanarSpace in 𝓝 x, |y j| < (1 / 2 : ℝ) :=
      (isOpen_lt (EuclideanSpace.proj j).continuous.abs continuous_const).mem_nhds (hx j).2
    by_cases hn : x j < 0
    · have hsign : ∀ᶠ y : PlanarSpace in 𝓝 x, y j < 0 :=
        (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const).mem_nhds hn
      filter_upwards [hs, hsign] with y hy hs'
      have hnorm : ‖((y j : ℝ) : UnitAddCircle)‖ = |y j| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hy.le)
      simp only [circleFold, torusQuotient, hnorm, hn, ite_true, abs_of_neg hs']
    · have hxn : x j ≠ 0 := abs_pos.mp (hx j).1
      have hp : 0 < x j := lt_of_le_of_ne (le_of_not_gt hn) hxn.symm
      have hsign : ∀ᶠ y : PlanarSpace in 𝓝 x, 0 < y j :=
        (isOpen_lt continuous_const (EuclideanSpace.proj j).continuous).mem_nhds hp
      filter_upwards [hs, hsign] with y hy hs'
      have hnorm : ‖((y j : ℝ) : UnitAddCircle)‖ = |y j| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hy.le)
      simp only [circleFold, torusQuotient, hnorm, hn, ite_false, abs_of_pos hs']
  apply (((2 : ℝ) • (squareCoordinateReflection x).toLinearIsometry.toContinuousLinearMap).hasFDerivAt).congr_of_eventuallyEq
  filter_upwards [eventually_all.mpr hj] with y hy
  ext j
  change circleFold (torusQuotient y j) = 2 * (squareCoordinateReflection x y j)
  rw [squareCoordinateReflection_apply]
  exact hy j

theorem centeredLift_away_squareFold_seams {z : Torus}
    (hz : squareReflection z ∈ openUnitSquare) (j : Fin 2) :
    0 < |centeredLift z j| ∧ |centeredLift z j| < (1 / 2 : ℝ) := by
  have hj := hz j (mem_univ j)
  change 0 < 2 * ‖z j‖ ∧ 2 * ‖z j‖ < 1 at hj
  rw [← norm_centeredLift_apply, Real.norm_eq_abs] at hj
  constructor <;> linarith [hj.1, hj.2]

/-- The full ordinary derivative, almost everywhere in the torus Haar
measure. The omitted seams have measure zero by the proved distribution
identity, not by a differentiability assumption. -/
theorem ae_hasFDerivAt_squareReflection_lift :
    ∀ᵐ z ∂torusMeasure,
      HasFDerivAt (fun y ↦ squareReflection (torusQuotient y))
        ((2 : ℝ) • (squareCoordinateReflection (centeredLift z)).toLinearIsometry.toContinuousLinearMap) (centeredLift z) := by
  filter_upwards [ae_squareReflection_mem_openUnitSquare] with z hz
  exact hasFDerivAt_squareReflection_lift (centeredLift_away_squareFold_seams hz)

theorem norm_comp_squareLinearIsometry (L : PlanarSpace →L[ℝ] ℝ)
    (e : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace) :
    ‖L.comp e.toLinearIsometry.toContinuousLinearMap‖ = ‖L‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro x
    change ‖L (e x)‖ ≤ ‖L‖ * ‖x‖
    simpa only [e.norm_map] using L.le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (L.comp e.toLinearIsometry.toContinuousLinearMap))
    intro x
    have h := (L.comp e.toLinearIsometry.toContinuousLinearMap).le_opNorm (e.symm x)
    change ‖L (e (e.symm x))‖ ≤
      ‖L.comp e.toLinearIsometry.toContinuousLinearMap‖ * ‖e.symm x‖ at h
    simpa only [e.apply_symm_apply, e.symm.norm_map] using h

theorem norm_fderiv_reflected_at {u : PlanarSpace → ℝ} {x : PlanarSpace}
    (hx : ∀ j : Fin 2, 0 < |x j| ∧ |x j| < (1 / 2 : ℝ))
    (hu : DifferentiableAt ℝ u (squareReflection (torusQuotient x))) :
    ‖fderiv ℝ (fun y ↦ u (squareReflection (torusQuotient y))) x‖ =
      2 * ‖fderiv ℝ u (squareReflection (torusQuotient x))‖ := by
  have hd := (hu.hasFDerivAt.comp x (hasFDerivAt_squareReflection_lift hx)).fderiv
  dsimp only [Function.comp_def] at hd
  rw [hd]
  have heq : (fderiv ℝ u (squareReflection (torusQuotient x))).comp
      ((2 : ℝ) • (squareCoordinateReflection x).toLinearIsometry.toContinuousLinearMap) =
      (2 : ℝ) • ((fderiv ℝ u (squareReflection (torusQuotient x))).comp
        (squareCoordinateReflection x).toLinearIsometry.toContinuousLinearMap) := by
    ext v
    simp
  rw [heq, norm_smul, norm_comp_squareLinearIsometry]
  norm_num

theorem ae_differentiableAt_on_square {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    ∀ᵐ x ∂squareLebesgue, DifferentiableAt ℝ u x := by
  have hd := hu.ae_differentiableWithinAt (μ := volume) measurableSet_closedUnitSquare
  filter_upwards [hd, ae_mem_openUnitSquare] with x hx hi
  exact hx.differentiableAt (closedUnitSquare_mem_nhds hi)

theorem ae_norm_fderiv_on_square_le {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    ∀ᵐ x ∂squareLebesgue, ‖fderiv ℝ u x‖ ≤ (K : ℝ) := by
  filter_upwards [ae_mem_openUnitSquare] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ (closedUnitSquare_mem_nhds hx) hu

theorem integrable_sq_norm_fderiv_on_square {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) squareLebesgue := by
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
    ((measurable_fderiv ℝ u).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_norm_fderiv_on_square_le hu] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖fderiv ℝ u x‖)] using
    pow_le_pow_left₀ (norm_nonneg _) hx 2

theorem ae_norm_fderiv_reflected_square {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    ∀ᵐ z ∂torusMeasure,
      ‖fderiv ℝ (fun y ↦ u (squareReflection (torusQuotient y))) (centeredLift z)‖ =
        2 * ‖fderiv ℝ u (squareReflection z)‖ := by
  have hd := measurePreserving_squareReflection.quasiMeasurePreserving.ae
    (ae_differentiableAt_on_square hu)
  filter_upwards [hd, ae_squareReflection_mem_openUnitSquare] with z hd hz
  simpa only [torusQuotient_centeredLift] using
    norm_fderiv_reflected_at (centeredLift_away_squareFold_seams hz)
      (by simpa only [torusQuotient_centeredLift] using hd)

/-- A genuine Riesz gradient; the norm is exactly the ordinary derivative's
operator norm, without a dimension or coordinate normalization. -/
def rectangleOrdinaryGradient (u : PlanarSpace → ℝ) (x : PlanarSpace) : PlanarSpace :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm (fderiv ℝ u x)

theorem norm_rectangleOrdinaryGradient (u : PlanarSpace → ℝ) (x : PlanarSpace) :
    ‖rectangleOrdinaryGradient u x‖ = ‖fderiv ℝ u x‖ :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map _

def reflectedSquareGradient (u : PlanarSpace → ℝ) (z : Torus) : PlanarSpace :=
  rectangleOrdinaryGradient (fun y ↦ u (squareReflection (torusQuotient y))) (centeredLift z)

theorem integrable_sq_norm_reflectedSquareGradient {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    Integrable (fun z ↦ ‖reflectedSquareGradient u z‖ ^ 2) torusMeasure := by
  have hi := (measurePreserving_squareReflection.integrable_comp_of_integrable
    (integrable_sq_norm_fderiv_on_square hu)).const_mul 4
  apply hi.congr
  filter_upwards [ae_norm_fderiv_reflected_square hu] with z hz
  dsimp only [Function.comp_def, reflectedSquareGradient]
  rw [norm_rectangleOrdinaryGradient, hz]
  ring

/-- Exact reflection energy, for any real function Lipschitz on the closed
unit square. All integrals here are separately proved integrable. -/
theorem integral_sq_norm_reflectedSquareGradient {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    ∫ z, ‖reflectedSquareGradient u z‖ ^ 2 ∂torusMeasure =
      4 * ∫ x, ‖rectangleOrdinaryGradient u x‖ ^ 2 ∂squareLebesgue := by
  calc
    _ = ∫ z, 4 * ‖fderiv ℝ u (squareReflection z)‖ ^ 2 ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_norm_fderiv_reflected_square hu] with z hz
      dsimp only [reflectedSquareGradient]
      rw [norm_rectangleOrdinaryGradient, hz]
      ring
    _ = 4 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂squareLebesgue := by
      rw [integral_const_mul, integral_squareReflection (integrable_sq_norm_fderiv_on_square hu)]
    _ = _ := by simp only [norm_rectangleOrdinaryGradient]

/-- Source's exact factor two, expressed as actual square-integral norms. -/
theorem sqrt_integral_sq_norm_reflectedSquareGradient {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    Real.sqrt (∫ z, ‖reflectedSquareGradient u z‖ ^ 2 ∂torusMeasure) =
      2 * Real.sqrt (∫ x, ‖rectangleOrdinaryGradient u x‖ ^ 2 ∂squareLebesgue) := by
  rw [integral_sq_norm_reflectedSquareGradient hu, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt (4 : ℝ) = 2 by convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1; norm_num]

/-- The two side lengths of the source's second reference rectangle. -/
def doubleRectangleWidth (j : Fin 2) : ℝ := if j = 0 then 2 else 1

def closedDoubleRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j : Fin 2 ↦ Icc 0 (doubleRectangleWidth j))

def openDoubleRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j : Fin 2 ↦ Ioo 0 (doubleRectangleWidth j))

/-- Actual normalized Lebesgue measure, with density one half. -/
def rectangleLebesgue : Measure PlanarSpace :=
  ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict closedDoubleRectangle

theorem measurableSet_closedDoubleRectangle : MeasurableSet closedDoubleRectangle :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem measurableSet_openDoubleRectangle : MeasurableSet openDoubleRectangle :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem closedDoubleRectangle_mem_nhds {x : PlanarSpace} (hx : x ∈ openDoubleRectangle) :
    closedDoubleRectangle ∈ 𝓝 x :=
  (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.preimage_mem_nhds
    (set_pi_mem_nhds Set.finite_univ fun j _ ↦
      Icc_mem_nhds (hx j (mem_univ j)).1 (hx j (mem_univ j)).2)

/-- The source map `(z₁,z₂) ↦ (2z₁,z₂)`, on the genuine Euclidean plane. -/
def rectangleStretch : PlanarSpace →L[ℝ] PlanarSpace :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin 2 ↦ doubleRectangleWidth j • EuclideanSpace.proj j)

@[simp] theorem rectangleStretch_apply (x : PlanarSpace) (j : Fin 2) :
    rectangleStretch x j = doubleRectangleWidth j * x j := rfl

theorem rectangleStretch_mem_closedDoubleRectangle {x : PlanarSpace}
    (hx : x ∈ closedUnitSquare) : rectangleStretch x ∈ closedDoubleRectangle := by
  intro j _
  have hj := hx j (mem_univ j)
  change 0 ≤ doubleRectangleWidth j * x j ∧
    doubleRectangleWidth j * x j ≤ doubleRectangleWidth j
  by_cases h : j = 0
  · have hj0 := hj
    rw [h] at hj0
    simp only [doubleRectangleWidth, h, ite_true]
    constructor <;> linarith [hj0.1, hj0.2]
  · simpa only [doubleRectangleWidth, h, ite_false, one_mul, mem_Icc, mem_Ioo] using! hj

theorem rectangleStretch_mem_openDoubleRectangle {x : PlanarSpace}
    (hx : x ∈ openUnitSquare) : rectangleStretch x ∈ openDoubleRectangle := by
  intro j _
  have hj := hx j (mem_univ j)
  change 0 < doubleRectangleWidth j * x j ∧
    doubleRectangleWidth j * x j < doubleRectangleWidth j
  by_cases h : j = 0
  · have hj0 := hj
    rw [h] at hj0
    simp only [doubleRectangleWidth, h, ite_true]
    constructor <;> linarith [hj0.1, hj0.2]
  · simpa only [doubleRectangleWidth, h, ite_false, one_mul, mem_Icc, mem_Ioo] using! hj

theorem measurePreserving_intervalStretch :
    MeasurePreserving (fun x : ℝ ↦ 2 * x) (volume.restrict (Icc (0 : ℝ) 1))
      (ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict (Icc (0 : ℝ) 2)) := by
  have hm : MeasurePreserving (fun x : ℝ ↦ 2 * x) volume
      (ENNReal.ofReal (1 / 2 : ℝ) • volume) := by
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    simpa using Real.map_volume_mul_left (a := 2) (by norm_num)
  have hp : (fun x : ℝ ↦ 2 * x) ⁻¹' Icc 0 2 = Icc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith
  simpa only [hp, Measure.restrict_smul] using
    hm.restrict_preimage (s := Icc 0 2) measurableSet_Icc

def rectangleCoordinateMeasure (j : Fin 2) : Measure ℝ :=
  if j = 0 then ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict (Icc (0 : ℝ) 2)
  else volume.restrict (Icc (0 : ℝ) 1)

instance isFiniteMeasure_rectangleCoordinateMeasure (j : Fin 2) :
    IsFiniteMeasure (rectangleCoordinateMeasure j) := by
  constructor
  by_cases hj : j = 0 <;>
    norm_num [rectangleCoordinateMeasure, hj, Measure.smul_apply, Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num)

theorem rectangleCoordinateMeasure_pi :
    Measure.pi rectangleCoordinateMeasure = ENNReal.ofReal (1 / 2 : ℝ) •
      (volume : Measure (Fin 2 → ℝ)).restrict
        (Set.pi Set.univ (fun j : Fin 2 ↦ Icc 0 (doubleRectangleWidth j))) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, MeasureTheory.volume_pi_pi]
  simp only [Fin.prod_univ_two, rectangleCoordinateMeasure, doubleRectangleWidth,
    ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    Measure.smul_apply, Measure.restrict_apply (hs 0), Measure.restrict_apply (hs 1),
    smul_eq_mul, mul_assoc]

theorem measurePreserving_rectangleStretch :
    MeasurePreserving rectangleStretch squareLebesgue rectangleLebesgue := by
  have hcoord (j : Fin 2) :
      MeasurePreserving (fun x : ℝ ↦ doubleRectangleWidth j * x)
        (volume.restrict (Icc (0 : ℝ) 1)) (rectangleCoordinateMeasure j) := by
    by_cases hj : j = 0
    · simpa only [doubleRectangleWidth, rectangleCoordinateMeasure, hj, ite_true] using
        measurePreserving_intervalStretch
    · simpa only [doubleRectangleWidth, rectangleCoordinateMeasure, hj, ite_false, one_mul,
        id_eq] using! MeasurePreserving.id (volume.restrict (Icc (0 : ℝ) 1))
  have hp := measurePreserving_pi
    (fun _ : Fin 2 ↦ volume.restrict (Icc (0 : ℝ) 1)) rectangleCoordinateMeasure hcoord
  have hi := (PiLp.volume_preserving_ofLp (Fin 2)).restrict_preimage
    (s := Set.pi Set.univ (fun _ : Fin 2 ↦ Icc (0 : ℝ) 1))
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)
  rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ ↦ volume) from rfl,
    Measure.restrict_pi_pi] at hi
  have ho := ((PiLp.volume_preserving_toLp (Fin 2)).restrict_preimage
    (s := closedDoubleRectangle) measurableSet_closedDoubleRectangle).smul_measure (ENNReal.ofReal (1 / 2 : ℝ))
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → PlanarSpace) ⁻¹' closedDoubleRectangle =
      Set.pi Set.univ (fun j : Fin 2 ↦ Icc 0 (doubleRectangleWidth j)) := by
    ext x
    rfl
  rw [hpre, ← rectangleCoordinateMeasure_pi] at ho
  exact ho.comp (hp.comp hi)

theorem rectangleLebesgue_univ : rectangleLebesgue Set.univ = 1 := by
  rw [← measurePreserving_rectangleStretch.map_eq,
    Measure.map_apply rectangleStretch.continuous.measurable MeasurableSet.univ]
  simp

theorem volume_closedDoubleRectangle : volume closedDoubleRectangle = 2 := by
  have h := congrArg (fun t : ℝ≥0∞ ↦ 2 * t) rectangleLebesgue_univ
  norm_num [rectangleLebesgue, Measure.smul_apply, ← mul_assoc,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  rw [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul] at h
  exact h

instance isProbabilityMeasure_rectangleLebesgue : IsProbabilityMeasure rectangleLebesgue :=
  ⟨rectangleLebesgue_univ⟩

theorem integral_rectangleStretch {f : PlanarSpace → ℝ}
    (hf : Integrable f rectangleLebesgue) :
    ∫ x, f (rectangleStretch x) ∂squareLebesgue = ∫ y, f y ∂rectangleLebesgue := by
  have hm := measurePreserving_rectangleStretch
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    (by simpa only [hm.map_eq] using hf.aestronglyMeasurable)).symm

theorem ae_mem_openDoubleRectangle :
    ∀ᵐ x ∂rectangleLebesgue, x ∈ openDoubleRectangle := by
  rw [← measurePreserving_rectangleStretch.map_eq]
  apply (ae_map_iff measurePreserving_rectangleStretch.aemeasurable
    measurableSet_openDoubleRectangle).mpr
  exact ae_mem_openUnitSquare.mono fun _ hx ↦ rectangleStretch_mem_openDoubleRectangle hx

theorem norm_rectangleStretch_le (x : PlanarSpace) : ‖rectangleStretch x‖ ≤ 2 * ‖x‖ := by
  have hs : ‖rectangleStretch x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, rectangleStretch_apply,
      doubleRectangleWidth, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
      mul_pow]
    nlinarith [sq_nonneg (x 1)]
  nlinarith [norm_nonneg (rectangleStretch x), norm_nonneg x]

theorem norm_rectangleStretch_le_two : ‖rectangleStretch‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) norm_rectangleStretch_le

theorem lipschitzWith_rectangleStretch : LipschitzWith 2 rectangleStretch := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change ‖rectangleStretch x - rectangleStretch y‖ ≤ 2 * ‖x - y‖
  rw [← rectangleStretch.map_sub]
  exact norm_rectangleStretch_le (x - y)

theorem lipschitzOnWith_rectanglePullback {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    LipschitzOnWith (2 * K) (fun x ↦ u (rectangleStretch x)) closedUnitSquare := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  calc
    _ ≤ (K : ℝ) * dist (rectangleStretch x) (rectangleStretch y) :=
      hu.dist_le_mul _ (rectangleStretch_mem_closedDoubleRectangle hx) _
        (rectangleStretch_mem_closedDoubleRectangle hy)
    _ ≤ (K : ℝ) * (2 * dist x y) :=
      mul_le_mul_of_nonneg_left (lipschitzWith_rectangleStretch.dist_le_mul x y) K.coe_nonneg
    _ = _ := by push_cast; ring

theorem ae_differentiableAt_on_rectangle {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    ∀ᵐ x ∂rectangleLebesgue, DifferentiableAt ℝ u x := by
  have hd : ∀ᵐ x ∂rectangleLebesgue, DifferentiableWithinAt ℝ u closedDoubleRectangle x := by
    exact Measure.ae_smul_measure (hu.ae_differentiableWithinAt (μ := volume)
      measurableSet_closedDoubleRectangle) _
  filter_upwards [hd, ae_mem_openDoubleRectangle] with x hx hi
  exact hx.differentiableAt (closedDoubleRectangle_mem_nhds hi)

theorem ae_norm_fderiv_on_rectangle_le {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    ∀ᵐ x ∂rectangleLebesgue, ‖fderiv ℝ u x‖ ≤ (K : ℝ) := by
  filter_upwards [ae_mem_openDoubleRectangle] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ (closedDoubleRectangle_mem_nhds hx) hu

theorem integrable_sq_norm_fderiv_on_rectangle {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) rectangleLebesgue := by
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
    ((measurable_fderiv ℝ u).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_norm_fderiv_on_rectangle_le hu] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖fderiv ℝ u x‖)] using
    pow_le_pow_left₀ (norm_nonneg _) hx 2

theorem norm_fderiv_rectanglePullback_le {u : PlanarSpace → ℝ} {x : PlanarSpace}
    (hu : DifferentiableAt ℝ u (rectangleStretch x)) :
    ‖fderiv ℝ (fun y ↦ u (rectangleStretch y)) x‖ ≤
      2 * ‖fderiv ℝ u (rectangleStretch x)‖ := by
  have hd := (hu.hasFDerivAt.comp x rectangleStretch.hasFDerivAt).fderiv
  dsimp only [Function.comp_def] at hd
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg _))
  intro v
  calc
    _ ≤ ‖fderiv ℝ u (rectangleStretch x)‖ * ‖rectangleStretch v‖ :=
      (fderiv ℝ u (rectangleStretch x)).le_opNorm _
    _ ≤ ‖fderiv ℝ u (rectangleStretch x)‖ * (2 * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_rectangleStretch_le v) (norm_nonneg _)
    _ = _ := by ring

/-- The normalized rectangle-to-square energy bound from source Lemma 3.1.
Neither differentiability nor a change-of-variables identity is assumed. -/
theorem integral_sq_norm_rectanglePullback_le {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    ∫ x, ‖rectangleOrdinaryGradient (fun y ↦ u (rectangleStretch y)) x‖ ^ 2 ∂squareLebesgue ≤
      4 * ∫ y, ‖rectangleOrdinaryGradient u y‖ ^ 2 ∂rectangleLebesgue := by
  simp only [norm_rectangleOrdinaryGradient]
  have hi := integrable_sq_norm_fderiv_on_rectangle hu
  have hd := measurePreserving_rectangleStretch.quasiMeasurePreserving.ae
    (ae_differentiableAt_on_rectangle hu)
  calc
    _ ≤ ∫ x, 4 * ‖fderiv ℝ u (rectangleStretch x)‖ ^ 2 ∂squareLebesgue := by
      apply integral_mono_ae
        (integrable_sq_norm_fderiv_on_square (lipschitzOnWith_rectanglePullback hu))
        ((measurePreserving_rectangleStretch.integrable_comp_of_integrable hi).const_mul 4)
      filter_upwards [hd] with x hx
      have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_rectanglePullback_le hx) 2
      change _ ≤ 4 * ‖fderiv ℝ u (rectangleStretch x)‖ ^ 2
      nlinarith
    _ = _ := by rw [integral_const_mul, integral_rectangleStretch hi]

theorem sqrt_integral_sq_norm_rectanglePullback_le {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    Real.sqrt (∫ x, ‖rectangleOrdinaryGradient (fun y ↦ u (rectangleStretch y)) x‖ ^ 2
      ∂squareLebesgue) ≤
      2 * Real.sqrt (∫ y, ‖rectangleOrdinaryGradient u y‖ ^ 2 ∂rectangleLebesgue) := by
  have h := Real.sqrt_le_sqrt (integral_sq_norm_rectanglePullback_le hu)
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt (4 : ℝ) = 2 by convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1; norm_num] using h

/-- The source uses half-open rectangles for disjoint cells. In the physical
Euclidean measure, replacing these by their closures leaves the measure
unchanged. This lemma also records the exact boundary-nullity bridge. -/
theorem volume_restrict_halfOpenRectangle_eq_closed (b : Fin 2 → ℝ) :
    (volume : Measure PlanarSpace).restrict
        (WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j ↦ Ico (0 : ℝ) (b j))) =
      volume.restrict (WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j ↦ Icc (0 : ℝ) (b j))) := by
  apply Measure.restrict_congr_set
  exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae
    (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : Fin 2 ↦ (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ ↦ 0) (g := b))

theorem volume_restrict_openRectangle_eq_closed (b : Fin 2 → ℝ) :
    (volume : Measure PlanarSpace).restrict
        (WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j ↦ Ioo (0 : ℝ) (b j))) =
      volume.restrict (WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j ↦ Icc (0 : ℝ) (b j))) := by
  apply Measure.restrict_congr_set
  exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae
    (Measure.pi_Ioo_ae_eq_pi_Icc (μ := fun _ : Fin 2 ↦ (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ ↦ 0) (g := b))

end PeriodicAttractiveLogGas
