import LeanResearch.PeriodicAttractiveLogGas.RectangleReflection
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.ZMod.Basic

/-!
# The exact half-open square mesh of the unit torus

Source lines 331--386: `A_a = J⁻¹(a + [0,1)²)` and the normalized
conditional cell measure `J² * 1_{A_a} m`. Labels are obtained from the actual
`[0,1)` circle representative, so they are defined and unique at every seam.
The statements hold for every positive natural `J`, in particular for the
source range `J ≥ 3`. The physical planar norm and ordinary Euclidean volume
are unchanged.

This unit proves the partition, its exact Haar masses, and the actual affine
square-chart pushforward. It does not assert the adjacent-union chart, nearby
cell count, conditional Gibbs laws, or any functional inequality.

Development proof bodies use only the pinned library and earlier geometry.
Independent review and protected acceptance have separate records.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas
namespace MeshCells

abbrev MeshIndex (J : ℕ) := Fin 2 → Fin J

/-- Exact equivalence with the source's pair of residue-class indices. -/
def meshIndexEquivZMod (J : ℕ) [NeZero J] : MeshIndex J ≃ (Fin 2 → ZMod J) :=
  Equiv.piCongrRight fun _ ↦ (ZMod.finEquiv J).toEquiv

theorem card_meshIndex (J : ℕ) : Fintype.card (MeshIndex J) = J ^ 2 := by
  simp [MeshIndex]

/-- The left-closed, right-open fundamental square in physical Euclidean space. -/
def halfOpenMeshSquare : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin 2 ↦ Ico (0 : ℝ) 1)

theorem measurableSet_halfOpenMeshSquare : MeasurableSet halfOpenMeshSquare :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

/-- The half-open and closed reference squares have exactly the same measure. -/
theorem restrict_halfOpenMeshSquare_eq_squareLebesgue :
    (volume : Measure PlanarSpace).restrict halfOpenMeshSquare = squareLebesgue := by
  apply Measure.restrict_congr_set
  have h : (Set.pi Set.univ (fun _ : Fin 2 ↦ Ico (0 : ℝ) 1)) =ᵐ[volume]
      Set.pi Set.univ (fun _ : Fin 2 ↦ Icc (0 : ℝ) 1) :=
    Measure.pi_Ico_ae_eq_pi_Icc
  exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.preimage_ae_eq h

theorem measurePreserving_torusQuotient_halfOpenMeshSquare :
    MeasurePreserving torusQuotient (volume.restrict halfOpenMeshSquare) torusMeasure := by
  have hcoord (j : Fin 2) : MeasurePreserving (fun t : ℝ ↦ (t : UnitAddCircle))
      (volume.restrict (Ico (0 : ℝ) 1)) AddCircle.haarAddCircle := by
    rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
    simpa only [zero_add, unitCircle_volume_eq_haar] using
      (UnitAddCircle.measurePreserving_mk (0 : ℝ))
  have hpi := measurePreserving_pi
    (fun _ : Fin 2 ↦ volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 2 ↦ AddCircle.haarAddCircle) hcoord
  have he := (PiLp.volume_preserving_ofLp (Fin 2)).restrict_preimage
    (s := Set.pi Set.univ (fun _ : Fin 2 ↦ Ico (0 : ℝ) 1))
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico)
  rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ ↦ volume) from rfl,
    Measure.restrict_pi_pi] at he
  exact hpi.comp he

/-- Canonical representative with exactly the source's endpoint convention. -/
def unitRepresentative (t : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 t : ℝ)

theorem unitRepresentative_mem (t : UnitAddCircle) : unitRepresentative t ∈ Ico (0 : ℝ) 1 := by
  simpa only [unitRepresentative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 t).property

theorem measurable_unitRepresentative : Measurable unitRepresentative :=
  measurable_subtype_coe.comp ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)

@[simp] theorem quotient_unitRepresentative (t : UnitAddCircle) :
    (unitRepresentative t : UnitAddCircle) = t := AddCircle.coe_equivIco

theorem unitRepresentative_quotient_of_mem {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    unitRepresentative (t : UnitAddCircle) = t := by
  exact AddCircle.equivIco_coe_of_mem (by simpa only [zero_add] using ht)

def halfOpenLift (z : Torus) : PlanarSpace :=
  WithLp.toLp 2 (fun j ↦ unitRepresentative (z j))

@[simp] theorem halfOpenLift_apply (z : Torus) (j : Fin 2) :
    halfOpenLift z j = unitRepresentative (z j) := rfl

theorem measurable_halfOpenLift : Measurable halfOpenLift := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable.comp
  exact measurable_pi_iff.mpr fun j ↦ measurable_unitRepresentative.comp (measurable_pi_apply j)

theorem halfOpenLift_mem (z : Torus) : halfOpenLift z ∈ halfOpenMeshSquare :=
  fun j _ ↦ unitRepresentative_mem (z j)

@[simp] theorem torusQuotient_halfOpenLift (z : Torus) :
    torusQuotient (halfOpenLift z) = z := by
  ext j
  exact quotient_unitRepresentative (z j)

theorem halfOpenLift_torusQuotient {x : PlanarSpace} (hx : x ∈ halfOpenMeshSquare) :
    halfOpenLift (torusQuotient x) = x := by
  ext j
  exact unitRepresentative_quotient_of_mem (hx j (mem_univ j))

theorem injOn_torusQuotient_halfOpenMeshSquare :
    Set.InjOn torusQuotient halfOpenMeshSquare := by
  intro x hx y hy hxy
  have h := congrArg halfOpenLift hxy
  simpa only [halfOpenLift_torusQuotient hx, halfOpenLift_torusQuotient hy] using h

/-- The floor label is less than `J` because the representative is strictly below one. -/
def coordinateLabel (J : ℕ) (hJ : 0 < J) (t : UnitAddCircle) : Fin J :=
  ⟨⌊(J : ℝ) * unitRepresentative t⌋₊, by
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
    apply (Nat.floor_lt (mul_nonneg hJr.le (unitRepresentative_mem t).1)).mpr
    simpa only [mul_one] using mul_lt_mul_of_pos_left (unitRepresentative_mem t).2 hJr⟩

theorem coordinateLabel_eq_iff (J : ℕ) (hJ : 0 < J) (t : UnitAddCircle) (a : Fin J) :
    coordinateLabel J hJ t = a ↔
      unitRepresentative t ∈ Ico ((a : ℝ) / J) (((a : ℝ) + 1) / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [Fin.ext_iff]
  change ⌊(J : ℝ) * unitRepresentative t⌋₊ = a.val ↔ _
  rw [Nat.floor_eq_iff (mul_nonneg hJr.le (unitRepresentative_mem t).1)]
  simp only [mem_Ico, div_le_iff₀ hJr, lt_div_iff₀ hJr]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

theorem measurable_coordinateLabel (J : ℕ) (hJ : 0 < J) :
    Measurable (coordinateLabel J hJ) := by
  apply measurable_to_countable'
  intro a
  have h : coordinateLabel J hJ ⁻¹' {a} =
      unitRepresentative ⁻¹' Ico ((a : ℝ) / J) (((a : ℝ) + 1) / J) := by
    ext t
    exact coordinateLabel_eq_iff J hJ t a
  rw [h]
  exact measurableSet_Ico.preimage measurable_unitRepresentative

def meshLabel (J : ℕ) (hJ : 0 < J) (z : Torus) : MeshIndex J :=
  fun j ↦ coordinateLabel J hJ (z j)

theorem measurable_meshLabel (J : ℕ) (hJ : 0 < J) : Measurable (meshLabel J hJ) :=
  measurable_pi_iff.mpr fun j ↦
    (measurable_coordinateLabel J hJ).comp (measurable_pi_apply j)

def meshCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Set Torus :=
  meshLabel J hJ ⁻¹' {a}

theorem measurableSet_meshCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurableSet (meshCell J hJ a) :=
  (measurableSet_singleton a).preimage (measurable_meshLabel J hJ)

@[simp] theorem mem_meshCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (z : Torus) :
    z ∈ meshCell J hJ a ↔ meshLabel J hJ z = a := Iff.rfl

theorem mem_meshCell_iff_coordinates (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (z : Torus) :
    z ∈ meshCell J hJ a ↔ ∀ j : Fin 2,
      unitRepresentative (z j) ∈ Ico ((a j : ℝ) / J) (((a j : ℝ) + 1) / J) := by
  rw [mem_meshCell, funext_iff]
  exact forall_congr' fun j ↦ coordinateLabel_eq_iff J hJ (z j) (a j)

theorem existsUnique_meshCell (J : ℕ) (hJ : 0 < J) (z : Torus) :
    ∃! a : MeshIndex J, z ∈ meshCell J hJ a := by
  refine ⟨meshLabel J hJ z, rfl, ?_⟩
  intro a ha
  exact ha.symm

theorem pairwiseDisjoint_meshCell (J : ℕ) (hJ : 0 < J) :
    Pairwise (fun a b : MeshIndex J ↦ Disjoint (meshCell J hJ a) (meshCell J hJ b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro z hza hzb
  exact hab (hza.symm.trans hzb)

theorem iUnion_meshCell (J : ℕ) (hJ : 0 < J) :
    (⋃ a : MeshIndex J, meshCell J hJ a) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact mem_iUnion.mpr ⟨meshLabel J hJ z, rfl⟩

/-- The genuine Euclidean small half-open rectangle defining one cell. -/
def meshBox (J : ℕ) (a : MeshIndex J) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ
    (fun j : Fin 2 ↦ Ico ((a j : ℝ) / J) (((a j : ℝ) + 1) / J))

theorem measurableSet_meshBox (J : ℕ) (a : MeshIndex J) : MeasurableSet (meshBox J a) :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem meshBox_subset_halfOpenMeshSquare (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    meshBox J a ⊆ halfOpenMeshSquare := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  intro x hx j hj
  have ha0 : (0 : ℝ) ≤ a j := Nat.cast_nonneg _
  have haj : (a j : ℝ) + 1 ≤ J := by exact_mod_cast Nat.succ_le_of_lt (a j).isLt
  have hu : ((a j : ℝ) + 1) / J ≤ 1 := (div_le_iff₀ hJr).mpr (by simpa using haj)
  exact ⟨(div_nonneg ha0 hJr.le).trans (hx j hj).1, (hx j hj).2.trans_le hu⟩

theorem quotient_mem_meshCell_iff (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {x : PlanarSpace} (hx : x ∈ halfOpenMeshSquare) :
    torusQuotient x ∈ meshCell J hJ a ↔ x ∈ meshBox J a := by
  rw [mem_meshCell_iff_coordinates]
  constructor
  · intro h j hj
    have he : unitRepresentative (torusQuotient x j) = x j :=
      unitRepresentative_quotient_of_mem (hx j (mem_univ j))
    simpa only [he] using h j
  · intro h j
    have he : unitRepresentative (torusQuotient x j) = x j :=
      unitRepresentative_quotient_of_mem (hx j (mem_univ j))
    simpa only [he] using h j (mem_univ j)

theorem quotient_preimage_meshCell_inter_square (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    (torusQuotient ⁻¹' meshCell J hJ a) ∩ halfOpenMeshSquare = meshBox J a := by
  ext x
  constructor
  · rintro ⟨hc, hx⟩
    exact (quotient_mem_meshCell_iff J hJ a hx).mp hc
  · intro hx
    have hs := meshBox_subset_halfOpenMeshSquare J hJ a hx
    exact ⟨(quotient_mem_meshCell_iff J hJ a hs).mpr hx, hs⟩

theorem halfOpenLift_mem_meshBox_iff (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (z : Torus) :
    halfOpenLift z ∈ meshBox J a ↔ z ∈ meshCell J hJ a := by
  simpa only [torusQuotient_halfOpenLift] using
    (quotient_mem_meshCell_iff J hJ a (halfOpenLift_mem z)).symm

theorem quotient_image_meshBox (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    torusQuotient '' meshBox J a = meshCell J hJ a := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (quotient_mem_meshCell_iff J hJ a
      (meshBox_subset_halfOpenMeshSquare J hJ a hx)).mpr hx
  · intro hz
    exact ⟨halfOpenLift z, (halfOpenLift_mem_meshBox_iff J hJ a z).mpr hz,
      torusQuotient_halfOpenLift z⟩

theorem measurePreserving_quotient_meshBox (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurePreserving torusQuotient (volume.restrict (meshBox J a))
      (torusMeasure.restrict (meshCell J hJ a)) := by
  have h := measurePreserving_torusQuotient_halfOpenMeshSquare.restrict_preimage
    (measurableSet_meshCell J hJ a)
  rw [Measure.restrict_restrict
    ((measurableSet_meshCell J hJ a).preimage
      measurePreserving_torusQuotient_halfOpenMeshSquare.measurable),
    quotient_preimage_meshCell_inter_square J hJ a] at h
  exact h

theorem volume_meshBox (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    volume (meshBox J a) = ((J : ℝ≥0∞) ^ 2)⁻¹ := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have h := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun j : Fin 2 ↦
      (measurableSet_Ico : MeasurableSet
        (Ico ((a j : ℝ) / J) (((a j : ℝ) + 1) / J)))).nullMeasurableSet
  change volume (meshBox J a) = volume
    (Set.pi Set.univ (fun j : Fin 2 ↦ Ico ((a j : ℝ) / J) (((a j : ℝ) + 1) / J))) at h
  rw [h, Real.volume_pi_Ico]
  have hwidth (j : Fin 2) : ((a j : ℝ) + 1) / J - (a j : ℝ) / J = (J : ℝ)⁻¹ := by
    ring
  simp_rw [hwidth, ENNReal.ofReal_inv_of_pos hJr]
  rw [ENNReal.inv_pow]
  simp [pow_two]

/-- Each half-open cell has exactly Haar mass `J⁻²`. -/
theorem torusMeasure_meshCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    torusMeasure (meshCell J hJ a) = ((J : ℝ≥0∞) ^ 2)⁻¹ := by
  have h := (measurePreserving_quotient_meshBox J hJ a).measure_preimage nullMeasurableSet_univ
  have heq : volume (meshBox J a) = torusMeasure (meshCell J hJ a) := by simpa using h
  rw [← heq, volume_meshBox J hJ a]

/-- Literal source normalization: `J²` times restricted probability Haar. -/
def meshCellMeasure (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Measure Torus :=
  (J : ℝ≥0∞) ^ 2 • torusMeasure.restrict (meshCell J hJ a)

theorem meshCellMeasure_apply (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {s : Set Torus} (hs : MeasurableSet s) :
    meshCellMeasure J hJ a s = (J : ℝ≥0∞) ^ 2 * torusMeasure (s ∩ meshCell J hJ a) := by
  rw [meshCellMeasure, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]

theorem meshCellMeasure_absolutelyContinuous (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    meshCellMeasure J hJ a ≪ torusMeasure :=
  Measure.absolutelyContinuous_restrict.smul_left ((J : ℝ≥0∞) ^ 2)

theorem meshCellMeasure_univ (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    meshCellMeasure J hJ a Set.univ = 1 := by
  have hJ0 : (J : ℝ≥0∞) ≠ 0 := by exact_mod_cast hJ.ne'
  simp only [meshCellMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    torusMeasure_meshCell J hJ a]
  exact ENNReal.mul_inv_cancel (pow_ne_zero _ hJ0) (by finiteness)

instance isProbabilityMeasure_meshCellMeasure (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    IsProbabilityMeasure (meshCellMeasure J hJ a) := ⟨meshCellMeasure_univ J hJ a⟩

theorem ae_mem_meshCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    ∀ᵐ z ∂meshCellMeasure J hJ a, z ∈ meshCell J hJ a :=
  Measure.ae_smul_measure (ae_restrict_mem (measurableSet_meshCell J hJ a)) _

/-- Integer index representatives in the ordinary Euclidean plane. -/
def meshIndexVector {J : ℕ} (a : MeshIndex J) : PlanarSpace :=
  WithLp.toLp 2 (fun j ↦ (a j : ℝ))

@[simp] theorem meshIndexVector_apply {J : ℕ} (a : MeshIndex J) (j : Fin 2) :
    meshIndexVector a j = (a j : ℝ) := rfl

/-- The literal source chart before passage to the torus. -/
def meshAffine (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) : PlanarSpace :=
  (J : ℝ)⁻¹ • (meshIndexVector a + Z)

@[simp] theorem meshAffine_apply (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) (j : Fin 2) :
    meshAffine J a Z j = ((a j : ℝ) + Z j) / J := by
  simp [meshAffine, div_eq_mul_inv, mul_comm, mul_add]

theorem continuous_meshAffine (J : ℕ) (a : MeshIndex J) : Continuous (meshAffine J a) :=
  (continuous_const.add continuous_id).const_smul (J : ℝ)⁻¹

def meshAffineInv (J : ℕ) (a : MeshIndex J) (x : PlanarSpace) : PlanarSpace :=
  (J : ℝ) • x - meshIndexVector a

@[simp] theorem meshAffineInv_apply (J : ℕ) (a : MeshIndex J) (x : PlanarSpace) (j : Fin 2) :
    meshAffineInv J a x j = (J : ℝ) * x j - (a j : ℝ) := by
  simp [meshAffineInv]

theorem meshAffine_left_inverse (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    Function.LeftInverse (meshAffineInv J a) (meshAffine J a) := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  intro Z
  ext j
  simp only [meshAffineInv_apply, meshAffine_apply]
  field_simp [hJr]; ring

theorem meshAffine_right_inverse (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    Function.RightInverse (meshAffineInv J a) (meshAffine J a) := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  intro x
  ext j
  simp only [meshAffineInv_apply, meshAffine_apply]
  field_simp [hJr]; ring

theorem meshAffine_preimage_meshBox (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    meshAffine J a ⁻¹' meshBox J a = halfOpenMeshSquare := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  ext Z
  change (∀ j ∈ (Set.univ : Set (Fin 2)),
    meshAffine J a Z j ∈ Ico ((a j : ℝ) / J) (((a j : ℝ) + 1) / J)) ↔
      ∀ j ∈ (Set.univ : Set (Fin 2)), Z j ∈ Ico (0 : ℝ) 1
  simp only [meshAffine_apply, mem_Ico, div_le_div_iff_of_pos_right hJr,
    div_lt_div_iff_of_pos_right hJr, le_add_iff_nonneg_right, add_lt_add_iff_left]

theorem meshAffine_image_square (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    meshAffine J a '' halfOpenMeshSquare = meshBox J a := by
  rw [← meshAffine_preimage_meshBox J hJ a]
  exact Set.image_preimage_eq _ (meshAffine_right_inverse J hJ a).surjective

/-- Actual inverse-dimensional Haar scaling, including translation. -/
theorem measurePreserving_meshAffine_volume (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurePreserving (meshAffine J a) (volume : Measure PlanarSpace)
      ((J : ℝ≥0∞) ^ 2 • volume) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : MeasurePreserving (fun Z : PlanarSpace ↦ (J : ℝ)⁻¹ • Z) volume
      ((J : ℝ≥0∞) ^ 2 • volume) := by
    refine ⟨measurable_const_smul _, ?_⟩
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hJr.ne'),
      finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hJr _),
      ENNReal.ofReal_pow hJr.le, ENNReal.ofReal_natCast]
  exact hs.comp (measurePreserving_add_left (volume : Measure PlanarSpace) (meshIndexVector a))

/-- Exact chart transport from the source half-open square. -/
theorem measurePreserving_meshAffine_square (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurePreserving (meshAffine J a) (volume.restrict halfOpenMeshSquare)
      ((J : ℝ≥0∞) ^ 2 • volume.restrict (meshBox J a)) := by
  have h := (measurePreserving_meshAffine_volume J hJ a).restrict_preimage
    (measurableSet_meshBox J a)
  rwa [meshAffine_preimage_meshBox J hJ a, Measure.restrict_smul] at h

def meshChart (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) : Torus :=
  torusQuotient (meshAffine J a Z)

@[simp] theorem meshChart_apply (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) (j : Fin 2) :
    meshChart J a Z j = ((((a j : ℝ) + Z j) / J : ℝ) : UnitAddCircle) := by
  change ((meshAffine J a Z j : ℝ) : UnitAddCircle) = _
  rw [meshAffine_apply]

theorem measurable_meshChart (J : ℕ) (a : MeshIndex J) : Measurable (meshChart J a) :=
  measurePreserving_torusQuotient_halfOpenMeshSquare.measurable.comp
    (continuous_meshAffine J a).measurable

theorem meshChart_image_square (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    meshChart J a '' halfOpenMeshSquare = meshCell J hJ a := by
  change (torusQuotient ∘ meshAffine J a) '' halfOpenMeshSquare = _
  rw [Set.image_comp, meshAffine_image_square J hJ a, quotient_image_meshBox J hJ a]

theorem injOn_meshChart_square (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    Set.InjOn (meshChart J a) halfOpenMeshSquare := by
  intro Z hZ W hW hZW
  apply (meshAffine_left_inverse J hJ a).injective
  apply injOn_torusQuotient_halfOpenMeshSquare
  · apply meshBox_subset_halfOpenMeshSquare J hJ a
    have h : Z ∈ meshAffine J a ⁻¹' meshBox J a := by
      simpa only [meshAffine_preimage_meshBox J hJ a] using hZ
    exact h
  · apply meshBox_subset_halfOpenMeshSquare J hJ a
    have h : W ∈ meshAffine J a ⁻¹' meshBox J a := by
      simpa only [meshAffine_preimage_meshBox J hJ a] using hW
    exact h
  · exact hZW

/-- The normalized conditional cell measure is the pushforward of the actual
square probability measure. Endpoint differences are removed only at the level
of measures; the pointwise bijection above retains the half-open convention. -/
theorem measurePreserving_meshChart (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurePreserving (meshChart J a) squareLebesgue (meshCellMeasure J hJ a) := by
  have hq := (measurePreserving_quotient_meshBox J hJ a).smul_measure ((J : ℝ≥0∞) ^ 2)
  have h := hq.comp (measurePreserving_meshAffine_square J hJ a)
  rw [restrict_halfOpenMeshSquare_eq_squareLebesgue] at h
  exact h

/-- Pullback integrability follows from the proved pushforward identity. -/
theorem integrable_meshChart_comp {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {f : Torus → ℝ} (hf : Integrable f (meshCellMeasure J hJ a)) :
    Integrable (fun Z ↦ f (meshChart J a Z)) squareLebesgue :=
  (measurePreserving_meshChart J hJ a).integrable_comp_of_integrable hf

theorem integral_meshChart {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {f : Torus → ℝ} (hf : Integrable f (meshCellMeasure J hJ a)) :
    (∫ Z, f (meshChart J a Z) ∂squareLebesgue) = ∫ z, f z ∂meshCellMeasure J hJ a := by
  have h := measurePreserving_meshChart J hJ a
  rw [← h.map_eq]
  exact (integral_map h.aemeasurable
    (by simpa only [h.map_eq] using hf.aestronglyMeasurable)).symm

/-- The label of a chart point is exact, including the left/bottom boundary. -/
theorem meshLabel_meshChart (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {Z : PlanarSpace} (hZ : Z ∈ halfOpenMeshSquare) :
    meshLabel J hJ (meshChart J a Z) = a := by
  apply (mem_meshCell J hJ a _).mp
  rw [← meshChart_image_square J hJ a]
  exact ⟨Z, hZ, rfl⟩

/-- Coordinatewise labels of a full configuration are measurable. No
conditional Gibbs-law or occupation-probability identity is asserted here. -/
def configurationMeshLabel (N J : ℕ) (hJ : 0 < J) (X : Configuration N) : Fin N → MeshIndex J :=
  fun i ↦ meshLabel J hJ (X i)

theorem measurable_configurationMeshLabel (N J : ℕ) (hJ : 0 < J) :
    Measurable (configurationMeshLabel N J hJ) :=
  measurable_pi_iff.mpr fun i ↦ (measurable_meshLabel J hJ).comp (measurable_pi_apply i)

end MeshCells
end PeriodicAttractiveLogGas
