import LeanResearch.PeriodicAttractiveLogGas.ReferencePotentialBounds
import LeanResearch.PeriodicAttractiveLogGas.ReferenceConditionalNormalization
import LeanResearch.PeriodicAttractiveLogGas.SharpPoleMoments
import LeanResearch.PeriodicAttractiveLogGas.OneCoordinateConditionals
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-! The sequential product-reference estimate in source Lemma
`crude-residual-integrated`, lines 3216--3278. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.CrudeResidualIntegrated

open MeshCells MeshNearbyGeometry NearCellLifts ReferenceResidual
  ConditionalLawEstimates PositiveLogPoleMoments ReferencePotentialBounds

/-- Literal source radius; the proved cell geometry is slightly sharper. -/
def nearRadius (R : ℕ) : ℝ := Real.sqrt 2 * ((R : ℝ) + 2)

def nearConstant (R : ℕ) : ℝ :=
  2 * Real.log (nearRadius R) + 4 * kernelConstant + Real.exp 2 * Real.pi / 2

def integratedConstant (R : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  Real.log (5 * Real.exp 1) + 3 * β₀ * (2 * (R : ℝ) + 1)^2 * t * nearConstant R +
    144 * β₀ * t * C₂

theorem referenceRadius_le (R : ℕ) : cellReferenceRadius R ≤ nearRadius R := by
  unfold cellReferenceRadius nearRadius
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem nearRadius_one_le (R : ℕ) : 1 ≤ nearRadius R :=
  (one_le_cellReferenceRadius R).trans (referenceRadius_le R)

theorem nearConstant_nonneg (R : ℕ) : 0 ≤ nearConstant R := by
  unfold nearConstant
  have := Real.log_nonneg (nearRadius_one_le R)
  have := kernelConstant_pos.le
  positivity

/-- Both one-sided bounds on the actual Green kernel, off only the single
planar pole. The unbounded upper logarithm is not replaced by an absolute bound. -/
theorem near_chart_bounds {J R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
    (a b : MeshIndex J) (hab : periodicIndexDistance a b ≤ R) {x : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) :
    ∃ Y : PlanarSpace, meshChart J b Y = x ∧ ∀ᵐ Z ∂squareLebesgue,
      Real.log (J : ℝ) - Real.log (nearRadius R) - kernelConstant ≤
        greenKernel x (meshChart J b Z) ∧
      greenKernel x (meshChart J b Z) ≤
        Real.log (J : ℝ) - Real.log ‖Z - Y‖ + kernelConstant := by
  have hba : periodicIndexDistance b a ≤ R := by
    rw [periodicIndexDistance_comm]; exact hab
  obtain ⟨Y, hY, hd⟩ := exists_reference_lift hJ hmesh b a hba hx
  refine ⟨Y, hY, ?_⟩
  have hne : ∀ᵐ Z ∂squareLebesgue, Z ≠ Y :=
    SingularRectangleMoments.squareLebesgue_le_volume.absolutelyContinuous.ae_le
      ((volume : Measure PlanarSpace).ae_ne Y)
  filter_upwards [PoleLogMoments.ae_mem_closed_square, hne] with Z hZ hZY
  have hh := GreenPointRescaling.abs_logRemainder_le
    (show (0 : ℝ) < J by exact_mod_cast hJ)
    (cellReferenceRadius_lt_half hmesh) kernel_log_bound hZY (hd Z hZ).2.1
  have hl := Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hZY))
    ((hd Z hZ).2.1.trans (referenceRadius_le R))
  rw [greenKernel_symm, ← hY]
  unfold greenKernel
  rw [meshChart_sub]
  unfold GreenPointRescaling.logRemainder at hh
  obtain ⟨hh₁, hh₂⟩ := abs_le.mp hh
  constructor <;> linarith

/-- The positive logarithmic excess has the exact planar first moment. -/
theorem near_excess_moment {J R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
    (a b : MeshIndex J) (hab : periodicIndexDistance a b ≤ R) {x : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) :
    Integrable (fun y => max 0 (greenKernel x y - Real.log (J : ℝ) - kernelConstant))
      (meshCellMeasure J hJ b) ∧
    (∫ y, max 0 (greenKernel x y - Real.log (J : ℝ) - kernelConstant)
      ∂meshCellMeasure J hJ b) ≤ Real.pi / 2 := by
  obtain ⟨Y, _, hY⟩ := near_chart_bounds hJ hmesh a b hab hx
  have hl := positiveLogPole_moment_le_of_measure_le
    SingularRectangleMoments.squareLebesgue_le_volume Y (p := 1) (by omega)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at hl
  let f : Torus → ℝ := fun y => max 0 (greenKernel x y - Real.log (J : ℝ) - kernelConstant)
  have hm : Measurable f := measurable_const.max
    (((regularGreenRepresentative_measurable.comp
      (measurable_const.sub measurable_id)).sub measurable_const).sub measurable_const)
  have hd : ∀ᵐ Z ∂squareLebesgue, f (meshChart J b Z) ≤ positiveLogPole Y Z := by
    filter_upwards [hY] with Z hZ
    exact max_le (positiveLogPole_nonneg Y Z) (by
      have := le_max_right (0 : ℝ) (-Real.log ‖Z - Y‖)
      change greenKernel x (meshChart J b Z) - Real.log (J : ℝ) - kernelConstant ≤
        max 0 (-Real.log ‖Z - Y‖)
      linarith [hZ.2])
  have hi : Integrable (fun Z => f (meshChart J b Z)) squareLebesgue :=
    hl.1.mono' (hm.comp (measurable_meshChart J b)).aestronglyMeasurable
      (hd.mono fun Z hZ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left (0 : ℝ) _)]; exact hZ)
  have hi' : Integrable f (meshCellMeasure J hJ b) :=
    ((measurePreserving_meshChart J hJ b).integrable_comp hm.aestronglyMeasurable).mp hi
  refine ⟨hi', ?_⟩
  change (∫ y, f y ∂meshCellMeasure J hJ b) ≤ _
  rw [← integral_meshChart hJ b hi']
  exact (integral_mono_ae hi hl.1 hd).trans hl.2.1

/-- Probability normalization keeps the constant logarithm outside the single
density comparison. These bounds hold at every pole of the other closed cell. -/
theorem near_potential_bounds {J R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
    (a b : MeshIndex J) (hab : periodicIndexDistance a b ≤ R)
    (ν : Measure Torus) [IsProbabilityMeasure ν]
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b)
    {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    Real.log (J : ℝ) - Real.log (nearRadius R) - kernelConstant ≤ potential ν x ∧
    potential ν x ≤ Real.log (J : ℝ) + kernelConstant + Real.exp 1 * Real.pi / 2 := by
  have hi := (global_potential_bound hJ b ν hν x).1
  obtain ⟨Y, _, hY⟩ := near_chart_bounds hJ hmesh a b hab hx
  have hm : MeasurableSet {y | Real.log (J : ℝ) - Real.log (nearRadius R) - kernelConstant ≤
      greenKernel x y} := measurableSet_le measurable_const
        (regularGreenRepresentative_measurable.comp (measurable_const.sub measurable_id))
  have hlo : ∀ᵐ y ∂meshCellMeasure J hJ b,
      Real.log (J : ℝ) - Real.log (nearRadius R) - kernelConstant ≤ greenKernel x y := by
    rw [← (measurePreserving_meshChart J hJ b).map_eq]
    exact (ae_map_iff (measurable_meshChart J b).aemeasurable hm).mpr (hY.mono fun _ h => h.1)
  have hloν := hν.absolutelyContinuous.ae_le (Measure.ae_smul_measure hlo _)
  constructor
  · have hh := integral_mono_ae (integrable_const _) hi hloν
    simpa only [potential, integral_const, probReal_univ, one_smul] using hh
  · let f : Torus → ℝ := fun y => max 0 (greenKernel x y - Real.log (J : ℝ) - kernelConstant)
    have he := near_excess_moment hJ hmesh a b hab hx
    have hs := he.1.smul_measure (c := ENNReal.ofReal (Real.exp 1)) ENNReal.ofReal_ne_top
    have hif : Integrable f ν := hs.mono_measure hν
    have hbound : (∫ y, f y ∂ν) ≤ Real.exp 1 * Real.pi / 2 := by
      calc
        _ ≤ ∫ y, f y ∂(ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) :=
          integral_mono_measure hν (Eventually.of_forall fun y => le_max_left _ _) hs
        _ = Real.exp 1 * ∫ y, f y ∂meshCellMeasure J hJ b := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos 1).le, smul_eq_mul]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he.2 (Real.exp_pos 1).le]
    have hpoint : ∀ y, greenKernel x y ≤ Real.log (J : ℝ) + kernelConstant + f y := by
      intro y
      have hh := le_max_right (0 : ℝ) (greenKernel x y - Real.log (J : ℝ) - kernelConstant)
      dsimp [f]; linarith
    have hh := integral_mono hi ((integrable_const _).add hif) hpoint
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const _) hif] at hh
    simp only [integral_const, probReal_univ, one_smul] at hh
    unfold potential
    linarith


/-- The double average is controlled by integration of the actual one-body
bound; the source exp(2) constant is retained. -/
theorem near_pairAverage_upper {J R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
    (a b : MeshIndex J) (hab : periodicIndexDistance a b ≤ R)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) :
    pairAverage μ ν ≤ Real.log (J : ℝ) + kernelConstant + Real.exp 2 * Real.pi / 2 := by
  have hi := (global_pairAverage_bound hJ b μ ν hν).1
  have hb : ∀ᵐ x ∂μ, potential ν x ≤
      Real.log (J : ℝ) + kernelConstant + Real.exp 1 * Real.pi / 2 := by
    filter_upwards [ae_mem_closed_cell_of_domination hJ a μ hμ] with x hx
    exact (near_potential_bounds hJ hmesh a b hab ν hν hx).2
  have hh := integral_mono_ae hi (integrable_const _) hb
  simp only [integral_const, probReal_univ, one_smul] at hh
  have he : Real.exp 1 ≤ Real.exp (2 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
  unfold pairAverage
  nlinarith [Real.pi_pos]

/-- Literal near residual bound with the four log(J) terms canceled. It is
AE in the integrated cell coordinate, uniformly for every fixed closed-cell pole. -/
theorem near_residual_chart_upper {J R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
    (a b : MeshIndex J) (hab : periodicIndexDistance a b ≤ R)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b)
    {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    ∃ Y : PlanarSpace, ∀ᵐ Z ∂squareLebesgue,
      residual μ ν x (meshChart J b Z) ≤ -Real.log ‖Z - Y‖ + nearConstant R := by
  obtain ⟨Y, _, hY⟩ := near_chart_bounds hJ hmesh a b hab hx
  have hpx := (near_potential_bounds hJ hmesh a b hab ν hν hx).1
  have hpair := near_pairAverage_upper hJ hmesh a b hab μ ν hμ hν
  have hba : periodicIndexDistance b a ≤ R := by rw [periodicIndexDistance_comm]; exact hab
  refine ⟨Y, ?_⟩
  filter_upwards [hY, PoleLogMoments.ae_mem_closed_square] with Z hZ hZmem
  have hzy : meshChart J b Z ∈ closure (meshCell J hJ b) := by
    rw [MeshAdjacentCells.closure_meshCell]; exact ⟨Z, hZmem, rfl⟩
  have hpy := (near_potential_bounds hJ hmesh b a hba μ hμ hzy).1
  rw [residual_eq_source_order]
  unfold nearConstant
  linarith [hZ.2]

/-- Source generalized Holder step, including an empty index type and zero
weights. This uses the actual probability square law and true integrability. -/
theorem poleProduct_integral_le_five {ι : Type*} [Fintype ι]
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : (∑ i, w i) ≤ 3 / 16) :
    Integrable (SingularRectangleMoments.poleProduct Y w) squareLebesgue ∧
      (∫ Z, SingularRectangleMoments.poleProduct Y w Z ∂squareLebesgue) ≤ 5 := by
  classical
  have hk0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  rcases eq_or_lt_of_le hk0 with hz | hp
  · have he := SingularRectangleMoments.poleProduct_eq_one_of_sum_eq_zero Y w hw hz.symm
    have he' : SingularRectangleMoments.poleProduct Y w = fun _ => (1 : ℝ) := funext he
    rw [he']; simp
  · obtain ⟨hi, _, hb⟩ := SingularRectangleMoments.poleProduct_moment_of_sum_pos
      SingularRectangleMoments.squareLebesgue_le_volume Y w hw hp
      (s := 1) (by norm_num) (by linarith)
    simp only [Real.rpow_one, one_mul] at hi hb
    refine ⟨hi, hb.trans ?_⟩
    have hd : 0 < 2 - ∑ i, w i := by linarith
    have hh : 2 * Real.pi / (2 - ∑ i, w i) ≤ 4 :=
      (div_le_iff₀ hd).mpr (by linarith [Real.pi_lt_d2])
    linarith

open ResidualCellGraph

/-- Integer displacement boundary; all four corners are counted once. -/
def windowBoundary (d : ℕ) : Finset (ℤ × ℤ) :=
  (signedWindow d ×ˢ signedWindow d) \ (signedWindow (d - 1) ×ˢ signedWindow (d - 1))

theorem card_windowBoundary {d : ℕ} (hd : 1 ≤ d) :
    (windowBoundary d).card = 8 * d := by
  have hs : signedWindow (d - 1) ×ˢ signedWindow (d - 1) ⊆
      signedWindow d ×ˢ signedWindow d := by
    intro p hp
    simp only [Finset.mem_product, signedWindow, Finset.mem_Icc] at hp ⊢
    constructor <;> constructor <;> omega
  rw [windowBoundary, Finset.card_sdiff_of_subset hs]
  simp only [Finset.card_product, card_signedWindow]
  have he : 2 * (d - 1) + 1 + 2 = 2 * d + 1 := by omega
  have he' : (2 * d + 1) * (2 * d + 1) =
      (2 * (d - 1) + 1) * (2 * (d - 1) + 1) + 8 * d := by
    nlinarith
  omega

def distanceShell {J : ℕ} (a : MeshIndex J) (d : ℕ) : Finset (MeshIndex J) :=
  Finset.univ.filter fun b => periodicIndexDistance a b = d

theorem card_distanceShell_le {J d : ℕ} (hJ : 0 < J) (hd : 1 ≤ d) (a : MeshIndex J) :
    (distanceShell a d).card ≤ 8 * d := by
  classical
  have hs : distanceShell a d ⊆ (windowBoundary d).image
      (fun p => shiftIndex J hJ a (MeshNearbyGeometry.pairFrequency p)) := by
    intro b hb
    have hb' : periodicIndexDistance a b = d := (Finset.mem_filter.mp hb).2
    obtain ⟨v, hv, he⟩ := nearby_displacement ((mem_nearbyCells a b).mpr hb'.le)
    have hev : shiftIndex J hJ a v = b := MeshNearbyGeometry.shiftIndex_eq J hJ a b v he
    refine Finset.mem_image.mpr ⟨(v 0, v 1), ?_, ?_⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hv 0), Finset.mem_Icc.mpr (hv 1)⟩, ?_⟩
      intro hin
      have hh : ∀ j : Fin 2, v j ∈ signedWindow (d - 1) := by
        intro j; fin_cases j
        · exact (Finset.mem_product.mp hin).1
        · exact (Finset.mem_product.mp hin).2
      have hnear := shiftIndex_mem_nearby hJ a v hh
      rw [hev, mem_nearbyCells, hb'] at hnear
      omega
    · rw [MeshNearbyGeometry.pairFrequency_coordinates]
      exact hev
  exact (Finset.card_le_card hs).trans
    ((Finset.card_image_le).trans (by rw [card_windowBoundary hd]))


/-- Periodic distances take values in the actual finite range. -/
theorem indexDistance_le_mesh {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J) :
    periodicIndexDistance a b ≤ J := by
  let hJnz : NeZero J := ⟨hJ.ne'⟩
  apply max_le
  · exact (ZMod.natAbs_valMinAbs_le _).trans (Nat.div_le_self _ _)
  · exact (ZMod.natAbs_valMinAbs_le _).trans (Nat.div_le_self _ _)

/-- The exact elementary harmonic bound used in the source far summation. -/
theorem distance_harmonic_sum_le (J : ℕ) :
    (∑ d ∈ Finset.Icc 2 J, (d : ℝ) / ((d : ℝ) - 1)^2) ≤ 3 + Real.log J := by
  have hsum : (∑ d ∈ Finset.Icc 2 J, (d : ℝ) / ((d : ℝ) - 1)^2) ≤
      ∑ k ∈ Finset.Icc 1 J, ((k : ℝ)⁻¹ + ((k : ℝ)^2)⁻¹) := by
    apply Finset.sum_le_sum_of_injOn (fun d : ℕ => d - 1)
    · intro x hx y hy hxy
      have hx' := Finset.mem_Icc.mp hx
      have hy' := Finset.mem_Icc.mp hy
      change x - 1 = y - 1 at hxy
      omega
    · intro k hk
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
      have hd' := Finset.mem_Icc.mp hd
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro d hd
      have hd' := Finset.mem_Icc.mp hd
      have hn : (d : ℝ) - 1 ≠ 0 := by
        have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd'.1
        linarith
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      apply le_of_eq
      field_simp
      ring
    · intro k _ _; positivity
  have hhar : (∑ k ∈ Finset.Icc 1 J, (k : ℝ)⁻¹) ≤ 1 + Real.log J := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log J
  have hsq : (∑ k ∈ Finset.Icc 1 J, ((k : ℝ)^2)⁻¹) ≤ 2 := by
    have he : Finset.Ioo 0 (J + 1) = Finset.Icc 1 J := by
      ext k; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    simpa only [he, Nat.cast_zero, zero_add, div_one] using
      (sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1))
  rw [Finset.sum_add_distrib] at hsum
  linarith

open LabelOccupations

theorem near_particle_count {J N R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    {t : ℝ} {η : LabelVector J N} (hη : OccupationCap t η)
    (I : Finset (Fin N)) (a : MeshIndex J) :
    ((sourceIndices η I (nearbyCells R a)).card : ℝ) ≤
      (2 * (R : ℝ) + 1)^2 * (t * N) := by
  have hh := source_count_le hη I (nearbyCells R a)
  simpa only [card_nearbyCells_exact hmesh, Nat.cast_pow, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh

/-- Counting each actual distance fibre once, with arbitrary selected particles. -/
theorem far_particle_sum_le {J N R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {t : ℝ} (ht : 0 ≤ t) {η : LabelVector J N} (hη : OccupationCap t η)
    (I : Finset (Fin N)) (a : MeshIndex J) {C₂ : ℝ} (hC : 0 ≤ C₂) :
    (∑ i ∈ I.filter (fun i => R < periodicIndexDistance a (η i)),
      2 * C₂ / ((periodicIndexDistance a (η i) : ℝ) - 1)^2) ≤
      16 * t * N * C₂ * (3 + Real.log J) := by
  classical
  let T := I.filter (fun i => R < periodicIndexDistance a (η i))
  let f : ℕ → ℝ := fun d => 2 * C₂ / ((d : ℝ) - 1)^2
  have hid : (∑ i ∈ T, f (periodicIndexDistance a (η i))) =
      ∑ d ∈ Finset.Icc 2 J, ∑ i ∈ T,
        if periodicIndexDistance a (η i) = d then f d else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hd : periodicIndexDistance a (η i) ∈ Finset.Icc 2 J :=
      Finset.mem_Icc.mpr ⟨by omega, indexDistance_le_mesh hJ a (η i)⟩
    simp only [Finset.sum_ite_eq, hd, ite_true]
  have hb (d : ℕ) (hd : d ∈ Finset.Icc 2 J) :
      (∑ i ∈ T, if periodicIndexDistance a (η i) = d then f d else 0) ≤
        (8 * (d : ℝ)) * (t * N) * f d := by
    have he : T.filter (fun i => periodicIndexDistance a (η i) = d) =
        sourceIndices η T (distanceShell a d) := by
      ext i; simp [sourceIndices, distanceShell]
    rw [← Finset.sum_filter, he, Finset.sum_const, nsmul_eq_mul]
    have hc := source_count_le hη T (distanceShell a d)
    have hd' := card_distanceShell_le hJ (show 1 ≤ d by have := (Finset.mem_Icc.mp hd).1; omega) a
    have hdr : ((distanceShell a d).card : ℝ) ≤ 8 * d := by exact_mod_cast hd'
    exact mul_le_mul_of_nonneg_right (hc.trans
      (mul_le_mul_of_nonneg_right hdr (by positivity))) (by dsimp [f]; positivity)
  change (∑ i ∈ T, f (periodicIndexDistance a (η i))) ≤ _
  rw [hid]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 2 J, (8 * (d : ℝ)) * (t * N) * f d := Finset.sum_le_sum hb
    _ = (16 * t * N * C₂) * ∑ d ∈ Finset.Icc 2 J, (d : ℝ) / ((d : ℝ) - 1)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _; dsimp [f]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (distance_harmonic_sum_le J) (by positivity)


/-- A finite family of logarithmic upper bounds gives an actual exponential
moment; the finite intersection of all exceptional pole sets is explicit. -/
theorem exponential_log_domination {ι : Type*} [Fintype ι]
    (Y : ι → PlanarSpace) (f : PlanarSpace → ℝ) (hf : Measurable f)
    {a B : ℝ} (ha : 0 ≤ a) (hκ : (Fintype.card ι : ℝ) * a ≤ 3 / 16)
    (hdom : ∀ᵐ Z ∂squareLebesgue, f Z ≤ B + ∑ i, -a * Real.log ‖Z - Y i‖) :
    Integrable (fun Z => Real.exp (f Z)) squareLebesgue ∧
      (∫ Z, Real.exp (f Z) ∂squareLebesgue) ≤ 5 * Real.exp B := by
  classical
  let w : ι → ℝ := fun _ => a
  have hm := poleProduct_integral_le_five Y w (fun _ => ha) (by simpa [w] using hκ)
  have hne : ∀ᵐ Z ∂squareLebesgue, ∀ i, Z ≠ Y i := by
    rw [ae_all_iff]
    intro i
    exact SingularRectangleMoments.squareLebesgue_le_volume.absolutelyContinuous.ae_le
      ((volume : Measure PlanarSpace).ae_ne (Y i))
  have hb : ∀ᵐ Z ∂squareLebesgue, Real.exp (f Z) ≤
      Real.exp B * SingularRectangleMoments.poleProduct Y w Z := by
    filter_upwards [hdom, hne] with Z hZ hZY
    have he : SingularRectangleMoments.poleProduct Y w Z =
        Real.exp (∑ i, -a * Real.log ‖Z - Y i‖) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [SingularRectangleMoments.inverseDistancePower,
        Real.rpow_def_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hZY i)))]
      dsimp [w]; congr 1; ring
    rw [he, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hZ
  have hiB := hm.1.const_mul (Real.exp B)
  have hi : Integrable (fun Z => Real.exp (f Z)) squareLebesgue := hiB.mono'
    (Real.continuous_exp.measurable.comp hf).aestronglyMeasurable (hb.mono fun Z hZ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hZ)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ Z, Real.exp B * SingularRectangleMoments.poleProduct Y w Z ∂squareLebesgue :=
      integral_mono_ae hi hiB hb
    _ = Real.exp B * ∫ Z, SingularRectangleMoments.poleProduct Y w Z ∂squareLebesgue :=
      integral_const_mul _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hm.2 (Real.exp_pos B).le]

/-- True density comparison of a nonnegative exponential after the cell chart. -/
theorem exponential_reference_bound {J : ℕ} (hJ : 0 < J) (b : MeshIndex J)
    (ν : Measure Torus) (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b)
    (f : Torus → ℝ) (hf : Measurable f) {B : ℝ}
    (hi : Integrable (fun Z => Real.exp (f (meshChart J b Z))) squareLebesgue)
    (hb : (∫ Z, Real.exp (f (meshChart J b Z)) ∂squareLebesgue) ≤ B) :
    Integrable (fun y => Real.exp (f y)) ν ∧
      (∫ y, Real.exp (f y) ∂ν) ≤ Real.exp 1 * B := by
  have hm : Measurable (fun y => Real.exp (f y)) := Real.continuous_exp.measurable.comp hf
  have hic : Integrable (fun y => Real.exp (f y)) (meshCellMeasure J hJ b) :=
    ((measurePreserving_meshChart J hJ b).integrable_comp hm.aestronglyMeasurable).mp hi
  have hs := hic.smul_measure (c := ENNReal.ofReal (Real.exp 1)) ENNReal.ofReal_ne_top
  refine ⟨hs.mono_measure hν, ?_⟩
  calc
    _ ≤ ∫ y, Real.exp (f y) ∂(ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) :=
      integral_mono_measure hν (Eventually.of_forall fun _ => (Real.exp_pos _).le) hs
    _ = Real.exp 1 * ∫ Z, Real.exp (f (meshChart J b Z)) ∂squareLebesgue := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos 1).le, smul_eq_mul,
        ← integral_meshChart hJ b hic]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_pos 1).le

/-- Source far estimate with support derived from upper density domination. -/
theorem far_residual_upper {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hd : 2 ≤ periodicIndexDistance a b) {C₂ : ℝ} (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b)
    {x y : Torus} (hx : x ∈ closure (meshCell J hJ a))
    (hy : y ∈ closure (meshCell J hJ b)) :
    residual μ ν x y ≤ 2 * C₂ / ((periodicIndexDistance a b : ℝ) - 1)^2 := by
  let R := periodicIndexDistance a b - 1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hfar : b ∉ nearbyCells R a := by rw [mem_nearbyCells]; dsimp [R]; omega
  have hh := FarReferenceResidual.far_residual_bound hJ hR a b hfar μ ν
    (ae_mem_closed_cell_of_domination hJ a μ hμ)
    (ae_mem_closed_cell_of_domination hJ b ν hν) hC hk hx hy
  have he : (R : ℝ) = (periodicIndexDistance a b : ℝ) - 1 := by
    dsimp [R]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  exact (le_abs_self _).trans (by simpa only [he] using hh)


/-- The actual section before one independent coordinate is integrated. -/
def sectionExponent {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (I : Finset (Fin N)) (b : MeshIndex J)
    (X : Fin N → Torus) (q : ℝ) (y : Torus) : ℝ :=
  q / N * ∑ i ∈ I, residual (μ (η i)) (μ b) (X i) y

def stepConstant (J R : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  Real.log (5 * Real.exp 1) + 3 * β₀ * (2 * (R : ℝ) + 1)^2 * t * nearConstant R +
    48 * β₀ * t * C₂ * (3 + Real.log J)

theorem stepConstant_le {J R : ℕ} (hJ : 0 < J) {β₀ t C₂ : ℝ}
    (hβ : 0 ≤ β₀) (ht : 0 ≤ t) (hC : 0 ≤ C₂) :
    stepConstant J R β₀ t C₂ ≤ integratedConstant R β₀ t C₂ * (1 + Real.log J) := by
  have hj : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hl : 0 ≤ Real.log (5 * Real.exp 1) := Real.log_nonneg (by linarith)
  have hn := nearConstant_nonneg R
  have hb : 0 ≤ Real.log (5 * Real.exp 1) +
      3 * β₀ * (2 * (R : ℝ) + 1)^2 * t * nearConstant R := by positivity
  have hbj := mul_nonneg hb hj
  have hfj := mul_nonneg (show 0 ≤ 96 * β₀ * t * C₂ by positivity) hj
  unfold stepConstant integratedConstant
  nlinarith

theorem measurable_sectionExponent {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J N)
    (I : Finset (Fin N)) (b : MeshIndex J) (X : Fin N → Torus) (q : ℝ) :
    Measurable (sectionExponent μ η I b X q) := by
  have hm (i : Fin N) : Measurable (fun y : Torus => residual (μ (η i)) (μ b) (X i) y) := by
    simp_rw [residual_eq_source_order]
    have hg : Measurable (fun y : Torus => greenKernel (X i) y) :=
      regularGreenRepresentative_measurable.comp (measurable_const.sub measurable_id)
    exact ((hg.sub measurable_const).sub (ReferenceSelfTerms.measurable_potential (μ (η i)))).add
      measurable_const
  have hs : Measurable (fun y : Torus => ∑ i ∈ I, residual (μ (η i)) (μ b) (X i) y) :=
    Finset.measurable_sum I (fun i _ => hm i)
  exact hs.const_mul (q / N)

/-- Pointwise fixed-source assumptions are only prescribed closed-cell support.
All potential, shell-count and pole-moment bounds above are consumed here. -/
theorem section_exponential_bound {J N R : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (hR : 1 ≤ R) (hmesh : 8 * (R + 1) ≤ J)
    {β₀ t C₂ q : ℝ} (_hβ : 0 ≤ β₀) (ht : 0 ≤ t) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hq : 0 ≤ q) (hqβ : q ≤ 3 * β₀)
    (hsmall : β₀ * (2 * (R : ℝ) + 1)^2 * t ≤ 1 / 16)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (hη : OccupationCap t η)
    (I : Finset (Fin N)) (b : MeshIndex J) (X : Fin N → Torus)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i))) :
    Integrable (fun y => Real.exp (sectionExponent μ η I b X q y)) (μ b) ∧
      (∫ y, Real.exp (sectionExponent μ η I b X q y) ∂μ b) ≤
        Real.exp (stepConstant J R β₀ t C₂) := by
  classical
  let S := sourceIndices η I (nearbyCells R b)
  let T := I.filter (fun i => R < periodicIndexDistance b (η i))
  let a : ℝ := q / N
  let H : ℝ := 16 * t * N * C₂ * (3 + Real.log J)
  let B : ℝ := a * ((S.card : ℝ) * nearConstant R + H)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ a := div_nonneg hq hNr.le
  have hcount := near_particle_count hmesh hη I b
  have hpower : (S.card : ℝ) * a ≤ 3 * β₀ * (2 * (R : ℝ) + 1)^2 * t := by
    calc
      _ ≤ ((2 * (R : ℝ) + 1)^2 * (t * N)) * a := mul_le_mul_of_nonneg_right hcount ha
      _ = q * (2 * (R : ℝ) + 1)^2 * t := by dsimp [a]; field_simp
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hqβ
          (show 0 ≤ (2 * (R : ℝ) + 1)^2 * t by positivity)
        nlinarith
  have hp : (Fintype.card S : ℝ) * a ≤ 3 / 16 := by
    rw [Fintype.card_coe]
    nlinarith
  have hY : ∀ i : S, ∃ Y : PlanarSpace, ∀ᵐ Z ∂squareLebesgue,
      residual (μ (η i)) (μ b) (X i) (meshChart J b Z) ≤
        -Real.log ‖Z - Y‖ + nearConstant R := by
    intro i
    have hi := (mem_sourceIndices η I (nearbyCells R b) i).mp i.property
    have hd : periodicIndexDistance (η i) b ≤ R := by
      rw [periodicIndexDistance_comm]; exact (mem_nearbyCells _ _).mp hi.2
    exact near_residual_chart_upper hJ hmesh (η i) b hd _ _ (hμ _) (hμ _) (hX i hi.1)
  choose Y hY using hY
  have hdom : ∀ᵐ Z ∂squareLebesgue,
      sectionExponent μ η I b X q (meshChart J b Z) ≤
        B + ∑ i : S, -a * Real.log ‖Z - Y i‖ := by
    have hall : ∀ᵐ Z ∂squareLebesgue, ∀ i : S,
        residual (μ (η i)) (μ b) (X i) (meshChart J b Z) ≤
          -Real.log ‖Z - Y i‖ + nearConstant R := by
      rw [ae_all_iff]; exact hY
    filter_upwards [hall, PoleLogMoments.ae_mem_closed_square] with Z hZ hZmem
    have hzy : meshChart J b Z ∈ closure (meshCell J hJ b) := by
      rw [MeshAdjacentCells.closure_meshCell]; exact ⟨Z, hZmem, rfl⟩
    let f : Fin N → ℝ := fun i => residual (μ (η i)) (μ b) (X i) (meshChart J b Z)
    have hn : (∑ i ∈ S, f i) ≤ ∑ i : S, (-Real.log ‖Z - Y i‖ + nearConstant R) := by
      rw [Finset.sum_subtype S (fun _ => Iff.rfl) f]
      exact Finset.sum_le_sum fun i _ => hZ i
    have hfar : (∑ i ∈ T, f i) ≤ H := by
      calc
        _ ≤ ∑ i ∈ T, 2 * C₂ / ((periodicIndexDistance b (η i) : ℝ) - 1)^2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_filter.mp hi
          have hd : 2 ≤ periodicIndexDistance (η i) b := by
            rw [periodicIndexDistance_comm]; omega
          have hh := far_residual_upper hJ (η i) b hd hC hk _ _ (hμ _) (hμ _) (hX i hi'.1) hzy
          simpa only [periodicIndexDistance_comm (η i) b] using hh
        _ ≤ H := far_particle_sum_le hJ hR ht hη I b hC
    have he : (∑ i ∈ I, f i) = (∑ i ∈ S, f i) + ∑ i ∈ T, f i := by
      dsimp [S, T, sourceIndices]
      simp only [Finset.sum_filter, mem_nearbyCells, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : periodicIndexDistance b (η i) ≤ R
      · simp [hi, not_lt.mpr hi]
      · simp [hi, lt_of_not_ge hi]
    have ht' := mul_le_mul_of_nonneg_left (add_le_add hn hfar) ha
    rw [← he] at ht'
    change a * ∑ i ∈ I, f i ≤ _
    refine ht'.trans_eq ?_
    dsimp [B]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_attach,
      nsmul_eq_mul, mul_add, Finset.mul_sum, mul_neg]
    ring_nf
  have hm := measurable_sectionExponent μ η I b X q
  obtain ⟨hi, hb⟩ := exponential_log_domination Y _
    (hm.comp (measurable_meshChart J b)) ha hp hdom
  obtain ⟨hiν, hbν⟩ := exponential_reference_bound hJ b (μ b) (hμ b) _ hm hi hb
  refine ⟨hiν, hbν.trans ?_⟩
  have hj : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hnear := mul_le_mul_of_nonneg_right hpower (nearConstant_nonneg R)
  have hfar : a * H ≤ 48 * β₀ * t * C₂ * (3 + Real.log J) := by
    calc
      _ = 16 * q * t * C₂ * (3 + Real.log J) := by dsimp [a, H]; field_simp
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hqβ
          (show 0 ≤ 16 * t * C₂ * (3 + Real.log J) by positivity)
        nlinarith
  have hB : B ≤ 3 * β₀ * (2 * (R : ℝ) + 1)^2 * t * nearConstant R +
      48 * β₀ * t * C₂ * (3 + Real.log J) := by dsimp [B]; nlinarith
  have hex : Real.exp 1 * (5 * Real.exp B) =
      Real.exp (Real.log (5 * Real.exp 1) + B) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]; ring
  rw [hex]
  exact Real.exp_le_exp.mpr (by unfold stepConstant; linarith)


open OneCoordinateConditionals

/-- Auxiliary literal upper-pair sum on a selected particle set. -/
def pairSumOn {N : ℕ} (K : Fin N → Fin N → Torus → Torus → ℝ)
    (I : Finset (Fin N)) (X : Configuration N) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, if i < j then K i j (X i) (X j) else 0

theorem measurable_pairSumOn {N : ℕ} (K : Fin N → Fin N → Torus → Torus → ℝ)
    (hK : ∀ i j, Measurable (Function.uncurry (K i j))) (I : Finset (Fin N)) :
    Measurable (pairSumOn K I) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i < j
  · have hp : Measurable (fun X : Configuration N => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    have hh := (hK i j).comp hp
    simpa only [hij, ite_true, Function.comp_def, Function.uncurry_apply_pair] using hh
  · simp only [hij, ite_false]; exact measurable_const

theorem pairSumOn_congr {N : ℕ} (K : Fin N → Fin N → Torus → Torus → ℝ)
    (I : Finset (Fin N)) {X Y : Configuration N} (hXY : ∀ i ∈ I, X i = Y i) :
    pairSumOn K I X = pairSumOn K I Y := by
  unfold pairSumOn
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hXY i hi, hXY j hj]

theorem pairSumOn_insert {N : ℕ} (K : Fin N → Fin N → Torus → Torus → ℝ)
    (hK : ∀ i j x y, K i j x y = K j i y x)
    (I : Finset (Fin N)) {j : Fin N} (hj : j ∉ I) (X : Configuration N) :
    pairSumOn K (insert j I) X = pairSumOn K I X + ∑ i ∈ I, K i j (X i) (X j) := by
  classical
  have hh : (∑ i ∈ I, if j < i then K j i (X j) (X i) else 0) +
      (∑ i ∈ I, if i < j then K i j (X i) (X j) else 0) =
      ∑ i ∈ I, K i j (X i) (X j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by intro he; subst i; exact hj hi
    by_cases hji : j < i
    · simp only [hji, not_lt.mpr hji.le, ite_true, ite_false, add_zero]
      exact hK j i (X j) (X i)
    · have hij' : i < j := by omega
      simp only [hji, hij', ite_false, ite_true, zero_add]
  unfold pairSumOn
  simp only [Finset.sum_insert hj, lt_self_iff_false, ite_false, zero_add,
    Finset.sum_add_distrib]
  linarith

theorem insertSite_other {n : ℕ} (j i : Fin (n + 1)) (hij : i ≠ j)
    (z w : Torus) (Y : Configuration n) : insertSite j z Y i = insertSite j w Y i := by
  obtain he | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j i
  · exact (hij he).elim
  · simp only [insertSite_succAbove]

theorem pairSumOn_insertSite {n : ℕ} (K : Fin (n + 1) → Fin (n + 1) → Torus → Torus → ℝ)
    (I : Finset (Fin (n + 1))) {j : Fin (n + 1)} (hj : j ∉ I)
    (z w : Torus) (Y : Configuration n) :
    pairSumOn K I (insertSite j z Y) = pairSumOn K I (insertSite j w Y) := by
  apply pairSumOn_congr
  intro i hi
  exact insertSite_other j i (by intro he; subst i; exact hj hi) z w Y

/-- Integrating an inserted vertex leaves the previous selected-pair factor
under the same independent product reference. No interacting marginal is used. -/
theorem pair_insert_lintegral_le {n : ℕ}
    (ν : Fin (n + 1) → Measure Torus) [∀ i, IsProbabilityMeasure (ν i)]
    (P : Fin (n + 1) → Torus → Prop) (hP : ∀ i, ∀ᵐ x ∂ν i, P i x)
    (K : Fin (n + 1) → Fin (n + 1) → Torus → Torus → ℝ)
    (hK : ∀ i j, Measurable (Function.uncurry (K i j)))
    (hsym : ∀ i j x y, K i j x y = K j i y x)
    (I : Finset (Fin (n + 1))) {j : Fin (n + 1)} (hj : j ∉ I) {B : ℝ}
    (hrow : ∀ X : Configuration (n + 1), (∀ i ∈ I, P i (X i)) →
      (∫⁻ z, ENNReal.ofReal (Real.exp (∑ i ∈ I, K i j (X i) z)) ∂ν j) ≤
        ENNReal.ofReal (Real.exp B)) :
    (∫⁻ X, ENNReal.ofReal (Real.exp (pairSumOn K (insert j I) X)) ∂Measure.pi ν) ≤
      (∫⁻ X, ENNReal.ofReal (Real.exp (pairSumOn K I X)) ∂Measure.pi ν) *
        ENNReal.ofReal (Real.exp B) := by
  classical
  let F : Configuration (n + 1) → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (pairSumOn K I X))
  let G : Configuration n → ℝ≥0∞ := fun Y => F (insertSite j 0 Y)
  have hF : Measurable F := ((measurable_pairSumOn K hK I).exp).ennreal_ofReal
  have hG : Measurable G := hF.comp ((measurable_insertSite j).comp
    (measurable_const.prodMk measurable_id))
  have hconst (Y : Configuration n) (z : Torus) : F (insertSite j z Y) = G Y := by
    dsimp [F, G]; rw [pairSumOn_insertSite K I hj z 0 Y]
  have hrest : (∫⁻ X, F X ∂Measure.pi ν) = ∫⁻ Y, G Y ∂outsideReference ν j := by
    rw [lintegral_pi_insert ν j hF]
    simp_rw [hconst]
    simp
  have hfactor (Y : Configuration n) (z : Torus) :
      ENNReal.ofReal (Real.exp (pairSumOn K (insert j I) (insertSite j z Y))) =
        G Y * ENNReal.ofReal (Real.exp (∑ i ∈ I, K i j (insertSite j 0 Y i) z)) := by
    rw [pairSumOn_insert K hsym I hj, pairSumOn_insertSite K I hj z 0 Y,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 2
    apply congrArg Real.exp
    apply Finset.sum_congr rfl
    intro i hi
    rw [insertSite_self, insertSite_other j i (by intro he; subst i; exact hj hi) z 0 Y]
  have hout : ∀ᵐ Y ∂outsideReference ν j, ∀ k : Fin n, P (j.succAbove k) (Y k) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_eval (fun k => ν (j.succAbove k)) k).quasiMeasurePreserving.ae
      (hP (j.succAbove k))
  have hsection : ∀ᵐ Y ∂outsideReference ν j,
      (∫⁻ z, ENNReal.ofReal (Real.exp (pairSumOn K (insert j I) (insertSite j z Y))) ∂ν j) ≤
        G Y * ENNReal.ofReal (Real.exp B) := by
    filter_upwards [hout] with Y hY
    have hs : ∀ i ∈ I, P i (insertSite j 0 Y i) := by
      intro i hi
      obtain he | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j i
      · exact (hj (he ▸ hi)).elim
      · simpa only [insertSite_succAbove] using hY k
    have hm : Measurable (fun z : Torus => ENNReal.ofReal
        (Real.exp (∑ i ∈ I, K i j (insertSite j 0 Y i) z))) := by
      apply Measurable.ennreal_ofReal
      apply Measurable.exp
      apply Finset.measurable_sum
      intro i _
      exact (hK i j).comp (measurable_const.prodMk measurable_id)
    simp_rw [hfactor]
    rw [lintegral_const_mul _ hm]
    gcongr
    exact hrow (insertSite j 0 Y) hs
  rw [lintegral_pi_insert ν j (((measurable_pairSumOn K hK _).exp).ennreal_ofReal)]
  calc
    _ ≤ ∫⁻ Y, G Y * ENNReal.ofReal (Real.exp B) ∂outsideReference ν j := lintegral_mono_ae hsection
    _ = (∫⁻ Y, G Y ∂outsideReference ν j) * ENNReal.ofReal (Real.exp B) :=
      lintegral_mul_const _ hG
    _ = _ := by rw [← hrest]


/-- Finite sequential integration of every selected upper pair. The section
premise of this reusable lemma is discharged by the actual residual estimate below. -/
theorem pair_lintegral_le {n : ℕ}
    (ν : Fin (n + 1) → Measure Torus) [∀ i, IsProbabilityMeasure (ν i)]
    (P : Fin (n + 1) → Torus → Prop) (hP : ∀ i, ∀ᵐ x ∂ν i, P i x)
    (K : Fin (n + 1) → Fin (n + 1) → Torus → Torus → ℝ)
    (hK : ∀ i j, Measurable (Function.uncurry (K i j)))
    (hsym : ∀ i j x y, K i j x y = K j i y x) {B : ℝ}
    (hrow : ∀ (I : Finset (Fin (n + 1))) (j : Fin (n + 1)), j ∉ I →
      ∀ X : Configuration (n + 1), (∀ i ∈ I, P i (X i)) →
      (∫⁻ z, ENNReal.ofReal (Real.exp (∑ i ∈ I, K i j (X i) z)) ∂ν j) ≤
        ENNReal.ofReal (Real.exp B)) (I : Finset (Fin (n + 1))) :
    (∫⁻ X, ENNReal.ofReal (Real.exp (pairSumOn K I X)) ∂Measure.pi ν) ≤
      ENNReal.ofReal (Real.exp ((I.card : ℝ) * B)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [pairSumOn]
  | @insert j I hj ih =>
    calc
      _ ≤ (∫⁻ X, ENNReal.ofReal (Real.exp (pairSumOn K I X)) ∂Measure.pi ν) *
          ENNReal.ofReal (Real.exp B) := pair_insert_lintegral_le ν P hP K hK hsym I hj (hrow I j hj)
      _ ≤ ENNReal.ofReal (Real.exp ((I.card : ℝ) * B)) * ENNReal.ofReal (Real.exp B) := by
        gcongr
      _ = _ := by
        rw [Finset.card_insert_of_notMem hj, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
          Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem pairSumOn_residual {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (q : ℝ) (X : Configuration N) :
    pairSumOn (fun i j x y => q / N * residual (μ (η i)) (μ (η j)) x y) Finset.univ X =
      q * ResidualExponential.residualSum μ η X := by
  classical
  unfold pairSumOn ResidualExponential.residualSum CanonicalPairs.canonicalSum
    CanonicalDecoupling.pairSum CanonicalPairs.upperKernel
  have hscale (S : ℝ) : q * (S / N) = q / N * S := by ring
  rw [hscale]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij]

/-- Complete analytic estimate under upper reference domination. All section,
counting, integrability and product-law hypotheses are derived from actual kernels. -/
theorem crude_residual_of_domination {J N R : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hR : 1 ≤ R) (hmesh : 8 * (R + 1) ≤ J)
    {β₀ t C₂ q : ℝ} (hβ : 0 ≤ β₀) (ht : 0 ≤ t) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hq : 0 ≤ q) (hqβ : q ≤ 3 * β₀)
    (hsmall : β₀ * (2 * (R : ℝ) + 1)^2 * t ≤ 1 / 16)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (hη : OccupationCap t η) :
    Integrable (fun X => Real.exp (q * ResidualExponential.residualSum μ η X))
      (Measure.pi (fun i => μ (η i))) ∧
    Real.log (∫ X, Real.exp (q * ResidualExponential.residualSum μ η X)
      ∂Measure.pi (fun i => μ (η i))) ≤
        integratedConstant R β₀ t C₂ * N * (1 + Real.log J) := by
  classical
  cases N with
  | zero => omega
  | succ n =>
    let ν : Fin (n + 1) → Measure Torus := fun i => μ (η i)
    let K : Fin (n + 1) → Fin (n + 1) → Torus → Torus → ℝ :=
      fun i j x y => q / (n + 1 : ℕ) * residual (μ (η i)) (μ (η j)) x y
    have hK : ∀ i j, Measurable (Function.uncurry (K i j)) := by
      intro i j
      have hm : Measurable (Function.uncurry (residual (μ (η i)) (μ (η j)))) :=
        ResidualDoubleCentering.measurable_doubleCenter _ _ greenKernel measurable_greenKernel
      exact hm.const_mul _
    have hsym : ∀ i j x y, K i j x y = K j i y x := by
      intro i j x y
      dsimp [K]
      rw [ReferenceConditionalNormalization.residual_symm hJ (η j) _ _ (hμ (η j)) x y]
    let P : Fin (n + 1) → Torus → Prop := fun i x => x ∈ closure (meshCell J hJ (η i))
    have hP : ∀ i, ∀ᵐ x ∂ν i, P i x := fun i =>
      ae_mem_closed_cell_of_domination hJ (η i) (μ (η i)) (hμ (η i))
    have hrow (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) (_hj : j ∉ I)
        (X : Configuration (n + 1)) (hX : ∀ i ∈ I, P i (X i)) :
        (∫⁻ z, ENNReal.ofReal (Real.exp (∑ i ∈ I, K i j (X i) z)) ∂ν j) ≤
          ENNReal.ofReal (Real.exp (stepConstant J R β₀ t C₂)) := by
      have hh := section_exponential_bound hJ (show 0 < n + 1 by omega) hR hmesh
        hβ ht hC hk hq hqβ hsmall μ hμ η hη I (η j) X hX
      have he : (fun z => ∑ i ∈ I, K i j (X i) z) = sectionExponent μ η I (η j) X q := by
        funext z
        dsimp [K, sectionExponent]
        rw [Finset.mul_sum]
      have he' (z : Torus) : (∑ i ∈ I, K i j (X i) z) = sectionExponent μ η I (η j) X q z :=
        congrFun he z
      simp_rw [he']
      change (∫⁻ z, ENNReal.ofReal (Real.exp (sectionExponent μ η I (η j) X q z)) ∂μ (η j)) ≤ _
      rw [← ofReal_integral_eq_lintegral_ofReal hh.1
        (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hh.2
    have hl := pair_lintegral_le ν P hP K hK hsym hrow Finset.univ
    have he (X : Configuration (n + 1)) : pairSumOn K Finset.univ X =
        q * ResidualExponential.residualSum μ η X := pairSumOn_residual μ η q X
    simp only [Finset.card_univ, Fintype.card_fin] at hl
    simp_rw [he] at hl
    have hm : Measurable (fun X => Real.exp (q * ResidualExponential.residualSum μ η X)) := by
      have hh := (measurable_pairSumOn K hK Finset.univ).exp
      simpa only [he] using hh
    have hi := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp (hl.trans_lt ENNReal.ofReal_lt_top).ne
    refine ⟨hi, ?_⟩
    have hb : (∫ X, Real.exp (q * ResidualExponential.residualSum μ η X) ∂Measure.pi ν) ≤
        Real.exp (((n + 1 : ℕ) : ℝ) * stepConstant J R β₀ t C₂) := by
      apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp
      rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
      exact hl
    have hh := Real.log_le_log (integral_exp_pos hi) hb
    rw [Real.log_exp] at hh
    refine hh.trans ?_
    have hs : ((n + 1 : ℕ) : ℝ) * stepConstant J R β₀ t C₂ ≤
        ((n + 1 : ℕ) : ℝ) * (integratedConstant R β₀ t C₂ * (1 + Real.log J)) :=
      mul_le_mul_of_nonneg_left (stepConstant_le (R := R) hJ hβ ht hC)
        (Nat.cast_nonneg (n + 1))
    nlinarith

/-- The manuscript's microscopic choice supplies the small total pole power,
including zero inverse temperature without division by that parameter. -/
theorem microscopic_power_bound {β₀ t : ℝ} (hβ : 0 ≤ β₀) (ht : 0 ≤ t)
    (htδ : t < occupationBound β₀) :
    β₀ * (2 * (radius β₀ : ℝ) + 1)^2 * t ≤ 1 / 16 := by
  have hp := (chosen_parameters β₀ hβ).2.2.1
  refine le_trans ?_ hp
  have hs : (2 * (radius β₀ : ℝ) + 1)^2 ≤ (2 * (radius β₀ : ℝ) + 2)^2 := by
    nlinarith [show (0 : ℝ) ≤ (radius β₀ : ℝ) from Nat.cast_nonneg _]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hβ) ht).trans
    (mul_le_mul_of_nonneg_left htδ.le (mul_nonneg hβ (sq_nonneg _)))

/-- Complete source Lemma `crude-residual-integrated` at every admissible finer
resolution. These are the original two-sided densities and the literal residual
under the probability product law; no reference fixed point is assumed. -/
theorem crude_residual_integrated {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β₀ t C₂ q : ℝ} (hβ : 0 ≤ β₀) (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (w : MeshIndex J → Torus → ℝ≥0∞)
    (hμw : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (w a))
    (hw : ∀ a, ∀ᵐ x ∂meshCellMeasure J hJ a,
      ENNReal.ofReal (Real.exp (-1)) ≤ w a x ∧ w a x ≤ ENNReal.ofReal (Real.exp 1))
    (η : LabelVector J N) (hη : OccupationCap t η) (hq : 0 ≤ q) (hqβ : q ≤ 3 * β₀) :
    Integrable (fun X => Real.exp (q * ResidualExponential.residualSum μ η X))
      (Measure.pi (fun i => μ (η i))) ∧
    Real.log (∫ X, Real.exp (q * ResidualExponential.residualSum μ η X)
      ∂Measure.pi (fun i => μ (η i))) ≤
        integratedConstant (radius β₀) β₀ t C₂ * N * (1 + Real.log J) := by
  apply crude_residual_of_domination hJ hN (radius_one_le β₀) (by omega)
    hβ ht.le hC hk hq hqβ (microscopic_power_bound hβ ht.le htδ) μ _ η hη
  intro a
  rw [hμw a]
  exact NearLogMomentBounds.withDensity_le_exp_smul _ _ ((hw a).mono fun _ h => h.2)

/-- The zero-power endpoint is exactly one, for all particle numbers and cells. -/
theorem crude_residual_zero {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) :
    Integrable (fun X => Real.exp (0 * ResidualExponential.residualSum μ η X))
      (Measure.pi (fun i => μ (η i))) ∧
    (∫ X, Real.exp (0 * ResidualExponential.residualSum μ η X)
      ∂Measure.pi (fun i => μ (η i))) = 1 := by
  simp

end PeriodicAttractiveLogGas.CrudeResidualIntegrated
