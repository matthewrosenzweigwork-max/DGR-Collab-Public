import LeanResearch.PeriodicAttractiveLogGas.StationaryCoordinateCuts

/-! The two coordinate cuts form a connected set. Since this set misses
a regular level, it lies in a single strict phase. The other phase can
therefore be lifted inside one open Euclidean fundamental square. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace PeriodicAttractiveLogGas.StationaryCutDomain
open StationaryCoarea StationarySard StationaryLevelGeometry StationaryCoordinateCuts

def vertical (p : Torus) (a : UnitAddCircle) : Torus := ![p 0, a]
def horizontal (p : Torus) (a : UnitAddCircle) : Torus := ![a, p 1]
def coordinateCross (p : Torus) : Set Torus := Set.range (vertical p) ∪ Set.range (horizontal p)

theorem vertical_continuous (p : Torus) : Continuous (vertical p) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp [vertical] <;> fun_prop

theorem horizontal_continuous (p : Torus) : Continuous (horizontal p) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp [horizontal] <;> fun_prop

theorem mem_coordinateCross (p z : Torus) :
    z ∈ coordinateCross p ↔ ∃ j : Fin 2, z j = p j := by
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨j, hj⟩
    fin_cases j
    · change z 0 = p 0 at hj
      left
      refine ⟨z 1, ?_⟩
      funext k
      fin_cases k <;> simp [vertical, hj]
    · change z 1 = p 1 at hj
      right
      refine ⟨z 0, ?_⟩
      funext k
      fin_cases k <;> simp [horizontal, hj]

theorem coordinateCross_connected (p : Torus) : IsConnected (coordinateCross p) := by
  have hv : IsConnected (Set.range (vertical p)) := by
    simpa only [image_univ] using isConnected_univ.image (vertical p) (vertical_continuous p).continuousOn
  have hh : IsConnected (Set.range (horizontal p)) := by
    simpa only [image_univ] using isConnected_univ.image (horizontal p) (horizontal_continuous p).continuousOn
  have hvm : p ∈ Set.range (vertical p) := by
    refine ⟨p 1, ?_⟩
    funext j
    fin_cases j <;> rfl
  have hhm : p ∈ Set.range (horizontal p) := by
    refine ⟨p 0, ?_⟩
    funext j
    fin_cases j <;> rfl
  exact IsConnected.union ⟨p, hvm, hhm⟩ hv hh

theorem cross_phase_sign {v : Torus → ℝ} (hv : Continuous v) {t : ℝ} (p : Torus)
    (hcut : ∀ z : Torus, v z = t → ∀ j : Fin 2, z j ≠ p j) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ coordinateCross p, σ * (v z - t) < 0 := by
  have hdis : Disjoint {z | t < v z} {z | v z < t} := by
    rw [Set.disjoint_left]
    intro z hz hw
    change t < v z at hz
    change v z < t at hw
    exact (not_lt_of_ge hz.le) hw
  have hcover : coordinateCross p ⊆ {z | t < v z} ∪ {z | v z < t} := by
    intro z hz
    have hne : v z ≠ t := by
      intro he
      obtain ⟨j, hj⟩ := (mem_coordinateCross p z).mp hz
      exact hcut z he j hj
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases (coordinateCross_connected p).isPreconnected.subset_or_subset
    (isOpen_lt continuous_const hv) (isOpen_lt hv continuous_const) hdis hcover with h | h
  · refine ⟨-1, Or.inr rfl, fun z hz ↦ ?_⟩
    have hh : t < v z := h hz
    nlinarith only [hh]
  · refine ⟨1, Or.inl rfl, fun z hz ↦ ?_⟩
    have hh : v z < t := h hz
    linarith only [hh]



def euclideanClosedBox (a : PlanarSpace) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j : Fin 2 ↦ Icc (a j) (a j + 1))

theorem closedBox_compact (a : PlanarSpace) : IsCompact (euclideanClosedBox a) :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

theorem fundamentalBox_subset_closedBox (a : PlanarSpace) :
    euclideanFundamentalBox a ⊆ euclideanClosedBox a := by
  intro x hx j hj
  exact ⟨(hx j hj).1.le, (hx j hj).2⟩

theorem closedBox_boundary_cross (a : PlanarSpace) {x : PlanarSpace}
    (hx : x ∈ euclideanClosedBox a) (hxo : x ∉ euclideanOpenBox a) :
    torusQuotient x ∈ coordinateCross (torusQuotient a) := by
  have hex : ∃ j : Fin 2, ¬ (a j < x j ∧ x j < a j + 1) := by
    by_contra hh
    apply hxo
    intro j _
    by_contra hj
    exact hh ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  have hc := hx j (mem_univ j)
  apply (mem_coordinateCross _ _).mpr
  refine ⟨j, ?_⟩
  change (x j : UnitAddCircle) = (a j : UnitAddCircle)
  rcases eq_or_lt_of_le hc.1 with he | he
  · rw [← he]
  · have hb : x j = a j + 1 := by
      apply le_antisymm hc.2
      apply le_of_not_gt
      intro h
      exact hj ⟨he, h⟩
    rw [hb, AddCircle.coe_add_period]

def closedPhase (a : PlanarSpace) (w : Torus → ℝ) : Set PlanarSpace :=
  euclideanClosedBox a ∩ {x | 0 ≤ w (torusQuotient x)}

theorem closedPhase_compact (a : PlanarSpace) {w : Torus → ℝ} (hw : Continuous w) :
    IsCompact (closedPhase a w) :=
  (closedBox_compact a).inter_right
    (isClosed_le continuous_const (hw.comp isOpenQuotientMap_torusQuotient.continuous))

theorem closedPhase_subset_openBox (a : PlanarSpace) {w : Torus → ℝ}
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), w z < 0) :
    closedPhase a w ⊆ euclideanOpenBox a := by
  intro x hx
  by_contra ho
  exact (not_lt_of_ge hx.2) (hc _ (closedBox_boundary_cross a hx.1 ho))

theorem closedPhase_eq_fundamental_preimage (a : PlanarSpace) {w : Torus → ℝ}
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), w z < 0) :
    closedPhase a w = torusQuotient ⁻¹' {z | 0 ≤ w z} ∩ euclideanFundamentalBox a := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hx.2, euclideanOpenBox_subset_fundamentalBox a (closedPhase_subset_openBox a hc hx)⟩
  · intro x hx
    exact ⟨fundamentalBox_subset_closedBox a hx.2, hx.1⟩

theorem closedPhase_volume (a : PlanarSpace) {w : Torus → ℝ} (hw : Continuous w)
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), w z < 0)
    (hzero : torusMeasure {z | w z = 0} = 0) :
    volume (closedPhase a w) = torusMeasure {z | 0 < w z} := by
  have hm : MeasurableSet {z | 0 ≤ w z} := (isClosed_le continuous_const hw).measurableSet
  have hp : MeasurableSet (torusQuotient ⁻¹' {z | 0 ≤ w z}) :=
    isOpenQuotientMap_torusQuotient.continuous.measurable hm
  rw [closedPhase_eq_fundamental_preimage a hc, ← Measure.restrict_apply hp,
    (measurePreserving_torusQuotient_box a).measure_preimage hm.nullMeasurableSet]
  apply measure_congr
  have hn : ∀ᵐ z ∂torusMeasure, w z ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hzero
  filter_upwards [hn] with z hz
  apply propext
  change (0 ≤ w z) ↔ 0 < w z
  exact ⟨fun h ↦ lt_of_le_of_ne h (Ne.symm hz), le_of_lt⟩

/-- The same fixed square contains a positive-width neighborhood of the
closed phase. The width is geometric and independent of later smoothing. -/
theorem exists_phase_thickening (a : PlanarSpace) {w : Torus → ℝ} (hw : Continuous w)
    (hc : ∀ z ∈ coordinateCross (torusQuotient a), w z < 0) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ (closedPhase a w) ⊆ euclideanOpenBox a :=
  (closedPhase_compact a hw).exists_thickening_subset_open (isOpen_euclideanOpenBox a)
    (closedPhase_subset_openBox a hc)

end PeriodicAttractiveLogGas.StationaryCutDomain
