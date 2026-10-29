import SharpSymmetricLSI.Infra.TorusLift

/-!
# Periodic functions on `ℝ^ι` and the torus (Phase 2, I1)

* `lintegral_shiftBox`: the integral of a lifted function over an integer translate of the unit
  box equals its torus integral.
* `lintegral_cube_le`: over the cube `[-R,R]^ι` the lifted integral is at most `(2R+2)^|ι|` times
  the torus integral.
* `quasiMeasurePreserving_liftT`: `liftT` pulls back Haar-null sets to Lebesgue-null sets;
  hence `ae_liftT_of_ae`, and lifts of torus `L¹` functions are locally integrable
  (`locallyIntegrable_comp_liftT`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

/-- An integer vector as a real vector. -/
def intVec (m : ι → ℤ) : ι → ℝ := fun i => (m i : ℝ)

omit [Fintype ι] in
theorem liftT_add_intVec (x : ι → ℝ) (m : ι → ℤ) : liftT (x + intVec m) = liftT x := by
  funext i; simp [liftT, intVec]

/-- The translate `m + (0,1]^ι` of the unit box. -/
def shiftBox (m : ι → ℤ) : Set (ι → ℝ) := (fun x => x - intVec m) ⁻¹' unitBox ι

omit [Fintype ι] in
theorem mem_shiftBox {m : ι → ℤ} {x : ι → ℝ} :
    x ∈ shiftBox m ↔ ∀ i, (m i : ℝ) < x i ∧ x i ≤ m i + 1 := by
  simp only [shiftBox, unitBox, mem_preimage, mem_pi, mem_univ, true_implies, mem_Ioc,
    Pi.sub_apply, intVec]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

omit [Fintype ι] in
theorem shiftBox_eq_ceil {m : ι → ℤ} {x : ι → ℝ} (hx : x ∈ shiftBox m) (i : ι) :
    m i = ⌈x i⌉ - 1 := by
  have := (mem_shiftBox.mp hx) i
  have : ⌈x i⌉ = m i + 1 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  omega

theorem measurableSet_shiftBox (m : ι → ℤ) : MeasurableSet (shiftBox m) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ioc).preimage (measurable_id.sub_const _)

theorem lintegral_shiftBox (m : ι → ℤ) {H : UnitAddTorus ι → ℝ≥0∞}
    (hH : AEMeasurable H volume) :
    ∫⁻ x in shiftBox m, H (liftT x) = ∫⁻ y, H y := by
  rw [← lintegral_indicator (measurableSet_shiftBox m),
    ← lintegral_add_right_eq_self (μ := volume) _ (intVec m)]
  have : ∀ z : ι → ℝ, (shiftBox m).indicator (fun x => H (liftT x)) (z + intVec m) =
      (unitBox ι).indicator (fun x => H (liftT x)) z := by
    intro z
    have hm : z + intVec m ∈ shiftBox m ↔ z ∈ unitBox ι := by
      unfold shiftBox; rw [Set.mem_preimage, add_sub_cancel_right]
    simp only [indicator, liftT_add_intVec]
    split_ifs <;> simp_all
  simp_rw [this]
  rw [lintegral_indicator (show MeasurableSet (unitBox ι) from
      MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
    ← lintegral_map' (by rwa [(measurePreserving_liftT (ι := ι)).map_eq])
      measurable_liftT.aemeasurable, (measurePreserving_liftT (ι := ι)).map_eq]

/-- The cube `[-R,R]^ι`. -/
def cube (ι : Type*) (R : ℝ) : Set (ι → ℝ) := univ.pi fun _ => Icc (-R) R

theorem lintegral_cube_le (R : ℕ) {H : UnitAddTorus ι → ℝ≥0∞} (hH : AEMeasurable H volume) :
    ∫⁻ x in cube ι R, H (liftT x) ≤ ((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ y, H y := by
  classical
  set S : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ) - 1) R with hS
  have hsub : cube ι R ⊆ ⋃ m ∈ S, shiftBox m := by
    intro x hx
    simp only [cube, mem_pi, mem_univ, true_implies, mem_Icc] at hx
    refine mem_biUnion (x := fun i => ⌈x i⌉ - 1) ?_ ?_
    · simp only [hS, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have h1 := Int.le_ceil (x i)
      have h2 := Int.ceil_lt_add_one (x i)
      have h3 : ⌈x i⌉ ≤ (R : ℤ) := Int.ceil_le.mpr (by exact_mod_cast (hx i).2)
      have h4 : -(R : ℤ) ≤ ⌈x i⌉ := by
        have : (-(R : ℝ)) ≤ ⌈x i⌉ := le_trans (hx i).1 h1
        exact_mod_cast this
      constructor <;> omega
    · rw [mem_shiftBox]
      intro i
      have h1 := Int.le_ceil (x i)
      have h2 := Int.ceil_lt_add_one (x i)
      push_cast
      constructor <;> linarith
  have hdisj : Set.PairwiseDisjoint (↑S) (shiftBox (ι := ι)) := by
    intro m _ m' _ hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    funext i
    rw [shiftBox_eq_ceil hx i, shiftBox_eq_ceil hx' i]
  calc ∫⁻ x in cube ι R, H (liftT x) ≤ ∫⁻ x in ⋃ m ∈ S, shiftBox m, H (liftT x) :=
        lintegral_mono_set hsub
    _ = ∑ m ∈ S, ∫⁻ x in shiftBox m, H (liftT x) :=
        lintegral_biUnion_finset hdisj (fun m _ => measurableSet_shiftBox m) _
    _ = ∑ m ∈ S, ∫⁻ y, H y := Finset.sum_congr rfl fun m _ => lintegral_shiftBox m hH
    _ = (S.card : ℝ≥0∞) * ∫⁻ y, H y := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        rw [hS, Fintype.card_piFinset]
        simp only [Finset.prod_const, Finset.card_univ, Int.card_Icc]
        apply le_of_eq
        have : ((R : ℤ) + 1 - (-(R : ℤ) - 1)).toNat = 2 * R + 2 := by omega
        rw [this, Nat.cast_pow]

/-- `liftT` pulls back Haar-null sets to Lebesgue-null sets. -/
theorem quasiMeasurePreserving_liftT :
    Measure.QuasiMeasurePreserving (liftT (ι := ι)) (volume : Measure (ι → ℝ))
      (volume : Measure (UnitAddTorus ι)) := by
  refine ⟨measurable_liftT, Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_⟩
  rw [Measure.map_apply measurable_liftT hN]
  have hcov : liftT ⁻¹' N ⊆ ⋃ R : ℕ, (cube ι R ∩ liftT ⁻¹' N) := by
    intro x hx
    obtain ⟨R, hR⟩ := exists_nat_ge (∑ i, |x i|)
    refine mem_iUnion.mpr ⟨R, ⟨?_, hx⟩⟩
    simp only [cube, mem_pi, mem_univ, true_implies, mem_Icc]
    intro i
    have : |x i| ≤ R := le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (x j))
      (Finset.mem_univ i)) hR
    exact abs_le.mp this
  refine measure_mono_null hcov (measure_iUnion_null fun R => ?_)
  have h := lintegral_cube_le (ι := ι) R (H := N.indicator 1)
    ((measurable_one.indicator hN).aemeasurable)
  rw [lintegral_indicator_one hN, h0, mul_zero, nonpos_iff_eq_zero] at h
  rw [← h]
  have e : (fun x => N.indicator 1 (liftT x)) = (liftT ⁻¹' N).indicator (1 : (ι → ℝ) → ℝ≥0∞) := by
    funext x; simp only [indicator]; split_ifs <;> simp_all
  rw [e, lintegral_indicator_one (hN.preimage measurable_liftT),
    Measure.restrict_apply (hN.preimage measurable_liftT), inter_comm]

theorem ae_liftT_of_ae {p : UnitAddTorus ι → Prop} (h : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)),
    p y) : ∀ᵐ x ∂(volume : Measure (ι → ℝ)), p (liftT x) :=
  quasiMeasurePreserving_liftT.ae h

/-- The lift of a torus `L¹` function is locally integrable. -/
theorem locallyIntegrable_comp_liftT {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    LocallyIntegrable (u ∘ liftT) (volume : Measure (ι → ℝ)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := (hK.isBounded.subset_closedBall 0).imp fun r h => h
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hKc : K ⊆ cube ι n := by
    intro x hx
    have := hR hx
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    simp only [cube, mem_pi, mem_univ, true_implies, mem_Icc]
    intro i
    have := (norm_le_pi_norm x i).trans (this.trans hn)
    rw [Real.norm_eq_abs] at this
    exact abs_le.mp this
  refine ⟨hu.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_liftT |>.restrict, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_set hKc) ?_
  refine lt_of_le_of_lt (lintegral_cube_le (H := fun y => ‖u y‖ₑ) n
    hu.aestronglyMeasurable.enorm) ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)).lt_top hu.2

end SharpLSI
