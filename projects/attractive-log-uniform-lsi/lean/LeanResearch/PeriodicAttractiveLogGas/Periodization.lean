import LeanResearch.PeriodicAttractiveLogGas.TorusLocalGeometry
import LeanResearch.PeriodicAttractiveLogGas.HarmonicMollification
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.BigOperators.Finprod

/-! Periodization of compactly supported Euclidean tests by a locally finite
integer-lattice sum. This will transport arbitrary local tests to the torus. -/

noncomputable section
open MeasureTheory Set Filter Metric
open InnerProductSpace
open scoped Topology ContDiff Laplacian

namespace PeriodicAttractiveLogGas

@[simp] theorem frequencyVector_add (k l : Frequency) :
    frequencyVector (k + l) = frequencyVector k + frequencyVector l := by
  ext j
  simp

theorem finite_frequencyVector_norm_le (R : ℝ) :
    Set.Finite {k : Frequency | ‖frequencyVector k‖ ≤ R} := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hfin := ZSpan.setFinite_inter b (s := closedBall (0 : PlanarSpace) R)
    isBounded_closedBall
  have hpre := Set.Finite.preimage frequencyVector_injective.injOn hfin
  refine hpre.subset fun k hk ↦ ⟨mem_closedBall_zero_iff.mpr hk, ?_⟩
  apply (b.mem_span_iff_repr_mem ℤ (frequencyVector k)).2
  intro j
  refine ⟨k j, ?_⟩
  simp [b]

theorem locallyFinite_integer_translates {f : PlanarSpace → ℝ} (hc : HasCompactSupport f) :
    LocallyFinite (fun k : Frequency ↦ Function.support (fun x ↦ f (x + frequencyVector k))) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
  refine (finite_frequencyVector_norm_le (R + ‖x‖ + 1)).subset ?_
  rintro k ⟨y, hyf, hyx⟩
  have hfR : ‖y + frequencyVector k‖ ≤ R :=
    mem_closedBall_zero_iff.mp (hR (subset_closure hyf))
  have hy : ‖y‖ ≤ ‖x‖ + 1 := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel] at ht
    have hd : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hyx
    linarith
  have ht := norm_sub_le (y + frequencyVector k) y
  have heq : y + frequencyVector k - y = frequencyVector k := by abel
  rw [heq] at ht
  exact le_trans ht (by linarith)

def periodicSum (f : PlanarSpace → ℝ) (x : PlanarSpace) : ℝ :=
  ∑ᶠ k : Frequency, f (x + frequencyVector k)

theorem contDiff_periodicSum {f : PlanarSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (periodicSum f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum (locallyFinite_integer_translates hc) x
  have hsum : ContDiff ℝ ∞ (fun y : PlanarSpace ↦ ∑ k ∈ s, f (y + frequencyVector k)) :=
    ContDiff.sum (fun k _ ↦ hf.comp (contDiff_id.add contDiff_const))
  exact hsum.contDiffAt.congr_of_eventuallyEq hs

theorem periodicSum_add_frequencyVector (f : PlanarSpace → ℝ) (x : PlanarSpace)
    (m : Frequency) : periodicSum f (x + frequencyVector m) = periodicSum f x := by
  unfold periodicSum
  have h := finsum_comp_equiv (Equiv.addLeft m) (f := fun k ↦ f (x + frequencyVector k))
  change (∑ᶠ k : Frequency, f (x + frequencyVector (m + k))) = _ at h
  simpa only [frequencyVector_add, add_assoc] using h

theorem isOpenQuotientMap_torusQuotient : IsOpenQuotientMap torusQuotient := by
  let e : PlanarSpace ≃ₜ (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
  have hc : IsOpenQuotientMap (fun t : ℝ ↦ (t : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  exact (IsOpenQuotientMap.piMap (fun _ : Fin 2 ↦ hc)).comp e.isOpenQuotientMap

theorem torusQuotient_surjective : Function.Surjective torusQuotient :=
  isOpenQuotientMap_torusQuotient.surjective

@[simp] theorem torusQuotient_zero : torusQuotient (0 : PlanarSpace) = (0 : Torus) := by
  ext j
  rfl

theorem exists_frequencyVector_of_torusQuotient_eq {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) :
    ∃ m : Frequency, y = x + frequencyVector m := by
  have hj (j : Fin 2) : ∃ n : ℤ, (n : ℝ) = y j - x j := by
    have h := congrFun hxy j
    change (x j : UnitAddCircle) = (y j : UnitAddCircle) at h
    have hz : ((y j - x j : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, ← h, sub_self]
    simpa using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  choose m hm using hj
  refine ⟨m, ?_⟩
  ext j
  simp only [PiLp.add_apply, frequencyVector_apply]
  linarith [hm j]

theorem periodicSum_eq_of_torusQuotient_eq (f : PlanarSpace → ℝ) {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) : periodicSum f x = periodicSum f y := by
  obtain ⟨m, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  exact (periodicSum_add_frequencyVector f x m).symm

def torusPeriodization (f : PlanarSpace → ℝ) (z : Torus) : ℝ :=
  periodicSum f (Classical.choose (torusQuotient_surjective z))

@[simp] theorem torusPeriodization_lift (f : PlanarSpace → ℝ) (x : PlanarSpace) :
    torusPeriodization f (torusQuotient x) = periodicSum f x := by
  apply periodicSum_eq_of_torusQuotient_eq
  exact Classical.choose_spec (torusQuotient_surjective (torusQuotient x))

theorem continuous_torusPeriodization {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Continuous (torusPeriodization f) := by
  apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, torusPeriodization_lift] using
    (contDiff_periodicSum hf hc).continuous

def periodizedTest (f : PlanarSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : C(Torus, ℝ) :=
  ⟨torusPeriodization f, continuous_torusPeriodization hf hc⟩

@[simp] theorem periodizedTest_lift (f : PlanarSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : PlanarSpace) :
    periodizedTest f hf hc (torusQuotient x) = periodicSum f x :=
  torusPeriodization_lift f x

theorem contDiff_lift_periodizedTest (f : PlanarSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun x ↦ periodizedTest f hf hc (torusQuotient x)) := by
  simpa only [periodizedTest_lift] using contDiff_periodicSum hf hc

@[simp] theorem torusQuotient_add_frequencyVector (x : PlanarSpace) (k : Frequency) :
    torusQuotient (x + frequencyVector k) = torusQuotient x := by
  ext j
  change ((x j + (k j : ℝ) : ℝ) : UnitAddCircle) = (x j : UnitAddCircle)
  have hz : ((k j : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k j, by simp⟩
  rw [AddCircle.coe_add, hz, add_zero]

theorem injOn_torusQuotient_box (a : PlanarSpace) :
    Set.InjOn torusQuotient (euclideanFundamentalBox a) := by
  intro x hx y hy hxy
  ext j
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hx j (mem_univ j))
    (hy j (mem_univ j))).mp (congrFun hxy j)

/-- A test supported inside one fundamental box agrees there with its periodization. -/
theorem periodicSum_eq_on_box {f : PlanarSpace → ℝ} {a : PlanarSpace}
    (hf : tsupport f ⊆ euclideanFundamentalBox a) {x : PlanarSpace}
    (hx : x ∈ euclideanFundamentalBox a) : periodicSum f x = f x := by
  unfold periodicSum
  have hzero (k : Frequency) (hk : k ≠ 0) : f (x + frequencyVector k) = 0 := by
    by_contra hn
    have hy := hf (subset_tsupport f hn)
    have heq : x + frequencyVector k = x :=
      injOn_torusQuotient_box a hy hx (torusQuotient_add_frequencyVector x k)
    have hv : frequencyVector k = frequencyVector 0 := by
      simpa using congrArg (fun z : PlanarSpace ↦ z - x) heq
    exact hk (frequencyVector_injective hv)
  simpa using finsum_eq_single (fun k : Frequency ↦ f (x + frequencyVector k)) 0 hzero

theorem periodicSum_eventuallyEq {f : PlanarSpace → ℝ} {a x : PlanarSpace}
    (hf : tsupport f ⊆ euclideanFundamentalBox a)
    (ha : ∀ j, a j < x j) (hb : ∀ j, x j < a j + 1) :
    periodicSum f =ᶠ[𝓝 x] f := by
  filter_upwards [euclideanFundamentalBox_mem_nhds a x ha hb] with y hy
  exact periodicSum_eq_on_box hf hy

def euclideanOpenBox (a : PlanarSpace) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j : Fin 2 ↦ Ioo (a j) (a j + 1))

theorem isOpen_euclideanOpenBox (a : PlanarSpace) : IsOpen (euclideanOpenBox a) :=
  (isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)).preimage
    (EuclideanSpace.equiv (Fin 2) ℝ).continuous

theorem euclideanOpenBox_subset_fundamentalBox (a : PlanarSpace) :
    euclideanOpenBox a ⊆ euclideanFundamentalBox a := by
  intro x hx j hj
  exact ⟨(hx j hj).1, (hx j hj).2.le⟩

def centeredBoxAnchor (x : PlanarSpace) : PlanarSpace :=
  WithLp.toLp 2 (fun j ↦ x j - 1 / 2)

theorem mem_centeredOpenBox (x : PlanarSpace) :
    x ∈ euclideanOpenBox (centeredBoxAnchor x) := by
  intro j _
  change x j - 1 / 2 < x j ∧ x j < x j - 1 / 2 + 1
  constructor <;> linarith

theorem measurableSet_euclideanFundamentalBox (a : PlanarSpace) :
    MeasurableSet (euclideanFundamentalBox a) :=
  (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioc)).preimage
    (EuclideanSpace.equiv (Fin 2) ℝ).continuous.measurable

theorem measurableSet_euclideanOpenBox (a : PlanarSpace) :
    MeasurableSet (euclideanOpenBox a) :=
  (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo)).preimage
    (EuclideanSpace.equiv (Fin 2) ℝ).continuous.measurable

theorem euclideanOpenBox_ae_eq_fundamentalBox (a : PlanarSpace) :
    euclideanOpenBox a =ᵐ[volume] euclideanFundamentalBox a := by
  have hp : (Set.pi Set.univ (fun j : Fin 2 ↦ Ioo (a j) (a j + 1))) =ᵐ[volume]
      (Set.pi Set.univ (fun j : Fin 2 ↦ Ioc (a j) (a j + 1))) :=
    Measure.pi_Ioo_ae_eq_pi_Ioc
  exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.preimage_ae_eq hp

theorem ae_strict_mem_fundamentalBox (a : PlanarSpace) :
    ∀ᵐ x ∂volume.restrict (euclideanFundamentalBox a),
      ∀ j, a j < x j ∧ x j < a j + 1 := by
  rw [← Measure.restrict_congr_set (euclideanOpenBox_ae_eq_fundamentalBox a)]
  filter_upwards [ae_restrict_mem (measurableSet_euclideanOpenBox a)] with x hx j
  exact hx j (mem_univ j)

/-- The torus operator agrees with the ordinary Euclidean Laplacian. -/
theorem torusNegativeLaplacian_lift_eq (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) (x : PlanarSpace) :
    torusNegativeLaplacian f hf (torusQuotient x) =
      -Δ (fun y ↦ f (torusQuotient y)) x := by
  rw [torusNegativeLaplacian_lift, laplacian_eq_sum_planarDirectionalDeriv hf]
  simp only [planarDirectionalDeriv, EuclideanSpace.basisFun_apply]
  rfl

theorem periodizedTest_negativeLaplacian_ae {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {a : PlanarSpace}
    (hs : tsupport f ⊆ euclideanFundamentalBox a) :
    (fun x ↦ torusNegativeLaplacian (periodizedTest f hf hc)
      (contDiff_lift_periodizedTest f hf hc) (torusQuotient x)) =ᵐ[
        volume.restrict (euclideanFundamentalBox a)] fun x ↦ -Δ f x := by
  filter_upwards [ae_strict_mem_fundamentalBox a] with x hx
  rw [torusNegativeLaplacian_lift_eq]
  have heq : (fun y ↦ periodizedTest f hf hc (torusQuotient y)) = periodicSum f :=
    funext (periodizedTest_lift f hf hc)
  rw [heq]
  exact congrArg Neg.neg (laplacian_congr_nhds
    (periodicSum_eventuallyEq hs (fun j ↦ (hx j).1) (fun j ↦ (hx j).2))).eq_of_nhds

theorem integral_periodizedTest {f : PlanarSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {a : PlanarSpace}
    (hs : tsupport f ⊆ euclideanFundamentalBox a) :
    (∫ z, periodizedTest f hf hc z ∂torusMeasure) = ∫ x, f x := by
  calc
    (∫ z, periodizedTest f hf hc z ∂torusMeasure) =
        ∫ x in euclideanFundamentalBox a, periodizedTest f hf hc (torusQuotient x) :=
      (integral_torus_lift_on_box (memLp_one_iff_integrable.mp
        (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ (periodizedTest f hf hc))) a).symm
    _ = ∫ x in euclideanFundamentalBox a, f x := by
      apply setIntegral_congr_fun (measurableSet_euclideanFundamentalBox a)
      intro x hx
      exact (periodizedTest_lift f hf hc x).trans (periodicSum_eq_on_box hs hx)
    _ = ∫ x, f x := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

end PeriodicAttractiveLogGas
