import LeanResearch.PeriodicAttractiveLogGas.CubeProbability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Exact periodic integration on cubes of integer side length. The
one-dimensional identity is proved on indicators before taking products;
no regularity of the subsequently integrated weight is required. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.PeriodicCubeVolume

/-- The quotient of an interval containing an integer number of periods
has exactly that multiple of the original circle Haar measure. -/
theorem map_interval_integer (n : ℕ) (a : ℝ) :
    (volume.restrict (Ioc a (a + (n : ℝ)))).map (fun x : ℝ => (x : UnitAddCircle)) =
      (n : ℝ≥0∞) • AddCircle.haarAddCircle := by
  ext s hs
  have hq : Measurable (fun x : ℝ => (x : UnitAddCircle)) := (UnitAddCircle.measurePreserving_mk a).measurable
  have hsm : Measurable (s.indicator (fun _ : UnitAddCircle => (1 : ℝ))) :=
    measurable_const.indicator hs
  let f : ℝ → ℝ := fun x => s.indicator (fun _ => (1 : ℝ)) (x : UnitAddCircle)
  have hfm : Measurable f := (measurable_const.indicator hs).comp hq
  have hbound (x : ℝ) : ‖f x‖ ≤ (1 : ℝ) := by
    by_cases hx : (x : UnitAddCircle) ∈ s <;> simp [f, hx]
  have hfi (u v : ℝ) : IntervalIntegrable f volume u v :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume u v).mono_fun'
      hfm.aestronglyMeasurable (Eventually.of_forall hbound)
  have hf : Function.Periodic f 1 := by
    intro x
    simp only [f, AddCircle.coe_add_period]
  have hperiod := hf.intervalIntegral_add_zsmul_eq (n : ℤ) a hfi
  have hunit : (∫ x in a..a + 1, f x) = AddCircle.haarAddCircle.real s := by
    rw [intervalIntegral.integral_of_le (by linarith : a ≤ a + 1)]
    have hmp := (UnitAddCircle.measurePreserving_mk a)
    have he := integral_map_of_stronglyMeasurable
      (μ := volume.restrict (Ioc a (a + 1))) hq hsm.stronglyMeasurable
    rw [hmp.map_eq, unitCircle_volume_eq_haar] at he
    simpa only [f, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using! he.symm
  have hmain : (∫ x in Ioc a (a + (n : ℝ)), f x) = (n : ℝ) * AddCircle.haarAddCircle.real s := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, hunit,
      intervalIntegral.integral_of_le (show a ≤ a + (n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])] using hperiod
  have hleft : (∫ x in Ioc a (a + (n : ℝ)), f x) =
      ((volume.restrict (Ioc a (a + (n : ℝ)))).map (fun x : ℝ => (x : UnitAddCircle))).real s := by
    have he := integral_map_of_stronglyMeasurable
      (μ := volume.restrict (Ioc a (a + (n : ℝ)))) hq hsm.stronglyMeasurable
    simpa only [f, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using! he.symm
  have hright : ((n : ℝ≥0∞) • AddCircle.haarAddCircle).real s =
      (n : ℝ) * AddCircle.haarAddCircle.real s := by
    simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (show ((n : ℝ≥0∞) • AddCircle.haarAddCircle) s ≠ ∞ by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _))).mp
  change ((volume.restrict (Ioc a (a + (n : ℝ)))).map (fun x : ℝ => (x : UnitAddCircle))).real s = _
  rw [← hleft, hmain, ← hright]
  rfl

/-- Closing either endpoint does not change the quotient law. -/
theorem map_closed_interval_integer (n : ℕ) (a : ℝ) :
    (volume.restrict (Icc a (a + (n : ℝ)))).map (fun x : ℝ => (x : UnitAddCircle)) =
      (n : ℝ≥0∞) • AddCircle.haarAddCircle := by
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  exact map_interval_integer n a


open CubeProbability PhysicalCubes

def intervalLaw (n : ℕ) (a : ℝ) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • volume.restrict (Icc a (a + (n : ℝ)))

theorem quotient_intervalLaw {n : ℕ} (hn : 0 < n) (a : ℝ) :
    MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (intervalLaw n a) AddCircle.haarAddCircle := by
  have hq := (UnitAddCircle.measurePreserving_mk a).measurable
  refine ⟨hq, ?_⟩
  rw [intervalLaw, Measure.map_smul _ hq.aemeasurable,
    map_closed_interval_integer, smul_smul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by finiteness), one_smul]

theorem intervalLaw_probability {n : ℕ} (hn : 0 < n) (a : ℝ) :
    IsProbabilityMeasure (intervalLaw n a) := by
  constructor
  have hh := (quotient_intervalLaw hn a).measure_preimage MeasurableSet.univ.nullMeasurableSet
  simpa only [preimage_univ, measure_univ] using hh

/-- The independent normalized interval laws are precisely normalized
Lebesgue measure on the planar coordinate square. -/
theorem square_interval_product {n : ℕ} (hn : 0 < n) (c : PlanarSpace) :
    Measure.pi (fun j : Fin 2 => intervalLaw n (c j - (n : ℝ) / 2)) =
      (ENNReal.ofReal ((n : ℝ) ^ 2))⁻¹ •
        Measure.pi (fun j : Fin 2 => volume.restrict
          (Icc (c j - (n : ℝ) / 2) (c j + (n : ℝ) / 2))) := by
  letI : ∀ j : Fin 2, IsProbabilityMeasure (intervalLaw n (c j - (n : ℝ) / 2)) :=
    fun j => intervalLaw_probability hn _
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  have he (j : Fin 2) : c j - (n : ℝ) / 2 + n = c j + (n : ℝ) / 2 := by ring
  simp only [intervalLaw, he, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.inv_pow, ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- The actual Euclidean square law is transported to the independent
coordinate interval laws without changing the volume normalization. -/
theorem squareLaw_coordinates {n : ℕ} (hn : 0 < n) (c : PlanarSpace) :
    MeasurePreserving (fun x : PlanarSpace => WithLp.ofLp x)
      (coordinateLaw c (n : ℝ))
      (Measure.pi fun j : Fin 2 => intervalLaw n (c j - (n : ℝ) / 2)) := by
  let s : Set (Fin 2 → ℝ) := pi univ
    (fun j => Icc (c j - (n : ℝ) / 2) (c j + (n : ℝ) / 2))
  have hs : MeasurableSet s := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hp := (PiLp.volume_preserving_ofLp (Fin 2)).restrict_preimage hs
  rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi] at hp
  have he : WithLp.ofLp ⁻¹' s = cube c (n : ℝ) := rfl
  rw [he] at hp
  refine ⟨hp.measurable, ?_⟩
  rw [coordinateLaw, Measure.map_smul _ hp.measurable.aemeasurable,
    hp.map_eq, square_interval_product hn c]

/-- Every positive integer-side square pushes its normalized Euclidean
volume to the original probability Haar measure of the two-dimensional torus. -/
theorem quotient_squareLaw_integer {n : ℕ} (hn : 0 < n) (c : PlanarSpace) :
    MeasurePreserving torusQuotient (coordinateLaw c (n : ℝ)) torusMeasure := by
  letI : ∀ j : Fin 2, IsProbabilityMeasure (intervalLaw n (c j - (n : ℝ) / 2)) :=
    fun j => intervalLaw_probability hn _
  have hh := measurePreserving_pi
    (fun j : Fin 2 => intervalLaw n (c j - (n : ℝ) / 2))
    (fun _ : Fin 2 => AddCircle.haarAddCircle) (fun j => quotient_intervalLaw hn _)
  exact hh.comp (squareLaw_coordinates hn c)

theorem quotient_productLaw_integer (k : ℕ) {n : ℕ} (hn : 0 < n)
    (c : Fin k → PlanarSpace) :
    MeasurePreserving (planarConfigurationQuotient k)
      (productLaw k c (n : ℝ)) (referenceMeasure k) := by
  letI : ∀ i : Fin k, IsProbabilityMeasure (coordinateLaw (c i) (n : ℝ)) :=
    fun i => coordinateLaw_probability (c i) (by exact_mod_cast hn)
  exact measurePreserving_pi (fun i : Fin k => coordinateLaw (c i) (n : ℝ))
    (fun _ : Fin k => torusMeasure) (fun i => quotient_squareLaw_integer hn (c i))

/-- Exact periodic averaging for any measurable function. Integrability
is not silently inferred from this totalized integral identity. -/
theorem integral_productLaw_integer (k : ℕ) {n : ℕ} (hn : 0 < n)
    (c : Fin k → PlanarSpace) (F : Configuration k → ℝ) (hF : Measurable F) :
    (∫ X, F (planarConfigurationQuotient k X) ∂productLaw k c (n : ℝ)) =
      ∫ Z, F Z ∂referenceMeasure k := by
  have hp := quotient_productLaw_integer k hn c
  have hh := integral_map_of_stronglyMeasurable
    (μ := productLaw k c (n : ℝ)) hp.measurable hF.stronglyMeasurable
  rw [hp.map_eq] at hh
  exact hh.symm

theorem integral_cube_integer (k : ℕ) {n : ℕ} (hn : 0 < n)
    (c : Fin k → PlanarSpace) (F : Configuration k → ℝ) (hF : Measurable F) :
    (∫ X in particleCube k c (n : ℝ), F (planarConfigurationQuotient k X)) =
      (n : ℝ) ^ (2 * k) * ∫ Z, F Z ∂referenceMeasure k := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := integral_productLaw_integer k hn c F hF
  rw [integral_productLaw k c hnr, smul_eq_mul] at hh
  have hmul := congrArg (fun y : ℝ => (n : ℝ) ^ (2 * k) * y) hh
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hnr.ne'), one_mul] at hmul
  exact hmul

end PeriodicAttractiveLogGas.PeriodicCubeVolume
