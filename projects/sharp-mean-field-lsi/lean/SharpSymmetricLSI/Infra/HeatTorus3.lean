import SharpSymmetricLSI.Infra.HeatTorus2

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 3): `heatT` as a torus convolution

The image of the Gaussian `G_t(y) dy` under `liftT` is the measure `P_t(z) dz`
(`map_gauss_eq`), by uniqueness of Fourier coefficients. Hence
`heatT t f x = ∫ P_t(z) f(x - z) dz` (`heatT_eq`), and:
mass conservation, `L¹` and `L^∞` contraction, positivity with a lower bound.
-/

open MeasureTheory Set Filter Topology UnitAddTorus
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

instance isNegInvariant_volume_torus : (volume : Measure (UnitAddTorus ι)).IsNegInvariant :=
  Pi.isNegInvariant_volume

theorem heatMult_neg (t : ℝ) (k : ι → ℤ) : heatMult t (-k) = heatMult t k := by
  unfold heatMult; simp

/-- The Gaussian `G_t(y) dy` on `ℝ^ι`. -/
noncomputable def gaussMeasure (t : ℝ) : Measure (ι → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (heatKernel t y)

/-- The kernel measure `P_t(z) dz` on `𝕋^ι`. -/
noncomputable def heatMeasure (t : ℝ) : Measure (UnitAddTorus ι) :=
  volume.withDensity fun z => ENNReal.ofReal (heatP t z)

theorem measurable_heatKernel (t : ℝ) : Measurable (heatKernel (ι := ι) t) := by
  unfold heatKernel; fun_prop

theorem gaussMeasure_univ {t : ℝ} (ht : 0 < t) : gaussMeasure (ι := ι) t univ = 1 := by
  rw [gaussMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel ht)
      (Eventually.of_forall fun y => (heatKernel_pos ht y).le), integral_heatKernel ht,
    ENNReal.ofReal_one]

instance {t : ℝ} [Fact (0 < t)] : IsProbabilityMeasure (gaussMeasure (ι := ι) t) :=
  ⟨gaussMeasure_univ Fact.out⟩

theorem integral_gaussMeasure {t : ℝ} (ht : 0 < t) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : (ι → ℝ) → E) :
    ∫ y, g y ∂gaussMeasure t = ∫ y, heatKernel t y • g y := by
  rw [gaussMeasure]
  have hm : Measurable fun y => (heatKernel (ι := ι) t y).toNNReal :=
    (measurable_heatKernel t).real_toNNReal
  change ∫ y, g y ∂(volume.withDensity fun y => ((heatKernel t y).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hm]
  congr 1; funext y
  rw [NNReal.smul_def, Real.coe_toNNReal _ (heatKernel_pos ht y).le]

theorem integral_heatMeasure {t : ℝ} (ht : 0 < t) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : UnitAddTorus ι → E) :
    ∫ z, g z ∂heatMeasure t = ∫ z, heatP t z • g z := by
  rw [heatMeasure]
  have hm : Measurable fun z => (heatP (ι := ι) t z).toNNReal :=
    (measurable_heatP ht).real_toNNReal
  change ∫ z, g z ∂(volume.withDensity fun z => ((heatP t z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hm]
  congr 1; funext z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (heatP_pos ht z).le]

theorem integrable_heatP {t : ℝ} (ht : 0 < t) : Integrable (heatP (ι := ι) t) :=
  (continuous_heatP ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem isFiniteMeasure_heatMeasure {t : ℝ} (ht : 0 < t) :
    IsFiniteMeasure (heatMeasure (ι := ι) t) :=
  isFiniteMeasure_withDensity_ofReal (integrable_heatP ht).2

/-- The image of the Gaussian under `liftT` is the kernel measure. -/
theorem map_gauss_eq {t : ℝ} (ht : 0 < t) :
    (gaussMeasure (ι := ι) t).map liftT = heatMeasure t := by
  have : Fact (0 < t) := ⟨ht⟩
  have : IsFiniteMeasure ((gaussMeasure (ι := ι) t).map liftT) := inferInstance
  have := isFiniteMeasure_heatMeasure (ι := ι) ht
  refine measure_eq_of_mFourier fun k => ?_
  rw [integral_map measurable_liftT.aemeasurable (mFourier k).continuous.aestronglyMeasurable,
    integral_gaussMeasure ht, integral_heatMeasure ht]
  have h1 := gauss_fourier (ι := ι) ht (-k)
  have h2 := heatP_fourier (ι := ι) ht (-k)
  rw [neg_neg] at h1 h2
  simp only [Complex.real_smul]
  rw [h1, h2]

/-- **`heatT` is convolution with the torus kernel.** -/
theorem heatT_eq {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) (x : UnitAddTorus ι) :
    heatT t f x = ∫ z, heatP t z * f (x - z) := by
  have hf' : AEStronglyMeasurable (fun z => f (x - z)) (heatMeasure (ι := ι) t) := by
    have : AEStronglyMeasurable (fun z => f (x - z)) volume :=
      hf.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    exact this.mono_ac (withDensity_absolutelyContinuous _ _)
  calc heatT t f x = ∫ y, heatKernel t y • f (x - liftT y) := by
        rw [heatT]; simp_rw [smul_eq_mul, mul_comm]
    _ = ∫ y, f (x - liftT y) ∂gaussMeasure t := (integral_gaussMeasure ht _).symm
    _ = ∫ z, f (x - z) ∂(gaussMeasure t).map liftT :=
        (integral_map measurable_liftT.aemeasurable (by rwa [map_gauss_eq (ι := ι) ht])).symm
    _ = ∫ z, f (x - z) ∂heatMeasure t := by rw [map_gauss_eq (ι := ι) ht]
    _ = ∫ z, heatP t z * f (x - z) := by rw [integral_heatMeasure ht]; simp_rw [smul_eq_mul]

/-- The same, with the kernel on the other factor. -/
theorem heatT_eq' {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) (x : UnitAddTorus ι) :
    heatT t f x = ∫ z, f z * heatP t (x - z) := by
  rw [heatT_eq ht hf]
  have := integral_sub_left_eq_self (fun z => f (x - z) * heatP t z)
    (volume : Measure (UnitAddTorus ι)) x
  simp only [sub_sub_cancel] at this
  simp_rw [mul_comm (heatP t _)]
  exact this.symm

theorem integral_heatP {t : ℝ} (ht : 0 < t) : ∫ z : UnitAddTorus ι, heatP t z = 1 := by
  have h := heatP_fourier (ι := ι) ht 0
  simp only [neg_zero, mFourier_zero, ContinuousMap.one_apply, mul_one, heatMult, Pi.zero_apply,
    Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
    Real.exp_zero, Finset.prod_const_one, Complex.ofReal_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem heatP_measurePreserving_integrable {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι => heatP t p.2 * f (p.1 - p.2))
      (volume.prod volume) := by
  obtain ⟨M, hM⟩ := heatP_bdd (ι := ι) ht
  have hsub : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι => f (p.1 - p.2))
      (volume.prod volume) := by
    have hmp : MeasurePreserving (fun p : UnitAddTorus ι × UnitAddTorus ι => (p.1 - p.2, p.2))
        (volume.prod volume) (volume.prod volume) :=
      measurePreserving_sub_prod volume volume
    exact hmp.integrable_comp_of_integrable
      (hf.comp_fst (ν := (volume : Measure (UnitAddTorus ι))))
  refine hsub.bdd_mul (c := M) ((measurable_heatP ht).comp measurable_snd).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]; exact hM _

/-- **Mass conservation.** -/
theorem integral_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Integrable f) :
    ∫ x, heatT t f x = ∫ x, f x := by
  simp_rw [heatT_eq ht hf.aestronglyMeasurable]
  rw [integral_integral_swap (heatP_measurePreserving_integrable ht hf)]
  have : ∀ z : UnitAddTorus ι, ∫ x, heatP t z * f (x - z) = heatP t z * ∫ x, f x := by
    intro z
    rw [integral_const_mul, integral_sub_right_eq_self]
  simp_rw [this]
  rw [integral_mul_const, integral_heatP ht, one_mul]

theorem integrable_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Integrable f) :
    Integrable (heatT t f) := by
  have := (heatP_measurePreserving_integrable ht hf).integral_prod_left
  refine this.congr (Eventually.of_forall fun x => ?_)
  exact (heatT_eq ht hf.aestronglyMeasurable x).symm

/-- **`L¹` contraction.** -/
theorem integral_abs_heatT_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : Integrable f) : ∫ x, |heatT t f x| ≤ ∫ x, |f x| := by
  have h1 : ∀ x, |heatT t f x| ≤ heatT t (fun y => |f y|) x := by
    intro x
    rw [heatT_eq ht hf.aestronglyMeasurable, heatT_eq ht hf.abs.aestronglyMeasurable]
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1; funext z
    rw [abs_mul, abs_of_pos (heatP_pos ht z)]
  calc ∫ x, |heatT t f x| ≤ ∫ x, heatT t (fun y => |f y|) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_heatT ht hf.abs) (Eventually.of_forall h1)
    _ = ∫ x, |f x| := integral_heatT ht hf.abs

/-- **Positivity**, with the lower bound `heatT t f ≥ c_t ∫ f` for `f ≥ 0`. -/
theorem heatT_lower {t : ℝ} (ht : 0 < t) :
    ∃ c > 0, ∀ f : UnitAddTorus ι → ℝ, Integrable f → (∀ᵐ y, 0 ≤ f y) →
      ∀ x, c * ∫ y, f y ≤ heatT t f x := by
  obtain ⟨c, hc, hle⟩ := heatP_lower (ι := ι) ht
  refine ⟨c, hc, fun f hf hf0 x => ?_⟩
  rw [heatT_eq' ht hf.aestronglyMeasurable, ← integral_const_mul]
  refine integral_mono_ae (hf.const_mul c) ?_ ?_
  · have hb := heatP_bdd (ι := ι) ht
    obtain ⟨M, hM⟩ := hb
    refine hf.bdd_mul (c := M)
      ((measurable_heatP ht).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_) |>.congr (Eventually.of_forall fun z => mul_comm _ _)
    rw [Real.norm_eq_abs]; exact hM _
  · filter_upwards [hf0] with z hz
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hle _) hz

/-- **`L^∞` contraction.** -/
theorem abs_heatT_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : ∀ᵐ y, |f y| ≤ B) (x : UnitAddTorus ι) :
    |heatT t f x| ≤ B := by
  rw [heatT_eq' ht hf]
  have hB' : ∀ᵐ z, |f z * heatP t (x - z)| ≤ B * heatP t (x - z) := by
    filter_upwards [hB] with z hz
    rw [abs_mul, abs_of_pos (heatP_pos ht _)]
    exact mul_le_mul_of_nonneg_right hz (heatP_pos ht _).le
  have hint : Integrable fun z => heatP (ι := ι) t (x - z) :=
    (integrable_heatP ht).comp_sub_left x
  calc |∫ z, f z * heatP t (x - z)| ≤ ∫ z, |f z * heatP t (x - z)| := abs_integral_le_integral_abs
    _ ≤ ∫ z, B * heatP t (x - z) := by
        by_cases hi : Integrable fun z => |f z * heatP t (x - z)|
        · exact integral_mono_ae hi (hint.const_mul B) hB'
        · rw [integral_undef hi]
          have : 0 ≤ ∫ z, B * heatP t (x - z) := by
            have h0 : ∀ᵐ z, 0 ≤ B * heatP t (x - z) := by
              filter_upwards [hB] with z hz
              exact mul_nonneg ((abs_nonneg _).trans hz) (heatP_pos ht _).le
            exact integral_nonneg_of_ae h0
          exact this
    _ = B := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun z => heatP (ι := ι) t z),
          integral_heatP ht, mul_one]

end SharpLSI
