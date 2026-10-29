import LeanResearch.PeriodicAttractiveLogGas.GreenConditionalInfluence
import LeanResearch.PeriodicAttractiveLogGas.DensityMoments

/-! Source Proposition 3.11: quantitative moments of the actual Euclidean
Green gradient under normalized patch reference measures and actual one-site
laws. The pole moment is proved before the Holder transfer. SOURCE_ONLY.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.GreenGradientMoments

open MeshCells MeshAdjacentCells GreenPointWeights GreenFarOscillation
  GreenPointRescaling ConditionalParameters SingularRectangleMoments
  GreenConditionalInfluence LabelOccupations OneCoordinateConditionals

def momentFactor (u : ℝ) : ℝ := (1 + 2 * Real.pi / (2 - u)) ^ (1 / u)

theorem momentFactor_nonneg {u : ℝ} (hu : u < 2) : 0 ≤ momentFactor u := by
  have hd : 0 < 2 - u := sub_pos.mpr hu
  exact Real.rpow_nonneg (by positivity) _

theorem momentFactor_four_thirds :
    momentFactor (4 / 3 : ℝ) = (1 + 3 * Real.pi) ^ (3 / 4 : ℝ) := by
  unfold momentFactor
  congr 1 <;> norm_num
  ring

theorem momentFactor_sixteen_ninths :
    momentFactor (16 / 9 : ℝ) = (1 + 9 * Real.pi) ^ (9 / 16 : ℝ) := by
  unfold momentFactor
  congr 1 <;> norm_num
  ring

theorem measurable_shiftedGradient (y : Torus) :
    Measurable (fun z ↦ greenGradient (z - y)) :=
  measurable_greenGradient.comp (measurable_id.sub measurable_const)

/-- Ordinary Green gradient and exact Euclidean radius in a half-period
chart. The pole is explicitly excluded; its later removal is measure theoretic. -/
theorem norm_greenGradient_chart_sub_le (A : PlanarSpace) {J D C₁ : ℝ}
    (hJ : 0 < J) (hD : D < J / 2) (hk : KernelGradientBound C₁)
    {Y Z : PlanarSpace} (hne : Z ≠ Y) (hd : ‖Z - Y‖ ≤ D) :
    ‖greenGradient (chart A J Z - chart A J Y)‖ ≤ C₁ * J / ‖Z - Y‖ := by
  have hn0 : 0 < ‖Z - Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hn : ‖J⁻¹ • (Z - Y)‖ = ‖Z - Y‖ / J := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJ),
      div_eq_mul_inv, mul_comm]
  have hsmall : ‖J⁻¹ • (Z - Y)‖ < (1 / 2 : ℝ) := by
    rw [hn]
    apply (div_lt_iff₀ hJ).mpr
    linarith
  have hrad := torusEuclideanNorm_quotient_eq_of_norm_lt_half hsmall
  rw [hn] at hrad
  have hq : torusQuotient (J⁻¹ • (Z - Y)) ≠ 0 := by
    intro he
    have hz : torusEuclideanNorm (torusQuotient (J⁻¹ • (Z - Y))) = 0 := by
      rw [he, torusEuclideanNorm_zero]
    rw [hrad] at hz
    exact (div_pos hn0 hJ).ne' hz
  rw [chart_sub]
  calc
    _ ≤ C₁ / torusEuclideanNorm (torusQuotient (J⁻¹ • (Z - Y))) := hk _ hq
    _ = C₁ * J / ‖Z - Y‖ := by rw [hrad]; field_simp [hJ.ne', hn0.ne']

/-- Reference-coordinate power integrability and its exact disk constant.
The prescribed closed-cell index is retained, including wrap boundaries. -/
theorem reference_power_bound_of_prescribed_cell {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    {C₁ u : ℝ} (hC : 0 ≤ C₁) (hk : KernelGradientBound C₁)
    (hu : 0 < u) (hu2 : u < 2) (a c : MeshIndex J) (b : Patch)
    {y : Torus} (hy : y ∈ closure (meshCell J hJ c)) :
    Integrable (fun Z ↦ ‖greenGradient (meshChart J a Z - y)‖ ^ u) (patchReference b) ∧
      (∫ Z, ‖greenGradient (meshChart J a Z - y)‖ ^ u ∂patchReference b) ≤
        (C₁ * J) ^ u * (1 + 2 * Real.pi / (2 - u)) := by
  classical
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hr0 : (0 : ℝ) < R := zero_lt_one.trans_le hr
  have hden : 0 < 2 - u := sub_pos.mpr hu2
  have hL : 0 ≤ C₁ * J := mul_nonneg hC hj.le
  have hLpow : 0 ≤ (C₁ * J) ^ u := Real.rpow_nonneg hL _
  have hm : Measurable (fun Z ↦ ‖greenGradient (meshChart J a Z - y)‖ ^ u) :=
    ((measurable_shiftedGradient y).comp (measurable_meshChart J a)).norm.pow_const u
  by_cases hc : c ∈ nearby J hJ R a b
  · obtain ⟨Y, hY, hd⟩ := nearby_lift hJ a c b hc hy
    have hb (Z : PlanarSpace) (hZ : Z ∈ patchClosed b) (hne : Z ≠ Y) :
        ‖greenGradient (meshChart J a Z - y)‖ ≤ C₁ * J / ‖Z - Y‖ := by
      rw [← hY]
      simpa only [meshChart_eq_chart] using
        norm_greenGradient_chart_sub_le (meshTranslation J a) hj
          (distanceBound_lt_half hR hmesh) hk hne (hd Z hZ)
    have hpow : ∀ᵐ Z ∂patchReference b,
        ‖greenGradient (meshChart J a Z - y)‖ ^ u ≤
          (C₁ * J) ^ u * inverseDistancePower Y u Z := by
      filter_upwards [ae_mem_patchClosed b,
        PoleLogMoments.ae_ne_pole (patchReference_le_volume b) Y] with Z hZ hne
      calc
        _ ≤ (C₁ * J / ‖Z - Y‖) ^ u :=
          Real.rpow_le_rpow (norm_nonneg _) (hb Z hZ hne) hu.le
        _ = _ := by
          rw [Real.div_rpow hL (norm_nonneg _) u]
          simp only [inverseDistancePower, Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]
    obtain ⟨hii, hib⟩ := inverseDistancePower_integrable_and_integral_le
      (patchReference_le_volume b) Y hu.le hu2
    have hmajor : Integrable (fun Z ↦ (C₁ * J) ^ u * inverseDistancePower Y u Z)
        (patchReference b) := hii.const_mul _
    have hi : Integrable (fun Z ↦ ‖greenGradient (meshChart J a Z - y)‖ ^ u)
        (patchReference b) := by
      apply hmajor.mono' hm.aestronglyMeasurable
      filter_upwards [hpow] with Z hZ
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hZ
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ Z, (C₁ * J) ^ u * inverseDistancePower Y u Z ∂patchReference b :=
        integral_mono_ae hi hmajor hpow
      _ = (C₁ * J) ^ u * ∫ Z, inverseDistancePower Y u Z ∂patchReference b :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hib hLpow
  · have hb (Z : PlanarSpace) (hZ : Z ∈ patchClosed b) :
        ‖greenGradient (meshChart J a Z - y)‖ ≤ C₁ * J := by
      have hsep := far_gap hJ a c b hc hZ hy
      have hz := ne_zero_of_separation hj hr0 hsep
      calc
        _ ≤ C₁ / torusEuclideanNorm (meshChart J a Z - y) := hk _ hz
        _ ≤ C₁ / ((R : ℝ) / J) :=
          div_le_div_of_nonneg_left hC (div_pos hr0 hj) hsep
        _ = C₁ * J / R := by field_simp [hj.ne', hr0.ne']
        _ ≤ C₁ * J := div_le_self hL hr
    have hpow : ∀ᵐ Z ∂patchReference b,
        ‖greenGradient (meshChart J a Z - y)‖ ^ u ≤ (C₁ * J) ^ u :=
      (ae_mem_patchClosed b).mono fun Z hZ ↦
        Real.rpow_le_rpow (norm_nonneg _) (hb Z hZ) hu.le
    have hi : Integrable (fun Z ↦ ‖greenGradient (meshChart J a Z - y)‖ ^ u)
        (patchReference b) := by
      apply (integrable_const ((C₁ * J) ^ u)).mono' hm.aestronglyMeasurable
      filter_upwards [hpow] with Z hZ
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hZ
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ _ : PlanarSpace, (C₁ * J) ^ u ∂patchReference b :=
        integral_mono_ae hi (integrable_const _) hpow
      _ = (C₁ * J) ^ u := by simp
      _ ≤ _ := by
        have ht : 0 ≤ 2 * Real.pi / (2 - u) := by positivity
        nlinarith

/-- Taking the power root is done only after actual integrability. -/
theorem memLp_and_lpNorm_of_power_bound {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] {μ : Measure A} {f : A → E} {u L B : ℝ}
    (hu : 0 < u) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f μ) (hi : Integrable (fun x ↦ ‖f x‖ ^ u) μ)
    (hb : (∫ x, ‖f x‖ ^ u ∂μ) ≤ L ^ u * B) :
    MemLp f (ENNReal.ofReal u) μ ∧ lpNorm f (ENNReal.ofReal u) μ ≤ L * B ^ (1 / u) := by
  have hm : MemLp f (ENNReal.ofReal u) μ :=
    (integrable_norm_rpow_iff hf (by positivity : ENNReal.ofReal u ≠ 0)
      ENNReal.ofReal_ne_top).mp (by simpa only [ENNReal.toReal_ofReal hu.le] using hi)
  refine ⟨hm, ?_⟩
  rw [DensityMoments.lpNorm_ofReal_eq hu hf]
  calc
    _ ≤ (L ^ u * B) ^ (1 / u) :=
      Real.rpow_le_rpow (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hb (one_div_nonneg.mpr hu.le)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hL _) hB, one_div,
        Real.rpow_rpow_inv hL hu.ne']

/-- The exact normalized chart transports the reference moment to the
actual torus patch. No whole-space Euclidean-to-Haar preservation is used. -/
theorem patch_gradient_moment_of_prescribed_cell {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    {C₁ u : ℝ} (hC : 0 ≤ C₁) (hk : KernelGradientBound C₁)
    (hu : 0 < u) (hu2 : u < 2) (a c : MeshIndex J) (b : Patch)
    {y : Torus} (hy : y ∈ closure (meshCell J hJ c)) :
    MemLp (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal u) (patchMeasure J hJ a b) ∧
      lpNorm (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal u) (patchMeasure J hJ a b) ≤
        C₁ * J * momentFactor u := by
  obtain ⟨hi, hb⟩ := reference_power_bound_of_prescribed_cell hJ hR hmesh hC hk hu hu2 a c b hy
  have hf : Measurable (fun Z ↦ greenGradient (meshChart J a Z - y)) :=
    (measurable_shiftedGradient y).comp (measurable_meshChart J a)
  have hden : 0 < 2 - u := sub_pos.mpr hu2
  have hr := memLp_and_lpNorm_of_power_bound hu (mul_nonneg hC (Nat.cast_nonneg J))
    (by positivity : 0 ≤ 1 + 2 * Real.pi / (2 - u)) hf.aestronglyMeasurable hi hb
  have he := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal u)
    (measurable_shiftedGradient y).aestronglyMeasurable (measurePreserving_patch J hJ a b)
  refine ⟨memLp_iff.mpr ?_, ?_⟩
  · rw [← he]
    exact hr.1.eLpNorm_lt_top
  · change (eLpNorm (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal u)
        (patchMeasure J hJ a b)).toReal ≤ _
    rw [← he]
    exact hr.2

/-- The same bound holds for every pole; the near/far split does not
change its constant. Thus it also covers every prescribed closed placement. -/
theorem patch_gradient_moment {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    {C₁ u : ℝ} (hC : 0 ≤ C₁) (hk : KernelGradientBound C₁)
    (hu : 0 < u) (hu2 : u < 2) (a : MeshIndex J) (b : Patch) (y : Torus) :
    MemLp (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal u) (patchMeasure J hJ a b) ∧
      lpNorm (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal u) (patchMeasure J hJ a b) ≤
        C₁ * J * momentFactor u := by
  exact patch_gradient_moment_of_prescribed_cell hJ hR hmesh hC hk hu hu2 a
    (meshLabel J hJ y) b (subset_closure ((mem_meshCell J hJ _ _).mpr rfl))

theorem patch_gradient_four_thirds {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    {C₁ : ℝ} (hC : 0 ≤ C₁) (hk : KernelGradientBound C₁)
    (a : MeshIndex J) (b : Patch) (y : Torus) :
    MemLp (fun z ↦ greenGradient (z - y)) conjugateExponent (patchMeasure J hJ a b) ∧
      lpNorm (fun z ↦ greenGradient (z - y)) conjugateExponent (patchMeasure J hJ a b) ≤
        C₁ * J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ) := by
  simpa only [conjugateExponent, momentFactor_four_thirds] using
    patch_gradient_moment hJ hR hmesh hC hk (by norm_num : (0 : ℝ) < 4 / 3)
      (by norm_num : (4 / 3 : ℝ) < 2) a b y

theorem patch_gradient_sixteen_ninths {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    {C₁ : ℝ} (hC : 0 ≤ C₁) (hk : KernelGradientBound C₁)
    (a : MeshIndex J) (b : Patch) (y : Torus) :
    MemLp (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal (16 / 9 : ℝ))
        (patchMeasure J hJ a b) ∧
      lpNorm (fun z ↦ greenGradient (z - y)) (ENNReal.ofReal (16 / 9 : ℝ))
        (patchMeasure J hJ a b) ≤ C₁ * J * (1 + 9 * Real.pi) ^ (9 / 16 : ℝ) := by
  simpa only [momentFactor_sixteen_ninths] using
    patch_gradient_moment hJ hR hmesh hC hk (by norm_num : (0 : ℝ) < 16 / 9)
      (by norm_num : (16 / 9 : ℝ) < 2) a b y

section DensityTransfer

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

/-- A genuine integrability equivalence for the actual density measure. -/
theorem integrable_nonnegative_density_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : A → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (f : A → E) :
    Integrable f (μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) ↔
      Integrable (fun x ↦ p x • f x) μ := by
  rw [integrable_withDensity_iff_integrable_smul' hp.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp0 _)]

/-- Holder transfer for unbounded vector functions. The reference moments
give actual integrability of both weighted powers; boundedness is not assumed. -/
theorem four_density_vector_moments {p : A → ℝ} {f : A → PlanarSpace} {K : ℝ}
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp4 : MemLp p 4 μ)
    (hK : lpNorm p 4 μ ≤ K) (hf : Measurable f)
    (hf4 : MemLp f conjugateExponent μ)
    (hf16 : MemLp f (ENNReal.ofReal (16 / 9 : ℝ)) μ) :
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (p x))
    Integrable f ν ∧
      (∫ x, ‖f x‖ ∂ν) ≤ K * lpNorm f conjugateExponent μ ∧
      MemLp f conjugateExponent ν ∧
      lpNorm f conjugateExponent ν ≤
        K ^ (3 / 4 : ℝ) * lpNorm f (ENNReal.ofReal (16 / 9 : ℝ)) μ := by
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (p x))
  have hK0 : 0 ≤ K := lpNorm_nonneg.trans hK
  have hi : Integrable f ν := by
    change Integrable f (μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    rw [integrable_nonnegative_density_iff hp hp0]
    exact memLp_one_iff_integrable.mp (hp4.smul hf4)
  have hmean : (∫ x, ‖f x‖ ∂ν) ≤ K * lpNorm f conjugateExponent μ := by
    rw [DensityMoments.integral_density (show ν = μ.withDensity _ from rfl)
      hp (Eventually.of_forall hp0)]
    have hh := integral_norm_mul_le hp4 hf4.norm
    simp only [abs_of_nonneg (hp0 _), abs_of_nonneg (norm_nonneg _),
      lpNorm_norm hf4.aestronglyMeasurable] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hK lpNorm_nonneg)
  have hpow : MemLp (fun x ↦ ‖f x‖ ^ (4 / 3 : ℝ)) conjugateExponent μ := by
    convert hf16.norm_rpow_div conjugateExponent using 1 <;>
      norm_num [conjugateExponent]
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  have hweighted : Integrable (fun x ↦ p x * ‖f x‖ ^ (4 / 3 : ℝ)) μ :=
    integrable_four_mul_conjugate hp4 hpow
  have hpowν : Integrable (fun x ↦ ‖f x‖ ^ (4 / 3 : ℝ)) ν := by
    change Integrable (fun x ↦ ‖f x‖ ^ (4 / 3 : ℝ))
      (μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    rw [integrable_nonnegative_density_iff hp hp0]
    simpa only [smul_eq_mul] using hweighted
  have hm : MemLp f conjugateExponent ν := by
    apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
      (by norm_num [conjugateExponent] : conjugateExponent ≠ 0)
      (by simp [conjugateExponent] : conjugateExponent ≠ ∞)).mp
    simpa only [conjugateExponent, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3)]
      using hpowν
  have hpower : (∫ x, ‖f x‖ ^ (4 / 3 : ℝ) ∂ν) ≤
      K * lpNorm f (ENNReal.ofReal (16 / 9 : ℝ)) μ ^ (4 / 3 : ℝ) := by
    rw [DensityMoments.integral_density (show ν = μ.withDensity _ from rfl)
      hp (Eventually.of_forall hp0)]
    have hh := integral_norm_mul_le hp4 hpow
    simp only [abs_of_nonneg (hp0 _),
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hh
    have he : lpNorm (fun x ↦ ‖f x‖ ^ (4 / 3 : ℝ)) conjugateExponent μ =
        lpNorm f (ENNReal.ofReal (16 / 9 : ℝ)) μ ^ (4 / 3 : ℝ) := by
      simpa only [conjugateExponent, show (4 / 3 : ℝ) * (4 / 3) = 16 / 9 by norm_num] using
        DensityMoments.lpNorm_norm_rpow (by norm_num : (0 : ℝ) < 4 / 3)
          (by norm_num : (0 : ℝ) < 4 / 3) hf.aestronglyMeasurable
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg lpNorm_nonneg _))
  refine ⟨hi, hmean, hm, ?_⟩
  rw [conjugateExponent, DensityMoments.lpNorm_ofReal_eq
    (by norm_num : (0 : ℝ) < 4 / 3) hf.aestronglyMeasurable]
  calc
    _ ≤ (K * lpNorm f (ENNReal.ofReal (16 / 9 : ℝ)) μ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) :=
      Real.rpow_le_rpow (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hpower (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow hK0 (Real.rpow_nonneg lpNorm_nonneg _), one_div,
        Real.rpow_rpow_inv lpNorm_nonneg (by norm_num : (4 / 3 : ℝ) ≠ 0)]
      norm_num

end DensityTransfer

/-- Both literal source constants, together with their genuine finite
moments. Norms are physical Euclidean norms of the actual Green gradient. -/
structure Estimates (ν : Measure Torus) (y : Torus) (C₁ K : ℝ) (J : ℕ) : Prop where
  integrable : Integrable (fun z ↦ greenGradient (z - y)) ν
  integral_norm_le : (∫ z, ‖greenGradient (z - y)‖ ∂ν) ≤
    K * C₁ * J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ)
  norm_integral_le : ‖∫ z, greenGradient (z - y) ∂ν‖ ≤
    K * C₁ * J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ)
  conjugate_memLp : MemLp (fun z ↦ greenGradient (z - y)) conjugateExponent ν
  conjugate_norm_le : lpNorm (fun z ↦ greenGradient (z - y)) conjugateExponent ν ≤
    K ^ (3 / 4 : ℝ) * C₁ * J * (1 + 9 * Real.pi) ^ (9 / 16 : ℝ)

/-- The actual point-density L4 estimate transfers both reference moments.
No nonzero coefficient at the observed pole is required. -/
theorem pointLaw_gradient_moments {I : Type*} [Fintype I] {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    {C₁ K : ℝ} (hC : 0 ≤ C₁) (hk : KernelGradientBound C₁)
    (a : MeshIndex J) (b : Patch) (Y : I → Torus) (w : I → ℝ)
    (hz : 0 < ∫ z, torusWeight Y w z ∂patchMeasure J hJ a b)
    (hp : MemLp (pointDensity (patchMeasure J hJ a b) Y w) 4 (patchMeasure J hJ a b))
    (hK : lpNorm (pointDensity (patchMeasure J hJ a b) Y w) 4 (patchMeasure J hJ a b) ≤ K)
    (y : Torus) : Estimates (pointLaw (patchMeasure J hJ a b) Y w) y C₁ K J := by
  have hf4 := patch_gradient_four_thirds hJ hR hmesh hC hk a b y
  have hf16 := patch_gradient_sixteen_ninths hJ hR hmesh hC hk a b y
  have hp0 (z : Torus) : 0 ≤ pointDensity (patchMeasure J hJ a b) Y w z :=
    div_nonneg (torusWeight_pos Y w z).le hz.le
  have hh := four_density_vector_moments (measurable_pointDensity _ Y w) hp0 hp hK
    (measurable_shiftedGradient y) hf4.1 hf16.1
  have hK0 : 0 ≤ K := lpNorm_nonneg.trans hK
  have hmean : (∫ z, ‖greenGradient (z - y)‖ ∂pointLaw (patchMeasure J hJ a b) Y w) ≤
      K * C₁ * J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ) := by
    exact hh.2.1.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf4.2 hK0)
  refine ⟨hh.1, hmean, (norm_integral_le_integral_norm _).trans hmean, hh.2.2.1, ?_⟩
  exact hh.2.2.2.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hf16.2 (Real.rpow_nonneg hK0 (3 / 4 : ℝ)))

/-- The raw and regular normalized densities are identified by the proved
fixed-placement AE transfer, then the actual kernel identity is used.
The Green constant and the radius are already proved choices. -/
theorem conditional_gradient_moments {n J : ℕ} (hJ : 0 < J) {β₀ β : ℝ}
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hb : ConditionalLawEstimates.LawBounds hJ β₀ β i Y a b) (y : Torus) :
    Estimates (conditionalKernel (patchMeasure J hJ a b) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J := by
  have hden := ConditionalLawEstimates.pointDensity_ae_rawDensity hJ
    (ConditionalLawEstimates.mesh_two_le hmesh) a b β Y
  have hp : MemLp (pointDensity (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ)))
      4 (patchMeasure J hJ a b) := (memLp_congr_ae hden).mpr hb.density_memLp
  have hK : lpNorm (pointDensity (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ)))
      4 (patchMeasure J hJ a b) ≤ ConditionalLawEstimates.densityNormBound β₀ := by
    change (eLpNorm _ 4 (patchMeasure J hJ a b)).toReal ≤ _
    rw [eLpNorm_congr_ae hden]
    exact hb.density_norm
  rw [hb.kernel_eq_pointLaw]
  exact pointLaw_gradient_moments hJ (ConditionalLawEstimates.radius_one_le β₀) hmesh
    ConditionalLawEstimates.kernelConstant_pos.le ConditionalLawEstimates.kernel_gradient_bound
    a b Y (fun _ ↦ β / (n + 1 : ℕ)) hb.regular_normalizer_pos hp hK y

/-- The same quantitative statement for the literal raw density appearing
in the source conditional-version formula. -/
theorem raw_conditional_gradient_moments {n J : ℕ} (hJ : 0 < J) {β₀ β : ℝ}
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hb : ConditionalLawEstimates.LawBounds hJ β₀ β i Y a b) (y : Torus) :
    Estimates ((patchMeasure J hJ a b).withDensity (fun z ↦ ENNReal.ofReal
      (ConditionalLawEstimates.rawDensity (patchMeasure J hJ a b) β Y z))) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J := by
  rw [← hb.kernel_eq_raw]
  exact conditional_gradient_moments hJ hmesh i Y a b hb y

/-- A valid completed cap discharges the density and normalizer premises
for every target patch and every pole, including coincident source positions. -/
theorem capped_conditional_gradient_moments {n J : ℕ} (hJ : 0 < J) {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) (y : Torus) :
    Estimates (conditionalKernel (patchMeasure J hJ a b) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J :=
  conditional_gradient_moments hJ hmesh i Y a b
    (ConditionalLawEstimates.capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY a b) y

/-- Literal specified-label endpoint of Proposition 3.11. The analytic
one-variable estimate itself also holds outside the global N≥2, β₀<4 gates. -/
theorem label_gradient_moments {n J : ℕ} {β₀ β δ : ℝ}
    (_hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (_hsub : β₀ < 4)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n)
    (hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y) (y : Torus) :
    Estimates (conditionalKernel
      (meshCellMeasure J (ConditionalLawEstimates.mesh_pos hmesh) (η i)) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J :=
  capped_conditional_gradient_moments (ConditionalLawEstimates.mesh_pos hmesh)
    hβ hβ₀ hδ hmesh η hη i Y hY (η i) .cell y

/-- The two cell conditionings used in the logarithmic-ratio estimate.
Each endpoint completion separately supplies its actual capped law. -/
theorem adjacent_endpoint_gradient_moments {n J : ℕ} {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η i a d)
    (Y : Configuration n)
    (hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y) (y : Torus) :
    Estimates (conditionalKernel
      (meshCellMeasure J (ConditionalLawEstimates.mesh_pos hmesh) a) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J ∧
    Estimates (conditionalKernel (meshCellMeasure J (ConditionalLawEstimates.mesh_pos hmesh)
      (nextCell J (ConditionalLawEstimates.mesh_pos hmesh) a d)) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J := by
  let hJ := ConditionalLawEstimates.mesh_pos hmesh
  have hout (c : MeshIndex J) : PrescribedOutside hJ (Function.update η i c) i Y := by
    intro j
    simpa only [Function.update_of_ne (Fin.succAbove_ne i j)] using hY j
  exact ⟨capped_conditional_gradient_moments hJ hβ hβ₀ hδ hmesh
      (Function.update η i a) hadm.1 i Y (hout a) a .cell y,
    capped_conditional_gradient_moments hJ hβ hβ₀ hδ hmesh
      (Function.update η i (nextCell J hJ a d)) hadm.2 i Y
      (hout (nextCell J hJ a d)) (nextCell J hJ a d) .cell y⟩

/-- Both endpoint completions are retained for the actual adjacent law;
the conditioned coordinate i may differ from its exceptional coordinate t. -/
theorem adjacent_gradient_moments {n J : ℕ} {β₀ β δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η t a d)
    (Y : Configuration n)
    (hY : PatchOutside (ConditionalLawEstimates.mesh_pos hmesh)
      (Function.update η t a) (adjacentShapes t d) i Y) (y : Torus) :
    Estimates (conditionalKernel
      (patchMeasure J (ConditionalLawEstimates.mesh_pos hmesh)
        (Function.update η t a i) (adjacentShapes t d i)) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J := by
  have hb := (ConditionalLawEstimates.adjacent_conditionals hN hβ hβ₀ hsub hδ hmesh
    η t i a d hadm).1 Y hY
  exact conditional_gradient_moments (ConditionalLawEstimates.mesh_pos hmesh) hmesh i Y
    (Function.update η t a i) (adjacentShapes t d i) hb y

/-- A probe freezes every outside source and requires every allowed
completion capped, including both labels of an edge patch. -/
theorem probe_gradient_moments {n J : ℕ} {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (b : Patch)
    (hadm : ProbeAdmissible δ η i
      (allowedPatchLabels (ConditionalLawEstimates.mesh_pos hmesh) a b))
    (Y : Configuration n)
    (hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y) (y : Torus) :
    Estimates (conditionalKernel
      (patchMeasure J (ConditionalLawEstimates.mesh_pos hmesh) a b) i β Y) y
      ConditionalLawEstimates.kernelConstant (ConditionalLawEstimates.densityNormBound β₀) J :=
  conditional_gradient_moments (ConditionalLawEstimates.mesh_pos hmesh) hmesh i Y a b
    (ConditionalLawEstimates.probe_law hβ hβ₀ hδ hmesh η i a b hadm Y hY) y

end PeriodicAttractiveLogGas.GreenGradientMoments
