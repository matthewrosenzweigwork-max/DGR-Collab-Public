import LeanResearch.PeriodicAttractiveLogGas.PhysicalCubes
import LeanResearch.PeriodicAttractiveLogGas.ClusterScaling

/-! The actual collision integral on product cubes. Dilation and the free
anchor are handled at the level of nonnegative extended integrals, before
finiteness or real-integral conversion is used. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.ClusterCubeIntegral
open PhysicalCubes

theorem clusterBox_preimage_inv_smul (n : ℕ) (ρ : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun w : Fin n → PlanarSpace => r⁻¹ • w) ⁻¹' clusterBox n ρ =
      clusterBox n (r * ρ) := by
  ext w
  change (∀ i, i ∈ univ → r⁻¹ • w i ∈ ball 0 ρ) ↔
    ∀ i, i ∈ univ → w i ∈ ball 0 (r * ρ)
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  simp only [← div_eq_mul_inv, mul_comm r⁻¹, div_lt_iff₀ hr, mul_comm ρ r]

theorem clusterIntegral_scaling (n : ℕ) (ρ a : ℝ) {r : ℝ} (hr : 0 < r) :
    clusterIntegral n (r * ρ) a =
      ENNReal.ofReal (r ^ clusterScalingExponent n a) * clusterIntegral n ρ a := by
  have hm : Measure.map (fun w : Fin n → PlanarSpace => r⁻¹ • w) volume =
      ENNReal.ofReal (r ^ (2 * n)) • (volume : Measure (Fin n → PlanarSpace)) := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), finrank_clusterSpace,
      inv_pow, inv_inv, abs_of_pos (pow_pos hr _)]
  have hf : Measurable (fun w : Fin n → PlanarSpace =>
      ENNReal.ofReal (clusterWeight n a (r • w))) :=
    ((measurable_clusterWeight n a).comp (measurable_const_smul r)).ennreal_ofReal
  have hchange := setLIntegral_map (μ := (volume : Measure (Fin n → PlanarSpace)))
    (measurableSet_clusterBox n ρ) hf (measurable_const_smul r⁻¹)
  have hexp : ((2 * n : ℕ) : ℝ) + (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) =
      clusterScalingExponent n a := by
    rw [clusterScalingExponent_eq_dimension_sub_degree]
    push_cast
    ring
  calc
    clusterIntegral n (r * ρ) a = ∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (clusterWeight n a (r • w))
          ∂Measure.map (fun w : Fin n → PlanarSpace => r⁻¹ • w) volume := by
      simpa only [clusterIntegral, clusterBox_preimage_inv_smul n ρ hr, smul_inv_smul₀ hr.ne']
        using hchange.symm
    _ = ENNReal.ofReal (r ^ (2 * n)) *
        ∫⁻ w in clusterBox n ρ, ENNReal.ofReal (clusterWeight n a (r • w)) := by
      simp only [hm, setLIntegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal (r ^ (2 * n)) *
        (ENNReal.ofReal (r ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2)) *
          clusterIntegral n ρ a) := by
      congr 1
      simp_rw [clusterWeight_smul n a hr,
        ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      exact lintegral_const_mul _ (measurable_clusterWeight n a).ennreal_ofReal
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _),
        ← Real.rpow_natCast, ← Real.rpow_add hr, hexp]

/-- Any product of measurable coordinate sets can be reanchored at its
first coordinate. No product integrability is required for this identity. -/
theorem pair_integral_eq_iterated (n : ℕ) (a : ℝ)
    (s : Fin (n + 1) → Set PlanarSpace) (hs : ∀ i, MeasurableSet (s i)) :
    (∫⁻ X in pi univ s, ENNReal.ofReal (planarPairWeight (n + 1) a X)) =
      ∫⁻ x in s 0, ∫⁻ W in pi univ (fun i : Fin n => s i.succ),
        ENNReal.ofReal (clusterWeight n a (fun i => W i - x)) := by
  let e : (PlanarSpace × (Fin n → PlanarSpace)) ≃ᵐ (Fin (n + 1) → PlanarSpace) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => PlanarSpace) 0).symm
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => PlanarSpace) 0).symm _
  have he_apply (p : PlanarSpace × (Fin n → PlanarSpace)) :
      e p = Fin.cons (α := fun _ => PlanarSpace) p.1 p.2 :=
    Fin.insertNth_zero' _ _
  have hpre : e ⁻¹' pi univ s = s 0 ×ˢ pi univ (fun i : Fin n => s i.succ) := by
    ext p
    rw [mem_preimage, he_apply]
    constructor
    · intro hp
      exact ⟨by simpa only [Fin.cons_zero] using hp 0 (mem_univ 0),
        fun i _ => by simpa only [Fin.cons_succ] using hp i.succ (mem_univ _)⟩
    · rintro ⟨hx, hw⟩ i _
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using hx
      · simpa only [Fin.cons_succ] using hw j (mem_univ j)
  have hf := (measurable_planarPairWeight (n + 1) a).ennreal_ofReal
  calc
    _ = ∫⁻ p in s 0 ×ˢ pi univ (fun i : Fin n => s i.succ),
        ENNReal.ofReal (planarPairWeight (n + 1) a (e p)) := by
      simpa only [hpre] using
        (he.setLIntegral_comp_preimage (MeasurableSet.univ_pi hs) hf).symm
    _ = ∫⁻ x in s 0, ∫⁻ W in pi univ (fun i : Fin n => s i.succ),
        ENNReal.ofReal (planarPairWeight (n + 1) a (e (x, W))) := by
      rw [Measure.volume_eq_prod]
      exact setLIntegral_prod _ (hf.comp e.measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro W
      rw [he_apply, planarPairWeight_reanchor]
      simp only [Fin.cons_zero, Fin.cons_succ]

/-- The free anchor contributes exactly its set volume; the differences
are then enlarged to the already proved anchored collision integral. -/
theorem pair_integral_le (n : ℕ) (a ρ : ℝ)
    (s : Fin (n + 1) → Set PlanarSpace) (hs : ∀ i, MeasurableSet (s i))
    (hdiam : ∀ x ∈ s 0, ∀ W ∈ pi univ (fun i : Fin n => s i.succ),
      ∀ i : Fin n, ‖W i - x‖ < ρ) :
    (∫⁻ X in pi univ s, ENNReal.ofReal (planarPairWeight (n + 1) a X)) ≤
      volume (s 0) * clusterIntegral n ρ a := by
  rw [pair_integral_eq_iterated n a s hs]
  have hinner (x : PlanarSpace) (hx : x ∈ s 0) :
      (∫⁻ W in pi univ (fun i : Fin n => s i.succ),
        ENNReal.ofReal (clusterWeight n a (fun i => W i - x))) ≤ clusterIntegral n ρ a := by
    let T : (Fin n → PlanarSpace) → (Fin n → PlanarSpace) := fun W => W - fun _ => x
    have hT : MeasurePreserving T volume volume := measurePreserving_sub_right volume (fun _ => x)
    have hsub : pi univ (fun i : Fin n => s i.succ) ⊆ T ⁻¹' clusterBox n ρ := by
      intro W hW i _
      exact mem_ball_zero_iff.mpr (hdiam x hx W hW i)
    calc
      _ ≤ ∫⁻ W in T ⁻¹' clusterBox n ρ, ENNReal.ofReal (clusterWeight n a (T W)) :=
        lintegral_mono_set hsub
      _ = _ := hT.setLIntegral_comp_preimage (measurableSet_clusterBox n ρ)
        (measurable_clusterWeight n a).ennreal_ofReal
  calc
    _ ≤ ∫⁻ _x in s 0, clusterIntegral n ρ a :=
      setLIntegral_mono measurable_const hinner
    _ = _ := by rw [setLIntegral_const, mul_comm]


/-- Complete cluster bound on a product cube, in the original coordinate
volume. The hypothesis is only the geometric diameter of the actual cube. -/
theorem pair_integral_on_cube_le (n : ℕ) (a : ℝ) (c : Fin (n + 1) → PlanarSpace)
    {ℓ ρ : ℝ} (hℓ : 0 ≤ ℓ)
    (hdiam : ∀ X ∈ particleCube (n + 1) c ℓ, ∀ i : Fin n, ‖X i.succ - X 0‖ < ρ) :
    (∫⁻ X in particleCube (n + 1) c ℓ,
      ENNReal.ofReal (planarPairWeight (n + 1) a X)) ≤
      ENNReal.ofReal (ℓ ^ 2) * clusterIntegral n ρ a := by
  have hh := pair_integral_le n a ρ (fun i => cube (c i) ℓ)
    (fun i => measurableSet_cube (c i) ℓ) (fun x hx W hW i => by
      let X := Fin.cons (α := fun _ : Fin (n + 1) => PlanarSpace) x W
      have hX : X ∈ particleCube (n + 1) c ℓ := by
        intro j _
        refine Fin.cases ?_ (fun k => ?_) j
        · exact hx
        · exact hW k (mem_univ k)
      exact hdiam X hX i)
  simpa only [particleCube, cube_volume (c 0) hℓ, Fintype.card_fin] using hh

theorem scaling_coefficient (n : ℕ) (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ ^ 2 * ℓ ^ clusterScalingExponent n a =
      ℓ ^ (2 * (n + 1)) * ℓ ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) := by
  rw [← Real.rpow_natCast ℓ 2, ← Real.rpow_natCast ℓ (2 * (n + 1)),
    ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
  congr 1
  rw [clusterScalingExponent_eq_dimension_sub_degree]
  push_cast
  ring

/-- True integrability and the real upper bound follow from the finite
anchored integral. The right side retains the singular homogeneity factor. -/
theorem integrable_pairWeight_cube_bound (n : ℕ) (a : ℝ) (c : Fin (n + 1) → PlanarSpace)
    {ℓ R H : ℝ} (hℓ : 0 < ℓ) (hH : 0 ≤ H)
    (hdiam : ∀ X ∈ particleCube (n + 1) c ℓ,
      ∀ i : Fin n, ‖X i.succ - X 0‖ < ℓ * R)
    (hcluster : clusterIntegral n R a ≤ ENNReal.ofReal H) :
    IntegrableOn (planarPairWeight (n + 1) a) (particleCube (n + 1) c ℓ) volume ∧
      (∫ X in particleCube (n + 1) c ℓ, planarPairWeight (n + 1) a X) ≤
        ℓ ^ (2 * (n + 1)) * ℓ ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) * H := by
  have hb := pair_integral_on_cube_le n a c hℓ.le hdiam
  rw [clusterIntegral_scaling n R a hℓ] at hb
  have he : ENNReal.ofReal (ℓ ^ 2) *
      (ENNReal.ofReal (ℓ ^ clusterScalingExponent n a) * ENNReal.ofReal H) =
      ENNReal.ofReal (ℓ ^ (2 * (n + 1)) * ℓ ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) * H) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg ℓ), scaling_coefficient n a hℓ,
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hℓ.le _) (Real.rpow_nonneg hℓ.le _))]
  have hb' := hb.trans (show ENNReal.ofReal (ℓ ^ 2) *
      (ENNReal.ofReal (ℓ ^ clusterScalingExponent n a) * clusterIntegral n R a) ≤
      ENNReal.ofReal (ℓ ^ 2) *
        (ENNReal.ofReal (ℓ ^ clusterScalingExponent n a) * ENNReal.ofReal H) by gcongr)
  rw [he] at hb'
  have hn : ∀ᵐ X ∂volume.restrict (particleCube (n + 1) c ℓ),
      0 ≤ planarPairWeight (n + 1) a X :=
    Filter.Eventually.of_forall (planarPairWeight_nonneg (n + 1) a)
  have hi : IntegrableOn (planarPairWeight (n + 1) a) (particleCube (n + 1) c ℓ) volume := by
    refine ⟨(measurable_planarPairWeight (n + 1) a).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hn).mpr (hb'.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hb'
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb'

end PeriodicAttractiveLogGas.ClusterCubeIntegral
