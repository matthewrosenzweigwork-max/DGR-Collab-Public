import LeanResearch.PeriodicAttractiveLogGas.FixedWeightConstants

/-! Physical axis-parallel cubes and their product-square representation.
All measures are ordinary Lebesgue measures; the Euclidean norm is not
replaced by the coordinate sup norm in derivative estimates. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.PhysicalCubes

variable {ι : Type*} [Fintype ι]

def cube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j ↦ Icc (c j - ℓ / 2) (c j + ℓ / 2))

theorem mem_cube (c x : EuclideanSpace ℝ ι) (ℓ : ℝ) :
    x ∈ cube c ℓ ↔ ∀ j, |x j - c j| ≤ ℓ / 2 := by
  constructor
  · intro hx j
    have hj := hx j (mem_univ j)
    exact abs_le.mpr ⟨by linarith only [hj.1], by linarith only [hj.2]⟩
  · intro hx j _
    obtain ⟨hl, hu⟩ := abs_le.mp (hx j)
    exact ⟨by linarith only [hl], by linarith only [hu]⟩

theorem isCompact_cube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : IsCompact (cube c ℓ) :=
  (PiLp.homeomorph 2 (fun _ : ι ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

theorem measurableSet_cube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : MeasurableSet (cube c ℓ) :=
  (isCompact_cube c ℓ).measurableSet

theorem cube_volume (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume (cube c ℓ) = ENNReal.ofReal (ℓ ^ Fintype.card ι) := by
  rw [cube, (PiLp.volume_preserving_ofLp ι).measure_preimage
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Icc, show ∀ j, (c j + ℓ / 2) - (c j - ℓ / 2) = ℓ from fun _ ↦ by ring,
    Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow hℓ]

theorem cube_volume_real (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume.real (cube c ℓ) = ℓ ^ Fintype.card ι := by
  rw [Measure.real, cube_volume c hℓ, ENNReal.toReal_ofReal (pow_nonneg hℓ _)]

theorem norm_sub_sq_le (c x : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hx : x ∈ cube c ℓ) : ‖x - c‖ ^ 2 ≤ (Fintype.card ι : ℝ) * (ℓ / 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have hb := (mem_cube c x ℓ).mp hx
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    pow_le_pow_left₀ (abs_nonneg (x j - c j)) (hb j) 2)
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using hs

theorem square_norm_sub_le {c x : PlanarSpace} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hx : x ∈ cube c ℓ) : ‖x - c‖ ≤ ℓ := by
  have hh := norm_sub_sq_le c x hℓ hx
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hh
  nlinarith [norm_nonneg (x - c)]

def particleCube (N : ℕ) (c : Fin N → PlanarSpace) (ℓ : ℝ) : Set (Fin N → PlanarSpace) :=
  Set.pi Set.univ (fun i ↦ cube (c i) ℓ)

theorem particleCube_volume (N : ℕ) (c : Fin N → PlanarSpace) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume (particleCube N c ℓ) = ENNReal.ofReal (ℓ ^ (2 * N)) := by
  rw [particleCube, volume_pi_pi]
  simp only [cube_volume _ hℓ, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
    ← ENNReal.ofReal_pow (sq_nonneg ℓ), ← pow_mul]

theorem particleCube_measurable (N : ℕ) (c : Fin N → PlanarSpace) (ℓ : ℝ) :
    MeasurableSet (particleCube N c ℓ) :=
  MeasurableSet.univ_pi fun i ↦ measurableSet_cube (c i) ℓ

theorem particle_cube_norm_sub {N : ℕ} {c X : Fin N → PlanarSpace} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hX : X ∈ particleCube N c ℓ) (i : Fin N) : ‖X i - c i‖ ≤ ℓ :=
  square_norm_sub_le hℓ (hX i (mem_univ i))

end PeriodicAttractiveLogGas.PhysicalCubes
