import Mathlib

/-!
# Tori, configurations, periodic lifts (infrastructure for D1, D8)

* `Torus d` is `𝕋^d = ℝ^d / ℤ^d`, realised as `UnitAddTorus (Fin d)`; its `volume` is the
  product of the Haar probability measures on `UnitAddCircle` (manuscript: normalized Haar
  measure `m`, Section 1.1).
* `Config N d := Fin N → Torus d` is the particle space `(𝕋^d)^N`; its `volume` is `m^{⊗N}`.
* Analysis on a torus is done through the periodic lift `liftT : (ι → ℝ) → UnitAddTorus ι`.
  A configuration space is identified with the single torus `UnitAddTorus (Fin N × Fin d)`
  through `flat` / `unflat`.
-/

open MeasureTheory
open scoped ContDiff

namespace SharpLSI

/-- The unit flat torus `𝕋^d = ℝ^d/ℤ^d` (manuscript, Section 1.1). -/
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)

/-- Particle configurations `X_N = (x_1, …, x_N) ∈ (𝕋^d)^N` (manuscript (1.1)). -/
abbrev Config (N d : ℕ) := Fin N → Torus d

/-- The Haar measure on `ℝ/ℤ` (total mass `1`) is a probability measure. -/
instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The normalized Haar measure `m` on `𝕋^d` (manuscript, Section 1.1). -/
noncomputable abbrev haar (d : ℕ) : Measure (Torus d) := volume

/-- Sanity check for D1: `m` is a probability measure. -/
theorem haar_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (haar d) := by
  infer_instance

/-- Sanity check for D8: `m^{⊗N}` (the `volume` of `Config N d`) is a probability measure. -/
theorem config_volume_isProbabilityMeasure (N d : ℕ) :
    IsProbabilityMeasure (volume : Measure (Config N d)) := by
  infer_instance

/-- `(𝕋^d)^k` is a standard Borel space (instance search does not find this through the nested
`abbrev`s; needed for conditional distributions of particle blocks). -/
instance standardBorel_blocks (k d : ℕ) : StandardBorelSpace (Fin k → Torus d) := by
  have : StandardBorelSpace (Torus d) := inferInstance
  exact StandardBorelSpace.pi_countable

/-- The periodic lift (covering map) `ℝ^ι → 𝕋^ι`. -/
def liftT {ι : Type*} (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

/-- The flat (Euclidean) distance on `𝕋^ι = ℝ^ι/ℤ^ι`: the minimum over integer shifts of the
Euclidean norm of the difference of lifts, `√(∑ₖ ‖xₖ - yₖ‖²)` with `‖·‖` on `ℝ/ℤ` the distance
to the nearest integer. (Mathlib's metric on `UnitAddTorus ι` is the sup metric; the two are
equivalent, `flatDist_comparison`.) -/
noncomputable def flatDist {ι : Type*} [Fintype ι] (x y : UnitAddTorus ι) : ℝ :=
  Real.sqrt (∑ k, ‖x k - y k‖ ^ 2)

/-- Lipschitz with constant `L` for the flat distance. -/
def FlatLipschitzWith {ι : Type*} [Fintype ι] (L : ℝ) (f : UnitAddTorus ι → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ L * flatDist x y

/-- Sanity lemma: `flatDist` is a metric inducing the topology of `𝕋^ι`. -/
theorem flatDist_metric {ι : Type*} [Fintype ι] :
    (∀ x : UnitAddTorus ι, flatDist x x = 0) ∧
    (∀ x y : UnitAddTorus ι, flatDist x y = flatDist y x) ∧
    (∀ x y z : UnitAddTorus ι, flatDist x z ≤ flatDist x y + flatDist y z) ∧
    (∀ x y : UnitAddTorus ι, flatDist x y = 0 → x = y) ∧
    ∀ x : UnitAddTorus ι, (nhds x).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {y | flatDist x y < ε}) := by
  -- the comparison with the sup metric (proved below as `flatDist_comparison`)
  have hcmp : ∀ x y : UnitAddTorus ι,
      dist x y ≤ flatDist x y ∧ flatDist x y ≤ Real.sqrt (Fintype.card ι) * dist x y := by
    intro x y
    have hk : ∀ k, ‖x k - y k‖ = dist (x k) (y k) := fun k => (dist_eq_norm _ _).symm
    constructor
    · unfold flatDist
      rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
      intro k
      rw [← hk]
      exact (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr
        (Finset.single_le_sum (f := fun k => ‖x k - y k‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ k))
    · unfold flatDist
      have h1 : ∑ k, ‖x k - y k‖ ^ 2 ≤ ∑ _k : ι, dist x y ^ 2 :=
        Finset.sum_le_sum fun k _ => by
          rw [hk]; exact pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist x y k) 2
      calc Real.sqrt (∑ k, ‖x k - y k‖ ^ 2) ≤ Real.sqrt (∑ _k : ι, dist x y ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = Real.sqrt (Fintype.card ι) * dist x y := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
              Real.sqrt_sq dist_nonneg]
  refine ⟨fun x => by simp [flatDist], fun x y => ?_, fun x y z => ?_, fun x y h => ?_, fun x => ?_⟩
  · unfold flatDist
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [norm_sub_rev]
  · unfold flatDist
    set a : ι → ℝ := fun k => ‖x k - y k‖
    set b : ι → ℝ := fun k => ‖y k - z k‖
    have hab : ∀ k, ‖x k - z k‖ ≤ a k + b k := fun k => by
      have := norm_sub_le_norm_sub_add_norm_sub (x k) (y k) (z k); simpa [a, b] using this
    have hnorm : ∀ v : ι → ℝ, Real.sqrt (∑ k, v k ^ 2) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ :=
      fun v => by rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
    calc Real.sqrt (∑ k, ‖x k - z k‖ ^ 2) ≤ Real.sqrt (∑ k, (a k + b k) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hab k) 2)
      _ = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι) + WithLp.toLp 2 b‖ := by
          rw [← WithLp.toLp_add, ← hnorm]; rfl
      _ ≤ ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ + ‖(WithLp.toLp 2 b : EuclideanSpace ℝ ι)‖ :=
          norm_add_le _ _
      _ = _ := by rw [← hnorm, ← hnorm]
  · have := (hcmp x y).1
    rw [h] at this
    exact dist_le_zero.mp this
  · refine Metric.nhds_basis_ball.to_hasBasis (fun ε hε => ?_) (fun ε hε => ?_)
    · refine ⟨ε, hε, fun y hy => ?_⟩
      simp only [Set.mem_ofPred_eq] at hy
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_le_of_lt (hcmp x y).1 hy
    · have hs : 0 ≤ Real.sqrt (Fintype.card ι) := Real.sqrt_nonneg _
      refine ⟨ε / (Real.sqrt (Fintype.card ι) + 1), by positivity, fun y hy => ?_⟩
      rw [Metric.mem_ball, dist_comm] at hy
      simp only [Set.mem_ofPred_eq]
      calc flatDist x y ≤ Real.sqrt (Fintype.card ι) * dist x y := (hcmp x y).2
        _ ≤ Real.sqrt (Fintype.card ι) * (ε / (Real.sqrt (Fintype.card ι) + 1)) :=
            mul_le_mul_of_nonneg_left hy.le hs
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith

/-- Sanity lemma: `dist ≤ flatDist ≤ √|ι| · dist` (Mathlib's sup metric `dist`). -/
theorem flatDist_comparison {ι : Type*} [Fintype ι] (x y : UnitAddTorus ι) :
    dist x y ≤ flatDist x y ∧ flatDist x y ≤ Real.sqrt (Fintype.card ι) * dist x y := by
  have hk : ∀ k, ‖x k - y k‖ = dist (x k) (y k) := fun k => (dist_eq_norm _ _).symm
  constructor
  · unfold flatDist
    rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
    intro k
    rw [← hk]
    exact (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr
      (Finset.single_le_sum (f := fun k => ‖x k - y k‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ k))
  · unfold flatDist
    have h1 : ∑ k, ‖x k - y k‖ ^ 2 ≤ ∑ _k : ι, dist x y ^ 2 :=
      Finset.sum_le_sum fun k _ => by
        rw [hk]; exact pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist x y k) 2
    calc Real.sqrt (∑ k, ‖x k - y k‖ ^ 2) ≤ Real.sqrt (∑ _k : ι, dist x y ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Fintype.card ι) * dist x y := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
            Real.sqrt_sq dist_nonneg]

/-- A configuration as a point of the single torus `𝕋^{N × d}`. -/
def flat {N d : ℕ} (X : Config N d) : UnitAddTorus (Fin N × Fin d) := fun p => X p.1 p.2

/-- Inverse of `flat`. -/
def unflat {N d : ℕ} (Y : UnitAddTorus (Fin N × Fin d)) : Config N d := fun i k => Y (i, k)

/-- A function on a torus is smooth if its periodic lift is `C^∞`. -/
def IsSmoothT {ι : Type*} [Fintype ι] (f : UnitAddTorus ι → ℝ) : Prop :=
  ContDiff ℝ ∞ (f ∘ liftT)

/-- Permutation invariance `f ∘ σ = f` for all `σ ∈ S_N`, with `S_N` acting by permuting the
coordinates (manuscript (1.8)). -/
def IsSymmetric {N d : ℕ} (f : Config N d → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (X : Config N d), f (X ∘ σ) = f X

end SharpLSI
