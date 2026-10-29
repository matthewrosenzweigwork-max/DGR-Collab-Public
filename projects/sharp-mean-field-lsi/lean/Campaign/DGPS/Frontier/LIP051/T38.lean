import Mathlib
import DGPS.Frontier.LIP051.T36

/-!
# LIP051.38: Mean and coincident-pair covariance

Task id: LIP051.38 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Mean and coincident-pair covariance.

Provides:
* `DGPS.Frontier.LIP051.lip051_38_mean_coincident_pair_covariance`: for a probability measure `μ` on a
  measurable space `E`, a measurable symmetric real kernel `F : E → E → ℝ` with
  `F ∈ L²(μ ⊗ μ)` and `∫ F(x, y) dμ(x) = 0` for almost every `y`, and two distinct labels
  `i ≠ j` in `Fin N`, the coordinate pair `x ↦ F (x i) (x j)` on the product space `Fin N → E`
  with law `Q_N = Measure.pi (fun _ => μ)` satisfies: it lies in `L²(Q_N)`; its mean is zero;
  and its second moment equals the squared `L²(μ ⊗ μ)` norm of `F`.
* Helpers (all suffixed `_LIP05138`): `injective_pair_LIP05138` (the label pair `![i, j]` is injective
  for `i ≠ j`), `measurePreserving_pair_LIP05138` (the pair map `x ↦ (x i, x j)` pushes `Q_N` to
  `μ ⊗ μ`, via LIP051.35 and the two-coordinate identification `finTwoArrow`),
  `integral_pair_LIP05138` (transfer of integrals of functions of the pair to `μ ⊗ μ`),
  `eLpNorm_two_sq_LIP05138` (the squared `L²` seminorm is the integral of the square).

R5 notes:
* Scalar field and space. The kernel is real valued (`F : E → E → ℝ`), as the specification says
  "real `L²` kernel". `E` is an arbitrary measurable space; no positive-mode or Gaussian structure is
  involved, so FD-002 (mode-zero indexing) does not arise in this unit.
* Probability measure. `μ` is `[IsProbabilityMeasure μ]`, as in LIP051.35 and LIP051.36.
* Kernel measurability. "Measurable" is read as `Measurable` of the uncurried map `p ↦ F p.1 p.2` for
  the product σ-algebra on `E × E`.
* `L²` membership. "`F ∈ L²(μ^⊗2)`" is `MemLp (fun p => F p.1 p.2) 2 (μ.prod μ)`.
* Symmetry. The specification's symmetry hypothesis is kept as the pointwise identity
  `∀ x y, F x y = F y x`. The proof does not need it (the mean and second moment are computed from
  the product law alone); it is retained as a binder, named `_hsymm`, because it is part of the stated
  kernel class. The measurability hypothesis `_hF` is likewise retained and unused, since `MemLp`
  already carries the measurability needed by the proof.
* Centering. "`∫ F(x, y) dμ(x) = 0` for almost every `y`" is `∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0`.
* Distinct labels. The condition `i ≠ j` is an explicit hypothesis `hij`. The diagonal `i = j` is not
  claimed: this task does not control it.
* Pair law. `F(X_i, X_j)` is the function `x ↦ F (x i) (x j)` on `Fin N → E`, with `Q_N` the product
  measure `Measure.pi (fun _ : Fin N => μ)`. The two-coordinate reduction uses the restriction law of
  LIP051.35 (available here through the LIP051.36 dependency) followed by Mathlib's
  `measurePreserving_finTwoArrow`.
* Norm. "`‖F‖₂²`" is written as `(eLpNorm (fun p => F p.1 p.2) 2 (μ.prod μ)).toReal ^ 2`, the square
  of the real `L²(μ ⊗ μ)` norm. Its equality with the integral of the square is proved, not assumed.
* Mean and second moment are Bochner integrals with respect to the displayed measure. The
  second moment is written as `∫ x, (F (x i) (x j)) ^ 2 ∂Q_N`.
* No hypothesis beyond the specification is added. `hij` is the restriction `i ≠ j` stated in the
  specification's "for every pair of distinct particle labels".
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory ENNReal

/-- The label pair `![i, j]` is injective when `i ≠ j`. -/
lemma injective_pair_LIP05138 {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Function.Injective (![i, j] : Fin 2 → Fin N) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

/-- The pair map `x ↦ (x i, x j)` pushes the product law `Q_N` forward to `μ ⊗ μ`. -/
lemma measurePreserving_pair_LIP05138 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin N → E => (x i, x j))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  have hT := lip051_35_finite_coordinate_restriction_law_measurePreserving μ _
    (injective_pair_LIP05138 hij)
  have hA := measurePreserving_finTwoArrow (m := inferInstance) μ
  exact hA.comp hT

/-- Integrals of a function of the pair, computed under `Q_N`, equal the integrals under `μ ⊗ μ`. -/
lemma integral_pair_LIP05138 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N : ℕ} {i j : Fin N} (hij : i ≠ j) (f : E × E → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod μ)) :
    ∫ x, f (x i, x j) ∂(Measure.pi (fun _ : Fin N => μ)) = ∫ p, f p ∂(μ.prod μ) := by
  have hS := measurePreserving_pair_LIP05138 μ hij
  have h1 : AEStronglyMeasurable f (Measure.map (fun x : Fin N → E => (x i, x j))
      (Measure.pi (fun _ : Fin N => μ))) := by
    rw [hS.map_eq]
    exact hf
  have h2 := integral_map hS.measurable.aemeasurable h1
  rw [hS.map_eq] at h2
  exact h2.symm

/-- The squared `L²` seminorm of a real function is the integral of its square. -/
lemma eLpNorm_two_sq_LIP05138 {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 ν) :
    (eLpNorm g 2 ν).toReal ^ 2 = ∫ a, g a ^ 2 ∂ν := by
  have hnn : 0 ≤ ∫ a, ‖g a‖ ^ (2 : ℝ) ∂ν := integral_nonneg fun a => by positivity
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _),
    ← Real.rpow_natCast ((∫ a, ‖g a‖ ^ (2 : ℝ) ∂ν) ^ (2⁻¹ : ℝ)) 2, ← Real.rpow_mul hnn]
  norm_num

/-- **LIP051.38.** Let `μ` be a probability measure on `E`, `F : E → E → ℝ` a measurable symmetric
kernel in `L²(μ ⊗ μ)` with `∫ F(x, y) dμ(x) = 0` for almost every `y`, and `i ≠ j` in `Fin N`.
Then, under `Q_N = Measure.pi (fun _ => μ)`, the variable `F(X_i, X_j)` lies in `L²(Q_N)`, has mean
zero, and has second moment `‖F‖²₂` in `L²(μ ⊗ μ)`. -/
theorem lip051_38_mean_coincident_pair_covariance
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → E → ℝ) (_hF : Measurable (fun p : E × E => F p.1 p.2))
    (_hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MemLp (fun x : Fin N → E => F (x i) (x j)) 2 (Measure.pi (fun _ : Fin N => μ)) ∧
    ∫ x, F (x i) (x j) ∂(Measure.pi (fun _ : Fin N => μ)) = 0 ∧
    ∫ x, (F (x i) (x j)) ^ 2 ∂(Measure.pi (fun _ : Fin N => μ)) =
      (eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)).toReal ^ 2 := by
  have hS := measurePreserving_pair_LIP05138 μ hij
  have hmem : MemLp (fun x : Fin N → E => F (x i) (x j)) 2 (Measure.pi (fun _ : Fin N => μ)) :=
    hL2.comp_measurePreserving hS
  have hint : Integrable (fun p : E × E => F p.1 p.2) (μ.prod μ) :=
    hL2.integrable (by norm_num)
  refine ⟨hmem, ?_, ?_⟩
  · have h1 := integral_pair_LIP05138 μ hij (fun p : E × E => F p.1 p.2) hL2.aestronglyMeasurable
    rw [show (fun x : Fin N → E => F (x i) (x j)) = fun x => (fun p : E × E => F p.1 p.2) (x i, x j)
      from rfl, h1, integral_prod_symm _ hint]
    rw [integral_congr_ae hcent]
    simp
  · have h1 := integral_pair_LIP05138 μ hij (fun p : E × E => F p.1 p.2 ^ 2)
      (hL2.integrable_sq.aestronglyMeasurable)
    rw [show (fun x : Fin N → E => F (x i) (x j) ^ 2) =
      fun x => (fun p : E × E => F p.1 p.2 ^ 2) (x i, x j) from rfl, h1,
      eLpNorm_two_sq_LIP05138 hL2]

end DGPS.Frontier.LIP051
