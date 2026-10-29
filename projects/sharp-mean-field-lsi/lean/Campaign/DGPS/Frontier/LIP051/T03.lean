import DGPS.Equilibrium.Hessian

/-!
# LIP051.03: Centering and integrability of the original kernel

Task id `LIP051.03`, title "Centering and integrability of the original kernel" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", category shared infrastructure, verification V2).

Let `μ` be a Borel probability measure on the torus and `W` a continuous symmetric function on the
square with `|W x y| ≤ M` (`0 ≤ M`). Put
`K x y = W x y - ∫ W x u dμ(u) - ∫ W u y dμ(u) + ∬ W dμ⊗μ` and `d_K = ∫ K x x dμ`.
Then `K` is measurable, symmetric and bounded by `4 M`, it is centered in the first variable for
every value of the second, its diagonal is measurable and bounded by `4 M`, `K` lies in `L²(μ⊗μ)`,
and the diagonal is integrable, so `d_K` is a finite integral of the specified diagonal.

## Provides

* `DGPS.Frontier.LIP051.centeredKernelOf_LIP05103`: the centered kernel `K` of `(μ, W)` by the
  displayed pointwise formula.
* `DGPS.Frontier.LIP051.lip051_03_centering_integrability_original_kernel`: the main statement,
  the conjunction of measurability of `K` (as a function on the product), symmetry, `|K| ≤ 4M`,
  `∫ K(x,y) dμ(x) = 0` for every `y`, measurability of the diagonal, `|K(x,x)| ≤ 4M`,
  `K ∈ L²(μ⊗μ)` and integrability of the diagonal.
* `DGPS.Frontier.LIP051.lip051_03_centering_integrability_original_kernel_continuous`: `K` is
  continuous on the product (the proof route behind measurability).
* `DGPS.Frontier.LIP051.lip051_03_centering_integrability_original_kernel_dK`: `d_K` is the
  integral of the diagonal, it is finite (integrable diagonal) and `|d_K| ≤ 4M`.
* `DGPS.Frontier.LIP051.lip051_03_centering_integrability_original_kernel_eq_centeredKernel`:
  for `J : InteractionData d` and a probability measure, `centeredKernelOf_LIP05103 μ J.W`
  agrees pointwise with the campaign declaration `DGPS.centeredKernel J μ`, so the result applies
  to the original kernel `D.K` of the campaign once `hD` is available.

## R5 notes

1. Abstract statement. The specification of LIP051.03 is about an arbitrary Borel probability `μ`
   on the torus and an arbitrary bounded continuous symmetric `W`; it involves no `Spec`, `Aux`,
   `KData`, mode index, Hilbert basis or Gaussian object. The statement is therefore proved for
   `μ : Measure (Torus d)` with `[IsProbabilityMeasure μ]` and `W : Torus d → Torus d → ℝ`
   with `Continuous (Function.uncurry W)`, symmetry and the uniform bound `M`, exactly the listed
   hypotheses (including `0 ≤ M`). The defect FD-002 (binder `S A D J hD` and mode zero of the
   closing statement) does not enter this unit: nothing here indexes modes, so no positive-mode
   restriction and no Gaussian object is imposed or assumed; mode zero is neither used nor
   excluded. The identification of `S.mu` with `μ` and of `D.K` with the kernel below belongs to
   LIP051.01 and is only supported here by the bridge lemma `..._eq_centeredKernel`.
2. Centering formula. `K` is defined with the second integral taken as `∫ W u y dμ(u)` exactly as
   displayed in the specification. The campaign `DGPS.centeredKernel` uses `∫ W y z dμ(z)` for
   this term; the two coincide by the symmetry of `W`, which the bridge lemma uses.
3. Measurability. "`K` is measurable" is read as measurability of `Function.uncurry K` on
   `Torus d × Torus d` (product Borel structure). This is proved through the stronger continuity of
   `K` (parameter integrals of a continuous bounded function over a compact space).
4. L². "In L2 of the product" is read as `MemLp (Function.uncurry K) 2 (μ.prod μ)`.
5. Diagonal. The diagonal is the pointwise `x ↦ K x x` of the displayed formula, never an
   almost-everywhere representative. Since `K` is continuous on all of the square, no diagonal
   subtlety arises; `d_K` is `∫ x, K x x ∂μ`.
6. The bound `|K| ≤ 4M` is obtained pointwise (each of the four terms is bounded by `M`),
   including the double integral, bounded through `μ.prod μ` being a probability measure.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

variable {d : ℕ}

/-- The centered kernel `K(x,y) = W(x,y) - ∫ W(x,u) dμ(u) - ∫ W(u,y) dμ(u) + ∬ W dμ⊗μ`. -/
noncomputable def centeredKernelOf_LIP05103 (μ : Measure (DGPS.Torus d))
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (x y : DGPS.Torus d) : ℝ :=
  W x y - ∫ u, W x u ∂μ - ∫ u, W u y ∂μ + ∫ p, W p.1 p.2 ∂(μ.prod μ)

section Helpers

variable {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
  {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}

theorem continuous_left_integral_LIP05103
    (hWc : Continuous (Function.uncurry W)) : Continuous (fun x => ∫ u, W x u ∂μ) := by
  have := continuous_parametric_integral_of_continuous (μ := μ) hWc
    (isCompact_univ : IsCompact (Set.univ : Set (DGPS.Torus d)))
  simpa using this

theorem continuous_right_integral_LIP05103
    (hWc : Continuous (Function.uncurry W)) : Continuous (fun y => ∫ u, W u y ∂μ) := by
  have hc : Continuous (Function.uncurry (fun y u => W u y)) := by
    have : Function.uncurry (fun y u => W u y) = Function.uncurry W ∘ Prod.swap := by
      funext p; rfl
    rw [this]
    exact hWc.comp continuous_swap
  have := continuous_parametric_integral_of_continuous (μ := μ) hc
    (isCompact_univ : IsCompact (Set.univ : Set (DGPS.Torus d)))
  simpa using this

theorem abs_left_integral_le_LIP05103 (hb : ∀ x y, |W x y| ≤ M) (x : DGPS.Torus d) :
    |∫ u, W x u ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => W x u) (C := M)
    (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb x u)
  simpa [Real.norm_eq_abs] using h

theorem abs_right_integral_le_LIP05103 (hb : ∀ x y, |W x y| ≤ M) (y : DGPS.Torus d) :
    |∫ u, W u y ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => W u y) (C := M)
    (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb u y)
  simpa [Real.norm_eq_abs] using h

theorem abs_double_integral_le_LIP05103 (hb : ∀ x y, |W x y| ≤ M) :
    |∫ p, W p.1 p.2 ∂(μ.prod μ)| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := μ.prod μ) (f := fun p => W p.1 p.2) (C := M)
    (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hb p.1 p.2)
  simpa [Real.norm_eq_abs] using h

theorem continuous_kernel_LIP05103 (hWc : Continuous (Function.uncurry W)) :
    Continuous (Function.uncurry (centeredKernelOf_LIP05103 μ W)) := by
  unfold centeredKernelOf_LIP05103 Function.uncurry
  have h1 : Continuous (fun p : DGPS.Torus d × DGPS.Torus d => W p.1 p.2) := hWc
  have h2 : Continuous (fun p : DGPS.Torus d × DGPS.Torus d => ∫ u, W p.1 u ∂μ) :=
    (continuous_left_integral_LIP05103 (μ := μ) hWc).comp continuous_fst
  have h3 : Continuous (fun p : DGPS.Torus d × DGPS.Torus d => ∫ u, W u p.2 ∂μ) :=
    (continuous_right_integral_LIP05103 (μ := μ) hWc).comp continuous_snd
  exact ((h1.sub h2).sub h3).add continuous_const

theorem abs_kernel_le_LIP05103 (hb : ∀ x y, |W x y| ≤ M) (x y : DGPS.Torus d) :
    |centeredKernelOf_LIP05103 μ W x y| ≤ 4 * M := by
  have h1 := hb x y
  have h2 := abs_left_integral_le_LIP05103 (μ := μ) hb x
  have h3 := abs_right_integral_le_LIP05103 (μ := μ) hb y
  have h4 := abs_double_integral_le_LIP05103 (μ := μ) hb
  unfold centeredKernelOf_LIP05103
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

omit [IsProbabilityMeasure μ] in
theorem kernel_symm_LIP05103 (hs : ∀ x y, W x y = W y x) (x y : DGPS.Torus d) :
    centeredKernelOf_LIP05103 μ W x y = centeredKernelOf_LIP05103 μ W y x := by
  unfold centeredKernelOf_LIP05103
  have h1 : (fun u => W x u) = fun u => W u x := funext fun u => hs x u
  have h2 : (fun u => W y u) = fun u => W u y := funext fun u => hs y u
  have e1 : ∫ u, W x u ∂μ = ∫ u, W u x ∂μ := by rw [h1]
  have e2 : ∫ u, W y u ∂μ = ∫ u, W u y ∂μ := by rw [h2]
  rw [hs x y, e1, e2]
  ring

theorem integral_left_integral_LIP05103
    (hWc : Continuous (Function.uncurry W)) (hb : ∀ x y, |W x y| ≤ M) :
    ∫ x, (∫ u, W x u ∂μ) ∂μ = ∫ p, W p.1 p.2 ∂(μ.prod μ) := by
  have hint : Integrable (fun p : DGPS.Torus d × DGPS.Torus d => W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (hWc.aestronglyMeasurable) M
      (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hb p.1 p.2)
  exact (integral_prod (fun p : DGPS.Torus d × DGPS.Torus d => W p.1 p.2) hint).symm

theorem integral_kernel_LIP05103
    (hWc : Continuous (Function.uncurry W)) (hb : ∀ x y, |W x y| ≤ M) (y : DGPS.Torus d) :
    ∫ x, centeredKernelOf_LIP05103 μ W x y ∂μ = 0 := by
  have i1 : Integrable (fun x => W x y) μ :=
    Integrable.of_bound
      (hWc.comp (continuous_id.prodMk continuous_const) : Continuous fun x => W x y).aestronglyMeasurable
      M (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x y)
  have i2 : Integrable (fun x => ∫ u, W x u ∂μ) μ :=
    Integrable.of_bound (continuous_left_integral_LIP05103 (μ := μ) hWc).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_left_integral_le_LIP05103 (μ := μ) hb x)
  have e1 := integral_add (μ := μ) ((i1.sub i2).sub (integrable_const (∫ u, W u y ∂μ)))
    (integrable_const (∫ p, W p.1 p.2 ∂(μ.prod μ)))
  have e2 := integral_sub (μ := μ) (i1.sub i2) (integrable_const (∫ u, W u y ∂μ))
  have e3 := integral_sub (μ := μ) i1 i2
  unfold centeredKernelOf_LIP05103
  simp only [Pi.sub_apply] at e1 e2 e3
  rw [e1, e2, e3, integral_left_integral_LIP05103 hWc hb]
  simp

end Helpers

section Main

variable {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
  {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}

/-- The centered kernel is continuous on the product. -/
theorem lip051_03_centering_integrability_original_kernel_continuous
    (hWc : Continuous (Function.uncurry W)) :
    Continuous (Function.uncurry (centeredKernelOf_LIP05103 μ W)) :=
  continuous_kernel_LIP05103 hWc

/-- LIP051.03: `K` is measurable, symmetric, bounded by `4M` and centered in the first variable;
its diagonal is measurable and bounded by `4M`; `K ∈ L²(μ⊗μ)` and the diagonal is integrable. -/
theorem lip051_03_centering_integrability_original_kernel
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M) :
    Measurable (Function.uncurry (centeredKernelOf_LIP05103 μ W)) ∧
    (∀ x y, centeredKernelOf_LIP05103 μ W x y = centeredKernelOf_LIP05103 μ W y x) ∧
    (∀ x y, |centeredKernelOf_LIP05103 μ W x y| ≤ 4 * M) ∧
    (∀ y, ∫ x, centeredKernelOf_LIP05103 μ W x y ∂μ = 0) ∧
    Measurable (fun x => centeredKernelOf_LIP05103 μ W x x) ∧
    (∀ x, |centeredKernelOf_LIP05103 μ W x x| ≤ 4 * M) ∧
    MemLp (Function.uncurry (centeredKernelOf_LIP05103 μ W)) 2 (μ.prod μ) ∧
    Integrable (fun x => centeredKernelOf_LIP05103 μ W x x) μ := by
  have _ := hM
  have hKc := continuous_kernel_LIP05103 (μ := μ) hWc
  have hdiag : Continuous (fun x => centeredKernelOf_LIP05103 μ W x x) :=
    hKc.comp (continuous_id.prodMk continuous_id)
  refine ⟨hKc.measurable, kernel_symm_LIP05103 hs, abs_kernel_le_LIP05103 hb,
    integral_kernel_LIP05103 hWc hb, hdiag.measurable,
    fun x => abs_kernel_le_LIP05103 hb x x, ?_, ?_⟩
  · exact MemLp.of_bound hKc.aestronglyMeasurable (4 * M)
      (Filter.Eventually.of_forall fun p => by
        simpa [Real.norm_eq_abs, Function.uncurry] using abs_kernel_le_LIP05103 (μ := μ) hb p.1 p.2)
  · exact Integrable.of_bound hdiag.aestronglyMeasurable (4 * M)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_kernel_le_LIP05103 (μ := μ) hb x x)

/-- `d_K = ∫ K(x,x) dμ(x)` is an integral of an integrable diagonal and `|d_K| ≤ 4M`. -/
theorem lip051_03_centering_integrability_original_kernel_dK
    (hWc : Continuous (Function.uncurry W)) (hb : ∀ x y, |W x y| ≤ M) :
    Integrable (fun x => centeredKernelOf_LIP05103 μ W x x) μ ∧
    |∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ| ≤ 4 * M := by
  have hKc := continuous_kernel_LIP05103 (μ := μ) hWc
  have hdiag : Continuous (fun x => centeredKernelOf_LIP05103 μ W x x) :=
    hKc.comp (continuous_id.prodMk continuous_id)
  have hbd : ∀ x, ‖centeredKernelOf_LIP05103 μ W x x‖ ≤ 4 * M := fun x => by
    simpa [Real.norm_eq_abs] using abs_kernel_le_LIP05103 (μ := μ) hb x x
  refine ⟨Integrable.of_bound hdiag.aestronglyMeasurable (4 * M)
    (Filter.Eventually.of_forall hbd), ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => centeredKernelOf_LIP05103 μ W x x) (C := 4 * M)
    (Filter.Eventually.of_forall hbd)
  simpa [Real.norm_eq_abs] using h

end Main

/-- Bridge to the campaign declaration: for the interaction data `J` the kernel
`centeredKernelOf_LIP05103 μ J.W` is `DGPS.centeredKernel J μ` pointwise. -/
theorem lip051_03_centering_integrability_original_kernel_eq_centeredKernel
    (J : DGPS.InteractionData d) (μ : MeasureTheory.ProbabilityMeasure (DGPS.Torus d))
    (x y : DGPS.Torus d) :
    centeredKernelOf_LIP05103 (μ : Measure (DGPS.Torus d)) J.W x y = DGPS.centeredKernel J μ x y := by
  unfold centeredKernelOf_LIP05103 DGPS.centeredKernel DGPS.interactionConvolution
    DGPS.meanInteraction
  have e : ∫ u, J.W u y ∂(μ : Measure (DGPS.Torus d)) =
      ∫ z, J.W y z ∂(μ : Measure (DGPS.Torus d)) := by
    congr 1; funext u; exact J.W_symm u y
  rw [e]

end DGPS.Frontier.LIP051
