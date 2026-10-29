import LeanResearch.PeriodicAttractiveLogGas.FarReferenceResidual
import LeanResearch.PeriodicAttractiveLogGas.CanonicalPairs
import Mathlib.Algebra.Order.Floor.Semiring

/-! Actual far canonical pair kernels and the source radius choice. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.ResidualFarExponential
open MeshCells MeshNearbyGeometry ReferenceResidual FarReferenceResidual
  GreenGradientOscillation CanonicalPairs CanonicalRowHolder

def farScale (R : ℕ) (C₂ : ℝ) : ℝ := 2 * C₂ / (R : ℝ) ^ 2

theorem farScale_nonneg (R : ℕ) {C₂ : ℝ} (hC : 0 ≤ C₂) : 0 ≤ farScale R C₂ := by
  unfold farScale
  positivity

def chosenRadius (β₀ C₂ : ℝ) : ℕ :=
  max 2 (Nat.ceil (Real.sqrt (24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂)))

theorem chosenRadius_two_le (β₀ C₂ : ℝ) : 2 ≤ chosenRadius β₀ C₂ := le_max_left _ _

/-- The natural radius is exactly the manuscript's ordinary integer ceiling. -/
theorem chosenRadius_intCast (β₀ C₂ : ℝ) :
    (chosenRadius β₀ C₂ : ℤ) =
      max 2 (Int.ceil (Real.sqrt (24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂))) := by
  have hn := Int.ceil_nonneg (Real.sqrt_nonneg (24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂))
  unfold chosenRadius
  rw [← Int.ceil_toNat]
  omega

theorem chosenRadius_square {β₀ C₂ : ℝ} (hβ : 0 ≤ β₀) (hC : 0 ≤ C₂) :
    24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂ ≤ (chosenRadius β₀ C₂ : ℝ) ^ 2 := by
  have h0 : 0 ≤ 24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂ := by positivity
  have hc : (Nat.ceil (Real.sqrt (24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂)) : ℝ) ≤
      chosenRadius β₀ C₂ := by exact_mod_cast (le_max_right 2 _)
  have hs := (Nat.le_ceil (Real.sqrt (24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂))).trans hc
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rwa [Real.sq_sqrt h0] at hp

theorem lintegral_norm_pow_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ L) (p : ℕ) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤ ENNReal.ofReal (L ^ p) := by
  calc
    _ ≤ ∫⁻ _x, (ENNReal.ofReal L) ^ p ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hb] with x hx
      apply pow_le_pow_left₀ (by positivity)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
    _ = _ := by simp [← ENNReal.ofReal_pow hL]

theorem conditional_factorial_of_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β → ℝ) {S : Set α} {T : Set β}
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ y ∂ν, y ∈ T)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ x ∈ S, ∀ y ∈ T, |f x y| ≤ L) (p : ℕ) :
    essSup (leftMoment μ f p) ν + essSup (rightMoment ν f p) μ ≤
      ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ)) := by
  have hl : essSup (leftMoment μ f p) ν ≤ ENNReal.ofReal (L ^ p) := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hν] with y hy
    apply lintegral_norm_pow_le μ hL
    filter_upwards [hμ] with x hx
    exact hb x hx y hy
  have hr : essSup (rightMoment ν f p) μ ≤ ENNReal.ofReal (L ^ p) := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hμ] with x hx
    apply lintegral_norm_pow_le ν hL
    filter_upwards [hν] with y hy
    exact hb x hx y hy
  calc
    _ ≤ ENNReal.ofReal (L ^ p) + ENNReal.ofReal (L ^ p) := add_le_add hl hr
    _ = ENNReal.ofReal (2 * L ^ p) := by
      rw [← ENNReal.ofReal_add (pow_nonneg hL p) (pow_nonneg hL p)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right (by positivity)
      (by exact_mod_cast Nat.factorial_pos p))

def farKernel {J N : ℕ} (R : ℕ) (μ : MeshIndex J → Measure Torus)
    (η : Fin N → MeshIndex J) (i j : Fin N) (x y : Torus) : ℝ :=
  if R < periodicIndexDistance (η i) (η j) then residual (μ (η i)) (μ (η j)) x y else 0

def farResidualSum {J N : ℕ} (R : ℕ) (μ : MeshIndex J → Measure Torus)
    (η : Fin N → MeshIndex J) (X : Fin N → Torus) : ℝ :=
  canonicalSum (farKernel R μ η) X / N

theorem farKernel_of_far {J N R : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : Fin N → MeshIndex J) {i j : Fin N} (hd : R < periodicIndexDistance (η i) (η j)) :
    farKernel R μ η i j = residual (μ (η i)) (μ (η j)) := by
  funext x y
  simp only [farKernel, hd, ite_true]

theorem farKernel_source_inputs {J N R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    {C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂) (η : Fin N → MeshIndex J) :
    (∀ i j, Measurable (Function.uncurry (farKernel R μ η i j))) ∧
    (∀ i j, ∀ᵐ y ∂μ (η j), (∫ x, farKernel R μ η i j x y ∂μ (η i)) = 0) ∧
    (∀ i j, ∀ᵐ x ∂μ (η i), (∫ y, farKernel R μ η i j x y ∂μ (η j)) = 0) ∧
    (∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (μ (η i)) (farKernel R μ η i j) p) (μ (η j)) +
        essSup (rightMoment (μ (η j)) (farKernel R μ η i j) p) (μ (η i)) ≤
          ENNReal.ofReal (2 * farScale R C₂ ^ p * (p.factorial : ℝ))) := by
  have hs (a : MeshIndex J) := ae_mem_closed_cell_of_domination hJ a (μ a) (hμ a)
  have hfar (i j : Fin N) (hd : R < periodicIndexDistance (η i) (η j)) :
      η j ∉ nearbyCells R (η i) := by rw [mem_nearbyCells]; omega
  have hc (i j : Fin N) (hd : R < periodicIndexDistance (η i) (η j)) :=
    far_residual_integrable_canonical hJ hR (η i) (η j) (hfar i j hd)
      (μ (η i)) (μ (η j)) (hs _) (hs _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hd : R < periodicIndexDistance (η i) (η j)
    · rw [farKernel_of_far μ η hd]
      exact ResidualDoubleCentering.measurable_doubleCenter (μ (η i)) (μ (η j)) greenKernel measurable_greenKernel
    · simp only [farKernel, hd, ite_false, Function.uncurry_def]
      exact measurable_const
  · intro i j
    by_cases hd : R < periodicIndexDistance (η i) (η j)
    · simpa only [farKernel, hd, ite_true] using (hc i j hd).2.1
    · simp [farKernel, hd]
  · intro i j
    by_cases hd : R < periodicIndexDistance (η i) (η j)
    · simpa only [farKernel, hd, ite_true] using (hc i j hd).2.2
    · simp [farKernel, hd]
  · intro p hp i j
    by_cases hd : R < periodicIndexDistance (η i) (η j)
    · have hb := conditional_factorial_of_bound (μ (η i)) (μ (η j))
        (residual (μ (η i)) (μ (η j))) (hs _) (hs _) (farScale_nonneg R hC)
        (fun x hx y hy => far_residual_bound hJ hR (η i) (η j) (hfar i j hd)
          (μ (η i)) (μ (η j)) (hs _) (hs _) hC hk hx hy) p
      rw [farKernel_of_far μ η hd]
      exact hb
    · change essSup (fun _y : Torus => ∫⁻ _x : Torus, ‖farKernel R μ η i j _x _y‖ₑ ^ p ∂μ (η i)) (μ (η j)) +
        essSup (fun _x : Torus => ∫⁻ _y : Torus, ‖farKernel R μ η i j _x _y‖ₑ ^ p ∂μ (η j)) (μ (η i)) ≤ _
      simp [farKernel, hd, show p ≠ 0 by omega]

theorem far_parameter_le_half {R : ℕ} (hR : 1 ≤ R) {β₀ τ C₂ : ℝ}
    (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀) (hC : 0 ≤ C₂)
    (hchoice : 24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂ ≤ (R : ℝ) ^ 2) :
    |2 * τ| * (8 * Real.sqrt 2 * Real.exp 1 * farScale R C₂) ≤ 1 / 2 := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hp := mul_le_mul_of_nonneg_right hτβ
    (show 0 ≤ (8 * Real.sqrt 2 * Real.exp 1) * C₂ by positivity)
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * τ)]
  change 2 * τ * (8 * Real.sqrt 2 * Real.exp 1 * (2 * C₂ / (R : ℝ) ^ 2)) ≤ _
  have he : 2 * τ * (8 * Real.sqrt 2 * Real.exp 1 * (2 * C₂ / (R : ℝ) ^ 2)) =
      (4 * τ * (8 * Real.sqrt 2 * Real.exp 1) * C₂) / (R : ℝ) ^ 2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hRr)).mpr
  nlinarith

/-- Source far exponential bound with the actual product reference law and
zero kernels on near pairs. Exponential integrability is a conclusion. -/
theorem far_exponential_bound {J N R : ℕ} (hJ : 0 < J) (hN : 2 ≤ N) (hR : 1 ≤ R)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    {β₀ τ C₂ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hchoice : 24 * β₀ * (8 * Real.sqrt 2 * Real.exp 1) * C₂ ≤ (R : ℝ) ^ 2)
    (η : Fin N → MeshIndex J) :
    Integrable (fun X => Real.exp (2 * τ * farResidualSum R μ η X)) (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, Real.exp (2 * τ * farResidualSum R μ η X) ∂Measure.pi (fun i => μ (η i))) ≤ 5 / 3 := by
  obtain ⟨hm, hl, hr, hp⟩ := farKernel_source_inputs hJ hR μ hμ hC hk η
  have hc := canonical_pairs (fun i => μ (η i)) (farKernel R μ η) (by omega)
    (fun i j _ => hm i j) (fun i j _ => hl i j) (fun i j _ => hr i j)
    (farScale_nonneg R hC) (fun p hp' i j _ => hp p hp' i j)
  have hx := far_parameter_le_half hR hτ hτβ hC hchoice
  have hx0 : 0 ≤ |2 * τ| * (8 * Real.sqrt 2 * Real.exp 1 * farScale R C₂) := by
    have := farScale_nonneg R hC
    positivity
  have he := hc.2.2.2.2.1 (2 * τ) (by linarith)
  have hf : (fun X => Real.exp (2 * τ * farResidualSum R μ η X)) =
      (fun X => Real.exp ((2 * τ) * canonicalSum (farKernel R μ η) X / (N : ℝ))) := by
    funext X
    congr 1
    unfold farResidualSum
    ring
  rw [hf]
  refine ⟨he.1, he.2.trans ?_⟩
  have hs : (|2 * τ| * (8 * Real.sqrt 2 * Real.exp 1 * farScale R C₂)) ^ 2 ≤ 1 / 4 := by
    nlinarith
  apply (div_le_iff₀ (by nlinarith)).mpr
  nlinarith

theorem chosen_far_exponential_bound {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    {β₀ τ C₂ : ℝ} (hβ : 0 ≤ β₀) (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂) (η : Fin N → MeshIndex J) :
    Integrable (fun X => Real.exp (2 * τ * farResidualSum (chosenRadius β₀ C₂) μ η X))
      (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, Real.exp (2 * τ * farResidualSum (chosenRadius β₀ C₂) μ η X)
        ∂Measure.pi (fun i => μ (η i))) ≤ 5 / 3 :=
  far_exponential_bound hJ hN (by have := chosenRadius_two_le β₀ C₂; omega)
    μ hμ hτ hτβ hC hk (chosenRadius_square hβ hC) η

end PeriodicAttractiveLogGas.ResidualFarExponential
