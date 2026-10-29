import SharpSymmetricLSI.Paper.LemmaA2_26
import SharpSymmetricLSI.Paper.ProductDissipation

/-!
# R25 Lemma A.2, part 27: the centered kernel

`K = W - W*μ - W*μ + W(μ,μ)` is continuous, bounded, symmetric, centered, and `L`-Lipschitz in
each variable for the Euclidean distance on lifts.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section ker

variable (hyp : Hyp V W KV KW) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
include hyp

theorem continuous_centeredKernel_A2 : Continuous (Function.uncurry (centeredKernel W ν)) := by
  have hW : Continuous (Function.uncurry W) := hyp.continuous_W
  have hc := continuous_convMeas hyp ν
  exact ((hW.sub (hc.comp continuous_fst)).sub (hc.comp continuous_snd)).add continuous_const

theorem centeredKernel_symm_A2 (x y : Torus d) : centeredKernel W ν x y = centeredKernel W ν y x := by
  unfold centeredKernel; rw [hyp.symm]; ring

theorem lipschitz_convMeas_lift :
    LipschitzWith (Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1)
      ((convMeas W ν) ∘ liftT) := by
  obtain ⟨BW, hBW⟩ := exists_bound_W hyp
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [Function.comp, Real.dist_eq, convMeas]
  have hi : ∀ z, Integrable (fun y => W (liftT z) y) ν := fun z =>
    (integrable_const BW).mono' (hyp.continuous_W.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hBW _ _)
  rw [← integral_sub (hi a) (hi b)]
  have hb : ∀ y, |W (liftT a) y - W (liftT b) y| ≤
      ((Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1 : ℝ≥0) : ℝ) * dist a b := by
    intro y
    have := (lipschitz_slice hyp y).dist_le_mul a b
    simpa [Function.comp, Real.dist_eq] using this
  calc |∫ y, (W (liftT a) y - W (liftT b) y) ∂ν| ≤ ∫ y, |W (liftT a) y - W (liftT b) y| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y, ((Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1 : ℝ≥0) : ℝ) * dist a b ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          (Eventually.of_forall hb)
    _ = _ := by simp

/-- **Lipschitz slices of the centered kernel.** -/
theorem centeredKernel_lip : ∃ LK : ℝ, 0 ≤ LK ∧
    (∀ y a b, centeredKernel W ν (liftT a) y - centeredKernel W ν (liftT b) y ≤ LK * dE a b) ∧
    (∀ x a b, centeredKernel W ν x (liftT a) - centeredKernel W ν x (liftT b) ≤ LK * dE a b) := by
  set K2 : ℝ≥0 := Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1
  have h1 : ∀ y a b, centeredKernel W ν (liftT a) y - centeredKernel W ν (liftT b) y ≤
      (2 * K2) * dE a b := by
    intro y a b
    have hs := (lipschitz_slice hyp y).dist_le_mul a b
    have hc := (lipschitz_convMeas_lift hyp ν).dist_le_mul a b
    simp only [Function.comp, Real.dist_eq] at hs hc
    have hd := dist_le_dE a b
    simp only [centeredKernel]
    have := le_abs_self (W (liftT a) y - W (liftT b) y)
    have := neg_abs_le (convMeas W ν (liftT a) - convMeas W ν (liftT b))
    have hK0 : (0 : ℝ) ≤ K2 := K2.2
    nlinarith [mul_le_mul_of_nonneg_left hd hK0]
  refine ⟨2 * K2, by positivity, h1, fun x a b => ?_⟩
  rw [centeredKernel_symm_A2 hyp ν x, centeredKernel_symm_A2 hyp ν x]
  exact h1 x a b

theorem integral_centeredKernel_left (y : Torus d) :
    ∫ x, centeredKernel W ν x y ∂ν = 0 := by
  obtain ⟨BW, hBW⟩ := exists_bound_W hyp
  have hci := continuous_convMeas hyp ν
  have hWi : Integrable (fun x => W x y) ν := (integrable_const BW).mono'
    (hyp.continuous_W.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBW _ _)
  have hcI : Integrable (convMeas W ν) ν := hci.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  simp only [centeredKernel]
  rw [integral_add (f := fun x => W x y - convMeas W ν x - convMeas W ν y)
      ((hWi.sub hcI).sub (integrable_const _)) (integrable_const _),
    integral_sub (f := fun x => W x y - convMeas W ν x) (hWi.sub hcI) (integrable_const _),
    integral_sub (f := fun x => W x y) hWi hcI]
  have e1 : ∫ x, W x y ∂ν = convMeas W ν y := by
    simp only [convMeas]; congr 1; funext x; rw [hyp.symm]
  have e2 : ∫ x, convMeas W ν x ∂ν = interE W ν ν := by
    simp only [convMeas, interE]; congr 1; funext x; congr 1; funext y'; rw [hyp.symm]
  rw [e1, e2]; simp

end ker

section cent

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
  {Kf : Torus d → Torus d → ℝ} (hKc : Continuous (Function.uncurry Kf))
  (hsymm : ∀ x y, Kf x y = Kf y x) (hcent : ∀ y, ∫ x, Kf x y ∂densMeasure ρ = 0)
include hρ hb hKc hsymm hcent

theorem T_zero_left (j : ℕ) :
    ∫ y', (∫ x', Kf x' y' * e 0 x' ∂densMeasure ρ) * e j y' ∂densMeasure ρ = 0 := by
  simp only [hb.zero, mul_one, hcent, zero_mul, integral_zero]

theorem T_zero_right (i : ℕ) :
    ∫ y', (∫ x', Kf x' y' * e i x' ∂densMeasure ρ) * e 0 y' ∂densMeasure ρ = 0 := by
  rw [fubini_coeff hρ hb hKc i 0]
  simp only [hb.zero, mul_one]
  have : ∀ x, ∫ y, Kf x y ∂densMeasure ρ = 0 := fun x => by
    simp_rw [hsymm x]; exact hcent x
  simp [this]

end cent

end SharpLSI
