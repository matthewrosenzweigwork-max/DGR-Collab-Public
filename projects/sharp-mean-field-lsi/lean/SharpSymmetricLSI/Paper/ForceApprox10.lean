import SharpSymmetricLSI.Paper.ForceApprox8
import SharpSymmetricLSI.Paper.ForceApprox9

/-!
# R31 groundwork: the difference fields `c_R`, `c_{Δ,R}`, uniformly in `R`
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Measurability, centering and bounds of `c`, `c_Δ`, with constants uniform in the kernel. -/
theorem cOff_props (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {φ : ℕ → Torus d → ℝ}, (∀ i, ContDiff ℝ 1 (φ i ∘ liftT)) →
      (∀ j, ∫ y, φ j y ∂(μ : Measure (Torus d)) = 0) → ∀ (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
      {CK : ℝ}, (∀ x y k, |finKerD φ s a x y k| ≤ CK) →
      (∀ k, Measurable (Function.uncurry fun x y => cOff W μ φ s a x y k)) ∧
      (∀ k, Measurable fun x => cDiag W μ φ s a x k) ∧
      (∀ x y k, |cOff W μ φ s a x y k| ≤ C0 + CK) ∧
      (∀ x k, |cDiag W μ φ s a x k| ≤ C0 + CK) ∧
      (∀ x k, ∫ y, cOff W μ φ s a x y k ∂(μ : Measure (Torus d)) = 0) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨-, hβm, ⟨Cβ, hCβ⟩, hβint⟩ := forceMean_props hyp hac
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  refine ⟨|Cb| + |Cβ|, by positivity, fun {φ} hφ hφ0 s a CK hCK => ⟨fun k => ?_, fun k => ?_,
    fun x y k => ?_, fun x k => ?_, fun x k => ?_⟩⟩
  · have h1 := measurable_bGrad hyp (W := W) k
    have h2 := measurable_finKerD hφ s a k
    have h3 := hβm k
    show Measurable fun p : Torus d × Torus d =>
      bGrad W p.1 p.2 k - bForceL W (densOf μm) p.1 k - finKerD φ s a p.1 p.2 k
    exact (h1.sub (h3.comp measurable_fst)).sub h2
  · have h2 := measurable_finKerD_diag hφ s a k
    have h3 := hβm k
    show Measurable fun x : Torus d => -bForceL W (densOf μm) x k - finKerD φ s a x x k
    exact h3.neg.sub h2
  · unfold cOff
    have := hCb x y k; have := hCβ x k; have := hCK x y k
    have h1 := abs_sub (bGrad W x y k - bForceL W (densOf μm) x k) (finKerD φ s a x y k)
    have h2 := abs_sub (bGrad W x y k) (bForceL W (densOf μm) x k)
    have := le_abs_self Cb; have := le_abs_self Cβ
    linarith
  · unfold cDiag
    have := hCβ x k; have := hCK x x k
    have h1 := abs_sub (-bForceL W (densOf μm) x k) (finKerD φ s a x x k)
    rw [abs_neg] at h1
    have := abs_nonneg Cb; have := le_abs_self Cβ
    linarith
  · have hb : Integrable (fun y => bGrad W x y k) μm :=
      integrable_of_bdd ((measurable_bGrad hyp (W := W) k).of_uncurry_left (x := x))
        fun y => hCb x y k
    have hf : Integrable (fun y => finKerD φ s a x y k) μm :=
      integrable_of_bdd ((measurable_finKerD hφ s a k).of_uncurry_left (x := x))
        fun y => hCK x y k
    unfold cOff
    rw [integral_sub (f := fun y => bGrad W x y k - bForceL W (densOf μm) x k)
      (g := fun y => finKerD φ s a x y k) (hb.sub (integrable_const _)) hf,
      integral_sub (f := fun y => bGrad W x y k) (g := fun _ => bForceL W (densOf μm) x k) hb
        (integrable_const _),
      ← hβint x k, integral_const, probReal_univ, one_smul, sub_self, zero_sub, neg_eq_zero]
    unfold finKerD
    have hij : ∀ i j, Integrable (fun y => a i j * cgrad (φ i) x k * φ j y) μm := fun i j => by
      obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hφ j)
      exact (integrable_of_bdd (measurable_of_contDiff (hφ j)) hB).const_mul _
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hij i j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, hφ0 j, mul_zero]

end SharpLSI
