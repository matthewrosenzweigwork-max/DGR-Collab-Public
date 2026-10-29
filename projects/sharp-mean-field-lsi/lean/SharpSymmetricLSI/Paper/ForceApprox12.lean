import SharpSymmetricLSI.Paper.ForceApprox11

/-!
# R31 groundwork: `A_R = ∫∫|c_R|² dμ dμ → 0`

The pair gradient of `kerC K_R - kerC K` has `(0,k)`-component `-c_R(x,y)_k`, so the `H¹`
convergence of (6.4) gives `A_R → 0`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem vecCons_two_eq (X : Config 2 d) : ![X 0, X 1] = X := by
  funext i; fin_cases i <;> rfl

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {KR : ℕ → Torus d → Torus d → ℝ}
  {eC : ℕ → Torus d → ℝ}
  (heC : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[haar d] e j ∧
    eC j =ᵐ[(μ : Measure (Torus d))] e j)
  {s : ℕ → Finset ℕ} {a : ℕ → ℕ → ℕ → ℝ} (ha : ∀ R i j, a R i j = a R j i)
  (hK : ∀ R x y, KR R x y = ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)
include hyp hμ heC ha hK

/-- A.e. on `μ^{⊗2}`: `∑_k c_R(X₀,X₁)_k² ≤ |∇(kerC K_R - kerC K)|²`. -/
theorem cOff_sq_le_ae (R : ℕ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => (μ : Measure (Torus d))),
      ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) (X 0) (X 1) k ^ 2 ≤
        gradSqC (fun Y => kerC (KR R) Y - kerC (centeredKernel W μ) Y) X := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  have hφ : ∀ i, ContDiff ℝ 1 ((fun i => eC (i + 1)) i ∘ liftT) := fun i => (heC (i + 1)).1
  have hR := (isWeakGrad_finKer_pair hφ (s R) (ha R)).congr_ae
    (pair_ae_finKer (fun j => (heC j).2.1) (s R) (a R) (hK R)).symm
  have h := hR.add ((isWeakGrad_K2 hyp hac (μ := μm)).cmul (-1))
  have hfun : (fun y => KR R (projBlock 0 y) (projBlock 1 y) + -1 * K2 W μm y) =
      (fun Y => kerC (KR R) Y - kerC (centeredKernel W μm) Y) ∘ unflat := by
    funext y; simp only [Function.comp_apply, K2, kerC]; rw [neg_one_mul, ← sub_eq_add_neg]; rfl
  rw [hfun] at h
  filter_upwards [ae_pi_of_ae_volume hyp hμ (weakGrad_ae_eq h)] with X hX
  rw [gradSqC_eq_sqNorm, hX]
  unfold sqNorm
  rw [Fintype.sum_prod_type]
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
    (Finset.mem_univ (0 : Fin 2)))
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  simp only [↓reduceIte, gK, if_neg (by decide : (0 : Fin 2) ≠ 1), sub_zero]
  have e1 : lipGrad (W2 W) (flat X) (0, k) = bGrad W (X 0) (X 1) k := by
    unfold bGrad; rw [vecCons_two_eq]
  rw [e1]
  unfold cOff
  have e2 : projBlock 0 (flat X) = X 0 := rfl
  have e3 : projBlock 1 (flat X) = X 1 := rfl
  rw [e2, e3]
  ring

/-- **`A_R → 0`.** -/
theorem tendsto_cOff_sq (hKR : IsKernelApprox W μ e KR) :
    Tendsto (fun R => ∫⁻ X, ENNReal.ofReal
      (∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) (X 0) (X 1) k ^ 2)
        ∂Measure.pi (fun _ : Fin 2 => (μ : Measure (Torus d)))) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hKR.2.2.1
    (fun _ => bot_le) fun R => lintegral_mono_ae ?_
  filter_upwards [cOff_sq_le_ae hyp hμ heC ha hK R] with X hX
  refine ENNReal.ofReal_le_ofReal (hX.trans ?_)
  exact le_add_of_nonneg_left (sq_nonneg _)

end

end SharpLSI
