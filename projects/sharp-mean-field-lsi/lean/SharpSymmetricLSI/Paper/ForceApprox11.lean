import SharpSymmetricLSI.Paper.ForceApprox10
import SharpSymmetricLSI.Paper.GroundT6

/-!
# R31 groundwork: the kernel approximation in terms of the difference fields

* The uniform force bound of (6.4) gives `|∂₁K_R| ≤ B` everywhere, uniformly in `R`
  (a.e. bound for the weak gradient on `𝕋^{2×d}`, then continuity and full support).
* The `H¹` convergence of (6.4) gives `∫∫|c_R|² dμ dμ → 0`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {KR : ℕ → Torus d → Torus d → ℝ}
  {eC : ℕ → Torus d → ℝ}
  (heC : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[haar d] e j ∧
    eC j =ᵐ[(μ : Measure (Torus d))] e j)
  {s : ℕ → Finset ℕ} {a : ℕ → ℕ → ℕ → ℝ} (ha : ∀ R i j, a R i j = a R j i)
  (hK : ∀ R x y, KR R x y = ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)
include hyp hμ heC ha hK

/-- A.e. on `μ^{⊗2}`: the pair weak gradient of `kerC (K_R)` is the classical one. -/
theorem weakGrad_kerC_ae (R : ℕ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => (μ : Measure (Torus d))),
      weakGrad (kerC (KR R) ∘ unflat) (flat X) = fun p =>
        if p.1 = 0 then finKerD (fun i => eC (i + 1)) (s R) (a R) (X 0) (X 1) p.2
        else finKerD (fun i => eC (i + 1)) (s R) (a R) (X 1) (X 0) p.2 := by
  have hφ : ∀ i, ContDiff ℝ 1 ((fun i => eC (i + 1)) i ∘ liftT) := fun i => (heC (i + 1)).1
  have hpair := weakGrad_ae_eq ((isWeakGrad_finKer_pair hφ (s R) (ha R)).congr_ae
    (pair_ae_finKer (fun j => (heC j).2.1) (s R) (a R) (hK R)).symm)
  filter_upwards [ae_pi_of_ae_volume hyp hμ hpair] with X hX
  exact hX

/-- **The uniform force bound.** -/
theorem finKerD_uniform_bound (hKR : IsKernelApprox W μ e KR) :
    ∃ B : ℝ, ∀ R x y k, |finKerD (fun i => eC (i + 1)) (s R) (a R) x y k| ≤ B := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨Bt, hBt, hB⟩ := hKR.2.2.2.1
  refine ⟨Bt.toReal, fun R => ?_⟩
  have hφ : ∀ i, ContDiff ℝ 1 ((fun i => eC (i + 1)) i ∘ liftT) := fun i => (heC (i + 1)).1
  have hg : eLpNorm (fun X => Real.sqrt (gradSqC (kerC (KR R)) X)) ⊤
      (Measure.pi fun _ : Fin 2 => μm) ≤ Bt := le_trans le_add_self (hB R)
  have h1 : ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μm),
      Real.sqrt (gradSqC (kerC (KR R)) X) ≤ Bt.toReal := by
    have hess : eLpNormEssSup (fun X => Real.sqrt (gradSqC (kerC (KR R)) X))
        (Measure.pi fun _ : Fin 2 => μm) ≤ Bt :=
      eLpNormEssSup_le_eLpNorm_top.trans hg
    filter_upwards [ae_le_eLpNormEssSup (μ := Measure.pi fun _ : Fin 2 => μm)
      (f := fun X => Real.sqrt (gradSqC (kerC (KR R)) X))] with X hX
    have := hX.trans hess
    rw [Real.enorm_of_nonneg (Real.sqrt_nonneg _)] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hBt.ne).1 this
  have h2 : ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μm), ∀ k,
      |finKerD (fun i => eC (i + 1)) (s R) (a R) (X 0) (X 1) k| ≤ Bt.toReal := by
    filter_upwards [h1, weakGrad_kerC_ae hyp hμ heC ha hK R] with X hX hW k
    refine le_trans ?_ hX
    rw [gradSqC_eq_sqNorm, hW, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    have := Finset.single_le_sum (f := fun p : Fin 2 × Fin d => (if p.1 = 0 then
      finKerD (fun i => eC (i + 1)) (s R) (a R) (X 0) (X 1) p.2 else
      finKerD (fun i => eC (i + 1)) (s R) (a R) (X 1) (X 0) p.2) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ ((0 : Fin 2), k))
    simpa using this
  have hmp := (MeasureTheory.measurePreserving_finTwoArrow μm).symm
  have h3 : ∀ᵐ p ∂μm.prod μm, ∀ k,
      |finKerD (fun i => eC (i + 1)) (s R) (a R) p.1 p.2 k| ≤ Bt.toReal := by
    filter_upwards [hmp.quasiMeasurePreserving.ae h2] with p hp
    simpa using hp
  intro x y k
  have hac2 : (haar d).prod (haar d) ≪ μm.prod μm :=
    (haar_ac_minimizer hyp hμ).prod (haar_ac_minimizer hyp hμ)
  have hcont : Continuous fun p : Torus d × Torus d =>
      |finKerD (fun i => eC (i + 1)) (s R) (a R) p.1 p.2 k| :=
    (continuous_finKerD hφ (s R) (a R) k).abs
  exact le_of_ae_le_of_continuous (ν' := (haar d).prod (haar d)) hac2 hcont
    (h3.mono fun p hp => hp k) (x, y)

end

end SharpLSI
