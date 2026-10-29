import SharpSymmetricLSI.Paper.ForceApprox4
import SharpSymmetricLSI.Paper.GroundT5

/-!
# R31: the particle gradient of `U_N - U_N^{(R)}` ((7.11), pointwise part)

`∇_i(U_N - U_N^{(R)}) = N⁻¹(∑_{l≠i} c(X_i,X_l) + c_Δ(X_i))` a.e., with
`c = ∇₁W - β - ∂₁K_R`, `c_Δ = -β - ∂₁K_R(x,x)` (`β = ∫∇₁W(·,y) dμ(y)`, `C¹` representatives).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `c(x,y) = ∇₁W(x,y) - β(x) - ∂₁K_R(x,y)`. -/
noncomputable def cOff (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (φ : ℕ → Torus d → ℝ)
    (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (x y : Torus d) (k : Fin d) : ℝ :=
  bGrad W x y k - bForceL W (densOf μ) x k - finKerD φ s a x y k

/-- `c_Δ(x) = -β(x) - ∂₁K_R(x,x)`. -/
noncomputable def cDiag (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (φ : ℕ → Torus d → ℝ)
    (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (x : Torus d) (k : Fin d) : ℝ :=
  -bForceL W (densOf μ) x k - finKerD φ s a x x k

theorem weakGradC_diff_ae (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {φ : ℕ → Torus d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i ∘ liftT))
    (s : Finset ℕ) {a : ℕ → ℕ → ℝ} (ha : ∀ i j, a i j = a j i) {KR : Torus d → Torus d → ℝ}
    {N : ℕ} (hN : 1 ≤ N)
    (hKR : (fun y : UnitAddTorus (Fin N × Fin d) => UkernelF KR N (unflat y)) =ᵐ[volume]
      fun y => UkernelF (finKer φ s a) N (unflat y)) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))), ∀ i k,
      weakGradC (fun Y => Ucentered W μ N Y - UkernelF KR N Y) X i k =
        (N : ℝ)⁻¹ * (∑ l ∈ Finset.univ.erase i, cOff W μ φ s a (X i) (X l) k +
          cDiag W μ φ s a (X i) k) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  have hU := isWeakGrad_gsU hyp hac hN (μ := μm)
  have hR := (isWeakGrad_Ukernel_finKer hφ s ha hN).congr_ae hKR.symm
  have h := hU.add (hR.cmul (-1))
  have hfun : (fun y => (Ucentered W μm N ∘ unflat) y + -1 * UkernelF KR N (unflat y)) =
      (fun Y => Ucentered W μm N Y - UkernelF KR N Y) ∘ unflat := by
    funext y; simp only [Function.comp_apply]; ring
  rw [hfun] at h
  have hae := weakGrad_ae_eq h
  filter_upwards [ae_pi_of_ae_volume hyp hμ hae] with X hX i k
  have e1 : weakGradC (fun Y => Ucentered W μ N Y - UkernelF KR N Y) X i k =
      weakGrad ((fun Y => Ucentered W μm N Y - UkernelF KR N Y) ∘ unflat) (flat X) (i, k) := rfl
  rw [e1, congrFun hX (i, k)]
  simp only [gsG, cOff, cDiag]
  have hsplit : ∑ b : Fin N, finKerD φ s a (projBlock i (flat X)) (projBlock b (flat X)) k =
      ∑ l ∈ Finset.univ.erase i, finKerD φ s a (X i) (X l) k + finKerD φ s a (X i) (X i) k := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]; rfl
  rw [hsplit, show unflat (flat X) = X from rfl]
  simp only [Finset.sum_sub_distrib]
  ring

end SharpLSI
