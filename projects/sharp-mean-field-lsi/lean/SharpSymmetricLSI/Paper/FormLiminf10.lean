import SharpSymmetricLSI.Paper.FormLiminf9

/-!
# R33 (8.20): the particle integration by parts under `P_N`

For `f ∈ H¹(P_N)` and a cylinder `φ`, with `φ_N = φ(Z_N)` (`C¹` representatives):
`E_N(f, φ_N) := ∫ ∇f · ∇φ_N dP_N = ∫ f 𝓛 dP_N`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The cross energy `∫ ∇f · ∇g dP`. -/
noncomputable def crossE {N : ℕ} (P : Measure (Config N d)) (f g : Config N d → ℝ) : ℝ :=
  ∫ X, ∑ l, ∑ k, weakGradC f X l k * weakGradC g X l k ∂P

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j) {N : ℕ} (hN : 1 ≤ N)
  (c : Cyl)
include hyp hμ he hφ heC hN

theorem gsE_sq (X : Config N d) :
    gsE W (μ : Measure (Torus d)) N (flat X) ^ 2 = rexp (-Ucentered W μ N X) := by
  unfold gsE
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  rw [show unflat (flat X) = X from rfl]
  ring

/-- `∇φ_N = gradZ` a.e. under `P_N`. -/
theorem weakGradC_cyl_ae :
    ∀ᵐ X ∂gibbs V W N, ∀ l k, weakGradC (fun X => c.φ (zC eC N c.J X)) X l k =
      gradZ eC N c.J c.φ (flat X) (l, k) := by
  have h1 : gibbs V W N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  have h := weakGrad_ae_eq (isWeakGrad_compZ hφ N c.φ (c.smooth.of_le (by simp)))
  filter_upwards [h1.ae_le (ae_pi_of_ae_volume hyp hμ h)] with X hX l k
  exact congrFun hX (l, k)

/-- **`E_N(f, φ_N) = ∫ f 𝓛 dP_N`.** -/
theorem gibbs_ibp {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    crossE (gibbs V W N) f (fun X => c.φ (zC eC N c.J X)) =
      ∫ X, f X * genL W (μ : Measure (Torus d)) eC lam N c X ∂gibbs V W N := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨hw, hFi, hgi⟩ := memH1C_gibbs_W11 hyp hμ hf
  have hibp := particle_ibp hyp hμ he hφ heC hN c hw hFi hgi
  have hK := centeredPartition_pos hyp μm N
  unfold crossE
  have hcg : ∫ X, ∑ l, ∑ k, weakGradC f X l k * weakGradC (fun X => c.φ (zC eC N c.J X)) X l k
      ∂gibbs V W N = ∫ X, ∑ l, ∑ k, weakGradC f X l k * gradZ eC N c.J c.φ (flat X) (l, k)
      ∂gibbs V W N := by
    refine integral_congr_ae ?_
    filter_upwards [weakGradC_cyl_ae hyp hμ he hφ heC hN c] with X hX
    simp only [hX]
  rw [hcg, integral_gibbs_eq' hyp hμ (G := fun X => ∑ l, ∑ k, weakGradC f X l k *
    gradZ eC N c.J c.φ (flat X) (l, k)), integral_gibbs_eq' hyp hμ (G := fun X =>
    f X * genL W μm eC lam N c X)]
  have e1 : ∀ X : Config N d, rexp (-Ucentered W μ N X) / centeredPartition W μ N *
      ∑ l, ∑ k, weakGradC f X l k * gradZ eC N c.J c.φ (flat X) (l, k) =
      (centeredPartition W μ N)⁻¹ * (gsE W μm N (flat X) ^ 2 *
        ∑ p, weakGrad (f ∘ unflat) (flat X) p * gradZ eC N c.J c.φ (flat X) p) := fun X => by
    rw [gsE_sq hyp hμ he hφ heC hN, Fintype.sum_prod_type]
    unfold weakGradC
    ring
  have e2 : ∀ X : Config N d, rexp (-Ucentered W μ N X) / centeredPartition W μ N *
      (f X * genL W μm eC lam N c X) =
      (centeredPartition W μ N)⁻¹ * (gsE W μm N (flat X) ^ 2 * (f ∘ unflat) (flat X) *
        genL W μm eC lam N c X) := fun X => by
    rw [gsE_sq hyp hμ he hφ heC hN]
    simp only [Function.comp_apply, show unflat (flat X) = X from rfl]
    ring
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul, hibp]

end

end SharpLSI
