import SharpSymmetricLSI.Paper.TestEnergy9
import SharpSymmetricLSI.Paper.FormLiminf6
import SharpSymmetricLSI.Paper.Prop21Conclusion
import SharpSymmetricLSI.Paper.FormLiminfS6
import SharpSymmetricLSI.Statements.R02_Prop_2_1
import SharpSymmetricLSI.Statements.R19_Lemma_5_2

/-!
# R33: the test energies in the `gradZ` form

`∫ ∑_{l,k} |gradZ φ_N|² dP_N → ℰ(φ)` (`tendsto_gradZ_energy`): the particle energy of the cylinder
test function equals `∫ ∑ gradZ²` (a.e. equality of weak gradients, `cyl_ae_eq`,
`isWeakGrad_compZ`; `gradZ` is bounded), and the test energies converge
(`test_energy_convergence_of`).
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The particle energy of a cylinder test function in the `gradZ` form. -/
theorem energy_cyl_eq_gradZ (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j) (N : ℕ) (c : Cyl) :
    energy V W N (fun X => c.φ (fun i => fluct e N i X)) =
      ENNReal.ofReal (∫ X, ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2 ∂gibbs V W N) := by
  have hPac : gibbs V W N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  have h := (isWeakGrad_compZ hφ N c.φ (c.smooth.of_le (by simp))).congr_ae
    (cyl_ae_eq heC N c).symm
  have hae : ∀ᵐ X ∂gibbs V W N, gradSqC (fun X => c.φ (fun i => fluct e N i X)) X =
      ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2 := by
    refine hPac.ae_le ?_
    filter_upwards [ae_pi_of_ae_volume hyp hμ (weakGrad_ae_eq h)] with X hX
    unfold gradSqC weakGradC
    simp_rw [hX]
    rfl
  obtain ⟨hm, L, hL⟩ := gradZ_props hφ (N := N) (c.smooth.of_le (by simp)) c.compact
  have hmeas : Measurable fun X : Config N d => ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2 :=
    Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun k _ =>
      ((hm (l, k)).comp measurable_flat).pow_const 2
  have hP : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hint : Integrable (fun X : Config N d => ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2)
      (gibbs V W N) := by
    refine integrable_of_bdd (C := ∑ _l : Fin N, ∑ _k : Fin d, L ^ 2) hmeas fun X => ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hL _ _) 2
  unfold energy
  rw [lintegral_congr_ae (hae.mono fun X hX => by rw [hX]),
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun X => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)]

theorem tendsto_gradZ_energy (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) {γ : Measure (ℕ → ℝ)}
    (hγ : IsCenteredGaussianCov γ C) (c : Cyl) :
    Tendsto (fun N => ∫ X, ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2 ∂gibbs V W N) atTop
      (𝓝 (c.form (lamShift lam) γ).toReal) := by
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  have h := test_energy_convergence_of hd hyp hr
    (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ) he hC hγ
    ⟨Cp, p, hp, fun N hN => ⟨(hCp N hN).2.1, (hCp N hN).2.2⟩⟩ c
  have := hγ.1
  have h2 := (ENNReal.tendsto_toReal (Cyl.form_ne_top _ c)).comp h
  refine h2.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [energy_cyl_eq_gradZ hyp hμ hφ heC N c, ENNReal.toReal_ofReal
    (integral_nonneg fun X => Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _)]

end SharpLSI
