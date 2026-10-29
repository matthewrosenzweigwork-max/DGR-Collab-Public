import SharpSymmetricLSI.Paper.FormLiminf11
import SharpSymmetricLSI.Paper.FormLiminfS6
import SharpSymmetricLSI.Paper.FormLiminfS9
import SharpSymmetricLSI.Paper.FormLiminfS10a
import SharpSymmetricLSI.Paper.FormLiminfS14e
import SharpSymmetricLSI.Statements.R32_Gaussian_Form

/-!
# R33 (8.20): the core lower bound `ℰ_∞(F) ≤ liminf ℰ_N(f_N)`

For every cylinder `φ`: `ℰ_N(f_N) ≥ 2ℰ_N(f_N, φ_N) - ℰ_N(φ_N)` (FormLiminf11), the cross term converges
to `⟨F, -𝓛_∞φ⟩` (`tendsto_cross_cyl`, via the particle integration by parts `gibbs_ibp`), and the test
energies converge to `ℰ_∞(φ)`; the duality (8.21) (R32 `form_duality`) then gives the bound.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
include hd hyp hr hμ he hC hγ

/-- **The core lower bound (8.20).** -/
theorem gaussForm_le_liminf_core : ∀ (Ns : ℕ → ℕ), Tendsto Ns atTop atTop →
    ∀ (f : (k : ℕ) → Config (Ns k) d → ℝ),
      (∀ k, MemH1C (gibbs V W (Ns k)) (f k)) →
      (∃ B : NNReal, ∀ k, (∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k)) +
        energy V W (Ns k) (f k) ≤ B) →
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, ∫⁻ X in {X | M < f k X ^ 2}, ENNReal.ofReal (f k X ^ 2)
        ∂gibbs V W (Ns k) ≤ ENNReal.ofReal ε) →
      ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ), Tendsto (fun k => ∫ X, g (f k X, fun n => fluct e (Ns k) n X)
        ∂gibbs V W (Ns k)) atTop (𝓝 (∫ z, g (F z, fun n => z n) ∂γ))) →
      gaussForm (lamShift lam) γ F ≤ liminf (fun k => energy V W (Ns k) (f k)) atTop := by
  intro Ns hNs f hf hB hUI F hF hlaw
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  have hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) := fun j => (heC j).1
  have heCh : ∀ j, eC j =ᵐ[haar d] e j := fun j => (heC j).2.1
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨Y, hY⟩ := exists_rowVariables_of_prop21 hyp hμ he h21 hC hγ
  have hγP : IsProbabilityMeasure γ := hγ.1
  obtain ⟨B, hB⟩ := hB
  have hP : ∀ k, IsProbabilityMeasure (gibbs V W (Ns k)) := fun k => gibbs_isProbabilityMeasure hyp _
  have hf2 : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ B := fun k => by
    have hL := (memLp_of_memH1C hyp (hf k)).integrable_sq
    have h1 : ENNReal.ofReal (∫ X, f k X ^ 2 ∂gibbs V W (Ns k)) ≤ B := by
      rw [ofReal_integral_eq_lintegral_ofReal hL (Eventually.of_forall fun X => sq_nonneg _)]
      exact le_trans le_self_add (hB k)
    have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun X => sq_nonneg _), ENNReal.coe_toReal] at this
  refine gaussForm_le_liminf_of_duality (fun k => (energy_lt_top hyp (hf k)).ne)
    (form_duality hd hyp hr hμ he hC hγ hY hF) fun c => ?_
  have hev : ∀ᶠ k in atTop, 1 ≤ Ns k := hNs.eventually_ge_atTop 1
  refine ⟨fun k => if 1 ≤ Ns k then ∫ X, f k X * genL W (μ : Measure (Torus d)) eC lam (Ns k) c X
      ∂gibbs V W (Ns k) else 0,
    fun k => if 1 ≤ Ns k then ∫ X, ∑ l, ∑ k', gradZ eC (Ns k) c.J c.φ (flat X) (l, k') ^ 2
      ∂gibbs V W (Ns k) else 0, ?_, ?_, fun k => ?_⟩
  · refine (tendsto_cross_cyl hd hyp hr hμ he hC hγ hY hφ heCh c hNs hf hf2 hUI hF hlaw).congr' ?_
    filter_upwards [hev] with k hk
    rw [if_pos hk]
  · refine ((tendsto_gradZ_energy hd hyp hr hμ he hφ heCh hC hγ c).comp hNs).congr' ?_
    filter_upwards [hev] with k hk
    simp only [Function.comp_apply, if_pos hk]
  · by_cases hk : 1 ≤ Ns k
    · simp only [if_pos hk]
      rw [← gibbs_ibp hyp hμ he hφ heCh hk c (hf k)]
      exact energy_ge_cross hyp hμ he hφ heCh hk c (hf k)
    · simp only [if_neg hk, mul_zero, sub_zero]
      exact ENNReal.toReal_nonneg

end

/-- **(8.20), (2.6)–(2.7) as a Paper lemma**: `CompactnessProperty'` for the closure of (8.1). -/
theorem form_liminf_of (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    CompactnessProperty' V W γ (gaussForm (lamShift lam) γ) :=
  form_liminf_of_core hd hyp hr hμ he hC hγ (gaussForm_le_liminf_core hd hyp hr hμ he hC hγ)

end SharpLSI
