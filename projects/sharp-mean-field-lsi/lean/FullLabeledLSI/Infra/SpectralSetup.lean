import FullLabeledLSI.Infra.HypercontrTorus1
import SharpSymmetricLSI.Statements.R22_Reference_LSI
import SharpSymmetricLSI.Statements.R23_Reference_Spectrum
import SharpSymmetricLSI.Paper.RefSpectrum17

/-!
# Standing hypotheses of the torus hypercontractivity theorems from the equilibrium data

For `μ` the minimizer (`Hyp`, `0 < r_*`) and `(e, lam)` any reference eigenbasis of `-L_μ`, we derive
the *standing hypotheses* used by the torus hypercontractivity theorems (`HypercontrTorus*`):
* `μ` and Haar measure are mutually absolutely continuous (`μ = ρ m` with `c ≤ ρ ≤ C`);
* `C¹` representatives `eC j` of the eigenfunctions (in the sense `C1T`);
* a rate `a > 0` with `ofReal a ≤ r_LS(μ)` (`a = c/C`, from the reference LSI (5.18));
* `λ₀ = 0`, `λ_j ≥ 0`, `0 < λ₁ ≤ λ_j` for `j ≥ 1`, and the Weyl growth `λ_j ≥ c j^{2/d}`.

Main result: `torus_standing`.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

namespace SharpLSI.FL.Gross

variable {d : ℕ}

/-- The Dirichlet integral of an `H¹(P)` function is finite (`|∇f| ∈ L²(P)`). -/
theorem dirichlet_lt_top_of_memH1 {P : Measure (Torus d)} [IsFiniteMeasure P] {f : Torus d → ℝ}
    (h : MemH1 P f) : dirichlet P f < ⊤ := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad f x))) P :=
    h.2.2.aestronglyMeasurable
  have := (memLp_two_iff_integrable_sq hm).1 h.2.2
  unfold dirichlet
  have h2 := this.2
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)] at h2
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [Real.sq_sqrt (sqNorm_nonneg _)]

/-- The one-particle LSI constant of a reference density `c ≤ ρ ≤ C` is at least `c / C`. -/
theorem rLS_ge_of_goodDens {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) :
    ENNReal.ofReal (c / C) ≤ SharpLSI.FL.rLS (densMeasure ρ) := by
  unfold SharpLSI.FL.rLS
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hfH, hent⟩ := hf
  have hr : 0 < c / C := div_pos hρ.pos hρ.C_pos
  have : IsProbabilityMeasure (densMeasure ρ) := hρ.isProb
  have hlsi := reference_lsi hρ.pos (fun x => ⟨hρ.lower x, hρ.upper x⟩) hρ.one hρ.meas hfH
  have hD := dirichlet_lt_top_of_memH1 hfH
  have hEt : ent (densMeasure ρ) (fun x => f x ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.ne) hlsi
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hEt)]
  calc ENNReal.ofReal (c / C) * ent (densMeasure ρ) (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (c / C) * (ENNReal.ofReal (2 / (c / C)) *
          dirichlet (densMeasure ρ) f) := by
        gcongr
        exact hlsi
    _ = 2 * dirichlet (densMeasure ρ) f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le]
        have hc0 := hρ.pos.ne'
        have hC0 := hρ.C_pos.ne'
        have : c / C * (2 / (c / C)) = 2 := by field_simp
        rw [this]
        simp

/-- The classical partial derivatives of a constant function vanish. -/
lemma dT_const (a : ℝ) (k : Fin d) (y : Torus d) : dT (fun _ : Torus d => a) k y = 0 := by
  simp [dT, Function.comp_def]

/-- `λ₀ = 0` for a reference eigenbasis (with `μ ≈ Haar` and `C¹` representatives). -/
theorem lam_zero_eq_zero {mu : Measure (Torus d)} [IsProbabilityMeasure mu]
    (hac : mu ≪ volume) (hca : volume ≪ mu) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (hb : IsRefEigenbasis mu e lam) {eC : ℕ → Torus d → ℝ} (hC1 : ∀ j, C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) : lam 0 = 0 := by
  have h1 : C1T (fun _ : Torus d => (1 : ℝ)) := by
    unfold C1T; exact contDiff_const
  have h := classical_eigen hac hca hb hC1 hae 0 h1
  have hG : ∀ y, GammaT (eC 0) (fun _ : Torus d => (1 : ℝ)) y = 0 := fun y => by
    simp [GammaT, dT_const]
  have hI : ∫ y, eC 0 y ∂mu = 1 := by
    rw [integral_congr_ae (hae 0), hb.zero]
    simp
  simp only [hG, integral_zero, hI, mul_one] at h
  exact h.symm

/-- **Standing hypotheses of the torus hypercontractivity theorems.** For `μ` the minimizer and
`(e, lam)` a reference eigenbasis: `μ ≈ Haar`, `C¹` representatives `eC j` of the eigenfunctions,
a rate `a > 0` with `ofReal a ≤ r_LS(μ)`, and the spectral facts `λ₀ = 0`, `λ_j ≥ 0`,
`0 < λ₁ ≤ λ_j` (`j ≥ 1`), `λ_j ≥ c j^{2/d}` (`j ≥ 1`). -/
theorem torus_standing {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ (eC : ℕ → Torus d → ℝ) (a : ℝ),
      (μ : Measure (Torus d)) ≪ volume ∧ volume ≪ (μ : Measure (Torus d)) ∧
      (∀ j, C1T (eC j)) ∧ (∀ j, eC j =ᵐ[(μ : Measure (Torus d))] e j) ∧
      0 < a ∧ ENNReal.ofReal a ≤ SharpLSI.FL.rLS (μ : Measure (Torus d)) ∧
      lam 0 = 0 ∧ (∀ j, 0 ≤ lam j) ∧ 0 < lam 1 ∧ (∀ j, 1 ≤ j → lam 1 ≤ lam j) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) := by
  obtain ⟨ρ, c, C, Lσ, hμρ, hρ, -, -⟩ := refSetup hyp hμ
  obtain ⟨hpos, hweyl, -, Cc, q, hex⟩ := (ref_spectrum hd hyp hr hμ).2 e lam he
  choose eC hC1 hae _ _ using hex
  have hac : (μ : Measure (Torus d)) ≪ volume := by rw [hμρ]; exact hρ.ac
  have hca : volume ≪ (μ : Measure (Torus d)) := by rw [hμρ]; exact hρ.ac'
  have h0 : lam 0 = 0 := lam_zero_eq_zero hac hca he hC1 hae
  refine ⟨eC, c / C, hac, hca, hC1, hae, div_pos hρ.pos hρ.C_pos, ?_, h0, ?_, hpos 1 le_rfl,
    fun j hj => he.mono hj, hweyl⟩
  · rw [hμρ]; exact rLS_ge_of_goodDens hρ
  · intro j
    have := he.mono (Nat.zero_le j)
    rwa [h0] at this

end SharpLSI.FL.Gross
