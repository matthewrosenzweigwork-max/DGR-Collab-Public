import SharpSymmetricLSI.Paper.Sec5_4
import SharpSymmetricLSI.Paper.GroundT7
import SharpSymmetricLSI.Paper.KLLsc

/-!
# R20 (Lemma 5.3), part 1: the force bound under `ν` (5.14)

`|∇U_N|² = |G ∘ flat|²` a.e. for the explicit bounded measurable field `G = gsG` ((5.12)); the
Donsker–Varadhan inequality with the bounded test function `a₀ |G|²` and the exponential moment
(5.13) (`force_exp_moment`) give `a₀ E_ν|∇U_N|² ≤ H(ν|μ^{⊗N}) + log C`, and (5.6) (Lemma 5.2,
conditional on Lemma 4.2 through `hco`) bounds `H(ν|μ^{⊗N})`.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section force
variable (hyp : Hyp V W KV KW)
include hyp

/-- `|∇U_N|² = |G(flat X)|²` for `μ^{⊗N}`-a.e. `X`. -/
theorem gradSqC_Ucentered_ae {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))),
      gradSqC (Ucentered W μ N) X = sqNorm (gsG W μ N (flat X)) := by
  have hU := isWeakGrad_gsU hyp (minimizer_ac hyp hμ) hN (μ := (μ : Measure (Torus d)))
  have h2 := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hU⟩) hU
  filter_upwards [ae_pi_of_ae_volume hyp hμ h2] with X hX
  rw [gradSqC_eq_sqNorm, hX]

/-- **(5.14)**, conditional on Lemma 4.2. -/
theorem force_under_nu_of (hd : 1 ≤ d) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (hco : MFCoercive V W μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      IsSymmetricMeasure ν → klDiv ν (gibbs V W N) ≠ ⊤ →
        ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
          ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨a₀, CE, ha₀, hCE⟩ := force_exp_moment hd hyp hμ
  obtain ⟨C19, p, -, hR⟩ := reference_entropy_of hyp hμ hco
  set CE' := max CE 1
  set L := Real.log CE'
  have hL0 : 0 ≤ L := Real.log_nonneg (le_max_right _ _)
  set C19' := max C19 0
  set C := (C19' + L + 1) / a₀
  have hC : 0 < C := by positivity
  refine ⟨C, hC, fun N hN ν hν hsym hfin => ?_⟩
  set P := Measure.pi fun _ : Fin N => μm
  have hH := klDiv_pi_ne_top_of_gibbs hyp hμ hfin
  have hνP : ν ≪ P := (klDiv_ne_top_iff.mp hH).1
  -- the measurable bounded representative
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_gsG hyp hac (μ := μm) (N := N)
  set G : Config N d → ℝ := fun X => sqNorm (gsG W μm N (flat X))
  have hGm : Measurable G := by
    refine Finset.measurable_sum _ fun q _ => ?_
    exact ((measurable_gsG hyp hac q).comp measurable_flat).pow_const 2
  have hG0 : ∀ X, 0 ≤ G X := fun X => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set BG : ℝ := (Fintype.card (Fin N × Fin d) : ℝ) * CG ^ 2
  have hGB : ∀ X, |G X| ≤ BG := fun X => by
    rw [abs_of_nonneg (hG0 X)]
    calc G X ≤ ∑ _q : Fin N × Fin d, CG ^ 2 := Finset.sum_le_sum fun q _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCG _ _) 2
      _ = BG := by simp [BG]
  have hae := gradSqC_Ucentered_ae hyp hμ hN
  -- Donsker–Varadhan
  have hgB : ∀ X, |a₀ * G X| ≤ a₀ * BG := fun X => by
    rw [abs_mul, abs_of_pos ha₀]; exact mul_le_mul_of_nonneg_left (hGB X) ha₀.le
  have hdv := dvFun_le_klDiv (ρ := ν) (ν := P) (hGm.const_mul a₀) hgB
  rw [← ENNReal.ofReal_toReal hH, EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
    at hdv
  have hdv' := EReal.coe_le_coe_iff.mp hdv
  unfold dvFun at hdv'
  -- the exponential moment
  have hexp_int : Integrable (fun X => exp (a₀ * G X)) P :=
    Integrable.of_bound (measurable_exp.comp (hGm.const_mul a₀)).aestronglyMeasurable
      (exp (a₀ * BG)) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (hgB X)))
  have hZ1 : 1 ≤ ∫ X, exp (a₀ * G X) ∂P := by
    have := integral_mono (integrable_const (1 : ℝ)) hexp_int fun X =>
      Real.one_le_exp (mul_nonneg ha₀.le (hG0 X))
    simpa using this
  have hZle : ∫ X, exp (a₀ * G X) ∂P ≤ CE' := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => (exp_pos _).le)
      hexp_int.aestronglyMeasurable]
    have h1 : ∫⁻ X, ENNReal.ofReal (exp (a₀ * G X)) ∂P =
        ∫⁻ X, ENNReal.ofReal (exp (a₀ * gradSqC (Ucentered W μ N) X)) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with X hX
      rw [hX]
    rw [h1]
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hCE N hN)
    rw [ENNReal.toReal_ofReal'] at h2
    exact h2.trans (max_le_max le_rfl zero_le_one)
  have hlogZ : Real.log (∫ X, exp (a₀ * G X) ∂P) ≤ L :=
    Real.log_le_log (by linarith) hZle
  -- `a₀ E_ν G ≤ H_0 + L`
  have hGν : a₀ * ∫ X, G X ∂ν ≤ (klDiv ν P).toReal + L := by
    rw [← integral_const_mul]; linarith
  -- (5.6)
  have h56 := (hR N hN).1 ν hν hsym
  have hH0 : (klDiv ν P).toReal ≤ C19' * ((klDiv ν (gibbs V W N)).toReal + 1) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.one_ne_top⟩)) h56
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_add hfin ENNReal.one_ne_top,
      ENNReal.toReal_one] at this
  -- conclusion
  have hGi : Integrable G ν := Integrable.of_bound hGm.aestronglyMeasurable BG
    (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hGB X)
  have hlin : ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν = ENNReal.ofReal (∫ X, G X ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0)]
    refine lintegral_congr_ae ?_
    filter_upwards [hνP.ae_le hae] with X hX
    rw [hX]
  rw [hlin]
  set HP := (klDiv ν (gibbs V W N)).toReal
  have hHP : 0 ≤ HP := ENNReal.toReal_nonneg
  have hfinal : ∫ X, G X ∂ν ≤ C * (HP + 1) := by
    have : ∫ X, G X ∂ν ≤ ((klDiv ν P).toReal + L) / a₀ := by
      rw [le_div_iff₀ ha₀]; linarith
    refine this.trans ?_
    simp only [C]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha₀]
    nlinarith [le_max_right C19 0]
  calc ENNReal.ofReal (∫ X, G X ∂ν) ≤ ENNReal.ofReal (C * (HP + 1)) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_add hHP zero_le_one, ENNReal.ofReal_one,
          ENNReal.ofReal_toReal hfin]

end force

end SharpLSI
