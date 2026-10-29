import FullLabeledLSI.Paper.Prop23Defs
import FullLabeledLSI.Statements.S19_Lemma_5_2
import SharpSymmetricLSI.Statements.R19_Lemma_5_2

/-!
# Proposition 2.3, WP-A: the non-symmetric ground-state transform

`ground_transform_nosym`: for bounded `f ∈ H¹(P_N)` (`|f| ≤ B` a.e.), the ground state
`Ψ_N = f √p_N` (`psiG`) lies in `H¹(Q_N)`, `‖Ψ_N‖₂ = ‖f‖₂`,
`∫|∇Ψ_N|² ≤ 2 ℰ_N(f) + C B²` and `∫|Ψ_N|^{2p} ≤ C B^{2p}`; no permutation symmetry is used.
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `gibbs`-a.e. statements are `Q_N`-a.e. statements (`Q_N ≪ P_N`). -/
theorem ae_QN_of_ae_gibbs (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (N : ℕ) {P : Config N d → Prop}
    (h : ∀ᵐ X ∂gibbs V W N, P X) : ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, P X := by
  rw [gibbs_eq_centered_aux hyp hμ N] at h
  have h := (ae_withDensity_iff (f := fun X => ENNReal.ofReal (Real.exp (-Ucentered W
    (μ : Measure (Torus d)) N X) / centeredPartition W (μ : Measure (Torus d)) N))
    (ENNReal.measurable_ofReal.comp
      (((measurable_Ucentered hyp (μ : Measure (Torus d)) N).neg.exp).div_const _))).1 h
  filter_upwards [h] with X hX
  exact hX (ENNReal.ofReal_pos.2 (div_pos (Real.exp_pos _)
    (centeredPartition_pos hyp (μ : Measure (Torus d)) N))).ne'

/-- The `2p` moment of the ground state. -/
theorem lintegral_psiG_rpow_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    {N : ℕ} {C1 p : ℝ}
    (hmom : ∫ X, (Real.exp (-Ucentered W (μ : Measure (Torus d)) N X) /
        centeredPartition W (μ : Measure (Torus d)) N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C1) (hp : 0 ≤ p)
    {f : Config N d → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, |f X| ≤ B) :
    ∫⁻ X, ENNReal.ofReal (|psiG W (μ : Measure (Torus d)) N f X| ^ (2 * p))
        ∂QN (μ : Measure (Torus d)) N ≤ ENNReal.ofReal (C1 * B ^ (2 * p)) := by
  have : IsProbabilityMeasure (QN (μ : Measure (Torus d)) N) := by unfold QN; infer_instance
  set K := centeredPartition W (μ : Measure (Torus d)) N
  have hK := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  set q : Config N d → ℝ := fun X => Real.exp (-Ucentered W (μ : Measure (Torus d)) N X) / K with hq
  have hq0 : ∀ X, 0 ≤ q X := fun X => (div_pos (Real.exp_pos _) hK).le
  have hqm : Measurable q := ((measurable_Ucentered hyp _ N).neg.exp).div_const _
  have hpt : ∀ X, |psiG W (μ : Measure (Torus d)) N f X| ^ (2 * p) = |f X| ^ (2 * p) * q X ^ p := by
    intro X
    have : |psiG W (μ : Measure (Torus d)) N f X| = |f X| * Real.sqrt (q X) := by
      simp only [psiG]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [this, Real.mul_rpow (abs_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (hq0 X)]
    congr 2; ring
  -- integrability of `q ^ p`
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp (μ : Measure (Torus d)) N
  have hint : Integrable (fun X => q X ^ p) (QN (μ : Measure (Torus d)) N) := by
    refine Integrable.of_bound (C := (Real.exp BU / K) ^ p) (hqm.pow_const p).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hq0 X) _)]
    refine Real.rpow_le_rpow (hq0 X) ?_ hp
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by
      have := hBU X; rw [abs_le] at this; linarith)) hK.le
  have hnn : 0 ≤ᵐ[QN (μ : Measure (Torus d)) N] fun X => q X ^ p :=
    Eventually.of_forall fun X => Real.rpow_nonneg (hq0 X) _
  have hlin : ∫⁻ X, ENNReal.ofReal (q X ^ p) ∂QN (μ : Measure (Torus d)) N =
      ENNReal.ofReal (∫ X, q X ^ p ∂QN (μ : Measure (Torus d)) N) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  calc ∫⁻ X, ENNReal.ofReal (|psiG W (μ : Measure (Torus d)) N f X| ^ (2 * p))
          ∂QN (μ : Measure (Torus d)) N
      ≤ ∫⁻ X, ENNReal.ofReal (B ^ (2 * p)) * ENNReal.ofReal (q X ^ p)
          ∂QN (μ : Measure (Torus d)) N := by
        refine lintegral_mono_ae ?_
        filter_upwards [hB] with X hX
        rw [hpt, ← ENNReal.ofReal_mul (Real.rpow_nonneg hB0 _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) hX (by linarith)) (Real.rpow_nonneg (hq0 X) _))
    _ = ENNReal.ofReal (B ^ (2 * p)) * ENNReal.ofReal (∫ X, q X ^ p ∂QN (μ : Measure (Torus d)) N) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlin]
    _ ≤ ENNReal.ofReal (B ^ (2 * p)) * ENNReal.ofReal C1 := by
        gcongr
        exact hmom
    _ = ENNReal.ofReal (C1 * B ^ (2 * p)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB0 _), mul_comm]

/-- **WP-A**: the non-symmetric ground-state transform for bounded `f`. -/
theorem ground_transform_nosym (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ p C : ℝ, 1 < p ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : Config N d → ℝ) (B : ℝ),
      MemH1C (gibbs V W N) f → (∀ᵐ X ∂gibbs V W N, |f X| ≤ B) →
      MemH1C (QN (μ : Measure (Torus d)) N) (psiG W (μ : Measure (Torus d)) N f) ∧
      ∫⁻ X, ENNReal.ofReal (psiG W (μ : Measure (Torus d)) N f X ^ 2)
          ∂QN (μ : Measure (Torus d)) N = ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N ∧
      ∫⁻ X, ENNReal.ofReal (gradSqC (psiG W (μ : Measure (Torus d)) N f) X)
          ∂QN (μ : Measure (Torus d)) N ≤ 2 * energy V W N f + ENNReal.ofReal (C * B ^ 2) ∧
      ∫⁻ X, ENNReal.ofReal (|psiG W (μ : Measure (Torus d)) N f X| ^ (2 * p))
          ∂QN (μ : Measure (Torus d)) N ≤ ENNReal.ofReal (C * B ^ (2 * p)) := by
  obtain ⟨C1, p, hp, hC1⟩ := SharpLSI.reference_entropy hd hyp hr hμ
  obtain ⟨C2, hC2⟩ := reference_all hd hyp hr μ hμ
  set C : ℝ := max (max C1 C2) 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC1le : C1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2le : C2 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨p, C, hp, hC0, fun N hN f B hf hB => ?_⟩
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hB0 : 0 ≤ B := by
    obtain ⟨X, hX⟩ := hB.exists
    exact (abs_nonneg _).trans hX
  have hfL := memLp_of_memH1C hyp hf
  have hE := energy_lt_top hyp hf
  have hM : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).1 hfL.integrable_sq.2
  -- force term, via `reference_all` at `ν = gibbs`
  have hforce : ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W (μ : Measure (Torus d)) N) X)
      ∂gibbs V W N ≤ ENNReal.ofReal C2 := by
    have h := (hC2 N hN (gibbs V W N) inferInstance (by rw [klDiv_self]; simp)).2.1
    rwa [klDiv_self, zero_add, mul_one] at h
  have hJ : ∫⁻ X, ENNReal.ofReal (f X ^ 2 * gradSqC (Ucentered W (μ : Measure (Torus d)) N) X)
      ∂gibbs V W N ≤ ENNReal.ofReal (B ^ 2 * C2) := by
    calc ∫⁻ X, ENNReal.ofReal (f X ^ 2 * gradSqC (Ucentered W (μ : Measure (Torus d)) N) X)
          ∂gibbs V W N
        ≤ ∫⁻ X, ENNReal.ofReal (B ^ 2) *
            ENNReal.ofReal (gradSqC (Ucentered W (μ : Measure (Torus d)) N) X) ∂gibbs V W N := by
          refine lintegral_mono_ae ?_
          filter_upwards [hB] with X hX
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (gradSqC_nonneg _ _))
          calc f X ^ 2 = |f X| ^ 2 := (sq_abs _).symm
            _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hX 2
      _ = ENNReal.ofReal (B ^ 2) * ∫⁻ X, ENNReal.ofReal
            (gradSqC (Ucentered W (μ : Measure (Torus d)) N) X) ∂gibbs V W N :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal C2 := by gcongr
      _ = ENNReal.ofReal (B ^ 2 * C2) := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hgrad : ∫⁻ X, ENNReal.ofReal (gradSqC (psiG W (μ : Measure (Torus d)) N f) X)
      ∂QN (μ : Measure (Torus d)) N ≤ 2 * energy V W N f + ENNReal.ofReal (C * B ^ 2) := by
    have h1 := lintegral_gradSqC_psi_le hyp hμ hN hf
    refine h1.trans ?_
    rw [ENNReal.ofReal_ofNat]
    gcongr
    calc ENNReal.ofReal (1 / 2) * ∫⁻ X, ENNReal.ofReal
          (f X ^ 2 * gradSqC (Ucentered W (μ : Measure (Torus d)) N) X) ∂gibbs V W N
        ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (B ^ 2 * C2) := by gcongr
      _ = ENNReal.ofReal (1 / 2 * (B ^ 2 * C2)) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ ≤ ENNReal.ofReal (C * B ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ B ^ 2 * (C - C2 / 2) := mul_nonneg (sq_nonneg _) (by linarith)
        nlinarith
  have hiso := lintegral_psi_sq hyp hμ f (N := N)
  have hmom := lintegral_psiG_rpow_le hyp (N := N) (C1 := C) (p := p)
    (le_trans (hC1 N hN).2.2 hC1le) (by linarith) (f := f) hB0 (ae_QN_of_ae_gibbs hyp hμ N hB)
  refine ⟨?_, hiso, hgrad, ?_⟩
  · -- `H¹(μ^{⊗N})`
    have hfin : ∫⁻ X, ENNReal.ofReal (gradSqC (psiG W (μ : Measure (Torus d)) N f) X)
        ∂QN (μ : Measure (Torus d)) N < ⊤ :=
      hgrad.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hE,
        ENNReal.ofReal_lt_top⟩)
    have hpair := isWeakGrad_psi hyp hμ hN hf
    have hac := pi_map_flat_ac hyp hμ (N := N)
    have hemb := measurableEmbedding_flat (N := N) (d := d)
    refine ⟨⟨_, hpair⟩, ?_, ?_⟩
    · refine memLp_two_of_lintegral (hpair.aestronglyMeasurable_fun.mono_ac hac) ?_
      rw [hemb.lintegral_map]
      exact (hiso.trans_lt hM)
    · have hw := isWeakGrad_weakGrad ⟨_, hpair⟩
      have hm : AEStronglyMeasurable
          (fun y => Real.sqrt (sqNorm (weakGrad (psiG W (μ : Measure (Torus d)) N f ∘ unflat) y)))
          volume := by
        unfold sqNorm
        exact Real.continuous_sqrt.comp_aestronglyMeasurable
          (Finset.aestronglyMeasurable_fun_sum _ fun p _ => (hw.aestronglyMeasurable_grad p).pow 2)
      refine memLp_two_of_lintegral (hm.mono_ac hac) ?_
      rw [hemb.lintegral_map]
      have : ∀ X, Real.sqrt (sqNorm (weakGrad (psiG W (μ : Measure (Torus d)) N f ∘ unflat)
          (flat X))) ^ 2 = gradSqC (psiG W (μ : Measure (Torus d)) N f) X := fun X => by
        have hn : 0 ≤ sqNorm (weakGrad (psiG W (μ : Measure (Torus d)) N f ∘ unflat) (flat X)) :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        rw [Real.sq_sqrt hn, gradSqC_eq_sqNorm]
      simp_rw [this]
      exact hfin
  · exact hmom

end SharpLSI.FL
