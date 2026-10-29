import SharpSymmetricLSI.Paper.Sec5_5
import SharpSymmetricLSI.Paper.GroundT8

/-!
# R20 (Lemma 5.3), part 2: the reference Fisher information (5.15) and the assembly

With `f = √(dν/dP_N)` and `p_N = e^{-U_N}/K_N`, `√(dν/dμ^{⊗N}) = f √p_N` a.e., and the ground-state
gradient bound (`lintegral_gradSqC_psi_le`) gives
`I(ν|μ^{⊗N}) ≤ 2 I(ν|P_N) + 2 E_ν|∇U_N|²` (`fisher_ref_le`). Together with (5.13)
(`force_exp_moment`) and (5.14) (`force_under_nu_of`) this is Lemma 5.3, conditional on Lemma 4.2.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem ac_of_map_flat_ac {N : ℕ} {ν P : Measure (Config N d)} (h : ν.map flat ≪ P.map flat) :
    ν ≪ P := by
  intro s hs
  have e : ∀ Q : Measure (Config N d), Q.map flat (flat '' s) = Q s := fun Q => by
    rw [measurableEmbedding_flat.map_apply, Set.preimage_image_eq _ measurableEmbedding_flat.injective]
  rw [← e ν]; rw [← e P] at hs
  exact h hs

section fisher
variable (hyp : Hyp V W KV KW)
include hyp

theorem fisher_ref_le {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {N : ℕ}
    (hN : 1 ≤ N) (ν : Measure (Config N d)) [IsProbabilityMeasure ν] :
    fisherInfoC ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
      2 * fisherInfoC ν (gibbs V W N) +
        ENNReal.ofReal 2 * ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν := by
  set μm := (μ : Measure (Torus d))
  set Q := Measure.pi fun _ : Fin N => μm
  set P := gibbs V W N
  haveI : IsProbabilityMeasure P := gibbs_isProbabilityMeasure hyp N
  by_cases hI : fisherInfoC ν P = ⊤
  · rw [hI, ENNReal.mul_top (by norm_num), top_add]; exact le_top
  set J := ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν
  by_cases hJ : J = ⊤
  · rw [hJ, ENNReal.mul_top (by simp), add_top]; exact le_top
  -- `ν ≪ P` and `f = √(dν/dP) ∈ H¹(P)`
  have hcond : ν.map flat ≪ P.map flat := by
    by_contra hc
    apply hI
    unfold fisherInfoC fisherInfo
    rw [if_neg (fun h => hc h.1)]
  have hac : ν ≪ P := ac_of_map_flat_ac hcond
  have hfe := fisherInfoC_eq hyp hac
  set f := sqrtDens ν P
  have hf : MemH1C P f := by
    by_contra hc
    apply hI
    rw [hfe, if_neg hc]
  rw [hfe, if_pos hf] at hI ⊢
  have hE : energy V W N f ≠ ⊤ := fun h => hI (by rw [h, ENNReal.mul_top (by norm_num)])
  -- `P = p μ^{⊗N}`
  set p : Config N d → ℝ := fun X => rexp (-Ucentered W μ N X) / centeredPartition W μ N
  have hK := centeredPartition_pos hyp μm N
  have hp0 : ∀ X, 0 ≤ p X := fun X => div_nonneg (exp_pos _).le hK.le
  have hpm : Measurable fun X => ENNReal.ofReal (p X) :=
    ENNReal.measurable_ofReal.comp (((measurable_Ucentered hyp _ N).neg.exp).div_const _)
  have hPQ : P = Q.withDensity fun X => ENNReal.ofReal (p X) := gibbs_eq_centered_aux hyp hμ N
  have hPQac : P ≪ Q := by rw [hPQ]; exact withDensity_absolutelyContinuous _ _
  -- `√(dν/dQ) = f √p` a.e.
  set Ψ : Config N d → ℝ := fun X => f X * Real.sqrt (p X)
  have hΨ : sqrtDens ν Q =ᵐ[Q] Ψ := by
    have h1 := Measure.rnDeriv_mul_rnDeriv (κ := Q) hac
    have h2 : P.rnDeriv Q =ᵐ[Q] fun X => ENNReal.ofReal (p X) := by
      rw [hPQ]; exact Measure.rnDeriv_withDensity Q hpm
    filter_upwards [h1, h2] with X hX1 hX2
    simp only [sqrtDens, Ψ, f]
    rw [← hX1, Pi.mul_apply, hX2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp0 X),
      Real.sqrt_mul ENNReal.toReal_nonneg]
  -- `Ψ ∈ H¹(μ^{⊗N})`
  have hΨw := isWeakGrad_psi hyp hμ hN hf
  have hQac := pi_map_flat_ac hyp hμ (N := N)
  have hvolQ : (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≪ Q.map flat :=
    (gibbs_map_flat_ac hyp N).2.trans (hPQac.map measurable_flat)
  have hΨm : Measurable Ψ :=
    ((Measure.measurable_rnDeriv ν P).ennreal_toReal.sqrt).mul
      (((measurable_Ucentered hyp _ N).neg.exp).div_const _).sqrt
  have hL2 : ∫⁻ X, ENNReal.ofReal (Ψ X ^ 2) ∂Q < ⊤ := by
    rw [lintegral_psi_sq hyp hμ f]
    calc ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂P = ∫⁻ X, ν.rnDeriv P X ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [Measure.rnDeriv_lt_top ν P] with X hX
          simp only [f, sqrtDens]
          rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hX.ne]
      _ ≤ ν Set.univ := Measure.lintegral_rnDeriv_le
      _ < ⊤ := measure_lt_top _ _
  have hgrad := lintegral_gradSqC_psi_le hyp hμ hN hf
  -- `∫ f² |∇U|² dP = E_ν |∇U|²`
  have hJeq : ∫⁻ X, ENNReal.ofReal (f X ^ 2 * gradSqC (Ucentered W μ N) X) ∂P = J := by
    have hU := isWeakGrad_gsU hyp (minimizer_ac hyp hμ) hN (μ := μm)
    have hGm : AEMeasurable (fun X => ENNReal.ofReal (gradSqC (Ucentered W μ N) X)) P :=
      ((aemeasurable_gradSqC_pi hyp hμ ⟨_, hU⟩).ennreal_ofReal).mono_ac hPQac
    rw [show J = _ from (lintegral_rnDeriv_mul hac hGm).symm]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν P] with X hX
    simp only [f, sqrtDens]
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hX.ne]
  rw [hJeq] at hgrad
  have hgrad_fin : ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q < ⊤ :=
    hgrad.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE.lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Ne.lt_top hJ)⟩)
  have hH1 : MemH1 (Q.map flat) (Ψ ∘ unflat) := by
    refine ⟨⟨_, hΨw⟩, ?_, ?_⟩
    · refine memLp_two_of_lintegral (hΨm.comp measurable_unflat).aestronglyMeasurable ?_
      rw [measurableEmbedding_flat.lintegral_map]
      exact hL2
    · refine memLp_two_of_lintegral
        ((Real.continuous_sqrt.comp_aestronglyMeasurable
          (isWeakGrad_weakGrad ⟨_, hΨw⟩).aestronglyMeasurable_sqNorm).mono_ac hQac) ?_
      rw [measurableEmbedding_flat.lintegral_map]
      calc ∫⁻ X, ENNReal.ofReal (Real.sqrt (sqNorm (weakGrad (Ψ ∘ unflat) (flat X))) ^ 2) ∂Q
          = ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q := by
            refine lintegral_congr fun X => ?_
            rw [Real.sq_sqrt (sqNorm_nonneg _), gradSqC_eq_sqNorm]
        _ < ⊤ := hgrad_fin
  -- identify the Fisher information against `μ^{⊗N}`
  set u : UnitAddTorus (Fin N × Fin d) → ℝ :=
    fun y => Real.sqrt ((ν.map flat).rnDeriv (Q.map flat) y).toReal
  have hu : (Ψ ∘ unflat) =ᵐ[Q.map flat] u := by
    have hmap := measurableEmbedding_flat.rnDeriv_map ν Q
    refine ae_map_flat_of_ae (p := fun y => (Ψ ∘ unflat) y = u y) ?_
    filter_upwards [hmap, hΨ] with X hX hX'
    simp only [Function.comp_apply, u]
    rw [show unflat (flat X) = X from rfl, ← hX', sqrtDens, ← hX]
  have hc := memH1_congr_ae hQac hvolQ hH1 hu
  have hacQ : ν.map flat ≪ Q.map flat := (hac.trans hPQac).map measurable_flat
  have hFQ : fisherInfoC ν Q = 4 * ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q := by
    unfold fisherInfoC fisherInfo
    rw [if_pos ⟨hacQ, hc.1⟩, hc.2]
    congr 1
    unfold dirichlet
    rw [measurableEmbedding_flat.lintegral_map]
    refine lintegral_congr fun X => ?_
    rw [gradSqC_eq_sqNorm]
  rw [hFQ]
  calc 4 * ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q
      ≤ 4 * (ENNReal.ofReal 2 * energy V W N f + ENNReal.ofReal (1 / 2) * J) := by gcongr
    _ = 2 * (4 * energy V W N f) + ENNReal.ofReal 2 * J := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc]
        congr 1
        · rw [show (4 : ℝ≥0∞) * ENNReal.ofReal 2 = 2 * 4 by
            rw [ENNReal.ofReal_ofNat]; ring]
        · rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num

end fisher

section assembly
variable (hyp : Hyp V W KV KW)
include hyp

/-- **Lemma 5.3**, (5.13)–(5.15), conditional on Lemma 4.2. -/
theorem force_exponential_of (hd : 1 ≤ d) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (hco : MFCoercive V W μ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ X, ENNReal.ofReal (Real.exp (a₀ * gradSqC (Ucentered W μ N) X))
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal C ∧
      ∀ ν : Measure (Config N d), IsProbabilityMeasure ν → IsSymmetricMeasure ν →
        klDiv ν (gibbs V W N) ≠ ⊤ →
        ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
            ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ∧
        fisherInfoC ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
          2 * fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
  obtain ⟨a₀, CE, ha₀, hCE⟩ := force_exp_moment hd hyp hμ
  obtain ⟨C14, hC14, hF⟩ := force_under_nu_of hyp hd hμ hco
  set C := max CE (2 * C14)
  refine ⟨a₀, C, ha₀, fun N hN => ⟨(hCE N hN).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
    fun ν hν hsym hfin => ?_⟩⟩
  have h14 := hF N hN ν hν hsym hfin
  have hC2 : C14 ≤ C := by
    have := le_max_right CE (2 * C14); linarith
  refine ⟨h14.trans (by gcongr), ?_⟩
  refine (fisher_ref_le hyp hμ hN ν).trans (add_le_add le_rfl ?_)
  calc ENNReal.ofReal 2 * ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν
      ≤ ENNReal.ofReal 2 * (ENNReal.ofReal C14 * (klDiv ν (gibbs V W N) + 1)) := by gcongr
    _ = ENNReal.ofReal (2 * C14) * (klDiv ν (gibbs V W N) + 1) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
        gcongr; exact le_max_right _ _

end assembly

end SharpLSI
