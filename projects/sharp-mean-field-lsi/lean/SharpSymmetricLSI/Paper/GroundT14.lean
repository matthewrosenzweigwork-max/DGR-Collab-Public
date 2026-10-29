import SharpSymmetricLSI.Paper.GroundT13

/-!
# R30 groundwork: uniform integrability under `P_N` ((7.9))

`∫_{f² > M} f² dP_N = (K'/K_N) ∫_{Ψ'² > M w(U_N)} Ψ'² dμ^{⊗N}` with `Ψ' = f √w(U_N)`,
`w(u) = e^{-u}/K'`. On `{U_N ≤ t}`, `w(U_N) ≥ η = w(t)`, so the set is inside
`{Ψ'² > Mη} ∪ {U_N > t}`; the second has `μ^{⊗N}`-measure `≤ CU/t²` (Chebyshev).
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

theorem pi_ac_gibbs (N : ℕ) :
    Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≪ gibbs V W N := by
  rw [gibbs_eq_centered_aux hyp hμ N]
  refine withDensity_absolutelyContinuous' ?_ (Eventually.of_forall fun X => ?_)
  · exact (ENNReal.measurable_ofReal.comp (((measurable_Ucentered hyp _ N).neg.exp).div_const
      _)).aemeasurable
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (Real.exp_pos _) (centeredPartition_pos hyp _ N)

/-- **(7.9)**, one particle number. -/
theorem ui_transfer {N : ℕ} {K' : ℝ} (hK' : 0 < K') {f : Config N d → ℝ}
    (hfm : AEStronglyMeasurable f (gibbs V W N)) {L t ε' CU : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hCU : ∫ X, Ucentered W μ N X ^ 2 ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ CU)
    (hui : ∫⁻ X in {X | L < (f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) ^ 2},
      ENNReal.ofReal ((f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) ^ 2)
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal ε') :
    ∫⁻ X in {X | L / wK K' t < f X ^ 2}, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N ≤
      ENNReal.ofReal (K' / centeredPartition W μ N) *
        (ENNReal.ofReal ε' + (ENNReal.ofReal ε' + ENNReal.ofReal (L * (CU / t ^ 2)))) := by
  set Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set P := gibbs V W N
  set K := centeredPartition W μ N
  have hK : 0 < K := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  set η := wK K' t
  have hη : 0 < η := wK_pos hK' t
  set M := L / η
  obtain ⟨g, hgm, hgf, -⟩ := exists_measurable_rep hyp hfm
  have hgfQ : g =ᵐ[Q] f := (pi_ac_gibbs hyp hμ N).ae_le hgf
  have hUm := measurable_Ucentered hyp (μ : Measure (Torus d)) N
  set ψ : Config N d → ℝ := fun X => g X * Real.sqrt (rexp (-Ucentered W μ N X) / K')
  have hψm : Measurable ψ := hgm.mul (Real.continuous_sqrt.measurable.comp (hUm.neg.exp.div_const _))
  -- replace `f` by `g`
  have hS : {X | M < f X ^ 2} =ᵐ[P] {X | M < g X ^ 2} :=
    hgf.mono fun X hX => by show (M < f X ^ 2) = (M < g X ^ 2); rw [hX]
  have e1 : ∫⁻ X in {X | M < f X ^ 2}, ENNReal.ofReal (f X ^ 2) ∂P =
      ∫⁻ X in {X | M < g X ^ 2}, ENNReal.ofReal (g X ^ 2) ∂P := by
    rw [Measure.restrict_congr_set hS]
    exact lintegral_congr_ae (ae_restrict_of_ae (hgf.mono fun X hX => by simp only [hX]))
  have hSQ : {X | L < (f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) ^ 2} =ᵐ[Q]
      {X | L < ψ X ^ 2} := hgfQ.mono fun X hX => by
    show (L < (f X * _) ^ 2) = (L < (g X * _) ^ 2); rw [hX]
  have hui' : ∫⁻ X in {X | L < ψ X ^ 2}, ENNReal.ofReal (ψ X ^ 2) ∂Q ≤ ENNReal.ofReal ε' := by
    refine le_trans (le_of_eq ?_) hui
    rw [Measure.restrict_congr_set hSQ]
    exact lintegral_congr_ae (ae_restrict_of_ae (hgfQ.mono fun X hX => by simp only [ψ, hX]))
  rw [e1]
  -- change of measure
  have hρm : Measurable fun X => ENNReal.ofReal (rexp (-Ucentered W μ N X) / K) :=
    ENNReal.measurable_ofReal.comp (hUm.neg.exp.div_const _)
  have hSm : MeasurableSet {X | M < g X ^ 2} := measurableSet_lt measurable_const (hgm.pow_const 2)
  have e2 : ∫⁻ X in {X | M < g X ^ 2}, ENNReal.ofReal (g X ^ 2) ∂P =
      ENNReal.ofReal (K' / K) * ∫⁻ X in {X | M < g X ^ 2}, ENNReal.ofReal (ψ X ^ 2) ∂Q := by
    rw [show P = Q.withDensity fun X => ENNReal.ofReal (rexp (-Ucentered W μ N X) / K) from
      gibbs_eq_centered_aux hyp hμ N, restrict_withDensity hSm,
      lintegral_withDensity_eq_lintegral_mul _ hρm (hgm.pow_const 2).ennreal_ofReal,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun X => ?_
    simp only [Pi.mul_apply, ψ]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hK.le),
      ← ENNReal.ofReal_mul (div_nonneg hK'.le hK.le), mul_pow,
      Real.sq_sqrt (div_nonneg (Real.exp_pos _).le hK'.le)]
    congr 1; field_simp
  rw [e2]
  refine mul_le_mul_right ?_ _
  -- the covering
  have hcov : {X | M < g X ^ 2} ⊆ {X | L < ψ X ^ 2} ∪ {X | t < Ucentered W μ N X} := by
    intro X hX
    simp only [mem_setOf_eq, mem_union] at hX ⊢
    by_contra h
    push_neg at h
    have hw : η ≤ rexp (-Ucentered W μ N X) / K' :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [h.2])) hK'.le
    have h1 : ψ X ^ 2 = g X ^ 2 * (rexp (-Ucentered W μ N X) / K') := by
      simp only [ψ]; rw [mul_pow, Real.sq_sqrt (div_nonneg (Real.exp_pos _).le hK'.le)]
    have h2 : L = M * η := by simp only [M]; field_simp
    have : L < ψ X ^ 2 := by
      rw [h1, h2]
      calc M * η < g X ^ 2 * η := mul_lt_mul_of_pos_right hX hη
        _ ≤ g X ^ 2 * (rexp (-Ucentered W μ N X) / K') :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    exact absurd this (not_lt.2 h.1)
  set A := {X | L < ψ X ^ 2}
  set T := {X | t < Ucentered W μ N X}
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (hψm.pow_const 2)
  have hT : ∫⁻ X in T, ENNReal.ofReal (ψ X ^ 2) ∂Q ≤
      ENNReal.ofReal ε' + ENNReal.ofReal (L * (CU / t ^ 2)) := by
    have hcovT : T ⊆ A ∪ (T ∩ Aᶜ) := fun X hX => by
      by_cases h : X ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hX, h⟩
    refine (lintegral_mono_set hcovT).trans ((lintegral_union_le _ _ _).trans (add_le_add hui' ?_))
    have hTm : MeasurableSet T := measurableSet_lt measurable_const hUm
    calc ∫⁻ X in T ∩ Aᶜ, ENNReal.ofReal (ψ X ^ 2) ∂Q ≤ ∫⁻ X in T ∩ Aᶜ, ENNReal.ofReal L ∂Q := by
          refine setLIntegral_mono' (hTm.inter hAm.compl) fun X hX => ?_
          exact ENNReal.ofReal_le_ofReal (not_lt.1 hX.2)
      _ = ENNReal.ofReal L * Q (T ∩ Aᶜ) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (CU / t ^ 2) :=
          mul_le_mul_right ((measure_mono inter_subset_left).trans
            (measure_Ucentered_gt_le hyp hCU ht)) _
      _ = ENNReal.ofReal (L * (CU / t ^ 2)) := (ENNReal.ofReal_mul hL.le).symm
  calc ∫⁻ X in {X | M < g X ^ 2}, ENNReal.ofReal (ψ X ^ 2) ∂Q ≤ ∫⁻ X in A ∪ T, ENNReal.ofReal (ψ X ^ 2) ∂Q :=
        lintegral_mono_set hcov
    _ ≤ _ := (lintegral_union_le _ _ _).trans (add_le_add hui' hT)

end

end SharpLSI
