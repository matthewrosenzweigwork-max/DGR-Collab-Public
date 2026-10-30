import DGPS.Lipschitz.T01OccupationCompactness
import SharpSymmetricLSI.Paper.R29UI

/-!
# Uniform integrability of actual reference occupation tests

Finite occupation projections have uniform fourth moments on the actual common basis.
The actual reference H1 energy bounds the complementary square mass. The original
functions and their a.e. symmetry are retained throughout.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz
open KernelApproximation SharpLSI

variable {d : ℕ}

private theorem t01_ui_memLp_occ (S : Spec d) (he : IsRefEigenbasis S.mu S.v S.lam)
    (α : ℕ →₀ ℕ) (N : ℕ) :
    MemLp (occBasis S.v α N) 2 (Measure.pi fun _ : Fin N => S.mu) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  unfold occBasis
  exact (memLp_finsetSum _ fun c _ => memLp_prod_eval fun i => he.memLp _).const_mul _

private theorem t01_ui_integrable_occ_pow4 (S : Spec d) (α : ℕ →₀ ℕ) (N : ℕ) :
    Integrable (fun X => occBasis S.v α N X ^ 4) (Measure.pi fun _ : Fin N => S.mu) := by
  have hc : Continuous (occBasis S.v α N) := by
    unfold occBasis
    exact continuous_const.mul (continuous_finsetSum _ fun c _ =>
      continuous_finsetProd _ fun i _ => (S.vc _).comp (continuous_apply i))
  exact (hc.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Uniform square-mass tails for the actual a.e.-symmetric reference H1 domain.
The threshold is uniform in particle number and every test with the stated mass/energy bounds. -/
theorem t01_reference_occupation_uniform_integrability (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, SharpLSI.FL.Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (htend : Tendsto S.lam atTop atTop) {B : ℝ} (hB0 : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (N : ℕ) (Ψ : Config N d → ℝ),
      MemH1C (Measure.pi fun _ : Fin N => S.mu) Ψ →
      (∀ σ : Equiv.Perm (Fin N), (fun X => Ψ (X ∘ σ)) =ᵐ[
        Measure.pi (fun _ : Fin N => S.mu)] Ψ) →
      (∫ X, Ψ X ^ 2 ∂Measure.pi (fun _ : Fin N => S.mu)) ≤ B →
      (SharpLSI.FL.refEnergy S.mu Ψ).toReal ≤ B →
      ∫⁻ X in {X | M < Ψ X ^ 2}, ENNReal.ofReal (Ψ X ^ 2)
        ∂Measure.pi (fun _ : Fin N => S.mu) ≤ ENNReal.ofReal ε := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  set L : ℝ := 4 * B / ε + 1
  have hL : 0 < L := by positivity
  set T := (t01_finite_occupation_energy_sublevel S hmono hlam1 htend L).toFinset
  have hS : ∀ α, occEnergy S.lam α ≤ L → α ∈ T := fun α h => by simp [T, h]
  have hBdd : ∀ j, ∃ C : ℝ, ∀ᵐ x ∂S.mu, |S.v j x| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := SharpLSI.exists_bound_of_continuous (S.vc j)
    exact ⟨C, Eventually.of_forall hC⟩
  choose Cm hCm using fun α => occBasis_moments_of_bdd he hBdd α 4
  set C' : (ℕ →₀ ℕ) → ℝ := fun α => max (Cm α) 0
  set K : ℝ := (T.card : ℝ) * B * ∑ α ∈ T, Real.sqrt (C' α)
  have hK0 : 0 ≤ K := by positivity
  set M : ℝ := B * (4 * K / ε) ^ 2 + 1
  have hM : 0 < M := by positivity
  refine ⟨M, hM, fun N Ψ hΨ hsym hB1 hB2 => ?_⟩
  set P := Measure.pi fun _ : Fin N => S.mu
  have hΨL : MemLp Ψ 2 P := (measurableEmbedding_flat.memLp_map_measure_iff).mp hΨ.2.1
  set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ Y, Ψ Y * occBasis S.v α N Y ∂P
  have hpar := t01_hasSum_sq_reference_occupation S he hΨL hsym
  have hc2 : ∀ α, c α ^ 2 ≤ B := by
    intro α
    have hx := (sum_le_hasSum {α} (fun β _ => sq_nonneg _) hpar).trans hB1
    simpa only [Finset.sum_singleton] using hx
  have hB4 : ∀ α, ∫ X, occBasis S.v α N X ^ 4 ∂P ≤ C' α := fun α => by
    by_cases hN : occSize α ≤ N
    · have h := hCm α N hN
      calc ∫ X, occBasis S.v α N X ^ 4 ∂P = ∫ X, |occBasis S.v α N X| ^ 4 ∂P := by
            congr 1; funext X; rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        _ ≤ C' α := h.trans (le_max_left _ _)
    · rw [occBasis_zero_of_lt (show N < occSize α by omega)]
      simp [C']
  -- a measurable representative
  set Ψ' := hΨL.aestronglyMeasurable.mk Ψ
  have hΨΨ : Ψ =ᵐ[P] Ψ' := hΨL.aestronglyMeasurable.ae_eq_mk
  have hΨ'm : Measurable Ψ' := hΨL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hΨ'L : MemLp Ψ' 2 P := hΨL.ae_eq hΨΨ
  set E := {X | M < Ψ' X ^ 2}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (hΨ'm.pow_const 2)
  -- Markov
  have hPE : P.real E ≤ B / M := by
    have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun X => sq_nonneg (Ψ' X))
      hΨ'L.integrable_sq M
    have h2 : ∫ X, Ψ' X ^ 2 ∂P ≤ B := by
      have : ∫ X, Ψ' X ^ 2 ∂P = ∫ X, Ψ X ^ 2 ∂P :=
        integral_congr_ae (hΨΨ.mono fun X hX => by simp only [hX])
      rw [this]; exact hB1
    have h3 : P.real E ≤ P.real {X | M ≤ Ψ' X ^ 2} :=
      measureReal_mono (fun X (hX : M < Ψ' X ^ 2) => (le_of_lt hX : M ≤ Ψ' X ^ 2))
    rw [le_div_iff₀ hM]
    nlinarith [measureReal_nonneg (μ := P) (s := E)]
  -- the projection and the tail
  set PS : Config N d → ℝ := fun X => ∑ α ∈ T, c α * occBasis S.v α N X
  have htail := t01_reference_occupation_projection_tail S he hC1 hlam0 hΨ hsym hB2 hL T hS
  have hPSL : MemLp PS 2 P := memLp_finsetSum _ fun α _ => (t01_ui_memLp_occ S he α N).const_mul _
  have hRL : MemLp (fun X => Ψ' X - PS X) 2 P := hΨ'L.sub hPSL
  have hR : ∫ X, (Ψ' X - PS X) ^ 2 ∂P ≤ B / L := by
    have : ∫ X, (Ψ' X - PS X) ^ 2 ∂P = ∫ X, (Ψ X - PS X) ^ 2 ∂P :=
      integral_congr_ae (hΨΨ.mono fun X hX => by simp only [hX])
    rw [this]; exact htail
  -- the projected part on `E`
  have hPSE : ∫ X in E, PS X ^ 2 ∂P ≤ K * Real.sqrt (B / M) := by
    have hpt : ∀ X, PS X ^ 2 ≤ (T.card : ℝ) * ∑ α ∈ T, c α ^ 2 * occBasis S.v α N X ^ 2 := fun X => by
      have := sq_sum_le_card_mul_sum_sq (s := T) (f := fun α => c α * occBasis S.v α N X)
      simpa [mul_pow] using this
    have hint : ∀ α, Integrable (fun X => occBasis S.v α N X ^ 2) P := fun α =>
      (t01_ui_memLp_occ S he α N).integrable_sq
    calc ∫ X in E, PS X ^ 2 ∂P
        ≤ ∫ X in E, (T.card : ℝ) * ∑ α ∈ T, c α ^ 2 * occBasis S.v α N X ^ 2 ∂P :=
          setIntegral_mono_on (hPSL.integrable_sq.integrableOn) (((integrable_finsetSum _ fun α _ =>
            (hint α).const_mul _).const_mul _).integrableOn) hE fun X _ => hpt X
      _ = (T.card : ℝ) * ∑ α ∈ T, c α ^ 2 * ∫ X in E, occBasis S.v α N X ^ 2 ∂P := by
          rw [integral_const_mul, integral_finsetSum _ fun α _ => ((hint α).const_mul _).integrableOn]
          simp_rw [integral_const_mul]
      _ ≤ (T.card : ℝ) * ∑ α ∈ T, B * (Real.sqrt (B / M) * Real.sqrt (C' α)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (Nat.cast_nonneg _)
          refine mul_le_mul (hc2 α) ?_ (setIntegral_nonneg hE fun X _ => sq_nonneg _) hB0
          refine (setIntegral_sq_le (t01_ui_memLp_occ S he α N).aestronglyMeasurable
            (t01_ui_integrable_occ_pow4 S α N) hE).trans ?_
          exact mul_le_mul (Real.sqrt_le_sqrt hPE) (Real.sqrt_le_sqrt (hB4 α))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = K * Real.sqrt (B / M) := by
          simp only [K, ← Finset.mul_sum]; ring
  -- assemble
  have hfin : ∫ X in E, Ψ' X ^ 2 ∂P ≤ ε := by
    have hpt : ∀ X, Ψ' X ^ 2 ≤ 2 * PS X ^ 2 + 2 * (Ψ' X - PS X) ^ 2 := fun X => by
      nlinarith [sq_nonneg (2 * PS X - Ψ' X)]
    have h1 : ∫ X in E, Ψ' X ^ 2 ∂P ≤ ∫ X in E, (2 * PS X ^ 2 + 2 * (Ψ' X - PS X) ^ 2) ∂P :=
      setIntegral_mono_on hΨ'L.integrable_sq.integrableOn
        ((hPSL.integrable_sq.const_mul 2).add (hRL.integrable_sq.const_mul 2)).integrableOn hE
        fun X _ => hpt X
    have h2 : ∫ X in E, (2 * PS X ^ 2 + 2 * (Ψ' X - PS X) ^ 2) ∂P ≤
        2 * (K * Real.sqrt (B / M)) + 2 * (B / L) := by
      rw [integral_add (hPSL.integrable_sq.const_mul 2).integrableOn
        (hRL.integrable_sq.const_mul 2).integrableOn, integral_const_mul, integral_const_mul]
      have h3 : ∫ X in E, (Ψ' X - PS X) ^ 2 ∂P ≤ ∫ X, (Ψ' X - PS X) ^ 2 ∂P :=
        setIntegral_le_integral hRL.integrable_sq (Eventually.of_forall fun X => sq_nonneg _)
      linarith
    have h4 : 2 * (B / L) ≤ ε / 2 := by
      have S.v : ε / 4 * L = B + ε / 4 := by simp only [L]; field_simp
      have : B / L ≤ ε / 4 := by rw [div_le_iff₀ hL]; linarith
      linarith
    have h5 : 2 * (K * Real.sqrt (B / M)) ≤ ε / 2 := by
      have hx0 : 0 ≤ K * Real.sqrt (B / M) := by positivity
      have hsq : (K * Real.sqrt (B / M)) ^ 2 ≤ (ε / 4) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg hB0 hM.le), mul_div_assoc', div_le_iff₀ hM]
        have S.v : (ε / 4) ^ 2 * M = K ^ 2 * B + (ε / 4) ^ 2 := by
          simp only [M]; field_simp
        rw [S.v]; nlinarith [sq_nonneg (ε / 4)]
      have : K * Real.sqrt (B / M) ≤ ε / 4 := by nlinarith
      linarith
    linarith
  -- back to `Ψ`
  have hset : {X | M < Ψ X ^ 2} =ᵐ[P] E := by
    filter_upwards [hΨΨ] with X hX
    simp only [E, Set.mem_ofPred_eq, hX]
  rw [setLIntegral_congr hset, setLIntegral_congr_fun_ae hE (hΨΨ.mono fun X hX _ => by rw [hX]),
    ← ofReal_integral_eq_lintegral_ofReal hΨ'L.integrable_sq.integrableOn
      (Eventually.of_forall fun X => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hfin

end DGPS.Lipschitz
