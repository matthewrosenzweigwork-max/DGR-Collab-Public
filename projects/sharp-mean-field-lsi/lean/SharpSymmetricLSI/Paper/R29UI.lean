import SharpSymmetricLSI.Paper.R29Pars

/-!
# Uniform integrability for `H¹`-bounded symmetric functions (Phase 3, lane D; R29 (7.5))

Split `Ψ = P_LΨ + (Ψ - P_LΨ)` along `{Λ_α ≤ L}`: the tail is `L²`-small (`≤ B/L`), and `P_LΨ` is
a fixed finite combination of the `B_{α,N}`, whose fourth moments are bounded uniformly in `N`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Cauchy–Schwarz on a measurable set. -/
theorem setIntegral_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hgm : AEStronglyMeasurable g P) (hg4 : Integrable (fun x => g x ^ 4) P)
    {E : Set Ω} (hE : MeasurableSet E) :
    ∫ x in E, g x ^ 2 ∂P ≤ Real.sqrt (P.real E) * Real.sqrt (∫ x, g x ^ 4 ∂P) := by
  have hg2 : MemLp (fun x => g x ^ 2) 2 P := by
    refine (memLp_two_iff_integrable_sq (f := fun x => g x ^ 2) (hgm.pow 2)).mpr ?_
    simpa [← pow_mul] using hg4
  have hI : MemLp (E.indicator fun _ => (1 : ℝ)) 2 P :=
    memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun x => by
      by_cases hx : x ∈ E <;> simp [hx]) ((measurable_const.indicator hE).aestronglyMeasurable) 2
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (f := E.indicator fun _ => (1 : ℝ)) (g := fun x => g x ^ 2) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => by by_cases hx : x ∈ E <;> simp [hx])
    (Eventually.of_forall fun x => sq_nonneg (g x)) (by rw [ENNReal.ofReal_ofNat]; exact hI)
    (by rw [ENNReal.ofReal_ofNat]; exact hg2)
  have e1 : ∫ x, E.indicator (fun _ => (1 : ℝ)) x * g x ^ 2 ∂P = ∫ x in E, g x ^ 2 ∂P := by
    rw [← integral_indicator hE]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ E <;> simp [hx]
  have e2 : ∫ x, E.indicator (fun _ => (1 : ℝ)) x ^ (2 : ℝ) ∂P = P.real E := by
    have : (fun x => E.indicator (fun _ => (1 : ℝ)) x ^ (2 : ℝ)) = E.indicator fun _ => (1 : ℝ) := by
      funext x; by_cases hx : x ∈ E <;> simp [hx]
    rw [this, integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
  have e3 : ∫ x, (g x ^ 2) ^ (2 : ℝ) ∂P = ∫ x, g x ^ 4 ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.rpow_two, ← pow_mul]
  rw [e1, e2, e3] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

section ui
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

theorem integrable_occBasis_pow4 (α : ℕ →₀ ℕ) (N : ℕ) :
    Integrable (fun X => occBasis e α N X ^ 4)
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  choose C hC using refEigen_bounded hyp hμ he
  have hall : ∀ᵐ X ∂P, ∀ (i : Fin N) (j : ℕ), |e j (X i)| ≤ C j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    exact (measurePreserving_eval (fun _ : Fin N => (μ : Measure (Torus d))) i).quasiMeasurePreserving.ae
      (hC j)
  set K := Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) *
    ∑ c ∈ occLabellings α N, ∏ i, C (c i : ℕ)
  have hbd : ∀ᵐ X ∂P, |occBasis e α N X| ≤ K := by
    filter_upwards [hall] with X hX
    unfold occBasis
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun c _ => ?_)) (Real.sqrt_nonneg _)
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hX i _
  refine Integrable.of_bound ((memLp_occBasis hyp hμ he α N).aestronglyMeasurable.pow 4) (K ^ 4)
    (hbd.mono fun X hX => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hX 4

/-- **Uniform integrability (7.5)** with a threshold depending only on `ε` and the `H¹` bound. -/
theorem ui_occ {B : ℝ} (hB0 : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, 0 < M ∧
    ∀ (N : ℕ) (Ψ : Config N d → ℝ),
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ → IsSymmetric Ψ →
      ∫ X, Ψ X ^ 2 ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ B →
      ∫ X, gradSqC Ψ X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ B →
      ∫⁻ X in {X | M < Ψ X ^ 2}, ENNReal.ofReal (Ψ X ^ 2)
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal ε := by
  set L : ℝ := 4 * B / ε + 1
  have hL : 0 < L := by positivity
  set S := (finite_occEnergy_le hyp hμ he L).toFinset
  have hS : ∀ α, occEnergy lam α ≤ L → α ∈ S := fun α h => by simp [S, h]
  choose Cm hCm using fun α => occBasis_moments_of_bdd he (refEigen_bounded hyp hμ he) α 4
  set C' : (ℕ →₀ ℕ) → ℝ := fun α => max (Cm α) 0
  set K : ℝ := (S.card : ℝ) * B * ∑ α ∈ S, Real.sqrt (C' α)
  have hK0 : 0 ≤ K := by positivity
  set M : ℝ := B * (4 * K / ε) ^ 2 + 1
  have hM : 0 < M := by positivity
  refine ⟨M, hM, fun N Ψ hΨ hsym hB1 hB2 => ?_⟩
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have hΨL : MemLp Ψ 2 P := (measurableEmbedding_flat.memLp_map_measure_iff).mp hΨ.2.1
  set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ Y, Ψ Y * occBasis e α N Y ∂P
  have hc2 : ∀ α, c α ^ 2 ≤ B := fun α => by
    by_cases hN : occSize α ≤ N
    · have := bessel_occ_L2 hyp hμ he hΨL {α} (by simpa using hN)
      rw [Finset.sum_singleton] at this
      exact this.trans hB1
    · simp only [c, occBasis_zero_of_lt (show N < occSize α by omega), Pi.zero_apply, mul_zero,
        integral_zero]
      simpa using hB0
  have hB4 : ∀ α, ∫ X, occBasis e α N X ^ 4 ∂P ≤ C' α := fun α => by
    by_cases hN : occSize α ≤ N
    · have h := hCm α N hN
      calc ∫ X, occBasis e α N X ^ 4 ∂P = ∫ X, |occBasis e α N X| ^ 4 ∂P := by
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
  set PS : Config N d → ℝ := fun X => ∑ α ∈ S, c α * occBasis e α N X
  have htail := integral_sub_proj_sq_le hyp hμ he hΨ hsym hB2 hL S hS
  have hPSL : MemLp PS 2 P := memLp_finsetSum _ fun α _ => (memLp_occBasis hyp hμ he α N).const_mul _
  have hRL : MemLp (fun X => Ψ' X - PS X) 2 P := hΨ'L.sub hPSL
  have hR : ∫ X, (Ψ' X - PS X) ^ 2 ∂P ≤ B / L := by
    have : ∫ X, (Ψ' X - PS X) ^ 2 ∂P = ∫ X, (Ψ X - PS X) ^ 2 ∂P :=
      integral_congr_ae (hΨΨ.mono fun X hX => by simp only [hX])
    rw [this]; exact htail
  -- the projected part on `E`
  have hPSE : ∫ X in E, PS X ^ 2 ∂P ≤ K * Real.sqrt (B / M) := by
    have hpt : ∀ X, PS X ^ 2 ≤ (S.card : ℝ) * ∑ α ∈ S, c α ^ 2 * occBasis e α N X ^ 2 := fun X => by
      have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun α => c α * occBasis e α N X)
      simpa [mul_pow] using this
    have hint : ∀ α, Integrable (fun X => occBasis e α N X ^ 2) P := fun α =>
      (memLp_occBasis hyp hμ he α N).integrable_sq
    calc ∫ X in E, PS X ^ 2 ∂P
        ≤ ∫ X in E, (S.card : ℝ) * ∑ α ∈ S, c α ^ 2 * occBasis e α N X ^ 2 ∂P :=
          setIntegral_mono_on (hPSL.integrable_sq.integrableOn) (((integrable_finsetSum _ fun α _ =>
            (hint α).const_mul _).const_mul _).integrableOn) hE fun X _ => hpt X
      _ = (S.card : ℝ) * ∑ α ∈ S, c α ^ 2 * ∫ X in E, occBasis e α N X ^ 2 ∂P := by
          rw [integral_const_mul, integral_finsetSum _ fun α _ => ((hint α).const_mul _).integrableOn]
          simp_rw [integral_const_mul]
      _ ≤ (S.card : ℝ) * ∑ α ∈ S, B * (Real.sqrt (B / M) * Real.sqrt (C' α)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (Nat.cast_nonneg _)
          refine mul_le_mul (hc2 α) ?_ (setIntegral_nonneg hE fun X _ => sq_nonneg _) hB0
          refine (setIntegral_sq_le (memLp_occBasis hyp hμ he α N).aestronglyMeasurable
            (integrable_occBasis_pow4 hyp hμ he α N) hE).trans ?_
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
      have e : ε / 4 * L = B + ε / 4 := by simp only [L]; field_simp
      have : B / L ≤ ε / 4 := by rw [div_le_iff₀ hL]; linarith
      linarith
    have h5 : 2 * (K * Real.sqrt (B / M)) ≤ ε / 2 := by
      have hx0 : 0 ≤ K * Real.sqrt (B / M) := by positivity
      have hsq : (K * Real.sqrt (B / M)) ^ 2 ≤ (ε / 4) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg hB0 hM.le), mul_div_assoc', div_le_iff₀ hM]
        have e : (ε / 4) ^ 2 * M = K ^ 2 * B + (ε / 4) ^ 2 := by
          simp only [M]; field_simp
        rw [e]; nlinarith [sq_nonneg (ε / 4)]
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

end ui

end SharpLSI
