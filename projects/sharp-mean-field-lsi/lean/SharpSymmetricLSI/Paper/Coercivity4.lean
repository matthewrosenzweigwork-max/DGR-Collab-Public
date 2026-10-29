import SharpSymmetricLSI.Paper.Coercivity3
import SharpSymmetricLSI.Paper.ProductEntropy

/-!
# Lemma 4.2 (lane s42; R16): global comparison with relative entropy

Manuscript, proof of Lemma 4.2, second paragraph. Given uniqueness of the minimizer and
`I + T ≥ σ I` (the conclusions of R15 `minSet_singleton`), `G(ρ) ≥ c H(ρ|μ)`:
* small `H`: `small_entropy_coercive`;
* large `H`: `G = H + J ≥ H - sup|J| ≥ H/2`;
* intermediate `H`: compactness of `𝒫(𝕋^d)`, lower semicontinuity of `F`, continuity of `J`
  and uniqueness give `η > 0` with `G ≤ η ⇒ |J| < δ/2`, hence `G ≥ min(η, δ/2)` when `H ≥ δ`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
include hyp

/-- `F` is weakly lower semicontinuous on `𝒫(𝕋^d)`. -/
theorem lowerSemicontinuous_freeEnergy :
    LowerSemicontinuous fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ := by
  have hreal : Continuous fun ρ : ProbabilityMeasure (Torus d) =>
      potE V ρ + interE W ρ ρ / 2 := by
    refine Continuous.add ?_ ((continuous_interAux hyp.continuous_W).div_const 2)
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨V, hyp.continuous_V⟩)
  refine LowerSemicontinuous.add' (lowerSemicontinuous_klDiv (haar d))
    (continuous_coe_real_ereal.comp hreal).lowerSemicontinuous fun ρ => ?_
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

theorem continuous_Jfun (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Continuous fun ρ : ProbabilityMeasure (Torus d) => Jfun W μ ρ :=
  (continuous_interAux (continuous_centeredKernel hyp μ)).div_const 2

theorem Jfun_self (μ : Measure (Torus d)) [IsProbabilityMeasure μ] : Jfun W μ μ = 0 := by
  have h := two_Jfun_eq_bForm hyp μ μ
  simp only [bForm, sub_self, zero_add] at h
  linarith

theorem abs_Jfun_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → |Jfun W μ ρ| ≤ B := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous (X := Torus d × Torus d)
    (continuous_centeredKernel hyp μ)
  refine ⟨|C| / 2, by positivity, fun ρ _ => ?_⟩
  unfold Jfun interE
  rw [abs_div, abs_two]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine abs_integral_le_of_bdd fun y => ?_
  exact abs_integral_le_of_bdd fun x => (hC (x, y)).trans (le_abs_self C)

/-- `G = H(·|μ) + J` as real numbers, for finite entropy. -/
theorem gap_real {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (ρ : ProbabilityMeasure (Torus d)) (hρ : klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤) :
    klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ ∧
    gap V W ρ = (((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
      Jfun W μ ρ : ℝ) : EReal) ∧
    freeEnergy V W ρ = (((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
      Jfun W μ ρ + (Fstar V W).toReal : ℝ) : EReal) := by
  have h1 := gap_eq_aux hyp hμ ρ
  have h2 := gap_eq_coe hyp hρ
  have hne : klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ := by
    intro htop
    have hg : gap V W ρ = ⊤ := by rw [h1, htop, EReal.coe_ennreal_top, EReal.top_add_coe]
    rw [hg] at h2
    exact EReal.coe_ne_top _ h2.symm
  refine ⟨hne, ?_, ?_⟩
  · rw [h1, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_add]
  · have h3 := freeEnergy_eq (V := V) (W := W) (ρ : Measure (Torus d)) hρ
    rw [h1, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_add] at h2
    have h4 := EReal.coe_injective h2
    rw [h3]
    congr 1
    linarith

/-- The intermediate-entropy step: small gap forces small `J`. -/
theorem exists_gap_forces_J {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (huniq : ∀ ν, IsMinimizer V W ν → ν = μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ ρ : ProbabilityMeasure (Torus d),
      freeEnergy V W ρ ≤ (((Fstar V W).toReal + 1 / ((n : ℝ) + 1) : ℝ) : EReal) →
        |Jfun W μ ρ| < δ / 2 := by
  set Fr := (Fstar V W).toReal with hFr
  have hFs : Fstar V W = (Fr : EReal) := Fstar_eq_coe hyp
  by_contra hcon
  push_neg at hcon
  set C : ℕ → Set (ProbabilityMeasure (Torus d)) := fun n =>
    {ρ | freeEnergy V W ρ ≤ ((Fr + 1 / ((n : ℝ) + 1) : ℝ) : EReal) ∧ δ / 2 ≤ |Jfun W μ ρ|}
    with hC
  have hcl : ∀ n, IsClosed (C n) := fun n =>
    ((lowerSemicontinuous_freeEnergy hyp).isClosed_preimage _).inter
      (isClosed_le continuous_const (continuous_Jfun hyp (μ : Measure (Torus d))).abs)
  have hsub : ∀ n, C (n + 1) ⊆ C n := fun n ρ ⟨h1, h2⟩ => by
    refine ⟨h1.trans (EReal.coe_le_coe_iff.mpr ?_), h2⟩
    have : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    linarith
  have hne : ∀ n, (C n).Nonempty := fun n => hcon n
  obtain ⟨ρ, hρ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hρ
  -- `ρ` is a minimizer
  have hFρ : freeEnergy V W ρ ≤ (Fr : EReal) := by
    have hlt : freeEnergy V W ρ ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) (hρ 0).1
    have hbot : freeEnergy V W ρ ≠ ⊥ := by
      unfold freeEnergy
      simp only [ne_eq, EReal.add_eq_bot_iff, not_or]
      exact ⟨EReal.coe_ennreal_ne_bot _, EReal.coe_ne_bot _⟩
    rw [← EReal.coe_toReal hlt hbot, EReal.coe_le_coe_iff]
    refine le_of_forall_pos_lt_add fun t ht => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    have h := (hρ n).1
    rw [← EReal.coe_toReal hlt hbot, EReal.coe_le_coe_iff] at h
    linarith
  have hmin : IsMinimizer V W ρ := by
    refine le_antisymm (hFs ▸ hFρ) ?_
    exact iInf_le (fun ρ' : ProbabilityMeasure (Torus d) => freeEnergy V W ρ') ρ
  have hρμ := huniq ρ hmin
  have hJ := (hρ 0).2
  rw [hρμ, Jfun_self hyp, abs_zero] at hJ
  linarith

/-- **Lemma 4.2 from uniqueness and nondegeneracy** (the conclusions of R15). -/
theorem coercivity_of_unique_nondegenerate {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (huniq : ∀ ν, IsMinimizer V W ν → ν = μ)
    (hσ : ∃ σ : ℝ, 0 < σ ∧ ∀ h, MemL20 μ h →
      σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ρ : ProbabilityMeasure (Torus d),
      klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
        (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) ≤
          gap V W ρ := by
  obtain ⟨σ, hσ0, hσb⟩ := hσ
  set σ₁ := min σ 1 with hσ₁
  have hσ₁0 : 0 < σ₁ := lt_min hσ0 one_pos
  have hσ₁1 : σ₁ ≤ 1 := min_le_right _ _
  have hσ₁b : ∀ h, MemL20 μ h → σ₁ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h :=
    fun h hh => (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (integral_nonneg fun x => sq_nonneg (h x))).trans (hσb h hh)
  obtain ⟨δ, hδ0, hsmall⟩ := small_entropy_coercive hyp hμ hσ₁0 hσ₁1 hσ₁b
  obtain ⟨B, hB0, hB⟩ := abs_Jfun_le hyp (μ : Measure (Torus d))
  obtain ⟨n, hn⟩ := exists_gap_forces_J hyp hμ huniq hδ0
  set η := min (1 / ((n : ℝ) + 1)) (δ / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  set M := 2 * (B + 1) with hM
  have hM0 : 0 < M := by positivity
  set c := min (min (σ₁ / 2) (1 / 2)) (η / M) with hc
  have hc0 : 0 < c := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hc1 : c ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  refine ⟨c, hc0, hc1, fun ρ hρ => ?_⟩
  obtain ⟨hne, hgap, hF⟩ := gap_real hyp hμ ρ hρ
  set H := (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal with hH
  set J := Jfun W μ ρ with hJ
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  rw [hgap, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hJB : |J| ≤ B := hB ρ inferInstance
  rcases le_or_gt H δ with hHδ | hHδ
  · -- small entropy
    have h := hsmall ρ inferInstance hne hHδ
    have : c ≤ σ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
    nlinarith
  rcases le_or_gt M H with hHM | hHM
  · -- large entropy
    have : c ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hJ' := neg_abs_le J
    nlinarith
  · -- intermediate entropy
    have hGη : η ≤ H + J := by
      by_contra hlt
      push_neg at hlt
      have hle : freeEnergy V W ρ ≤ (((Fstar V W).toReal + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        rw [hF, EReal.coe_le_coe_iff]
        have : η ≤ 1 / ((n : ℝ) + 1) := min_le_left _ _
        linarith
      have h1 := hn ρ hle
      have h2 := neg_abs_le J
      have h3 : η ≤ δ / 2 := min_le_right _ _
      linarith
    have : c ≤ η / M := min_le_right _ _
    have h1 : c * H ≤ η / M * H := mul_le_mul_of_nonneg_right this hH0
    have h2 : η / M * H ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
      exact mul_le_mul_of_nonneg_left hHM.le hη0.le
    linarith

end SharpLSI
