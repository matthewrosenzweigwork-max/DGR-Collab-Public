import FullLabeledLSI.Statements.S03_Prop_2_2
import FullLabeledLSI.Paper.Sec2AssemblyA
import SharpSymmetricLSI.Paper.R7Positive

/-!
# Theorem 1.1 (FL), Section 2.3: toolkit without symmetry

* `FiniteNConclusionAll'`: a definitional copy of `FiniteNConclusionAll` (Statements/S01), so
  that the assembly does not import the statement of Theorem 1.1.
* `le_rAll_of_lsi`: (1.15) at size `N` gives `r ≤ r_N^all`.
* `var_mul_lamAll_le`: the Poincaré inequality from the definition of `λ_N^all`.
* `exists_violators_all`: normalized violating sequences (2.13) for the full-labeled problem.
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A definitional copy of `FiniteNConclusionAll` (Statements/S01). -/
def FiniteNConclusionAll' (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rMs V W →
    ∃ Nr : ℕ, ∀ N : ℕ, Nr ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f

/-- (1.15) at size `N` gives `r ≤ r_N^all`. -/
theorem le_rAll_of_lsi (hyp : Hyp V W KV KW) {r : ℝ} (hr0 : 0 < r) {N : ℕ}
    (h : ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f) :
    ENNReal.ofReal r ≤ rAll V W N := by
  unfold rAll
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hmem, hent⟩ := hf
  have hE := energy_lt_top hyp hmem
  have h1 := h f hmem
  have hEt : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne) h1
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hEt)]
  calc ENNReal.ofReal r * ent (gibbs V W N) (fun X => f X ^ 2)
      ≤ ENNReal.ofReal r * (ENNReal.ofReal (2 / r) * energy V W N f) := by gcongr
    _ = 2 * energy V W N f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le, mul_div_cancel₀ (2 : ℝ) hr0.ne',
          ENNReal.ofReal_ofNat]

/-- The Poincaré inequality from the definition of `λ_N^all`. -/
theorem var_mul_lamAll_le (hyp : Hyp V W KV KW) {N : ℕ} {g : Config N d → ℝ}
    (hg : MemH1C (gibbs V W N) g) :
    var (gibbs V W N) g * lamAll V W N ≤ energy V W N g := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  by_cases h0 : var (gibbs V W N) g = 0
  · rw [h0, zero_mul]; exact zero_le
  have hvt : var (gibbs V W N) g ≠ ⊤ := (evariance_lt_top (memLp_of_memH1C hyp hg)).ne
  have hle : lamAll V W N ≤ energy V W N g / var (gibbs V W N) g := by
    unfold lamAll
    exact iInf₂_le (f := fun (f : Config N d → ℝ) _ => energy V W N f / var (gibbs V W N) f) g
      ⟨hg, pos_iff_ne_zero.mpr h0⟩
  rw [mul_comm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hvt)).mp hle

/-- Normalization of one violator. -/
theorem normalize_violator_all (hyp : Hyp V W KV KW) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < rMs V W) (h22 : DefectiveConclusionAll V W) {N : ℕ} (hN : 1 ≤ N)
    {f : Config N d → ℝ} (hmem : MemH1C (gibbs V W N) f)
    (hviol : ENNReal.ofReal (2 / r) * energy V W N f < ent (gibbs V W N) (fun X => f X ^ 2)) :
    ∃ g : Config N d → ℝ, MemH1C (gibbs V W N) g ∧ (∀ X, 0 ≤ g X) ∧
      ∫ X, g X ^ 2 ∂gibbs V W N = 1 ∧ ent (gibbs V W N) (fun X => g X ^ 2) ≠ ⊤ ∧
      2 * (energy V W N g).toReal < r * (ent (gibbs V W N) (fun X => g X ^ 2)).toReal := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  have hL2 := memLp_of_memH1C hyp hmem
  have hi : Integrable (fun X => f X ^ 2) P := hL2.integrable_sq
  set A := ∫ X, f X ^ 2 ∂P with hA
  have hA0 : 0 ≤ A := integral_nonneg fun X => sq_nonneg _
  -- `A > 0`
  have hApos : 0 < A := by
    rcases hA0.eq_or_lt with h | h
    · exfalso
      have hz : (fun X => f X ^ 2) =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun X => sq_nonneg _) hi).mp h.symm
      rw [ent_eq_zero_of_ae_zero P hz] at hviol
      exact (not_lt.mpr zero_le) hviol
    · exact h
  -- finite entropy
  obtain ⟨B, hB⟩ := h22 r hr0 hr
  have hentf : ent P (fun X => f X ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hB N hN f hmem)
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (energy_lt_top hyp hmem).ne, ENNReal.mul_ne_top ENNReal.coe_ne_top ?_⟩
    exact ((hasFiniteIntegral_iff_ofReal (f := fun X => f X ^ 2)
      (Eventually.of_forall fun X => sq_nonneg _)).mp hi.2).ne
  set c := 1 / Real.sqrt A with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ^ 2 = 1 / A := by rw [hc, div_pow, Real.sq_sqrt hA0, one_pow]
  refine ⟨fun X => c * |f X|, memH1C_smul hyp (memH1C_abs hyp hmem) c,
    fun X => mul_nonneg hc0 (abs_nonneg _), ?_, ?_, ?_⟩
  · simp_rw [mul_pow, sq_abs]
    rw [integral_const_mul, ← hA, hc2, one_div, inv_mul_cancel₀ hApos.ne']
  · have e : (fun X => (c * |f X|) ^ 2) = fun X => c ^ 2 * f X ^ 2 := by
      funext X; rw [mul_pow, sq_abs]
    rw [e, ent_const_mul P hi (sq_nonneg c)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hentf
  · have e : (fun X => (c * |f X|) ^ 2) = fun X => c ^ 2 * f X ^ 2 := by
      funext X; rw [mul_pow, sq_abs]
    rw [e, ent_const_mul P hi (sq_nonneg c), energy_smul hyp (memH1C_abs hyp hmem) c,
      energy_abs hyp hmem]
    have hEf := (energy_lt_top hyp hmem).ne
    have hk : 0 < c ^ 2 := by rw [hc2]; positivity
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)]
    have hv := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEf) hentf).mpr
      hviol
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hv
    have : 2 * (energy V W N f).toReal < r * (ent P fun X => f X ^ 2).toReal := by
      have := mul_lt_mul_of_pos_left hv hr0
      field_simp at this
      linarith
    nlinarith

/-- **(2.13).** Normalized violating sequences. -/
theorem exists_violators_all (hyp : Hyp V W KV KW) (h22 : DefectiveConclusionAll V W)
    (hfail : ¬ FiniteNConclusionAll' V W) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < rMs V W ∧
      ∃ (Ns : ℕ → ℕ) (f : (k : ℕ) → Config (Ns k) d → ℝ), (∀ k, k + 1 ≤ Ns k) ∧
        (∀ k, MemH1C (gibbs V W (Ns k)) (f k)) ∧
        (∀ k X, 0 ≤ f k X) ∧ (∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) = 1) ∧
        (∀ k, ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≠ ⊤) ∧
        ∀ k, 2 * (energy V W (Ns k) (f k)).toReal <
          r * (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal := by
  unfold FiniteNConclusionAll' at hfail
  push Not at hfail
  obtain ⟨r, hr0, hr, hall⟩ := hfail
  have hk : ∀ k : ℕ, ∃ N, k + 1 ≤ N ∧ ∃ g : Config N d → ℝ, MemH1C (gibbs V W N) g ∧
      (∀ X, 0 ≤ g X) ∧ ∫ X, g X ^ 2 ∂gibbs V W N = 1 ∧
      ent (gibbs V W N) (fun X => g X ^ 2) ≠ ⊤ ∧
      2 * (energy V W N g).toReal < r * (ent (gibbs V W N) (fun X => g X ^ 2)).toReal := by
    intro k
    obtain ⟨N, hN, f, hmem, hviol⟩ := hall (k + 1)
    exact ⟨N, hN, normalize_violator_all hyp hr0 hr h22 (by omega) hmem hviol⟩
  choose Ns hNs f hf using hk
  exact ⟨r, hr0, hr, Ns, f, hNs, fun k => (hf k).1, fun k => (hf k).2.1,
    fun k => (hf k).2.2.1, fun k => (hf k).2.2.2.1, fun k => (hf k).2.2.2.2⟩

end SharpLSI.FL
