import SharpSymmetricLSI.Paper.R7Basic
import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates

/-!
# R7: normalized violating sequences (Section 2.3, (2.13))

If (1.10) fails at a rate `0 < r < r_*`, there are `N_k → ∞` and nonnegative symmetric
`f_k ∈ H¹(P_{N_k})` with `∫ f_k² = 1`, finite entropy and `2ℰ(f_k) < r Ent(f_k²)`
(`exists_violators`). Finiteness of the entropy comes from the defective inequality.
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A definitional copy of `FiniteNConclusion` (Statements/R01), so that this file does not
import the statement of Theorem 1.1 (which uses the lower bound). -/
def FiniteNConclusion' (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rStar V W →
    ∃ Nr : ℕ, ∀ N : ℕ, Nr ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f → IsSymmetric f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f

/-- A definitional copy of `DefectiveConclusion` (Statements/R03). -/
def DefectiveConclusion' (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rStar V W →
    ∃ B : NNReal, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f → IsSymmetric f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤
          ENNReal.ofReal (2 / r) * energy V W N f +
            (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N

theorem ent_eq_zero_of_ae_zero {α : Type*} [MeasurableSpace α] (P : Measure α) {u : α → ℝ}
    (hu : u =ᵐ[P] 0) : ent P u = 0 := by
  have hi : Integrable u P := (integrable_zero _ _ _).congr hu.symm
  unfold ent
  simp only [hi, ↓reduceIte, integral_congr_ae hu, Pi.zero_apply, integral_zero, zero_mul,
    ENNReal.ofReal_zero, lintegral_zero]

theorem IsSymmetric.abs_smul {N : ℕ} {f : Config N d → ℝ} (hf : IsSymmetric f) (c : ℝ) :
    IsSymmetric (fun X => c * |f X|) := fun σ X => by simp only [hf σ X]

/-- Normalization of one violator. -/
theorem normalize_violator (hyp : Hyp V W KV KW) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < rStar V W) (h22 : DefectiveConclusion' V W) {N : ℕ} (hN : 1 ≤ N)
    {f : Config N d → ℝ} (hmem : MemH1C (gibbs V W N) f) (hsym : IsSymmetric f)
    (hviol : ENNReal.ofReal (2 / r) * energy V W N f < ent (gibbs V W N) (fun X => f X ^ 2)) :
    ∃ g : Config N d → ℝ, MemH1C (gibbs V W N) g ∧ IsSymmetric g ∧ (∀ X, 0 ≤ g X) ∧
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
    refine ne_top_of_le_ne_top ?_ (hB N hN f hmem hsym)
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (energy_lt_top hyp hmem).ne, ENNReal.mul_ne_top ENNReal.coe_ne_top ?_⟩
    exact ((hasFiniteIntegral_iff_ofReal (f := fun X => f X ^ 2)
      (Eventually.of_forall fun X => sq_nonneg _)).mp hi.2).ne
  set c := 1 / Real.sqrt A with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ^ 2 = 1 / A := by rw [hc, div_pow, Real.sq_sqrt hA0, one_pow]
  refine ⟨fun X => c * |f X|, memH1C_smul hyp (memH1C_abs hyp hmem) c, hsym.abs_smul c,
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
theorem exists_violators (hyp : Hyp V W KV KW) (h22 : DefectiveConclusion' V W)
    (hfail : ¬ FiniteNConclusion' V W) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < rStar V W ∧
      ∃ (Ns : ℕ → ℕ) (f : (k : ℕ) → Config (Ns k) d → ℝ), (∀ k, k + 1 ≤ Ns k) ∧
        (∀ k, MemH1C (gibbs V W (Ns k)) (f k)) ∧ (∀ k, IsSymmetric (f k)) ∧
        (∀ k X, 0 ≤ f k X) ∧ (∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) = 1) ∧
        (∀ k, ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≠ ⊤) ∧
        ∀ k, 2 * (energy V W (Ns k) (f k)).toReal <
          r * (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal := by
  unfold FiniteNConclusion' at hfail
  push Not at hfail
  obtain ⟨r, hr0, hr, hall⟩ := hfail
  have hk : ∀ k : ℕ, ∃ N, k + 1 ≤ N ∧ ∃ g : Config N d → ℝ, MemH1C (gibbs V W N) g ∧
      IsSymmetric g ∧ (∀ X, 0 ≤ g X) ∧ ∫ X, g X ^ 2 ∂gibbs V W N = 1 ∧
      ent (gibbs V W N) (fun X => g X ^ 2) ≠ ⊤ ∧
      2 * (energy V W N g).toReal < r * (ent (gibbs V W N) (fun X => g X ^ 2)).toReal := by
    intro k
    obtain ⟨N, hN, f, hmem, hsym, hviol⟩ := hall (k + 1)
    exact ⟨N, hN, normalize_violator hyp hr0 hr h22 (by omega) hmem hsym hviol⟩
  choose Ns hNs f hf using hk
  exact ⟨r, hr0, hr, Ns, f, hNs, fun k => (hf k).1, fun k => (hf k).2.1, fun k => (hf k).2.2.1,
    fun k => (hf k).2.2.2.1, fun k => (hf k).2.2.2.2.1, fun k => (hf k).2.2.2.2.2⟩

end SharpLSI
