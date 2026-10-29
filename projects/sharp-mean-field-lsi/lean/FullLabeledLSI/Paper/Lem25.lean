import FullLabeledLSI.Paper.Lem25Trunc
import FullLabeledLSI.Statements.S04_Prop_2_3
import FullLabeledLSI.Statements.S05_Lemma_2_4
import SharpSymmetricLSI.Paper.R7Basic
import SharpSymmetricLSI.Paper.LipChain3

/-!
# Lemma 2.5 (`lem:PI`): an unrestricted Poincaré lower bound

The manuscript argument. If `liminf λ_N^all < b`, a subsequence has mean-zero, norm-one `h_N` with
`ℰ_N(h_N) ≤ κ < b`. Lemma 2.4 (`unifIntegrable_sq`) makes `h_N²` uniformly integrable, so the signed
truncations `g_N = (-A) ∨ (h_N ∧ A)` have `Var(g_N) ≥ 1 - 2√ε` and `ℰ_N(g_N) ≤ κ` (Lipschitz chain
rule). Proposition 2.3 (`prop_bounded`, in the form `BoundedComparison`) applied to `1 + t g_N`, with
the entropy expansion `ent_one_add_ge`, contradicts `κ < b` for small `t` and `ε`.

* `exists_normalized`: normalization of a Poincaré test function.
* `lem25_core`: the contradiction, for any `b` with `BoundedComparison V W b`.
* `liminf_lamAll_ge_aux`: Lemma 2.5.
The only non-closed input is Proposition 2.3 (`prop_bounded`, S04).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem exists_normalized (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (hv : 0 < var (gibbs V W N) f) {κ : ℝ}
    (hlt : energy V W N f / var (gibbs V W N) f < ENNReal.ofReal κ) :
    ∃ h : Config N d → ℝ, MemH1C (gibbs V W N) h ∧ ∫ X, h X ∂gibbs V W N = 0 ∧
      ∫ X, h X ^ 2 ∂gibbs V W N = 1 ∧ energy V W N h < ENNReal.ofReal κ := by
  haveI := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N with hP
  have hL2 : MemLp f 2 P := memLp_of_memH1C hyp hf
  set v := ProbabilityTheory.variance f P with hvdef
  have hvv : ENNReal.ofReal v = var P f := hL2.ofReal_variance_eq
  have hvpos : 0 < v := ENNReal.ofReal_pos.1 (by rw [hvv]; exact hv)
  set m := ∫ X, f X ∂P with hm
  set c := (Real.sqrt v)⁻¹ with hc
  have hc2 : c ^ 2 = v⁻¹ := by simp [hc, inv_pow, Real.sq_sqrt hvpos.le]
  refine ⟨fun X => c * (f X + -m), ?_, ?_, ?_, ?_⟩
  · exact memH1C_smul hyp (memH1C_add_const hyp hf (-m)) c
  · have hi : Integrable f P := hL2.integrable (by norm_num)
    rw [integral_const_mul, integral_add hi (integrable_const _)]
    simp [hm]
  · have : ∀ X, (c * (f X + -m)) ^ 2 = c ^ 2 * (f X - m) ^ 2 := fun X => by ring
    simp_rw [this]
    rw [integral_const_mul]
    have hvar : v = ∫ X, (f X - m) ^ 2 ∂P := ProbabilityTheory.variance_eq_integral hL2.aemeasurable
    rw [← hvar, hc2]
    field_simp
  · rw [energy_smul hyp (memH1C_add_const hyp hf (-m)) c, energy_add_const hyp hf (-m), hc2]
    have : ENNReal.ofReal v⁻¹ * energy V W N f = energy V W N f / var P f := by
      rw [← hvv, ENNReal.ofReal_inv_of_pos hvpos, div_eq_mul_inv, mul_comm]
    rw [this]; exact hlt

theorem lem25_core (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) {b : ℝ≥0∞}
    (hbd : BoundedComparison V W b) {c κ : ℝ} (hc : 0 < c) (hκ0 : 0 ≤ κ) (hκc : κ < c)
    (hcb : ENNReal.ofReal c ≤ b) (Ns : ℕ → ℕ) (hNt : Tendsto Ns atTop atTop)
    (hNs : ∀ k, 1 ≤ Ns k) (h : (k : ℕ) → Config (Ns k) d → ℝ)
    (hH : ∀ k, MemH1C (gibbs V W (Ns k)) (h k))
    (h0 : ∀ k, ∫ X, h k X ∂gibbs V W (Ns k) = 0)
    (h1 : ∀ k, ∫ X, h k X ^ 2 ∂gibbs V W (Ns k) = 1)
    (hE : ∀ k, energy V W (Ns k) (h k) ≤ ENNReal.ofReal κ) : False := by
  have hP : ∀ k, IsProbabilityMeasure (gibbs V W (Ns k)) := fun k =>
    gibbs_isProbabilityMeasure hyp _
  set γ := c - κ with hγ
  have hγ0 : 0 < γ := by linarith
  -- the tail parameter `ε`
  set ε : ℝ := min 1 ((γ / (6 * c)) ^ 2) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hsq : Real.sqrt ε ≤ γ / (6 * c) := by
    calc Real.sqrt ε ≤ Real.sqrt ((γ / (6 * c)) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = γ / (6 * c) := Real.sqrt_sq (by positivity)
  -- uniform integrability (Lemma 2.4)
  have hB : ∃ B : NNReal, ∀ k, (∫⁻ X, ENNReal.ofReal (h k X ^ 2) ∂gibbs V W (Ns k)) +
      energy V W (Ns k) (h k) ≤ B := by
    refine ⟨(1 + κ).toNNReal, fun k => ?_⟩
    have hint : ∫⁻ X, ENNReal.ofReal (h k X ^ 2) ∂gibbs V W (Ns k) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal (memLp_of_memH1C hyp (hH k)).integrable_sq
        (Filter.Eventually.of_forall fun X => sq_nonneg _), h1 k]
      simp
    rw [hint]
    calc 1 + energy V W (Ns k) (h k) ≤ ENNReal.ofReal 1 + ENNReal.ofReal κ := by
          rw [ENNReal.ofReal_one]; gcongr; exact hE k
      _ = ENNReal.ofReal (1 + κ) := (ENNReal.ofReal_add one_pos.le hκ0).symm
      _ = ((1 + κ).toNNReal : ℝ≥0∞) := rfl
  obtain ⟨M, hM⟩ := unifIntegrable_sq hd hyp hr Ns hNs h hH hB ε hε0
  set A : ℝ := Real.sqrt (max M 1) with hAdef
  have hmax : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hApos : 0 < A := Real.sqrt_pos.2 hmax
  have hA2 : A ^ 2 = max M 1 := Real.sq_sqrt hmax.le
  have htail : ∀ k, ∫⁻ x in {x | A ^ 2 < h k x ^ 2}, ENNReal.ofReal (h k x ^ 2)
      ∂gibbs V W (Ns k) ≤ ENNReal.ofReal ε := fun k =>
    (lintegral_mono_set (fun x hx => by
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [hA2] at hx
      exact lt_of_le_of_lt (le_max_left _ _) hx)).trans (hM k)
  -- truncations
  set g : (k : ℕ) → Config (Ns k) d → ℝ := fun k X => truncR A (h k X) with hgdef
  have hgvar : ∀ k, 1 - 2 * Real.sqrt ε ≤ (∫ X, g k X ^ 2 ∂gibbs V W (Ns k)) -
      (∫ X, g k X ∂gibbs V W (Ns k)) ^ 2 := fun k =>
    trunc_var_lower (gibbs V W (Ns k)) (memLp_of_memH1C hyp (hH k)) (h0 k) (h1 k) hApos hε0 hε1
      (htail k)
  have hgH : ∀ k, MemH1C (gibbs V W (Ns k)) (g k) := fun k =>
    (memH1C_comp_lipschitz hyp (hH k) (truncR_lipschitz A)).1
  have hgE : ∀ k, energy V W (Ns k) (g k) ≤ ENNReal.ofReal κ := fun k => by
    have := (memH1C_comp_lipschitz hyp (hH k) (truncR_lipschitz A)).2
    refine this.trans ?_
    simpa using hE k
  have hgb : ∀ k X, |g k X| ≤ A := fun k X => abs_truncR_le hApos.le _
  -- the parameter `t`
  set Kc : ℝ := 1 + 25 * c * A ^ 3 / 2 with hKc
  have hKc0 : 0 < Kc := by positivity
  set t : ℝ := min (min 1 (1 / (16 * A))) (γ / (3 * Kc)) with htdef
  have ht0 : 0 < t := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have htA : t * A ≤ 1 / 16 := by
    have : t ≤ 1 / (16 * A) := (min_le_left _ _).trans (min_le_right _ _)
    calc t * A ≤ 1 / (16 * A) * A := mul_le_mul_of_nonneg_right this hApos.le
      _ = 1 / 16 := by field_simp
  have htK : t * Kc ≤ γ / 3 := by
    have : t ≤ γ / (3 * Kc) := min_le_right _ _
    calc t * Kc ≤ γ / (3 * Kc) * Kc := mul_le_mul_of_nonneg_right this hKc0.le
      _ = γ / 3 := by field_simp
  -- the test functions `1 + t g`
  set f : (k : ℕ) → Config (Ns k) d → ℝ := fun k X => 1 + t * g k X with hfdef
  have hfe : ∀ k, f k = fun X => (fun X => t * g k X) X + 1 := fun k => by
    funext X; simp only [hfdef]; ring
  have hfH : ∀ k, MemH1C (gibbs V W (Ns k)) (f k) := fun k => by
    rw [hfe k]; exact memH1C_add_const hyp (memH1C_smul hyp (hgH k) t) 1
  have hfE : ∀ k, energy V W (Ns k) (f k) ≤ ENNReal.ofReal (t ^ 2 * κ) := fun k => by
    rw [hfe k, energy_add_const hyp (memH1C_smul hyp (hgH k) t) 1, energy_smul hyp (hgH k) t,
      ENNReal.ofReal_mul (sq_nonneg t)]
    exact mul_le_mul' (le_refl _) (hgE k)
  have hbound : ∃ B : NNReal, ∀ k, (∀ᵐ X ∂gibbs V W (Ns k), |f k X| ≤ B) ∧
      energy V W (Ns k) (f k) ≤ B := by
    refine ⟨(2 + κ).toNNReal, fun k => ⟨Filter.Eventually.of_forall fun X => ?_, ?_⟩⟩
    · have h1 : |t * g k X| ≤ 1 / 16 := by
        rw [abs_mul, abs_of_pos ht0]
        exact (mul_le_mul_of_nonneg_left (hgb k X) ht0.le).trans htA
      have h2 := abs_le.1 h1
      have : ((2 + κ).toNNReal : ℝ) = 2 + κ := Real.coe_toNNReal _ (by linarith)
      rw [this, hfdef]
      simp only
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
    · refine (hfE k).trans ?_
      have ht2 : t ^ 2 ≤ 1 := by nlinarith
      have := mul_le_mul_of_nonneg_right ht2 hκ0
      exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨k, hk⟩ := (hbd Ns hNt f hfH hbound (t ^ 3) (by positivity)).exists
  -- the entropy lower bound
  have hent : ENNReal.ofReal (2 * t ^ 2 * ((∫ X, g k X ^ 2 ∂gibbs V W (Ns k)) -
      (∫ X, g k X ∂gibbs V W (Ns k)) ^ 2) - 25 * t ^ 3 * A ^ 3) ≤
      ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) :=
    ent_one_add_ge (gibbs V W (Ns k)) (g k) (memLp_of_memH1C hyp (hgH k)).aestronglyMeasurable
      hApos ht0 htA (hgb k)
  have hcb2 : ENNReal.ofReal (c / 2) ≤ b / 2 := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_div_right hcb 2
  set X0 : ℝ := 2 * t ^ 2 * ((∫ X, g k X ^ 2 ∂gibbs V W (Ns k)) -
      (∫ X, g k X ∂gibbs V W (Ns k)) ^ 2) - 25 * t ^ 3 * A ^ 3 with hX0
  have hchain : ENNReal.ofReal (c / 2 * X0) ≤ ENNReal.ofReal (t ^ 2 * κ + t ^ 3) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (c / 2) * ENNReal.ofReal X0 ≤ b / 2 * ent (gibbs V W (Ns k))
          (fun X => f k X ^ 2) := mul_le_mul' hcb2 hent
      _ ≤ energy V W (Ns k) (f k) + ENNReal.ofReal (t ^ 3) := hk
      _ ≤ ENNReal.ofReal (t ^ 2 * κ) + ENNReal.ofReal (t ^ 3) := by gcongr; exact hfE k
      _ = ENNReal.ofReal (t ^ 2 * κ + t ^ 3) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hreal : c / 2 * X0 ≤ t ^ 2 * κ + t ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  -- conclude
  have hV := hgvar k
  set V0 := (∫ X, g k X ^ 2 ∂gibbs V W (Ns k)) - (∫ X, g k X ∂gibbs V W (Ns k)) ^ 2 with hV0
  have h2 : t ^ 2 * (c * V0 - 25 / 2 * c * t * A ^ 3 - κ - t) ≤ 0 := by
    rw [hX0] at hreal; nlinarith [hreal]
  have h3 : c * V0 - 25 / 2 * c * t * A ^ 3 - κ - t ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have : 0 < t ^ 2 * (c * V0 - 25 / 2 * c * t * A ^ 3 - κ - t) := mul_pos (by positivity) hcon
    linarith
  have h4 : c * (1 - 2 * Real.sqrt ε) ≤ c * V0 := mul_le_mul_of_nonneg_left hV hc.le
  have h5 : 2 * c * Real.sqrt ε ≤ γ / 3 := by
    calc 2 * c * Real.sqrt ε ≤ 2 * c * (γ / (6 * c)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = γ / 3 := by field_simp; ring
  have h6 : t * Kc = t + 25 / 2 * c * t * A ^ 3 := by rw [hKc]; ring
  nlinarith

/-- Lemma 2.5 from any rate `b` satisfying the bounded-observable comparison. -/
theorem le_liminf_lamAll_of_bounded (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {b : ℝ≥0∞} (hbd : BoundedComparison V W b) :
    b ≤ liminf (fun N => lamAll V W N) atTop := by
  refine le_of_forall_lt fun a ha => ?_
  obtain ⟨c, hc0, hac, hcb⟩ := ENNReal.lt_iff_exists_real_btwn.1 ha
  have hcpos : 0 < c := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hac)
  refine lt_of_lt_of_le hac ?_
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨κ, hκ0, hl1, hl2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hnot
  have hκc : κ < c := (ENNReal.ofReal_lt_ofReal_iff hcpos).1 hl2
  have hfreq : ∃ᶠ N in atTop, lamAll V W N < ENNReal.ofReal κ :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hl1
  have hfreq2 : ∃ᶠ N in atTop, 1 ≤ N ∧ lamAll V W N < ENNReal.ofReal κ :=
    (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun N hN => ⟨hN.2, hN.1⟩
  obtain ⟨Ns, hmono, hNs⟩ := Filter.extraction_of_frequently_atTop hfreq2
  have hex : ∀ k, ∃ f : Config (Ns k) d → ℝ, MemH1C (gibbs V W (Ns k)) f ∧
      0 < var (gibbs V W (Ns k)) f ∧
      energy V W (Ns k) f / var (gibbs V W (Ns k)) f < ENNReal.ofReal κ := by
    intro k
    have h := (hNs k).2
    unfold lamAll at h
    rw [iInf_lt_iff] at h
    obtain ⟨f, hf⟩ := h
    rw [iInf_lt_iff] at hf
    obtain ⟨hmem, hlt⟩ := hf
    exact ⟨f, hmem.1, hmem.2, hlt⟩
  choose f hfH hfv hflt using hex
  have hnorm := fun k => exists_normalized hyp (hfH k) (hfv k) (hflt k)
  choose h hhH hh0 hh1 hhE using hnorm
  exact lem25_core hd hyp hr hbd hcpos hκ0 hκc hcb.le Ns hmono.tendsto_atTop
    (fun k => (hNs k).1) h hhH hh0 hh1 (fun k => (hhE k).le)

/-- Lemma 2.5, (2.5). -/
theorem liminf_lamAll_ge_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    bRate (μ : Measure (Torus d)) lam C ≤ liminf (fun N => lamAll V W N) atTop :=
  le_liminf_lamAll_of_bounded hd hyp hr (prop_bounded hd hyp hr μ hμ e lam he C hC)

end SharpLSI.FL
