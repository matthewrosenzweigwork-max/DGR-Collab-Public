import FullLabeledLSI.Statements.S02_Prop_2_1
import FullLabeledLSI.Statements.S03_Prop_2_2

/-!
# Lemma 2.4 (`lem:UI`): uniform integrability from one defective inequality

* `tail_le_of_ent`: on a probability space, a nonnegative `u` with `Ent_P(u) ≤ E` and
  `∫ u ≤ B` has `∫_{u > A} u ≤ ε` for `A = B exp (2 + E/ε)`. (This is the manuscript's
  `∫_{g² > A} g² ≤ C / log A`, proved directly from the nonnegative form of `Ent`.)
* `unifIntegrable_sq_aux`: Lemma 2.4 from `prop_defective_all` and `0 < r_ms`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

section Tail

variable {α : Type*} [MeasurableSpace α]

/-- The core estimate, for a measurable function. -/
theorem tail_le_of_ent_meas (P : Measure α) [IsProbabilityMeasure P] (u : α → ℝ)
    (hum : Measurable u) (hu : 0 ≤ᵐ[P] u) {E B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) (hE0 : 0 ≤ E)
    (hent : ent P u ≤ ENNReal.ofReal E) (hm : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≤ ENNReal.ofReal B) :
    ∫⁻ x in {x | B * Real.exp (2 + E / ε) < u x}, ENNReal.ofReal (u x) ∂P ≤
      ENNReal.ofReal ε := by
  classical
  have hint : Integrable u P := by
    by_contra h
    have : ent P u = ⊤ := by unfold ent; simp [h]
    rw [this] at hent
    exact absurd hent (by simp)
  set m : ℝ := ∫ y, u y ∂P with hmdef
  have hm0 : 0 ≤ m := integral_nonneg_of_ae hu
  have hofm : ENNReal.ofReal m = ∫⁻ x, ENNReal.ofReal (u x) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hint hu
  have hmB : m ≤ B := by
    have := hofm ▸ hm
    exact (ENNReal.ofReal_le_ofReal_iff hB.le).1 this
  set A : ℝ := B * Real.exp (2 + E / ε) with hA
  have hApos : 0 < A := mul_pos hB (Real.exp_pos _)
  rcases hm0.eq_or_lt with h0 | hpos
  · -- `m = 0`
    have : ∫⁻ x, ENNReal.ofReal (u x) ∂P = 0 := by rw [← hofm, ← h0]; simp
    exact (setLIntegral_le_lintegral _ _).trans (this.le.trans (by positivity))
  · -- `m > 0`
    set L : ℝ := 1 + E / ε with hL
    have hLpos : 0 < L := by positivity
    have hent' : ∫⁻ x, ENNReal.ofReal (m * klFun (u x / m)) ∂P ≤ ENNReal.ofReal E := by
      have := hent
      unfold ent at this
      simpa [hint] using this
    have hpt : ∀ x ∈ {x | A < u x},
        ENNReal.ofReal L * ENNReal.ofReal (u x) ≤ ENNReal.ofReal (m * klFun (u x / m)) := by
      intro x hx
      have hx : A < u x := hx
      have hux : 0 < u x := hApos.trans hx
      rw [← ENNReal.ofReal_mul hLpos.le]
      apply ENNReal.ofReal_le_ofReal
      have hk : m * klFun (u x / m) = u x * Real.log (u x / m) + m - u x := by
        unfold klFun
        field_simp
      rw [hk]
      have hratio : A / B ≤ u x / m := by
        rw [div_le_div_iff₀ hB hpos]
        nlinarith [mul_le_mul hx.le hmB hpos.le (hux.le)]
      have hlog : 2 + E / ε ≤ Real.log (u x / m) := by
        have := Real.log_le_log (div_pos hApos hB) hratio
        have e : A / B = Real.exp (2 + E / ε) := by rw [hA]; field_simp
        rwa [e, Real.log_exp] at this
      nlinarith [mul_le_mul_of_nonneg_left hlog hux.le]
    have hmeasS : MeasurableSet {x | A < u x} := measurableSet_lt measurable_const hum
    have h1 : ENNReal.ofReal L * ∫⁻ x in {x | A < u x}, ENNReal.ofReal (u x) ∂P ≤
        ENNReal.ofReal E := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ∫⁻ x in {x | A < u x}, ENNReal.ofReal L * ENNReal.ofReal (u x) ∂P
          ≤ ∫⁻ x in {x | A < u x}, ENNReal.ofReal (m * klFun (u x / m)) ∂P :=
            setLIntegral_mono' hmeasS hpt
        _ ≤ ∫⁻ x, ENNReal.ofReal (m * klFun (u x / m)) ∂P := setLIntegral_le_lintegral _ _
        _ ≤ ENNReal.ofReal E := hent'
    have hEL : ENNReal.ofReal E ≤ ENNReal.ofReal ε * ENNReal.ofReal L := by
      rw [← ENNReal.ofReal_mul hε.le]
      apply ENNReal.ofReal_le_ofReal
      rw [hL]
      have : ε * (1 + E / ε) = ε + E := by field_simp
      rw [this]; linarith
    have h2 : ENNReal.ofReal L * ∫⁻ x in {x | A < u x}, ENNReal.ofReal (u x) ∂P ≤
        ENNReal.ofReal L * ENNReal.ofReal ε := by
      refine h1.trans (hEL.trans (le_of_eq ?_))
      rw [mul_comm]
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hLpos) ENNReal.ofReal_ne_top).1 h2

/-- The tail estimate for a nonnegative function (a.e. measurable suffices through integrability). -/
theorem tail_le_of_ent (P : Measure α) [IsProbabilityMeasure P] (u : α → ℝ)
    (hu : ∀ x, 0 ≤ u x) {E B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) (hE0 : 0 ≤ E)
    (hent : ent P u ≤ ENNReal.ofReal E) (hm : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≤ ENNReal.ofReal B) :
    ∫⁻ x in {x | B * Real.exp (2 + E / ε) < u x}, ENNReal.ofReal (u x) ∂P ≤
      ENNReal.ofReal ε := by
  classical
  have hint : Integrable u P := by
    by_contra h
    have : ent P u = ⊤ := by unfold ent; simp [h]
    rw [this] at hent
    exact absurd hent (by simp)
  have hae : AEMeasurable u P := hint.aestronglyMeasurable.aemeasurable
  set v := hae.mk u with hv
  have huv : u =ᵐ[P] v := hae.ae_eq_mk
  have hvm : Measurable v := hae.measurable_mk
  have hent' : ent P v ≤ ENNReal.ofReal E := by
    have : ent P v = ent P u := by
      unfold ent
      have hiv : Integrable v P := hint.congr huv
      simp only [hint, hiv, ite_true]
      rw [integral_congr_ae huv.symm]
      refine lintegral_congr_ae ?_
      filter_upwards [huv] with x hx
      rw [hx]
    rwa [this]
  have hm' : ∫⁻ x, ENNReal.ofReal (v x) ∂P ≤ ENNReal.ofReal B := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hm
    filter_upwards [huv] with x hx
    rw [hx]
  have hv0 : 0 ≤ᵐ[P] v := by filter_upwards [huv] with x hx; rw [← hx]; exact hu x
  have key := tail_le_of_ent_meas P v hvm hv0 hB hε hE0 hent' hm'
  have hset : {x | B * Real.exp (2 + E / ε) < u x} =ᵐ[P] {x | B * Real.exp (2 + E / ε) < v x} := by
    filter_upwards [huv] with x hx
    simp only [hx]
  rw [setLIntegral_congr hset]
  refine le_trans (le_of_eq ?_) key
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [huv] with x hx
  rw [hx]

end Tail

variable {d : ℕ}

/-- Lemma 2.4 (`lem:UI`), the proof body. -/
theorem unifIntegrable_sq_aux {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (Ns : ℕ → ℕ) (hNs : ∀ k, 1 ≤ Ns k) (g : (k : ℕ) → Config (Ns k) d → ℝ)
    (hg : ∀ k, MemH1C (gibbs V W (Ns k)) (g k))
    (hB : ∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns k)) + energy V W (Ns k) (g k) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
      ∫⁻ X in {X | M < g k X ^ 2}, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns k) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨B, hB⟩ := hB
  obtain ⟨⟨μ, hμ⟩, -, -⟩ := exists_minimizer hyp
  have hpos : 0 < rMs V W := (rMs_pos_le_rLS hd hyp hr μ hμ).1
  obtain ⟨r, hr0, hr1, hrlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
  have hr0' : 0 < r := ENNReal.ofReal_pos.1 hr1
  obtain ⟨Br, hBr⟩ := prop_defective_all hd hyp hr r hr0' hrlt
  set B' : ℝ := max (B : ℝ) 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set E : ℝ := 2 / r * B' + (Br : ℝ) * B' with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ 2 / r := by positivity
    positivity
  refine ⟨B' * Real.exp (2 + E / ε), fun k => ?_⟩
  have : IsProbabilityMeasure (gibbs V W (Ns k)) := gibbs_isProbabilityMeasure hyp (Ns k)
  have hBle : (B : ℝ≥0∞) ≤ ENNReal.ofReal B' := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h1 : ∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns k) ≤ ENNReal.ofReal B' :=
    le_trans (le_self_add) (hB k) |>.trans hBle
  have h2 : energy V W (Ns k) (g k) ≤ ENNReal.ofReal B' :=
    le_trans (le_add_self) (hB k) |>.trans hBle
  have hent : ent (gibbs V W (Ns k)) (fun X => g k X ^ 2) ≤ ENNReal.ofReal E := by
    refine (hBr (Ns k) (hNs k) (g k) (hg k)).trans ?_
    rw [hE, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact (ENNReal.ofReal_coe_nnreal).ge
  exact tail_le_of_ent (gibbs V W (Ns k)) (fun X => g k X ^ 2) (fun X => sq_nonneg _)
    hB'pos hε hE0 hent h1

end SharpLSI.FL
