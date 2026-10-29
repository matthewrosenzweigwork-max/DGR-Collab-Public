import FullLabeledLSI.Paper.Thm11Positive
import FullLabeledLSI.Paper.Thm11Vanishing
import FullLabeledLSI.Statements.S02_Prop_2_1
import FullLabeledLSI.Statements.S03_Prop_2_2
import FullLabeledLSI.Statements.S04_Prop_2_3
import FullLabeledLSI.Statements.S05_Lemma_2_4
import FullLabeledLSI.Statements.S06_Lemma_2_5
import SharpSymmetricLSI.Statements.R04_Prop_2_3

/-!
# Theorem 1.1 (FL): assembly from Propositions 2.1--2.3 and Lemmas 2.4, 2.5

* `finiteN_all_core`: (1.15) for every `r < r_ms` when `r_* > 0`. A failure produces normalized
  violators (`exists_violators_all`); after extraction `h_N → h`, `ℰ_N → E`; the bounded
  comparison (Proposition 2.3) is applied to the truncations `f_N ∧ M` when `h > 0`
  (`positive_contra_all`), and the uniform integrability of Lemma 2.4 to
  `v_N = (f_N - 1)/√h_N` together with `liminf λ_N^all ≥ b ≥ r_ms` (Lemma 2.5) when `h = 0`
  (`vanishing_contra_all`).
* `limit_all_of_finiteN`: (1.14) from (1.15) and the upper bound of Proposition 2.1.

This file does not import `Statements/S01_Theorem_1_1`.
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

set_option maxHeartbeats 2000000 in
/-- **(1.15)** for every rate below `r_ms`, when `r_* > 0`. -/
theorem finiteN_all_core (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    FiniteNConclusionAll' V W := by
  by_contra hfail
  have h22 := prop_defective_all hd hyp hr
  obtain ⟨μ, hμ⟩ := (prop_equilibrium hd hyp hr).1.exists
  obtain ⟨⟨e, lam, he⟩, h2⟩ := prop_compactness hd hyp hr μ hμ
  obtain ⟨⟨C, hC⟩, h3⟩ := h2 e lam he
  obtain ⟨⟨γ, hγ⟩, h4⟩ := h3 C hC
  have hG := h4 γ hγ
  have hbR : rMs V W ≤ bRate (μ : Measure (Torus d)) lam C :=
    le_min (rMs_pos_le_rLS_aux hd hyp hr μ hμ).2 (rMs_le_rStar.trans hG.1)
  have hcomp0 := prop_bounded hd hyp hr μ hμ e lam he C hC
  have hlamb := liminf_lamAll_ge hd hyp hr μ hμ e lam he C hC
  obtain ⟨r, hr0, hrS, Ns, f, hNs, hmem, hf0, hnorm, hfin, hviol⟩ :=
    exists_violators_all hyp h22 hfail
  -- `r < r₀ < r_ms`
  obtain ⟨r₀, -, hrr₀', hr₀S⟩ := ENNReal.lt_iff_exists_real_btwn.mp hrS
  have hrr₀ : r < r₀ := by
    rcases le_or_gt r₀ 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h] at hrr₀'; exact absurd hrr₀' (not_lt.mpr zero_le)
    · exact (ENNReal.ofReal_lt_ofReal_iff h).mp hrr₀'
  have hr₀ : 0 < r₀ := by linarith
  set η := (r₀ - r) / (2 * r) with hη
  have hη0 : 0 < η := by rw [hη]; apply div_pos <;> linarith
  have hrη : (1 + η) * r < r₀ := by
    rw [hη]; field_simp; nlinarith
  obtain ⟨B, hB⟩ := h22 r₀ hr₀ hr₀S
  have hNs1 : ∀ k, 1 ≤ Ns k := fun k => le_trans (by omega) (hNs k)
  have hNsT : Tendsto Ns atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (Nat.le_succ k) (hNs k)) tendsto_id
  -- notation
  set hseq : ℕ → ℝ := fun k => (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal with hhs
  set Eseq : ℕ → ℝ := fun k => (energy V W (Ns k) (f k)).toReal with hEs
  have hE0 : ∀ k, 0 ≤ Eseq k := fun k => ENNReal.toReal_nonneg
  -- bounds on `h_k`, `E_k`
  have hL2one : ∀ k, ∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k) = 1 := by
    intro k
    have : IsProbabilityMeasure (gibbs V W (Ns k)) := gibbs_isProbabilityMeasure hyp (Ns k)
    have hi := (memLp_of_memH1C hyp (hmem k)).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun X => sq_nonneg _),
      hnorm k, ENNReal.ofReal_one]
  have hhbound : ∀ k, hseq k ≤ B * r₀ / (r₀ - r) := by
    intro k
    have h1 := hB (Ns k) (hNs1 k) (f k) (hmem k)
    rw [hL2one k, mul_one] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (energy_lt_top hyp (hmem k)).ne, ENNReal.coe_ne_top⟩) h1
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (energy_lt_top hyp (hmem k)).ne) ENNReal.coe_ne_top, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal] at h2
    have h3 := hviol k
    rw [le_div_iff₀ (by linarith)]
    have h4 : 2 / r₀ * Eseq k ≤ r / r₀ * hseq k := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr₀]; linarith
    have h5 : hseq k ≤ r / r₀ * hseq k + B := by
      change hseq k ≤ _ at h2; linarith
    rw [div_mul_eq_mul_div, div_add' _ _ _ hr₀.ne', le_div_iff₀ hr₀] at h5
    nlinarith
  have hhpos : ∀ k, 0 < hseq k := fun k => by have := hviol k; nlinarith [hE0 k]
  have hEbound : ∀ k, Eseq k ≤ r / 2 * (B * r₀ / (r₀ - r)) := fun k => by
    have := hviol k; nlinarith [hhbound k]
  -- extraction: `h_k → h`, `E_k → E`
  set Kb := B * r₀ / (r₀ - r) with hKb
  have hbdd : Bornology.IsBounded (Set.Icc (0 : ℝ) Kb ×ˢ Set.Icc (0 : ℝ) (r / 2 * Kb)) :=
    (Metric.isBounded_Icc 0 Kb).prod (Metric.isBounded_Icc 0 (r / 2 * Kb))
  obtain ⟨⟨h, E⟩, -, φ1, hφ1, hlim⟩ := tendsto_subseq_of_bounded hbdd
    (x := fun k => (hseq k, Eseq k))
    (fun k => ⟨⟨(hhpos k).le, hhbound k⟩, ⟨hE0 k, hEbound k⟩⟩)
  have hh1 : Tendsto (fun k => hseq (φ1 k)) atTop (𝓝 h) := (continuous_fst.tendsto _).comp hlim
  have hE1 : Tendsto (fun k => Eseq (φ1 k)) atTop (𝓝 E) := (continuous_snd.tendsto _).comp hlim
  have hT1 : Tendsto (fun k => Ns (φ1 k)) atTop atTop := hNsT.comp hφ1.tendsto_atTop
  have hh0 : 0 ≤ h := ge_of_tendsto' hh1 fun k => (hhpos _).le
  rcases hh0.eq_or_lt with h0 | hpos
  · -- vanishing entropy: Lemma 2.4 for `v_k = (f_k - 1)/√h_k`
    set v : (k : ℕ) → Config (Ns (φ1 k)) d → ℝ :=
      fun k X => 1 / Real.sqrt (hseq (φ1 k)) * (f (φ1 k) X + (-1)) with hvdef
    have hv_eq : ∀ k X, v k X = (f (φ1 k) X - 1) / Real.sqrt (hseq (φ1 k)) := by
      intro k X; simp only [hvdef]; ring
    have hvmem : ∀ k, MemH1C (gibbs V W (Ns (φ1 k))) (v k) := fun k =>
      memH1C_smul hyp (memH1C_add_const hyp (hmem _) (-1)) _
    have hvbound : ∃ B' : NNReal, ∀ k,
        (∫⁻ X, ENNReal.ofReal (v k X ^ 2) ∂gibbs V W (Ns (φ1 k))) +
          energy V W (Ns (φ1 k)) (v k) ≤ B' := by
      refine ⟨(1 + r / 2).toNNReal, fun k => ?_⟩
      have : IsProbabilityMeasure (gibbs V W (Ns (φ1 k))) :=
        gibbs_isProbabilityMeasure hyp (Ns (φ1 k))
      set hk := hseq (φ1 k)
      have hkpos := hhpos (φ1 k)
      have hsq : (1 / Real.sqrt hk) ^ 2 = 1 / hk := by
        rw [div_pow, Real.sq_sqrt hkpos.le, one_pow]
      have hfL := memLp_of_memH1C hyp (hmem (φ1 k))
      -- the `L²` part
      have h1 : ∫⁻ X, ENNReal.ofReal (v k X ^ 2) ∂gibbs V W (Ns (φ1 k)) ≤ 1 := by
        have e : ∀ X, v k X ^ 2 = 1 / hk * (f (φ1 k) X - 1) ^ 2 := fun X => by
          rw [hv_eq, div_pow, Real.sq_sqrt hkpos.le]; ring
        simp_rw [e]
        have hi : Integrable (fun X => (f (φ1 k) X - 1) ^ 2) (gibbs V W (Ns (φ1 k))) :=
          (hfL.sub (memLp_const 1)).integrable_sq
        rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (Eventually.of_forall
          fun X => mul_nonneg (by positivity) (sq_nonneg _)), integral_const_mul]
        have := integral_sub_one_sq_le_ent (hf0 (φ1 k)) hfL (hnorm _) (hfin _)
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [div_mul_eq_mul_div, one_mul, div_le_one hkpos]
        exact this
      -- the energy part
      have h2 : energy V W (Ns (φ1 k)) (v k) ≤ ENNReal.ofReal (r / 2) := by
        rw [show v k = fun X => 1 / Real.sqrt hk * (f (φ1 k) X + (-1)) from rfl,
          energy_smul hyp (memH1C_add_const hyp (hmem _) (-1)),
          energy_add_const hyp (hmem _), hsq,
          ← ENNReal.ofReal_toReal (energy_lt_top hyp (hmem (φ1 k))).ne,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := hviol (φ1 k)
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hkpos]
        change 2 * Eseq (φ1 k) < r * hk at this
        change Eseq (φ1 k) ≤ r / 2 * hk
        linarith
      calc (∫⁻ X, ENNReal.ofReal (v k X ^ 2) ∂gibbs V W (Ns (φ1 k))) +
            energy V W (Ns (φ1 k)) (v k) ≤ 1 + ENNReal.ofReal (r / 2) := add_le_add h1 h2
        _ = ((1 + r / 2).toNNReal : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]; rfl
    have hUI := unifIntegrable_sq hd hyp hr (fun k => Ns (φ1 k)) (fun k => hNs1 _) v hvmem hvbound
    simp only [hv_eq] at hUI
    have hlam : ∀ᶠ k in atTop, ENNReal.ofReal r₀ ≤ lamAll V W (Ns (φ1 k)) := by
      have hlt : ENNReal.ofReal r₀ < liminf (fun N => lamAll V W N) atTop :=
        lt_of_lt_of_le hr₀S (hbR.trans hlamb)
      exact (hT1.eventually (eventually_lt_of_lt_liminf hlt)).mono fun _ hk => hk.le
    have hh2 : Tendsto (fun k => hseq (φ1 k)) atTop (𝓝 0) := by rw [h0]; exact hh1
    exact vanishing_contra_all hyp lemma_B1 hr0 hrr₀ le_rfl hB (Ns := fun k => Ns (φ1 k))
      (fun k => hNs1 _) hlam (f := fun k => f (φ1 k)) (fun k => hmem _)
      (fun k => hf0 _) (fun k => hnorm _) (fun k => hfin _) (fun k => hviol _) hh2 hUI
  · -- positive entropy: bounded comparison for the truncations `f_k ∧ M`
    have hEle : ∀ k M, energy V W (Ns (φ1 k)) (fun X => min (f (φ1 k) X) M) ≤
        energy V W (Ns (φ1 k)) (f (φ1 k)) := by
      intro k M
      rw [energy_eq_min_add_posPart hyp (hmem (φ1 k)) M]
      exact le_self_add
    have hEf : ∀ k, energy V W (Ns (φ1 k)) (f (φ1 k)) ≤ ENNReal.ofReal (r / 2 * Kb) := by
      intro k
      rw [← ENNReal.ofReal_toReal (energy_lt_top hyp (hmem (φ1 k))).ne]
      exact ENNReal.ofReal_le_ofReal (hEbound (φ1 k))
    have hcomp : ∀ M : ℝ, 1 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        r₀ / 2 * (ent (gibbs V W (Ns (φ1 k))) (fun X => min (f (φ1 k) X) M ^ 2)).toReal ≤
          (energy V W (Ns (φ1 k)) (fun X => min (f (φ1 k) X) M)).toReal + ε := by
      intro M hM ε hε
      have hbnd : ∃ B' : NNReal, ∀ k,
          (∀ᵐ X ∂gibbs V W (Ns (φ1 k)), |min (f (φ1 k) X) M| ≤ B') ∧
          energy V W (Ns (φ1 k)) (fun X => min (f (φ1 k) X) M) ≤ B' := by
        refine ⟨(max M (r / 2 * Kb)).toNNReal, fun k => ⟨Eventually.of_forall fun X => ?_, ?_⟩⟩
        · have hm0 : 0 ≤ min (f (φ1 k) X) M := le_min (hf0 _ X) (by linarith)
          rw [abs_of_nonneg hm0, Real.coe_toNNReal _ (le_trans (by linarith) (le_max_left _ _))]
          exact (min_le_right _ _).trans (le_max_left _ _)
        · refine (hEle k M).trans ((hEf k).trans ?_)
          rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (le_trans (by linarith)
            (le_max_left _ _))]
          exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
      have hbc := hcomp0 (fun k => Ns (φ1 k)) hT1 (fun k X => min (f (φ1 k) X) M)
        (fun k => memH1C_min hyp (hmem _) M) hbnd ε hε
      filter_upwards [hbc] with k hk
      have hEfin : energy V W (Ns (φ1 k)) (fun X => min (f (φ1 k) X) M) ≠ ⊤ :=
        (energy_lt_top hyp (memH1C_min hyp (hmem _) M)).ne
      have hbge : ENNReal.ofReal r₀ ≤ bRate (μ : Measure (Torus d)) lam C :=
        hr₀S.le.trans hbR
      have hk' : ENNReal.ofReal r₀ / 2 *
          ent (gibbs V W (Ns (φ1 k))) (fun X => min (f (φ1 k) X) M ^ 2) ≤
          energy V W (Ns (φ1 k)) (fun X => min (f (φ1 k) X) M) + ENNReal.ofReal ε :=
        le_trans (mul_le_mul_left (ENNReal.div_le_div_right hbge 2) _) hk
      have hrhs : energy V W (Ns (φ1 k)) (fun X => min (f (φ1 k) X) M) +
          ENNReal.ofReal ε ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hEfin, ENNReal.ofReal_ne_top⟩
      have := ENNReal.toReal_mono hrhs hk'
      rw [ENNReal.toReal_mul, ENNReal.toReal_add hEfin ENNReal.ofReal_ne_top,
        ENNReal.toReal_div, ENNReal.toReal_ofReal hr₀.le, ENNReal.toReal_ofReal hε.le] at this
      simpa using this
    exact positive_contra_all hyp hr0 hη0 hrη hB (Ns := fun k => Ns (φ1 k))
      (fun k => hNs1 _) (f := fun k => f (φ1 k)) (fun k => hmem _)
      (fun k => hf0 _) (fun k => hnorm _) (fun k => hfin _) (fun k => hviol _)
      hh1 hpos hE1 hcomp

/-- `r_ms = 0` when `r_* = 0`. -/
theorem rMs_eq_zero_aux (hr : rStar V W = 0) : rMs V W = 0 :=
  le_antisymm (hr ▸ rMs_le_rStar) zero_le

/-- `0 < r_ms` when `r_* > 0` (Proposition 2.1). -/
theorem rMs_pos_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) : 0 < rMs V W := by
  obtain ⟨μ, hμ⟩ := (prop_equilibrium hd hyp hr).1.exists
  exact (rMs_pos_le_rLS_aux hd hyp hr μ hμ).1

/-- **(1.14)**. For `r_* > 0` from (1.15) and the upper bound; for `r_* = 0` from `r_ms = 0`. -/
theorem limit_all_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ (limsup_rAll_le_rMs hd hyp)
  rcases eq_or_ne (rStar V W) 0 with h0 | h0
  · rw [rMs_eq_zero_aux h0]; exact zero_le
  · have hfin := finiteN_all_core hd hyp (pos_iff_ne_zero.2 h0)
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨r, -, hcr, hrS⟩ := ENNReal.lt_iff_exists_real_btwn.mp hc
    have hr0 : 0 < r := by
      rcases le_or_gt r 0 with h | h
      · rw [ENNReal.ofReal_of_nonpos h] at hcr; exact absurd hcr (not_lt.mpr zero_le)
      · exact h
    obtain ⟨Nr, hNr⟩ := hfin r hr0 hrS
    refine lt_of_lt_of_le hcr (le_liminf_of_le (by isBoundedDefault) ?_)
    filter_upwards [eventually_ge_atTop Nr] with N hN
    exact le_rAll_of_lsi hyp hr0 (hNr N hN)

end SharpLSI.FL
