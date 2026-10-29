import SharpSymmetricLSI.Paper.R7Positive
import SharpSymmetricLSI.Statements.R04_Prop_2_3

/-!
# R7: Section 2.3, assembly

`lower_bound_core`: under (1.2), `r_* > 0`, the defective inequality (Proposition 2.2), Lemma B.1,
and the Gaussian input properties (2.4)–(2.8) for some `(γ, ℰ_∞, λ_G)`, the finite-`N`
inequality (1.10) holds. A failure produces normalized violators (`exists_violators`); after
extraction, `h_N → h`, `ℰ_N → E`; Proposition 2.3 is applied to `f_N` when `h > 0`
(`positive_contra`) and to `v_N = (f_N - 1)/√h_N` when `h = 0` (`vanishing_contra`).
-/

open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

set_option maxHeartbeats 2000000 in
/-- Section 2.3 from the abstract Gaussian input. -/
theorem lower_bound_core (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (h22 : DefectiveConclusion' V W) (hB1 : TruncationConclusion) {γ : Measure (ℕ → ℝ)}
    [IsProbabilityMeasure γ] {EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞} {lG : ℝ≥0∞}
    (hG : GaussianInputProperties V W γ EInf lG) : FiniteNConclusion' V W := by
  by_contra hfail
  obtain ⟨r, hr0, hrS, Ns, f, hNs, hmem, hsym, hf0, hnorm, hfin, hviol⟩ :=
    exists_violators hyp h22 hfail
  -- `r < r₀ < r_*`
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
  have hlGr : ENNReal.ofReal r₀ < lG := lt_of_lt_of_le hr₀S hG.1
  -- notation
  set hseq : ℕ → ℝ := fun k => (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal with hhs
  set Eseq : ℕ → ℝ := fun k => (energy V W (Ns k) (f k)).toReal with hEs
  have hE0 : ∀ k, 0 ≤ Eseq k := fun k => ENNReal.toReal_nonneg
  -- bounds on `h_k`, `E_k`
  have hL2one : ∀ k, ∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k) = 1 := by
    intro k
    have hi := (memLp_of_memH1C hyp (hmem k)).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun X => sq_nonneg _),
      hnorm k, ENNReal.ofReal_one]
  have hhbound : ∀ k, hseq k ≤ B * r₀ / (r₀ - r) := by
    intro k
    have h1 := hB (Ns k) (hNs1 k) (f k) (hmem k) (hsym k)
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
  · -- vanishing entropy: apply Proposition 2.3 to `v_k = (f_k - 1)/√h_k`
    set v : (k : ℕ) → Config (Ns (φ1 k)) d → ℝ :=
      fun k X => 1 / Real.sqrt (hseq (φ1 k)) * (f (φ1 k) X + (-1)) with hvdef
    have hv_eq : ∀ k X, v k X = (f (φ1 k) X - 1) / Real.sqrt (hseq (φ1 k)) := by
      intro k X; simp only [hvdef]; ring
    have hvmem : ∀ k, MemH1C (gibbs V W (Ns (φ1 k))) (v k) := fun k =>
      memH1C_smul hyp (memH1C_add_const hyp (hmem _) (-1)) _
    have hvsym : ∀ k, IsSymmetric (v k) := fun k σ X => by
      simp only [hvdef, hsym (φ1 k) σ X]
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
    obtain ⟨φ2, hφ2, F, hF, -, hUI, -, -, -, -⟩ := hG.2.2.1 (fun k => Ns (φ1 k)) hT1 v
      (fun k => ⟨hvmem k, hvsym k⟩) hvbound
    simp only [hv_eq] at hUI
    have hT2 : Tendsto (fun k => Ns (φ1 (φ2 k))) atTop atTop := hT1.comp hφ2.tendsto_atTop
    have hlam : ∀ᶠ k in atTop, ENNReal.ofReal r₀ ≤ lamSym V W (Ns (φ1 (φ2 k))) :=
      ((hG.2.2.2.comp hT2).eventually (lt_mem_nhds hlGr)).mono fun _ hk => hk.le
    have hh2 : Tendsto (fun k => hseq (φ1 (φ2 k))) atTop (𝓝 0) := by
      rw [h0]; exact hh1.comp hφ2.tendsto_atTop
    exact vanishing_contra hyp hB1 hr0 hrr₀ le_rfl hB (Ns := fun k => Ns (φ1 (φ2 k)))
      (fun k => hNs1 _) hlam (f := fun k => f (φ1 (φ2 k))) (fun k => hmem _) (fun k => hsym _)
      (fun k => hf0 _) (fun k => hnorm _) (fun k => hfin _) (fun k => hviol _) hh2 hUI
  · -- positive entropy: apply Proposition 2.3 to `f_k`
    have hfbound : ∃ B' : NNReal, ∀ k,
        (∫⁻ X, ENNReal.ofReal (f (φ1 k) X ^ 2) ∂gibbs V W (Ns (φ1 k))) +
          energy V W (Ns (φ1 k)) (f (φ1 k)) ≤ B' := by
      refine ⟨(1 + r / 2 * Kb).toNNReal, fun k => ?_⟩
      rw [hL2one, ← ENNReal.ofReal_toReal (energy_lt_top hyp (hmem (φ1 k))).ne,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (by linarith [hEbound (φ1 k)])
    obtain ⟨φ2, hφ2, F, hF, hlaw, -, -, hsq, hEF, hχ⟩ := hG.2.2.1 (fun k => Ns (φ1 k)) hT1
      (fun k => f (φ1 k)) (fun k => ⟨hmem _, hsym _⟩) hfbound
    exact positive_contra hyp hB1 hr0 hη0 hrη hB (Ns := fun k => Ns (φ1 (φ2 k)))
      (fun k => hNs1 _) (f := fun k => f (φ1 (φ2 k))) (fun k => hmem _) (fun k => hsym _)
      (fun k => hf0 _) (fun k => hnorm _) (fun k => hfin _) (fun k => hviol _)
      (hh1.comp hφ2.tendsto_atTop) hpos (hE1.comp hφ2.tendsto_atTop) hlGr.le
      (fun F hF => (hG.2.1 F hF).1) hF hlaw hsq hEF hχ

end SharpLSI
