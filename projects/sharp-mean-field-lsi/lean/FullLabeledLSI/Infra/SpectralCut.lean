import FullLabeledLSI.Infra.SpectralEnergy

/-!
# Spectral calculus, stage 3: the cut package (manuscript Section 6.3, (6.18)-(6.21))

* `eLpNorm_Sfun_gross_le` (hypercontractivity of the semigroup on all of `L²`):
  `‖S_t Ψ‖_{1 + e^{at}} ≤ ‖Ψ‖₂` for every `Ψ ∈ L²(Q)`, `t ≥ 0`.  It follows from the corresponding bound for
  the cutoffs `Fcut t L Ψ` (`eLpNorm_Fcut_gross_le`), because `Fcut t L Ψ → S_t Ψ` in `L²` as
  `L → ∞` (`eLpNorm_Sfun_sub_Fcut_le`), hence along an a.e. convergent subsequence, and Fatou's lemma for
  `eLpNorm`.
* `cut_package`: one statement collecting all ingredients of the `J`-cut estimate for `Ψ ∈ H¹(Q) ∩ L^s`,
  with `Ψt = S_t Ψ` and `F = Fcut t L Ψ`.  The `L^s`-contraction `‖S_tΨ‖_s ≤ ‖Ψ‖_s` (P5) is an explicit
  hypothesis.
-/

open MeasureTheory SharpLSI Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace SharpLSI.FL.Spectral

/-! ### `L²` norm from a bound on the integral of the square -/

lemma eLpNorm_two_le_ofReal_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) {c : ℝ} (h : ∫ x, f x ^ 2 ∂μ ≤ c) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt c) := by
  have h1 : eLpNorm f 2 μ = ENNReal.ofReal ‖hf.toLp f‖ := by
    rw [← eLpNorm_coe_eq_ofReal_norm, eLpNorm_congr_ae hf.coeFn_toLp]
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : ‖hf.toLp f‖ ^ 2 ≤ c := by rw [norm_toLp_sq hf]; exact h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h2)

/-! ### Hypercontractivity of `S_t` on `L²` -/

section SfunGross

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **Hypercontractivity of the reference semigroup**:
`‖S_t Ψ‖_{1 + e^{at}} ≤ ‖Ψ‖₂` for every `Ψ ∈ L²(μ^{⊗N})` and `t ≥ 0`. -/
theorem eLpNorm_Sfun_gross_le (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    {t : ℝ} (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Sfun hb t Ψ) (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤
      eLpNorm Ψ 2 (Q mu N) := by
  have hlam := lam_nonneg_of_ref hb hlam0
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have h2 : ENNReal.ofReal (1 + Real.exp (a * 0)) = 2 := by
      rw [mul_zero, Real.exp_zero]
      norm_num
    rw [h2]
    exact eLpNorm_Sfun_le hb hlam le_rfl hΨ
  · have hSmem := Sfun_memLp hb t hΨ
    have hbound : ∀ n : ℕ, eLpNorm (Sfun hb t Ψ - Fcut mu e lam t (n : ℝ) Ψ) 2 (Q mu N) ≤
        ENNReal.ofReal (Real.exp (-(t * n))) * eLpNorm Ψ 2 (Q mu N) := fun n =>
      eLpNorm_Sfun_sub_Fcut_le hb hlam0 hd hgrow ht (n : ℝ) hΨ
    have hrate : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(t * n))) *
        eLpNorm Ψ 2 (Q mu N)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.exp (-(t * n))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.const_mul_atTop htpos)
      have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(t * n)))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal h1
      have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr hΨ.eLpNorm_ne_top)
      simpa using h3
    have hconv : Tendsto (fun n : ℕ => eLpNorm (Fcut mu e lam t (n : ℝ) Ψ - Sfun hb t Ψ) 2
        (Q mu N)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrate
        (fun n => bot_le) (fun n => ?_)
      rw [eLpNorm_sub_comm]
      exact hbound n
    have hmeasure : TendstoInMeasure (Q mu N) (fun n : ℕ => Fcut mu e lam t (n : ℝ) Ψ) atTop
        (Sfun hb t Ψ) := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
    obtain ⟨ns, hns, hae'⟩ := hmeasure.exists_seq_tendsto_ae
    have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm
      (p := ENNReal.ofReal (1 + Real.exp (a * t)))
      (f := fun k => Fcut mu e lam t (ns k : ℝ) Ψ)
      (fun k => (memLp_Fcut hb t (ns k : ℝ) Ψ).aestronglyMeasurable) (Sfun hb t Ψ)
      hSmem.aestronglyMeasurable hae'
    refine hfat.trans (le_trans Filter.liminf_le_limsup (limsup_le_of_le (by isBoundedDefault)
      (Eventually.of_forall fun k => ?_)))
    exact eLpNorm_Fcut_gross_le hac hca hb hC1 hae ha hrls hlam0 ht (ns k : ℝ) hΨ

end SfunGross

/-! ### The cut package -/

section Package

/-- The ingredients of the `J`-cut estimate (manuscript (6.18)-(6.21)) for `Ψ`, its smoothing
`Ψt = S_t Ψ` and the spectral cutoff `F = Π_L S_t Ψ`.  Here `q_t = 1 + exp (a t)`, and
`Bs` bounds `‖Ψ‖_s` (hence `‖Ψ‖₂`). -/
structure CutPackage {N d : ℕ} (mu : Measure (Torus d)) (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ)
    (a s Bs t L : ℝ) (Ψ Ψt F : Config N d → ℝ) : Prop where
  /-- (P1) `∫ (Ψ - Ψt)² ≤ t ℰ⁰(Ψ)`. -/
  integral_sq_le : ∫ X, (Ψ X - Ψt X) ^ 2 ∂(Q mu N) ≤ t * (refEnergy mu Ψ).toReal
  /-- (P1) `‖Ψ - Ψt‖₂ ≤ √(t ℰ⁰(Ψ))`. -/
  eLpNorm_sub_le :
    eLpNorm (Ψ - Ψt) 2 (Q mu N) ≤ ENNReal.ofReal (Real.sqrt (t * (refEnergy mu Ψ).toReal))
  /-- (P2) `‖Ψt - F‖₂ ≤ e^{-tL} ‖Ψ‖₂`. -/
  eLpNorm_cut_le :
    eLpNorm (Ψt - F) 2 (Q mu N) ≤ ENNReal.ofReal (Real.exp (-(t * L))) * eLpNorm Ψ 2 (Q mu N)
  /-- (P2) `‖Ψt - F‖₂ ≤ e^{-tL} Bs`. -/
  eLpNorm_cut_le_B :
    eLpNorm (Ψt - F) 2 (Q mu N) ≤ ENNReal.ofReal (Real.exp (-(t * L)) * Bs)
  /-- (P3) `ℰ⁰(F) ≤ ℰ⁰(Ψ)`. -/
  refEnergy_le : refEnergy mu F ≤ refEnergy mu Ψ
  /-- (P4) `F` is in the range of the spectral projection. -/
  inRange : InSpectralRange e lam L F
  /-- The exponent `s` is finite. -/
  s_ne_top : ENNReal.ofReal s ≠ ⊤
  /-- Common `L^s` bounds for the pair `(Ψ, Ψt)` (the bound for `Ψt` is (P5)). -/
  memLp_Ψ_s : MemLp Ψ (ENNReal.ofReal s) (Q mu N)
  memLp_Ψt_s : MemLp Ψt (ENNReal.ofReal s) (Q mu N)
  eLpNorm_Ψ_s_le : eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) ≤ ENNReal.ofReal Bs
  eLpNorm_Ψt_s_le : eLpNorm Ψt (ENNReal.ofReal s) (Q mu N) ≤ ENNReal.ofReal Bs
  /-- The exponent `q_t = 1 + exp (a t)` is `> 2` and finite. -/
  two_lt_q : (2 : ℝ≥0∞) < ENNReal.ofReal (1 + Real.exp (a * t))
  q_ne_top : ENNReal.ofReal (1 + Real.exp (a * t)) ≠ ⊤
  /-- Common `L^{q_t}` bounds for the pair `(Ψt, F)` (hypercontractivity, (P4)). -/
  memLp_Ψt_q : MemLp Ψt (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N)
  memLp_F_q : MemLp F (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N)
  eLpNorm_Ψt_q_le : eLpNorm Ψt (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤
    eLpNorm Ψ 2 (Q mu N)
  eLpNorm_F_q_le : eLpNorm F (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤
    eLpNorm Ψ 2 (Q mu N)
  eLpNorm_two_le_B : eLpNorm Ψ 2 (Q mu N) ≤ ENNReal.ofReal Bs
  eLpNorm_Ψt_q_le_B : eLpNorm Ψt (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤
    ENNReal.ofReal Bs
  eLpNorm_F_q_le_B : eLpNorm F (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤
    ENNReal.ofReal Bs

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **The cut package.**  For `Ψ ∈ H¹(Q) ∩ L^s(Q)`, `2 ≤ s`, `t > 0`, `L` real, with the `L^s`
contraction `hP5` of the semigroup as hypothesis. -/
theorem cut_package {Cu Cl : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    {s Bs t : ℝ} (hs : 2 ≤ s) (ht : 0 < t) (L : ℝ) {Ψ : Config N d → ℝ}
    (hH : MemH1C (Q mu N) Ψ) (hΨs : MemLp Ψ (ENNReal.ofReal s) (Q mu N))
    (hBs : eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) ≤ ENNReal.ofReal Bs)
    (hP5 : eLpNorm (Sfun hb t Ψ) (ENNReal.ofReal s) (Q mu N) ≤
      eLpNorm Ψ (ENNReal.ofReal s) (Q mu N)) :
    CutPackage mu e lam a s Bs t L Ψ (Sfun hb t Ψ) (Fcut mu e lam t L Ψ) := by
  have hac : mu ≪ volume := Measure.absolutelyContinuous_of_le_smul hup
  have hca : volume ≪ mu := Measure.absolutelyContinuous_of_le_smul hlow
  have hΨ2 : MemLp Ψ 2 (Q mu N) := memLp_of_H1 hH
  have hSmem : MemLp (Sfun hb t Ψ) 2 (Q mu N) := Sfun_memLp hb t hΨ2
  have h2s : eLpNorm Ψ 2 (Q mu N) ≤ eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) :=
    eLpNorm_le_eLpNorm_of_exponent_le (by
      calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hs)
  have h2B : eLpNorm Ψ 2 (Q mu N) ≤ ENNReal.ofReal Bs := h2s.trans hBs
  have hqt : 1 < Real.exp (a * t) := Real.one_lt_exp_iff.2 (mul_pos ha ht)
  have hq2 : (2 : ℝ≥0∞) < ENNReal.ofReal (1 + Real.exp (a * t)) := by
    calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      _ < ENNReal.ofReal (1 + Real.exp (a * t)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hF := eLpNorm_Fcut_gross_le hac hca hb hC1 hae ha hrls hlam0 ht.le L hΨ2
  have hSq := eLpNorm_Sfun_gross_le hac hca hb hC1 hae ha hrls hlam0 hd hgrow ht.le hΨ2
  have hP1 := integral_Sfun_sub_sq_le_of_H1 hup hlow hb hC1 hae hlam0 ht.le hH
  have hP2 := eLpNorm_Sfun_sub_Fcut_le hb hlam0 hd hgrow ht.le L hΨ2
  have hI : ∫ X, (Ψ X - Sfun hb t Ψ X) ^ 2 ∂(Q mu N) ≤ t * (refEnergy mu Ψ).toReal :=
    (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun X => by ring))).trans hP1
  exact
    { integral_sq_le := hI
      eLpNorm_sub_le := eLpNorm_two_le_ofReal_sqrt (f := Ψ - Sfun hb t Ψ) (hΨ2.sub hSmem) hI
      eLpNorm_cut_le := hP2
      eLpNorm_cut_le_B := hP2.trans
        ((by gcongr : ENNReal.ofReal (Real.exp (-(t * L))) * eLpNorm Ψ 2 (Q mu N) ≤
          ENNReal.ofReal (Real.exp (-(t * L))) * ENNReal.ofReal Bs).trans_eq
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm)
      refEnergy_le := refEnergy_Fcut_le_of_H1 hup hlow hb hC1 hae hlam0 ht.le L hH
      inRange := InSpectralRange_Fcut hb hlam0 hd hgrow t L Ψ
      s_ne_top := ENNReal.ofReal_ne_top
      memLp_Ψ_s := hΨs
      memLp_Ψt_s := lt_of_le_of_lt hP5 hΨs
      eLpNorm_Ψ_s_le := hBs
      eLpNorm_Ψt_s_le := hP5.trans hBs
      two_lt_q := hq2
      q_ne_top := ENNReal.ofReal_ne_top
      memLp_Ψt_q := lt_of_le_of_lt hSq hΨ2
      memLp_F_q := lt_of_le_of_lt hF hΨ2
      eLpNorm_Ψt_q_le := hSq
      eLpNorm_F_q_le := hF
      eLpNorm_two_le_B := h2B
      eLpNorm_Ψt_q_le_B := hSq.trans h2B
      eLpNorm_F_q_le_B := hF.trans h2B }

end Package

end SharpLSI.FL.Spectral

end
