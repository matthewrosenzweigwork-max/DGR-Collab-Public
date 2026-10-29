import SharpSymmetricLSI.Paper.Sec42Lip
import SharpSymmetricLSI.Statements.R36_Lemma_A_1
import SharpSymmetricLSI.Paper.Coercivity4
import SharpSymmetricLSI.Paper.LyapSchmidt13

/-!
# Section 4.2 (lane s42; R15): the limit of one mean-field flow

Manuscript, "Contraction by the mean-field evolution": for bounded initial data the length
estimate (4.9) and the decay (4.10) make `ρ_t` Cauchy in `d_Lip`; its limit `R(ρ₀)` is a
minimizer, and `d_Lip(ρ_t, R(ρ₀)) ≤ √(2/r_*) √(G(ρ₀) e^{-2 r_* t})` (`tailR`).

The case `r_* = ∞` (where `(r_*).toReal = 0`) is included: then the flow is stationary, and the
dissipation of the initial datum vanishes, which forces `G(ρ₀) = 0` by the definition of `r_*`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

open Classical in
/-- A density as a probability measure (with a fallback). -/
noncomputable def pmOf (μ₀ : ProbabilityMeasure (Torus d)) (f : Torus d → ℝ) :
    ProbabilityMeasure (Torus d) :=
  if h : IsProbabilityMeasure (densMeasure f) then ⟨densMeasure f, h⟩ else μ₀

theorem pmOf_coe (μ₀ : ProbabilityMeasure (Torus d)) {f : Torus d → ℝ}
    (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1) :
    (pmOf μ₀ f : Measure (Torus d)) = densMeasure f := by
  have h := isProbabilityMeasure_densMeasure_ae h0 h1
  have e : pmOf μ₀ f = ⟨densMeasure f, h⟩ := dif_pos h
  rw [e]; rfl

/-- The tail bound `√(2/r_*) √(G e^{-2 r_* t})`. -/
noncomputable def tailR (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (G t : ℝ) : ℝ :=
  Real.sqrt (2 / (rStar V W).toReal) * Real.sqrt (G * Real.exp (-2 * (rStar V W).toReal * t))

theorem tailR_nonneg (G t : ℝ) : 0 ≤ tailR V W G t :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem tailR_mono {G G' : ℝ} (h : G ≤ G') (t : ℝ) : tailR V W G t ≤ tailR V W G' t :=
  mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le))
    (Real.sqrt_nonneg _)

theorem tendsto_tailR (G : ℝ) : Tendsto (fun t => tailR V W G t) atTop (𝓝 0) := by
  rcases (ENNReal.toReal_nonneg (a := rStar V W)).eq_or_lt with h0 | hpos
  · have : (fun t => tailR V W G t) = fun _ => 0 := by
      funext t; unfold tailR; rw [← h0, div_zero, Real.sqrt_zero, zero_mul]
    rw [this]; exact tendsto_const_nhds
  · have h1 : Tendsto (fun t : ℝ => -2 * (rStar V W).toReal * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have h2 : Tendsto (fun t : ℝ => G * Real.exp (-2 * (rStar V W).toReal * t)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp h1).const_mul G
      simpa using this
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h3
    have := h3.const_mul (Real.sqrt (2 / (rStar V W).toReal))
    rw [mul_zero] at this
    exact this

theorem ereal_toENNReal_coe (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

theorem ae_eq_of_densMeasure_eq {f g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) (hf0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (hg0 : ∀ᵐ x ∂haar d, 0 ≤ g x)
    (h : densMeasure f = densMeasure g) : f =ᵐ[haar d] g := by
  unfold densMeasure at h
  have := (withDensity_eq_iff hf.1.aemeasurable.ennreal_ofReal hg.1.aemeasurable.ennreal_ofReal
    (by rw [← ofReal_integral_eq_lintegral_ofReal hf hf0]; exact ENNReal.ofReal_ne_top)).1 h
  filter_upwards [this, hf0, hg0] with x hx a b
  exact (ENNReal.ofReal_eq_ofReal_iff a b).1 hx

section flow
variable (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
  {ρ₀ : Torus d → ℝ} (hm : Measurable ρ₀) (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1)
  (hb : ∃ B, ∀ x, ρ₀ x ≤ B) {ρ : ℝ → Torus d → ℝ} (hρ : IsMildSolution V W ρ₀ ρ)
  (μ₀ : ProbabilityMeasure (Torus d)) {G : ℝ} (hG0 : 0 ≤ G)
  (hG : (gap V W (densMeasure ρ₀)).toENNReal ≤ ENNReal.ofReal G)
include hd hyp hr hm h0 h1 hb hρ hG0 hG

theorem gap_flow_le {s : ℝ} (hs : 0 ≤ s) :
    (gap V W (densMeasure (ρ s))).toENNReal ≤
      ENNReal.ofReal (G * Real.exp (-2 * (rStar V W).toReal * s)) := by
  obtain ⟨-, -, hev⟩ := mf_evolution hd hyp hm h0 h1 hb
  obtain ⟨-, -, h410⟩ := hev ρ hρ
  obtain ⟨hdec, -⟩ := h410 hr s hs
  rw [hρ.2.2.1] at hdec
  have hg0 : 0 ≤ gap V W (densMeasure ρ₀) := by
    haveI := isProbabilityMeasure_densMeasure' h0 h1
    exact gap_nonneg' hyp ⟨densMeasure ρ₀, inferInstance⟩
  refine (EReal.toENNReal_le_toENNReal hdec).trans ?_
  rw [EReal.toENNReal_mul hg0, ereal_toENNReal_coe, ENNReal.ofReal_mul hG0]
  gcongr

/-- **(4.9)–(4.10)**: `d_Lip(ρ_s, ρ_t) ≤ tailR G s` for `0 ≤ s ≤ t`. -/
theorem dLip_flow_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    dLip (pmOf μ₀ (ρ s)) (pmOf μ₀ (ρ t)) ≤ tailR V W G s := by
  obtain ⟨-, -, hev⟩ := mf_evolution hd hyp hm h0 h1 hb
  obtain ⟨-, h49, h410⟩ := hev ρ hρ
  obtain ⟨-, htail⟩ := h410 hr s hs
  have hlen := h49 s t hs hst
  have hP : ∀ u, 0 ≤ u → (pmOf μ₀ (ρ u) : Measure (Torus d)) = densMeasure (ρ u) :=
    fun u hu => pmOf_coe μ₀ (hρ.1 u hu).1 (hρ.1 u hu).2
  have hdl : dLip (pmOf μ₀ (ρ s)) (pmOf μ₀ (ρ t)) =
      dLipM (densMeasure (ρ s)) (densMeasure (ρ t)) := by
    unfold dLip; rw [hP s hs, hP t (hs.trans hst)]
  rw [hdl]
  have hGs := gap_flow_le hd hyp hr hm h0 h1 hb hρ hG0 hG hs
  have hsub : ∫⁻ u in Icc s t, dissipation V W (ρ u) ^ (1 / 2 : ℝ) ≤
      ∫⁻ u in Ioi s, dissipation V W (ρ u) ^ (1 / 2 : ℝ) := by
    rw [setLIntegral_congr Ioi_ae_eq_Ici]
    exact lintegral_mono_set Icc_subset_Ici_self
  have hfin : ENNReal.ofReal (dLipM (densMeasure (ρ s)) (densMeasure (ρ t))) ≤
      ENNReal.ofReal (tailR V W G s) := by
    refine hlen.trans (hsub.trans (htail.trans ?_))
    unfold tailR
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    gcongr
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg hG0 (Real.exp_pos _).le) (by norm_num)]
    exact ENNReal.rpow_le_rpow hGs (by norm_num)
  exact (ENNReal.ofReal_le_ofReal_iff (tailR_nonneg G s)).1 hfin

/-- The limit `R(ρ₀)`, with the uniform rate `tailR`. -/
theorem exists_flow_limit : ∃ R : ProbabilityMeasure (Torus d),
    ∀ t, 0 ≤ t → dLip (pmOf μ₀ (ρ t)) R ≤ tailR V W G t := by
  set P : ℕ → ProbabilityMeasure (Torus d) := fun n => pmOf μ₀ (ρ n)
  obtain ⟨R, -, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := ProbabilityMeasure (Torus d))).tendsto_subseq (x := P) (fun n => mem_univ _)
  refine ⟨R, fun t ht => ?_⟩
  have hl1 := (dLip_metrizes (P ∘ φ) R).1 hlim
  have hl2 : Tendsto (fun k => tailR V W G t + dLip ((P ∘ φ) k) R) atTop
      (𝓝 (tailR V W G t + 0)) := tendsto_const_nhds.add hl1
  rw [add_zero] at hl2
  refine ge_of_tendsto hl2 ?_
  filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop ⌈t⌉₊] with k hk
  have htk : t ≤ (φ k : ℝ) := (Nat.le_ceil t).trans (by exact_mod_cast hk)
  exact (dLip_triangle _ _ _).trans
    (add_le_add (dLip_flow_le hd hyp hr hm h0 h1 hb hρ μ₀ hG0 hG ht htk) le_rfl)

/-- **The limit is a minimizer.** -/
theorem flow_limit_minimizer {R : ProbabilityMeasure (Torus d)}
    (hR : ∀ t, 0 ≤ t → dLip (pmOf μ₀ (ρ t)) R ≤ tailR V W G t) : IsMinimizer V W R := by
  set c := (Fstar V W).toReal
  have hFs : Fstar V W = (c : EReal) := Fstar_eq_coe hyp
  set g : ProbabilityMeasure (Torus d) → ℝ≥0∞ := fun ν => (gap V W ν).toENNReal with hgdef
  have hmin : ∀ ν : ProbabilityMeasure (Torus d), g ν = 0 → IsMinimizer V W ν := fun ν hν => by
    have hl : gap V W ν ≤ 0 := EReal.toENNReal_eq_zero_iff.mp hν
    have hu : Fstar V W ≤ freeEnergy V W ν :=
      iInf_le (fun ρ' : ProbabilityMeasure (Torus d) => freeEnergy V W ρ') ν
    unfold IsMinimizer
    unfold gap at hl
    rw [hFs] at hl hu ⊢
    refine le_antisymm ?_ hu
    revert hl hu
    generalize freeEnergy V W ν = F
    intro hl hu
    induction F using EReal.rec with
    | bot => exact bot_le
    | top => simp at hl
    | coe x =>
      rw [← EReal.coe_sub] at hl
      have : x - c ≤ 0 := by exact_mod_cast hl
      exact_mod_cast (by linarith : x ≤ c)
  have hP : ∀ u, 0 ≤ u → (pmOf μ₀ (ρ u) : Measure (Torus d)) = densMeasure (ρ u) :=
    fun u hu => pmOf_coe μ₀ (hρ.1 u hu).1 (hρ.1 u hu).2
  by_cases hrt : rStar V W = ⊤
  · -- `r_* = ∞`: the flow is stationary
    have htail0 : ∀ t, tailR V W G t = 0 := fun t => by simp [tailR, hrt]
    have hconst : ∀ t, 0 ≤ t → pmOf μ₀ (ρ t) = R := fun t ht =>
      eq_of_dLip_eq_zero (le_antisymm ((hR t ht).trans (htail0 t).le) (dLip_nonneg _ _))
    have hρ0 : ρ 0 = ρ₀ := hρ.2.2.1
    have hd0 : densMeasure ρ₀ = (R : Measure (Torus d)) := by
      rw [← hconst 0 le_rfl, hP 0 le_rfl, hρ0]
    have hae : ∀ u, 0 ≤ u → ρ u =ᵐ[haar d] ρ₀ := fun u hu => by
      refine ae_eq_of_densMeasure_eq (integrable_of_integral_eq_one' (hρ.1 u hu).2)
        (integrable_of_integral_eq_one' h1) (hρ.1 u hu).1 (Eventually.of_forall h0) ?_
      rw [← hP u hu, hconst u hu, hd0]
    obtain ⟨-, -, hev⟩ := mf_evolution hd hyp hm h0 h1 hb
    obtain ⟨h48, -, -⟩ := hev ρ hρ
    have he := h48 0 1 le_rfl zero_le_one
    have hI : ∫⁻ u in Icc (0 : ℝ) 1, dissipation V W (ρ u) = dissipation V W ρ₀ := by
      rw [setLIntegral_congr_fun measurableSet_Icc (fun u hu => dissipation_congr_ae (hae u hu.1)),
        setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    rw [hI, hρ0, ← hP 1 zero_le_one, hconst 1 zero_le_one, ← hd0] at he
    -- the free energy of `ρ₀` is finite
    have hF0 : freeEnergy V W (densMeasure ρ₀) ≠ ⊤ := by
      intro htop
      have : gap V W (densMeasure ρ₀) = ⊤ := by unfold gap; rw [htop, hFs]; rfl
      rw [this, EReal.toENNReal_top] at hG
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hG)
    have hF0' : freeEnergy V W (densMeasure ρ₀) ≠ ⊥ := by
      have hu : Fstar V W ≤ freeEnergy V W (pmOf μ₀ ρ₀) :=
        iInf_le (fun ρ' : ProbabilityMeasure (Torus d) => freeEnergy V W ρ') _
      rw [pmOf_coe μ₀ (Eventually.of_forall h0) h1, hFs] at hu
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) hu
    have hD : dissipation V W ρ₀ = 0 := by
      set F := freeEnergy V W (densMeasure ρ₀)
      have hx : F = ((F.toReal : ℝ) : EReal) := (EReal.coe_toReal hF0 hF0').symm
      rw [hx] at he
      have h2 : ((-F.toReal : ℝ) : EReal) + (((F.toReal : ℝ) : EReal) +
          ((dissipation V W ρ₀ : ℝ≥0∞) : EReal)) ≤ ((-F.toReal : ℝ) : EReal) + ((F.toReal : ℝ) : EReal) :=
        add_le_add le_rfl he
      rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add] at h2
      have h3 : ((dissipation V W ρ₀ : ℝ≥0∞) : EReal) ≤ ((0 : ℝ≥0∞) : EReal) := by
        simpa using h2
      exact nonpos_iff_eq_zero.mp (EReal.coe_ennreal_le_coe_ennreal_iff.mp h3)
    have hgtop : gap V W (densMeasure ρ₀) ≠ ⊤ := fun htop => by
      rw [htop, EReal.toENNReal_top] at hG
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hG)
    have hpl := rStar_mul_gap_le (V := V) (W := W) (Eventually.of_forall h0) h1 hgtop
    rw [hD, hrt, nonpos_iff_eq_zero] at hpl
    have hg0 : (gap V W (densMeasure ρ₀)).toENNReal = 0 := by
      rcases mul_eq_zero.mp hpl with h | h
      · exact absurd h (by simp)
      · exact h
    refine hmin R ?_
    show (gap V W (R : Measure (Torus d))).toENNReal = 0
    rw [← hd0]; exact hg0
  · -- `r_* < ∞`: the gap decays
    have hrpos : 0 < (rStar V W).toReal := ENNReal.toReal_pos hr.ne' hrt
    set P : ℕ → ProbabilityMeasure (Torus d) := fun n => pmOf μ₀ (ρ n)
    have hPR : Tendsto P atTop (𝓝 R) := tendsto_of_dLip_le
      ((tendsto_tailR (V := V) (W := W) G).comp tendsto_natCast_atTop_atTop)
      (fun n => hR n (Nat.cast_nonneg n))
    have hgP : ∀ n, g (P n) ≤ ENNReal.ofReal (G * Real.exp (-2 * (rStar V W).toReal * n)) :=
      fun n => by
        show (gap V W (pmOf μ₀ (ρ n) : Measure (Torus d))).toENNReal ≤ _
        rw [hP n (Nat.cast_nonneg n)]
        exact gap_flow_le hd hyp hr hm h0 h1 hb hρ hG0 hG (Nat.cast_nonneg n)
    have hup : Tendsto (fun n : ℕ => ENNReal.ofReal (G * Real.exp (-2 * (rStar V W).toReal * n)))
        atTop (𝓝 0) := by
      have h1' : Tendsto (fun t : ℝ => -2 * (rStar V W).toReal * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      have h2' : Tendsto (fun t : ℝ => G * Real.exp (-2 * (rStar V W).toReal * t)) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_atBot.comp h1').const_mul G
        simpa using this
      have := (ENNReal.continuous_ofReal.tendsto 0).comp (h2'.comp tendsto_natCast_atTop_atTop)
      rw [ENNReal.ofReal_zero] at this
      exact this
    have hg0 : Tendsto (fun n => g (P n)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => bot_le) hgP
    -- lower semicontinuity of `g`
    have hlsc : LowerSemicontinuousAt g R := by
      have hF := (lowerSemicontinuous_freeEnergy hyp (V := V) (W := W)) R
      set k : EReal → ℝ≥0∞ := fun z => (z + ((-c : ℝ) : EReal)).toENNReal
      have hk : ContinuousAt k (freeEnergy V W R) := by
        have hadd : ContinuousAt (fun z : EReal => z + ((-c : ℝ) : EReal)) (freeEnergy V W R) := by
          have := EReal.continuousAt_add (p := (freeEnergy V W R, ((-c : ℝ) : EReal)))
            (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
          exact this.comp (f := fun z : EReal => (z, ((-c : ℝ) : EReal))) (by fun_prop)
        exact EReal.continuous_toENNReal.continuousAt.comp hadd
      have hkm : Monotone k := fun a b hab =>
        EReal.toENNReal_le_toENNReal (add_le_add hab le_rfl)
      have := hk.comp_lowerSemicontinuousAt
        (f := fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ) hF hkm
      have hgk : g = k ∘ fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ := by
        funext ν
        simp only [hgdef, k, Function.comp, gap, hFs, sub_eq_add_neg, EReal.coe_neg]
      rw [hgk]; exact this
    refine hmin R ?_
    by_contra hne
    obtain ⟨y, hy0, hyR⟩ := exists_between (pos_iff_ne_zero.mpr hne)
    have h1e := hPR.eventually (hlsc y hyR)
    have h2e := hg0.eventually (gt_mem_nhds hy0)
    obtain ⟨n, hn1, hn2⟩ := (h1e.and h2e).exists
    exact absurd (hn1.trans hn2) (lt_irrefl _)

end flow

end SharpLSI
