import FullLabeledLSI.Paper.Sec3DiluteD

/-!
# Proposition 3.3 (≤): the dilute two-species families

For `f ∈ H¹(μ)` bounded, `θ₁ = ε`, `ρ₁ = μ f²/∫f²dμ`, `θ₂ = 1 - ε`, `ρ₂ = (μ - ερ₁)/(1-ε)`:
the family has average `μ` and quotient tending to `2 ∫|∇f|²dμ/Ent_μ(f²)` as `ε → 0`.

`inf_le_rLS_of_q`: for a reference density `q` (bounded above and below, `√q ∈ H¹`) with
`D(q) = 0`, `G(q) = 0`, the infimum over admissible families with average `q` is at most
`r_LS(q)`. The proof truncates `f` to `min(|f|, n)` (Fatou for the entropy, parts C and D) and
applies the dilute family of part C.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem inf_le_rLS_of_q (hyp : Hyp V W KV KW) {q : Torus d → ℝ} {c C : ℝ}
    (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C) (hqm : Measurable q)
    (hq1 : ∫ x, q x ∂haar d = 1) (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x)))
    (hD0 : dissipation V W q = 0) (hG0 : gap V W (densMeasure q) = 0) :
    (⨅ F ∈ {F : Family d | MsAdmissible V W F ∧ densMeasure F.bar = densMeasure q},
      msDiss V W F / (2 * (msGap V W F).toENNReal)) ≤ rLS (densMeasure q) := by
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hbd x).1
  haveI hP : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  have hac : densMeasure q ≪ haar d := withDensity_absolutelyContinuous _ _
  unfold rLS
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hfH, hent⟩ := hf
  have hfH1 : MemH1 (haar d) f := memH1_haar_of_dens hc (fun x => (hbd x).1) hfH
  have hEne : ent (densMeasure q) (fun x => f x ^ 2) ≠ ⊤ :=
    ent_sq_ne_top hc hbd hq1 hqm hfH
  have hDlt := dirichlet_lt_top hfH
  set Er : ℝ := (ent (densMeasure q) (fun x => f x ^ 2)).toReal with hErdef
  have hEr : ent (densMeasure q) (fun x => f x ^ 2) = ENNReal.ofReal Er :=
    (ENNReal.ofReal_toReal hEne).symm
  set Dhat : ℝ := (dirichlet (densMeasure q) f).toReal with hDdef
  have hDe : dirichlet (densMeasure q) f = ENNReal.ofReal Dhat :=
    (ENNReal.ofReal_toReal hDlt.ne).symm
  have hEr0 : 0 < Er := by
    rw [hEr] at hent; simpa using hent
  have hDhat0 : 0 ≤ Dhat := ENNReal.toReal_nonneg
  have hR : 2 * dirichlet (densMeasure q) f / ent (densMeasure q) (fun x => f x ^ 2) =
      ENNReal.ofReal (2 * Dhat / Er) := by
    rw [hDe, hEr, ENNReal.ofReal_div_of_pos hEr0, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [hR]
  set t : ℝ := 2 * Dhat / Er with ht
  have ht0 : 0 ≤ t := by positivity
  refine ENNReal.le_of_forall_pos_le_add fun η' hη' _ => ?_
  set η : ℝ := (η' : ℝ) with hηdef
  have hη : 0 < η := by exact_mod_cast hη'
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add ht0 hη.le]
  -- choose the truncation level
  set κ : ℝ := η / (2 * (t + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hlt : ENNReal.ofReal (Er / (1 + κ)) < ent (densMeasure q) (fun x => f x ^ 2) := by
    rw [hEr, ENNReal.ofReal_lt_ofReal_iff hEr0]
    exact div_lt_self hEr0 (by linarith)
  have hev := Filter.eventually_lt_of_lt_liminf
    (lt_of_lt_of_le hlt (ent_le_liminf_trunc (P := densMeasure q) hfH.2.1))
  obtain ⟨n, hn1, hn⟩ := ((eventually_ge_atTop 1).and hev).exists
  set M : ℝ := (n : ℝ) with hMdef
  have hM1 : 1 ≤ M := by simp only [hMdef]; exact_mod_cast hn1
  have hM0 : 0 < M := by linarith
  obtain ⟨G, hgG, hGL, hGle⟩ := exists_trunc_grad hfH1 M
  set g : Torus d → ℝ := fun x => min |f x| M with hgdef
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min (abs_nonneg _) hM0.le
  have hgM : ∀ x, g x ≤ M := fun x => min_le_right _ _
  have hgsq : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => pow_le_pow_left₀ (hg0 x) (hgM x) 2
  -- `g ∈ H¹(q)`
  have hgmeas : AEStronglyMeasurable g (densMeasure q) := hgG.aestronglyMeasurable_fun.mono_ac hac
  have hgH : MemH1 (densMeasure q) g := by
    refine ⟨⟨G, hgG⟩, MemLp.of_bound hgmeas M (Eventually.of_forall fun x => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgM x
    · refine hfH.2.2.of_le (Real.continuous_sqrt.comp_aestronglyMeasurable
        ((isWeakGrad_weakGrad ⟨G, hgG⟩).aestronglyMeasurable_sqNorm.mono_ac hac)) ?_
      filter_upwards [hac.ae_le (weakGrad_ae_eq hgG)] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _), hx]
      exact Real.sqrt_le_sqrt (hGle x)
  have hEnne : ent (densMeasure q) (fun x => g x ^ 2) ≠ ⊤ := ent_sq_ne_top hc hbd hq1 hqm hgH
  set Ern : ℝ := (ent (densMeasure q) (fun x => g x ^ 2)).toReal with hErndef
  have hErn : ent (densMeasure q) (fun x => g x ^ 2) = ENNReal.ofReal Ern :=
    (ENNReal.ofReal_toReal hEnne).symm
  have hn' : ENNReal.ofReal (Er / (1 + κ)) < ENNReal.ofReal Ern := by
    rw [← hErn]; exact hn
  rw [ENNReal.ofReal_lt_ofReal_iff'] at hn'
  obtain ⟨hn2, hErn0⟩ := hn'
  -- the normalization
  set Z : ℝ := ∫ x, q x * g x ^ 2 ∂haar d with hZdef
  have hgint : Integrable (fun x => g x ^ 2) (densMeasure q) :=
    Integrable.of_bound (C := M ^ 2) (hgmeas.pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hgsq x)
  have hZ0 : 0 ≤ Z := integral_nonneg fun x => mul_nonneg (hq0 x).le (sq_nonneg _)
  have hZ : 0 < Z := by
    rcases hZ0.eq_or_lt with h | h
    · exfalso
      have h0 : ent (densMeasure q) (fun x => g x ^ 2) = 0 := by
        unfold ent
        rw [if_pos hgint, integral_densMeasure' (fun x => (hq0 x).le) hq1, ← hZdef, ← h]
        simp
      rw [h0] at hErn
      exact (not_le.2 hErn0) (by simpa using hErn.symm)
    · exact h
  have hZa : 1 / Z * Z = 1 := by field_simp
  -- the Dirichlet bound
  have hD : ∫⁻ x, ENNReal.ofReal (q x * sqNorm (G x)) ∂haar d ≤ ENNReal.ofReal Dhat := by
    rw [← hDe, dirichlet_densMeasure_eq hqm (fun x => (hq0 x).le) hfH.1]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hGle x) (hq0 x).le)
  -- the dilute parameter
  set a : ℝ := 1 / Z with hadef
  have ha : 0 < a := by positivity
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 / 2 ∧ ε * a * M ^ 2 ≤ 1 / 2 ∧
      16 * ε * a * M ^ 2 * Dhat / Ern < η / 2 := by
    have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / 2 :=
      eventually_nhdsWithin_of_eventually_nhds
        ((continuous_id.tendsto (0 : ℝ)).eventually_lt_const (by norm_num))
    have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * a * M ^ 2 < 1 / 2 :=
      eventually_nhdsWithin_of_eventually_nhds
        (((by fun_prop : Continuous fun ε : ℝ => ε * a * M ^ 2).tendsto (0 : ℝ)).eventually_lt_const
          (by norm_num))
    have e4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 16 * ε * a * M ^ 2 * Dhat / Ern < η / 2 :=
      eventually_nhdsWithin_of_eventually_nhds
        (((by fun_prop : Continuous fun ε : ℝ => 16 * ε * a * M ^ 2 * Dhat / Ern).tendsto
          (0 : ℝ)).eventually_lt_const (by simp; positivity))
    filter_upwards [e1, e2, e3, e4] with ε h1 h2 h3 h4
    exact ⟨h1, h2.le, h3.le, h4⟩
  obtain ⟨ε, hε0, hε1, hεM, hε4⟩ := hev2.exists
  obtain ⟨F, hadm, hbar, hquot⟩ := dilute_bounded hyp hc hbd hqm hq1 hqH hD0 hG0 hgG hg0 hgM hGL
    ha (by rw [hadef]; exact hZa) hErn hErn0 hDhat0 hD hε0 hε1 hεM
  refine (iInf₂_le F ⟨hadm, hbar⟩).trans (hquot.trans (ENNReal.ofReal_le_ofReal ?_))
  -- real arithmetic
  have h1 : 2 * Dhat / Ern ≤ 2 * Dhat / (Er / (1 + κ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hn2.le
  have h2 : 2 * Dhat / (Er / (1 + κ)) = (1 + κ) * t := by
    rw [ht]; field_simp
  have h3 : κ * t ≤ η / 2 := by
    rw [hκ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hη.le ht0]
  nlinarith

theorem equilibrium_inf_le_rLS (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    (⨅ F ∈ {F : Family d | MsAdmissible V W F ∧ densMeasure F.bar = (μ : Measure (Torus d))},
      msDiss V W F / (2 * (msGap V W F).toENNReal)) ≤ rLS (μ : Measure (Torus d)) := by
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  obtain ⟨hqm, -, hq1⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  obtain ⟨-, hqH⟩ := memH1_sqrt_of_lipschitz hc hb hL
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    minimizer_eq_elDensity hyp hμ
  have h := inf_le_rLS_of_q hyp hc hb hqm hq1 hqH (dissipation_elDens_eq_zero hyp hμ)
    (by rw [← hμq]; exact gap_minimizer_eq_zero hyp hμ)
  rw [hμq]
  exact h

end SharpLSI.FL
