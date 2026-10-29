import SharpSymmetricLSI.Paper.Defective27

/-!
# R03 (Proposition 2.2), part 28: the large-`N` estimate for the regularized laws

Conditional on Lemma 4.2 (`MFCoercive`): for `0 < r < r_*` there are `N₀` and `K` such that for
`N ≥ N₀`, symmetric measurable `f ∈ H¹(P_N)` with a measurable weak gradient `g`, and every `n`,
the regularized law `ν = ψ_n(f)² P_N / Z` satisfies `2r H(ν|P_N) ≤ ∑ᵢ E_ν|sᵢ|² + K`
(`large_N_reg`). This is the proof of Proposition 2.2 in Section 5.4, with `M = ⌈τN⌉`.
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Bookkeeping for `M = ⌈τN⌉`. -/
theorem ceil_tau_facts {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 4) {N : ℕ} (hN : ⌈4 / τ⌉₊ + 4 ≤ N) :
    3 ≤ ⌈τ * N⌉₊ ∧ ⌈τ * N⌉₊ ≤ N ∧ τ ≤ (⌈τ * N⌉₊ : ℝ) / N ∧ (⌈τ * N⌉₊ : ℝ) / N ≤ 2 * τ ∧
      0 < (N : ℝ) := by
  have hN' : (⌈4 / τ⌉₊ : ℝ) + 4 ≤ N := by exact_mod_cast hN
  have h4 : 4 / τ ≤ (⌈4 / τ⌉₊ : ℝ) := Nat.le_ceil _
  have hNpos : (0 : ℝ) < N := by have := Nat.cast_nonneg (α := ℝ) ⌈4 / τ⌉₊; linarith
  have hτN : 4 ≤ τ * N := by
    have : 4 / τ ≤ N := by linarith
    rwa [div_le_iff₀ hτ0, mul_comm] at this
  have hM1 : τ * N ≤ (⌈τ * N⌉₊ : ℝ) := Nat.le_ceil _
  have hM2 : (⌈τ * N⌉₊ : ℝ) < τ * N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN4 : (4 : ℝ) ≤ N := by have := Nat.cast_nonneg (α := ℝ) ⌈4 / τ⌉₊; linarith
  refine ⟨?_, ?_, ?_, ?_, hNpos⟩
  · have : (3 : ℝ) < ⌈τ * N⌉₊ := by linarith
    exact_mod_cast this.le
  · have : (⌈τ * N⌉₊ : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  · rw [le_div_iff₀ hNpos]; linarith
  · rw [div_le_iff₀ hNpos]; nlinarith

section large
variable (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
  (hμ : IsMinimizer V W μ) (hco : MFCoercive V W μ)
include hd hyp hμ hco

/-- **The large-`N` estimate** for the regularized laws. -/
theorem large_N_reg {r : ℝ} (hr0 : 0 < r) (hr : ENNReal.ofReal r < rStar V W) :
    ∃ N₀ : ℕ, ∃ K : ℝ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → ∀ f : Config N d → ℝ, Measurable f →
      MemH1C (gibbs V W N) f → IsSymmetric f →
      ∀ g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ, IsWeakGrad (f ∘ unflat) g →
      (∀ p, Measurable fun y => g y p) → (∀ p, MemLp (fun y => g y p) 2 volume) → ∀ n : ℕ,
      2 * r * (klDiv ((volume : Measure (Config N d)).withDensity
          fun X => ENNReal.ofReal (Qreg V W n f X)) (gibbs V W N)).toReal ≤
        (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
          ∂((volume : Measure (Config N d)).withDensity
            fun X => ENNReal.ofReal (Qreg V W n f X))).toReal + K := by
  have hac := minimizer_ac hyp hμ
  set μm := (μ : Measure (Torus d)) with hμm
  obtain ⟨r₀, hrr₀, hr₀⟩ := exists_r0 hr0 hr
  have hr₀0 : 0 < r₀ := hr0.trans hrr₀
  obtain ⟨A, hA0, hA⟩ := exists_klDiv_le_reference hyp hμ
  obtain ⟨C19, p19, -, h19⟩ := reference_entropy_of hyp hμ hco
  obtain ⟨C20, hC20, h20⟩ := force_under_nu_of hyp hd hμ hco
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp μm
  set B : (Fin 2 → Torus d) → ℝ := fun z => 1 * centeredKernel W μm (z 0) (z 1) / 2 with hBdef
  have hBm : Measurable B := by
    have h := (measurable_centeredKernel hyp μm).comp
      (show Measurable fun z : Fin 2 → Torus d => (z 0, z 1) from
        (measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
    simp only [Function.comp_def, Function.uncurry_apply_pair] at h
    exact (h.const_mul 1).div_const 2
  obtain ⟨C18, h18⟩ := conditional_empirical_aux μm 2 B hBm ⟨|BK|, fun z => by
    simp only [hBdef, one_mul, abs_div, abs_two]
    exact (div_le_self (abs_nonneg _) one_le_two).trans ((hBK _ _).trans (le_abs_self _))⟩
  obtain ⟨C21, h21⟩ := conditional_force_aux hyp hμ
  set C18' := max C18 0
  set C19' := max C19 0
  set C21' := max C21 0
  have hC18' : 0 ≤ C18' := le_max_right _ _
  have hC19' : 0 ≤ C19' := le_max_right _ _
  have hC21' : 0 ≤ C21' := le_max_right _ _
  obtain ⟨τ, ε, hτ0, hτ, hε, hchoice⟩ := exists_tau_eps hr0 hrr₀
    (a := 2 + 4 * A * C20) (b := 8 * r₀ * A) (by positivity) (by positivity)
  set α := 2 * r₀ * (1 - (2 + 4 * A * C20) * τ) with hα
  set β := 1 + ε + 8 * r₀ * A * τ with hβ
  set q := Real.sqrt (C19' / τ) with hq
  set K₁ := 2 * r₀ * (4 * τ * A * C20 + C19' + C18') + (1 + 1 / ε) * C21' with hK₁
  set K₂ := (2 * r₀ * C18' + (1 + 1 / ε) * C21') * q with hK₂
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hβ1 : 1 ≤ β := by
    have h8 : 0 ≤ 8 * r₀ * A * τ := by positivity
    rw [hβ]; linarith
  have hαβ : 2 * r * β < α := by
    rw [hα, hβ]; linarith
  refine ⟨⌈4 / τ⌉₊ + 4, max 0 (K₁ + (α - 2 * r * β) + K₂ ^ 2 / (4 * (α - 2 * r * β))), ?_⟩
  intro N hN0 hN f hfm hf hsym g hw hgm hg2 n
  obtain ⟨hM3, hMN, hτM, hM2τ, hNpos⟩ := ceil_tau_facts hτ0 hτ hN0
  set M := ⌈τ * N⌉₊ with hMdef
  set ℓ := N - M with hℓdef
  have hgi : ∀ p, Integrable (fun y => g y p) volume := fun p => (hg2 p).integrable one_le_two
  haveI := isProbabilityMeasure_Qreg hyp hf hfm n
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)
    with hνdef
  have hνsym := isSymmetricMeasure_Qreg hyp hf hfm hsym n
  have hHg := klDiv_Qreg_gibbs_ne_top hyp hf hfm n
  have hH0 := klDiv_pi_ne_top_of_gibbs hyp hμ hHg
  set Hr := (klDiv ν (gibbs V W N)).toReal with hHr
  set H0r := (klDiv ν (Measure.pi fun _ : Fin N => μm)).toReal with hH0r
  have hHr0 : 0 ≤ Hr := ENNReal.toReal_nonneg
  have hH0r0 : 0 ≤ H0r := ENNReal.toReal_nonneg
  -- the score sums are finite
  have hItop : ∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν ≠ ⊤ := by
    rw [fisher_Qreg_eq hyp hf hfm hw hgm n]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (energy_lt_top hyp hf).ne (energy_regF_le hyp hf n))
  have hIi : ∀ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hItop (Finset.single_le_sum (f := fun i => ∑ k, ∫⁻ X,
      ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν) (fun _ _ => bot_le) (Finset.mem_univ i))
  set Iv : ℕ → ℝ := fun j => if hj : j < N then
    (∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g ⟨j, hj⟩ k X ^ 2) ∂ν).toReal else 0 with hIv
  have hIv0 : ∀ j, 0 ≤ Iv j := fun j => by
    simp only [hIv]; split_ifs <;> simp
  set Ir := (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν).toReal with hIr
  have hIrsum : Ir = ∑ j ∈ Finset.range N, Iv j := by
    rw [hIr, ENNReal.toReal_sum fun i _ => hIi i, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hIv, dif_pos i.2]
  have hIr0 : 0 ≤ Ir := ENNReal.toReal_nonneg
  -- (i) the mean-field inequality on the conditional laws, summed
  set S : ℕ → ℝ := fun j => (hCondT ν μm j).toReal + condProductMean ν 2 B j with hS
  have hstep1 : 2 * r₀ * ∑ j ∈ Finset.range ℓ, S j ≤
      (1 + ε) * ∑ j ∈ Finset.range ℓ, Iv j + (1 + 1 / ε) * ∑ j ∈ Finset.range ℓ, fcTerm W μm ν j := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjN : j < N := by simp at hj; omega
    have := two_r_gap_real_le hyp hμ hN hfm hf hw hgm hg2 hgi n hjN hr₀0.le hr₀ hε (hIi ⟨j, hjN⟩)
    simp only [hS, hIv, dif_pos hjN]
    exact this
  have hIℓ : ∑ j ∈ Finset.range ℓ, Iv j ≤ Ir := by
    rw [hIrsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N M))
      fun j _ _ => hIv0 j
  have hfc := h21 N M τ ν hνsym hH0 hMN hM3 hτ0 hτM
  -- (ii) the entropy increments
  obtain ⟨hmono, hsum, -, -⟩ := summed_dependence_aux μm ν hνsym hH0
  set h : ℕ → ℝ := fun j => (hCondT ν μm j).toReal with hhdef
  have hsumR : ∑ j ∈ Finset.range N, h j = H0r := by
    simp only [hhdef, hH0r]
    rw [← ENNReal.toReal_sum fun j _ => hCondT_ne_top μm ν hH0 j, hsum]
  have hmonoR : ∀ j, j + 1 < N → h j ≤ h (j + 1) := fun j hj =>
    ENNReal.toReal_mono (hCondT_ne_top μm ν hH0 _) (hmono j hj)
  have htail := sum_Ico_le_of_mono (Nat.sub_le N M) hmonoR
  have hNℓ : N - ℓ = M := by omega
  rw [hNℓ] at htail
  have hhead : ∑ j ∈ Finset.range ℓ, h j ≥ H0r - M * h (N - 1) := by
    have := Finset.sum_range_add_sum_Ico h (Nat.sub_le N M)
    linarith
  -- (iii) the last increment and exchangeability
  have hN1 : N - 1 < N := by omega
  set Y : Fin N → ℝ≥0∞ := fun i => ∫⁻ X, ENNReal.ofReal
    (∑ k, (sfun n f g i k X - Gfun W μm i k X) ^ 2) ∂ν with hYdef
  have hYeq : ∀ i, Y i = Y ⟨N - 1, hN1⟩ := fun i =>
    lintegral_sG_eq hyp hac hN hfm hf hsym hw hgm hg2 hgi n i _
  have hlast : hCondT ν μm (N - 1) ≤ ENNReal.ofReal A * Y ⟨N - 1, hN1⟩ := by
    unfold hCondT; rw [dif_pos hN1]
    exact hCond_le_sG hyp hμ hN hfm hf hw hgm hg2 hgi n hN1 hA
  -- (iv) `∑ᵢ Yᵢ ≤ 2 I + 2 E|∇U|²`
  have hsm : ∀ i k, Measurable (sfun n f g i k) := fun i k =>
    measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n i k
  have hGm : ∀ i k, Measurable (Gfun W μm i k) := fun i k =>
    measurable_Gfun hyp hac hN i k
  have hGG : ∀ᵐ X ∂ν, ∑ i, ∑ k, Gfun W μm i k X ^ 2 = gradSqC (Ucentered W μ N) X := by
    have h1 := gradSqC_Ucentered_ae hyp hμ hN
    have h2 : ∀ᵐ X ∂(volume : Measure (Config N d)), gradSqC (Ucentered W μ N) X =
        sqNorm (gsG W μm N (flat X)) := (volume_ac_pi_minimizer hyp hμ N).ae_le h1
    filter_upwards [(withDensity_absolutelyContinuous _ _ : ν ≪ volume).ae_le h2] with X hX
    rw [hX]; unfold sqNorm; rw [Fintype.sum_prod_type]; rfl
  have hYsum : ∑ i, Y i ≤ 2 * (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν) +
      2 * ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν := by
    have hYm : ∀ i, Measurable fun X => ENNReal.ofReal (∑ k, (sfun n f g i k X - Gfun W μm i k X) ^ 2) :=
      fun i => (Finset.measurable_sum _ fun k _ =>
        ((hsm i k).sub (hGm i k)).pow_const 2).ennreal_ofReal
    have hsm2 : ∀ i k, Measurable fun X => ENNReal.ofReal (sfun n f g i k X ^ 2) := fun i k =>
      ((hsm i k).pow_const 2).ennreal_ofReal
    simp only [hYdef]
    rw [← lintegral_finset_sum _ fun i _ => hYm i]
    have e2 : ∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν =
        ∫⁻ X, ∑ i, ∑ k, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν := by
      rw [lintegral_finset_sum _ fun i _ => Finset.measurable_sum _ fun k _ => hsm2 i k]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_finset_sum _ fun k _ => hsm2 i k]
    rw [e2, ← lintegral_const_mul _ (Finset.measurable_sum _ fun i _ =>
        Finset.measurable_sum _ fun k _ => hsm2 i k),
      ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
      ← lintegral_add_left ((Finset.measurable_sum _ fun i _ =>
        Finset.measurable_sum _ fun k _ => hsm2 i k).const_mul _)]
    refine lintegral_mono_ae ?_
    filter_upwards [hGG] with X hX
    rw [← hX]
    have hs0 : ∀ i k, 0 ≤ sfun n f g i k X ^ 2 := fun i k => sq_nonneg _
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _]
    have e3 : (2 : ℝ≥0∞) * ∑ i, ∑ k, ENNReal.ofReal (sfun n f g i k X ^ 2) =
        ENNReal.ofReal (2 * ∑ i, ∑ k, sfun n f g i k X ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun k _ => hs0 i k]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ => hs0 i k]
    rw [e3, (by norm_num : (2 : ℝ≥0∞) = ENNReal.ofReal 2), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ i, ∑ k, (sfun n f g i k X - Gfun W μm i k X) ^ 2
        ≤ ∑ i, ∑ k, (2 * sfun n f g i k X ^ 2 + 2 * Gfun W μm i k X ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
            nlinarith [sq_nonneg (sfun n f g i k X + Gfun W μm i k X)]
      _ = 2 * ∑ i, ∑ k, sfun n f g i k X ^ 2 + 2 * ∑ i, ∑ k, Gfun W μm i k X ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  -- (v) the empirical interaction
  have hemp := h18 N M τ ν hνsym hH0 hMN (by omega) hτ0 hτM
  have hempU : ∫ X, empiricalTensor 2 B X ∂ν = (∫ X, Ucentered W μ N X ∂ν) / N := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    have := mul_empiricalTensor_two (fun x y => 1 * centeredKernel W μm x y) X
    simp only [one_mul] at this ⊢
    simp only [hBdef, one_mul]
    rw [eq_div_iff hNpos.ne', mul_comm, this]
    rfl
  -- (vi) the entropy identities and the bounds of Lemmas 5.2 and 5.3
  obtain ⟨-, hid⟩ := centered_entropy_identities_aux hyp hμ hN
  obtain ⟨hHid, -⟩ := hid ν inferInstance hH0
  obtain ⟨h19a, h19b, -⟩ := h19 N hN
  have hH0le : H0r ≤ C19' * (Hr + 1) := by
    have h := h19a ν inferInstance hνsym
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hHg, ENNReal.one_ne_top⟩)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hHg ENNReal.one_ne_top, ENNReal.toReal_ofReal',
      ENNReal.toReal_one] at h'
    calc H0r ≤ max C19 0 * (Hr + 1) := h'
      _ = C19' * (Hr + 1) := rfl
  have hlogK : Real.log (centeredPartition W μ N) ≤ C19' :=
    ((le_abs_self _).trans h19b).trans (le_max_left _ _)
  have hGGr : (∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν).toReal ≤ C20 * (Hr + 1) := by
    have h := h20 N hN ν inferInstance hνsym hHg
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hHg, ENNReal.one_ne_top⟩)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hHg ENNReal.one_ne_top, ENNReal.toReal_ofReal hC20.le,
      ENNReal.toReal_one] at h'
  -- assembling the real inequalities
  set GG := ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν with hGGdef
  have hGGtop : GG ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨hHg, ENNReal.one_ne_top⟩)) (h20 N hN ν inferInstance hνsym hHg)
  have hRHStop : 2 * (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν) + 2 * GG ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hItop,
      ENNReal.mul_ne_top (by norm_num) hGGtop⟩
  have hYtop : Y ⟨N - 1, hN1⟩ ≠ ⊤ := ne_top_of_le_ne_top hRHStop
    ((Finset.single_le_sum (f := Y) (fun _ _ => bot_le) (Finset.mem_univ _)).trans hYsum)
  set Ylast := (Y ⟨N - 1, hN1⟩).toReal with hYlast
  set GGr := GG.toReal with hGGr'
  have hNY : (N : ℝ) * Ylast ≤ 2 * Ir + 2 * GGr := by
    have hsumY : ∑ i, Y i = (N : ℝ≥0∞) * Y ⟨N - 1, hN1⟩ := by
      rw [Finset.sum_congr rfl fun i _ => hYeq i, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have h := ENNReal.toReal_mono hRHStop hYsum
    rw [hsumY, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) hItop) (ENNReal.mul_ne_top (by norm_num) hGGtop),
      ENNReal.toReal_mul, ENNReal.toReal_mul] at h
    simpa using h
  have hhl : h (N - 1) ≤ A * Ylast := by
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYtop) hlast
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0.le] at h'
  have hYl0 : 0 ≤ Ylast := ENNReal.toReal_nonneg
  have hGGr0 : 0 ≤ GGr := ENNReal.toReal_nonneg
  set sH := Real.sqrt (Hr + 1) with hsH
  set w := Real.sqrt (H0r / τ) with hw'
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hsH0 : 0 ≤ sH := Real.sqrt_nonneg _
  have hwq : w ≤ q * sH := by
    rw [hq, hsH, ← Real.sqrt_mul (div_nonneg hC19' hτ0.le)]
    refine Real.sqrt_le_sqrt ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hH0le hτ0.le
  have hF : ∑ j ∈ Finset.range ℓ, fcTerm W μm ν j ≤ C21' * (1 + q * sH) :=
    hfc.trans (mul_le_mul (le_max_left _ _) (by linarith) (by positivity) hC21')
  set EU := ∫ X, Ucentered W μ N X ∂ν with hEU
  set cps := ∑ j ∈ Finset.range ℓ, condProductMean ν 2 B j with hcps
  set m := (M : ℝ) / N with hm
  have hℓN : (ℓ : ℝ) = N - M := Nat.cast_sub hMN
  have hcpsle : (1 - m) * EU - C18' * (1 + q * sH) ≤ cps := by
    have h1 := (abs_le.mp hemp).1
    rw [hempU] at h1
    have h2 : (ℓ : ℝ) * (EU / N) = (1 - m) * EU := by
      rw [hℓN, hm]
      first | (field_simp; done) | (field_simp; ring)
    have h3 : C18 * (1 + Real.sqrt ((klDiv ν (Measure.pi fun _ : Fin N => μm)).toReal / τ)) ≤
        C18' * (1 + q * sH) :=
      mul_le_mul (le_max_left _ _) (by linarith) (by positivity) hC18'
    linarith
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hMhl : (M : ℝ) * h (N - 1) ≤ m * A * (2 * Ir + 2 * GGr) := by
    calc (M : ℝ) * h (N - 1) ≤ M * (A * Ylast) :=
          mul_le_mul_of_nonneg_left hhl (Nat.cast_nonneg _)
      _ = m * A * (N * Ylast) := by
          rw [hm]
          first | (field_simp; done) | (field_simp; ring)
      _ ≤ m * A * (2 * Ir + 2 * GGr) :=
          mul_le_mul_of_nonneg_left hNY (mul_nonneg hm0 hA0.le)
  have hEU' : EU = Hr - H0r - Real.log (centeredPartition W μ N) := by
    simp only [hEU, hHr, hH0r]; linarith
  have hSsum : ∑ j ∈ Finset.range ℓ, S j = ∑ j ∈ Finset.range ℓ, h j + cps := by
    simp only [hS, hhdef, hcps]; rw [Finset.sum_add_distrib]
  clear_value S h cps EU m sH w GGr Ylast GG Ir Iv Hr H0r
  have hP1 : m * A * (2 * Ir + 2 * GGr) ≤ 2 * τ * A * (2 * Ir + 2 * (C20 * (Hr + 1))) := by
    have : 2 * Ir + 2 * GGr ≤ 2 * Ir + 2 * (C20 * (Hr + 1)) := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hM2τ hA0.le) this (by linarith)
      (by have := hτ0.le; positivity)
  have hQ1 : (1 - 2 * τ) * Hr ≤ (1 - m) * Hr := mul_le_mul_of_nonneg_right (by linarith) hHr0
  have hQ2 : (1 - m) * Real.log (centeredPartition W μ N) ≤ C19' := by
    have h1m : 0 ≤ 1 - m := by linarith
    calc (1 - m) * Real.log (centeredPartition W μ N) ≤ (1 - m) * C19' :=
          mul_le_mul_of_nonneg_left hlogK h1m
      _ ≤ C19' := by have := mul_nonneg hm0 hC19'; linarith
  have hQ3 : 0 ≤ m * H0r := mul_nonneg hm0 hH0r0
  have hEUe : (1 - m) * EU = (1 - m) * Hr - (1 - m) * H0r -
      (1 - m) * Real.log (centeredPartition W μ N) := by
    rw [hEU']; ring
  have hlow : (1 - 2 * τ) * Hr - 2 * τ * A * (2 * Ir + 2 * (C20 * (Hr + 1))) - C19' -
      C18' * (1 + q * sH) ≤ ∑ j ∈ Finset.range ℓ, S j := by
    rw [hSsum]; linarith only [hhead, hMhl, hP1, hcpsle, hEUe, hQ1, hQ2, hQ3]
  have hlow2 := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * r₀)
  have hup : 2 * r₀ * ∑ j ∈ Finset.range ℓ, S j ≤ (1 + ε) * Ir + (1 + 1 / ε) * (C21' * (1 + q * sH)) := by
    have h1 : (1 + ε) * ∑ j ∈ Finset.range ℓ, Iv j ≤ (1 + ε) * Ir :=
      mul_le_mul_of_nonneg_left hIℓ (by positivity)
    have h2 : (1 + 1 / ε) * ∑ j ∈ Finset.range ℓ, fcTerm W μm ν j ≤ (1 + 1 / ε) * (C21' * (1 + q * sH)) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    linarith only [hstep1, h1, h2]
  have hfinal : α * Hr ≤ β * Ir + K₁ + K₂ * Real.sqrt (Hr + 1) := by
    rw [← hsH, hα, hβ, hK₁, hK₂]
    linarith only [hlow2, hup]
  exact absorb_sqrt hr0 hβ1 hαβ hK₂0 hHr0 hfinal

end large

end SharpLSI
