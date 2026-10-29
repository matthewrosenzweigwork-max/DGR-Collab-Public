import FullLabeledLSI.Paper.Sec5LNA
import FullLabeledLSI.Paper.Sec5LND
import FullLabeledLSI.Paper.Sec5LNE
import FullLabeledLSI.Paper.Sec5LNF
import FullLabeledLSI.Paper.Sec5LNG

/-!
# Large-N assembly H: the large-N theorem without symmetry
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 8. L6: the large-`N` theorem without symmetry -/

/-- **L6.  The large-`N` estimate for the regularized laws, without symmetry**
(`large_N_reg` of Defective28 minus `IsSymmetric f` and `hco`; `hr : 0 < rStar` replaces `hco`, `rMs`
replaces `rStar`).  See the module header for the order of choices.  Proof (for `N ≥ N₀`, `ℓ = N - M`):
 1. `obtain ⟨c, C, hS⟩ := scoreData_Qreg …` (once per `(N, f, g, n)`), `ν := Qreg·volume` probability
    (`isProbabilityMeasure_Qreg`), `H = (klDiv ν P_N).toReal` finite (`klDiv_Qreg_gibbs_ne_top`),
    `H0 ≤ C19(H+1)` (`reference_all_aux` ⇒ `H0 ≠ ⊤`), `I = fisherS ν (sfun n f g)` finite
    (`fisher_Qreg_eq`; `fisher_toReal_eq`).
 2. `Σ_{j<ℓ}` of `level_bound` (with `ℓ ≤ N` so `ℓ/N·I ≤ I`) ⇒ `hmain`; `abstract_force_sum hB τ hτ`
    ⇒ `hSf` (with `√H0 ≤ …`); `chain_lower` ⇒ `hSh` with `P = M h_{N-1}`; `hRev_toReal_le` (j = N-1) and
    `sum_sG_le` ⇒ `hP` (`P ≤ (M/N) A (2I + 2GG)`); `products_J` ⇒ `hScp`; `centered_entropy_identities_aux`
    ⇒ `hEU`; `|log K_N| ≤ CK` from `SharpLSI.reference_entropy`; `reference_all_aux` ⇒ `hH0le`, `hGGle`.
 3. `large_N_algebra` gives `2 r H ≤ I + algK …`.
Estimate: ~180 lines of glue.  The statement is that of `Defective28.large_N_reg`. -/
theorem large_N_reg_all (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {r : ℝ} (hr0 : 0 < r) (hrr : ENNReal.ofReal r < rMs V W) :
    ∃ N₀ : ℕ, ∃ K : ℝ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → ∀ f : Config N d → ℝ, Measurable f →
      MemH1C (gibbs V W N) f →
      ∀ g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ, IsWeakGrad (f ∘ unflat) g →
      (∀ p, Measurable fun y => g y p) → (∀ p, MemLp (fun y => g y p) 2 volume) → ∀ n : ℕ,
      2 * r * (klDiv ((volume : Measure (Config N d)).withDensity
          fun X => ENNReal.ofReal (Qreg V W n f X)) (gibbs V W N)).toReal ≤
        (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
          ∂((volume : Measure (Config N d)).withDensity
            fun X => ENNReal.ofReal (Qreg V W n f X))).toReal + K := by
  classical
  obtain ⟨r₀, hrr₀, hr₀⟩ := exists_r0 hr0 hrr
  have hr₀0 : 0 < r₀ := hr0.trans hrr₀
  obtain ⟨A, hA0, hA⟩ := exists_refLSI hyp hμ
  obtain ⟨C, hC⟩ := reference_all_aux hd hyp hr μ hμ
  obtain ⟨CK0, p, -, hCK⟩ := SharpLSI.reference_entropy hd hyp hr hμ
  obtain ⟨bF, bΔ, Bb, hB, hbF, hG⟩ := exists_force_rep hd hyp μ hμ
  set C' : ℝ := max C 0 with hC'def
  set CK : ℝ := max CK0 0 with hCKdef
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCK0 : 0 ≤ CK := le_max_right _ _
  obtain ⟨τ, ε, hτ0, hτ, hε, hchoice⟩ := exists_tau_eps hr0 hrr₀
    (a := 2 + 4 * A * C') (b := 8 * r₀ * A) (by positivity) (by positivity)
  obtain ⟨C18, h18⟩ := products_J hyp (μ : Measure (Torus d)) τ hτ0
  obtain ⟨C21, h21⟩ := abstract_force_sum hB τ hτ0
  set C18' : ℝ := max C18 0 with hC18'def
  set C21' : ℝ := max C21 0 with hC21'def
  have hC18' : 0 ≤ C18' := le_max_right _ _
  have hC21' : 0 ≤ C21' := le_max_right _ _
  refine ⟨⌈4 / τ⌉₊ + 4, algK r r₀ τ ε A C18' C' C' C21' CK, ?_⟩
  intro N hN0 hN f hfm hf g hw hgm hg2 n
  obtain ⟨hM3, hMN, hτM, hM2τ, hNpos⟩ := ceil_tau_facts hτ0 hτ hN0
  generalize ⌈τ * (N : ℝ)⌉₊ = M at hM3 hMN hτM hM2τ
  obtain ⟨c, Cd, hS⟩ := scoreData_Qreg hd hyp hμ hB hbF hG hN hfm hf hw hgm hg2 n
  have := isProbabilityMeasure_Qreg hyp hf hfm n
  have hHg := klDiv_Qreg_gibbs_ne_top hyp hf hfm n
  have hH0 := klDiv_pi_ne_top_of_gibbs hyp hμ hHg
  rw [fisher_toReal_eq hS.sL2]
  set ν := (volume : Measure (Config N d)).withDensity
    fun X => ENNReal.ofReal (Qreg V W n f X) with hνdef
  set μm : Measure (Torus d) := (μ : Measure (Torus d)) with hμm
  set H : ℝ := (klDiv ν (gibbs V W N)).toReal with hHdef
  set H0 : ℝ := (klDiv ν (Measure.pi fun _ : Fin N => μm)).toReal with hH0def
  set I : ℝ := fisherS ν (sfun n f g) with hIdef
  have hH0nn : 0 ≤ H0 := ENNReal.toReal_nonneg
  have hHnn : 0 ≤ H := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ I := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
    integral_nonneg fun X => sq_nonneg _
  obtain ⟨h19a, h19b, -⟩ := hC N hN ν inferInstance hHg
  have hfin1 : ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hHg, ENNReal.one_ne_top⟩)
  have hH0le : H0 ≤ C' * (H + 1) := by
    have h' := ENNReal.toReal_mono hfin1 h19a
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hHg ENNReal.one_ne_top,
      ENNReal.toReal_ofReal', ENNReal.toReal_one] at h'
    exact h'
  have hGGtop : ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μm N) X) ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top hfin1 h19b
  set GG : ℝ := (∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μm N) X) ∂ν).toReal with hGGdef
  have hGG0 : 0 ≤ GG := ENNReal.toReal_nonneg
  have hGGle : GG ≤ C' * (H + 1) := by
    have h' := ENNReal.toReal_mono hfin1 h19b
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hHg ENNReal.one_ne_top,
      ENNReal.toReal_ofReal', ENNReal.toReal_one] at h'
    exact h'
  -- the summed level bounds
  have hℓN : ((N - M : ℕ) : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hNpos]; exact_mod_cast Nat.sub_le N M
  have hmain : 2 * r₀ * (∑ j ∈ Finset.range (N - M), (hRev ν μm j).toReal +
      ∑ j ∈ Finset.range (N - M), condMeanS ν 2 (Bk W μm) j) ≤
      (1 + ε) * I + (1 + 1 / ε) * ∑ j ∈ Finset.range (N - M), forceDelta bF bΔ ν j := by
    have hlev : ∀ j ∈ Finset.range (N - M),
        2 * r₀ * ((hRev ν μm j).toReal + condMeanS ν 2 (Bk W μm) j) ≤
          (1 + ε) * ((N : ℝ)⁻¹ * I) + (1 + 1 / ε) * forceDelta bF bΔ ν j := fun j hj =>
      level_bound hyp hμ hS hr₀0.le hr₀ hε (by simp at hj; omega)
    have h1 := Finset.sum_le_sum hlev
    have e1 : ∑ j ∈ Finset.range (N - M),
        2 * r₀ * ((hRev ν μm j).toReal + condMeanS ν 2 (Bk W μm) j) =
        2 * r₀ * (∑ j ∈ Finset.range (N - M), (hRev ν μm j).toReal +
          ∑ j ∈ Finset.range (N - M), condMeanS ν 2 (Bk W μm) j) := by
      rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
    have e2 : ∑ j ∈ Finset.range (N - M),
        ((1 + ε) * ((N : ℝ)⁻¹ * I) + (1 + 1 / ε) * forceDelta bF bΔ ν j) =
        ((N - M : ℕ) : ℝ) * ((1 + ε) * ((N : ℝ)⁻¹ * I)) +
          (1 + 1 / ε) * ∑ j ∈ Finset.range (N - M), forceDelta bF bΔ ν j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.mul_sum]
    have e3 : ((N - M : ℕ) : ℝ) * ((1 + ε) * ((N : ℝ)⁻¹ * I)) ≤ (1 + ε) * I := by
      have : ((N - M : ℕ) : ℝ) * ((1 + ε) * ((N : ℝ)⁻¹ * I)) =
          (((N - M : ℕ) : ℝ) * (N : ℝ)⁻¹) * ((1 + ε) * I) := by ring
      rw [this]
      exact mul_le_of_le_one_left (by positivity) hℓN
    rw [e1, e2] at h1
    linarith
  have hSf : ∑ j ∈ Finset.range (N - M), forceDelta bF bΔ ν j ≤ C21' * (1 + Real.sqrt H0) :=
    (h21 N M hM3 hMN hτM μm ν hH0).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hSh : H0 - (M : ℝ) * (hRev ν μm (N - 1)).toReal ≤
      ∑ j ∈ Finset.range (N - M), (hRev ν μm j).toReal :=
    chain_lower ν μm hH0 hMN
  have hP : (M : ℝ) * (hRev ν μm (N - 1)).toReal ≤ ((M : ℝ) / N) * A * (2 * I + 2 * GG) := by
    have h1 := hRev_toReal_le hyp hμ hS hA0 hA (j := N - 1) (by omega)
    have h2 : ∑ i, ∫ X, ∑ k : Fin d, (sfun n f g i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν ≤
        2 * I + 2 * GG := sum_sG_le hyp hμ hS hGGtop
    have hNi : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    calc (M : ℝ) * (hRev ν μm (N - 1)).toReal
        ≤ M * (A * ((N : ℝ)⁻¹ * ∑ i, ∫ X, ∑ k : Fin d,
            (sfun n f g i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ M * (A * ((N : ℝ)⁻¹ * (2 * I + 2 * GG))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h2 hNi) hA0.le) (Nat.cast_nonneg _)
      _ = ((M : ℝ) / N) * A * (2 * I + 2 * GG) := by
          rw [div_eq_mul_inv]; ring
  have hEUid : ∫ X, Ucentered W μm N X ∂ν = H - H0 - Real.log (centeredPartition W μm N) := by
    obtain ⟨-, hid⟩ := centered_entropy_identities_aux hyp hμ hN
    obtain ⟨hHid, -⟩ := hid ν inferInstance hH0
    linarith
  have hScp : (1 - (M : ℝ) / N) * ∫ X, Ucentered W μm N X ∂ν - C18' * (1 + Real.sqrt H0) ≤
      ∑ j ∈ Finset.range (N - M), condMeanS ν 2 (Bk W μm) j := by
    have h := h18 N M (by omega) hMN hτM ν hH0
    have h1 := (abs_le.mp h).1
    have e : ((N - M : ℕ) : ℝ) / N = 1 - (M : ℝ) / N := by
      rw [Nat.cast_sub hMN, sub_div, div_self hNpos.ne']
    have h3 : C18 * (1 + Real.sqrt H0) ≤ C18' * (1 + Real.sqrt H0) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [e] at h1
    linarith
  have hL : Real.log (centeredPartition W μm N) ≤ CK :=
    ((le_abs_self _).trans (hCK N hN).2.1).trans (le_max_left _ _)
  have hm0 : 0 ≤ (M : ℝ) / N := by positivity
  exact large_N_algebra hr0 hrr₀ hτ0 hτ hε hA0.le hC18' hC'0 hC'0 hC21' hCK0 hchoice hHnn hH0nn
    hI0 hGG0 hm0 hM2τ hmain hSf hSh hP hScp hEUid hL hH0le hGGle


end SharpLSI.FL
