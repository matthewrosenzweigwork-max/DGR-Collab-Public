import SharpSymmetricLSI.Paper.Defective28

/-!
# R03 (Proposition 2.2), part 29: the defective inequality

`prop_defective_of`: Proposition 2.2, conditional on Lemma 4.2 (`MFCoercive` at every minimizer).
Large `N`: `large_N_reg` for the regularized laws, converted with
`H(ν|P_N) = Ent(ψ_n(f)²)/Z` and `∑ᵢ E_ν|sᵢ|² = (4/Z) ℰ(ψ_n(f))`, then `n → ∞` (`defective_of_regF`).
Small `N`: `fixedN_defective` with `η = 2/r`.
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section final
variable (hyp : Hyp V W KV KW)
include hyp

/-- One regularization level: from `2r H ≤ I + K` to the defective inequality for `ψ_n(f)`. -/
theorem regF_defective_of_bound {N : ℕ} {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f)
    (hfm : Measurable f) {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hw : IsWeakGrad (f ∘ unflat) g) (hgm : ∀ p, Measurable fun y => g y p) (n : ℕ)
    {r K : ℝ} (hr0 : 0 < r) (hK0 : 0 ≤ K)
    (hbound : 2 * r * (klDiv ((volume : Measure (Config N d)).withDensity
          fun X => ENNReal.ofReal (Qreg V W n f X)) (gibbs V W N)).toReal ≤
        (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
          ∂((volume : Measure (Config N d)).withDensity
            fun X => ENNReal.ofReal (Qreg V W n f X))).toReal + K) :
    ent (gibbs V W N) (fun X => regF n f X ^ 2) ≤
      ENNReal.ofReal (2 / r) * energy V W N (regF n f) +
        ENNReal.ofReal (K / (2 * r)) * ∫⁻ X, ENNReal.ofReal (regF n f X ^ 2) ∂gibbs V W N := by
  haveI := gibbs_isProbabilityMeasure hyp N
  rcases (bot_le : (0 : ℝ≥0∞) ≤ ent (gibbs V W N) (fun X => regF n f X ^ 2)).eq_or_lt with h0 | hent
  · rw [← h0]; exact bot_le
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)
  set Z := Zreg V W n f with hZdef
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  set E := energy V W N (regF n f) with hEdef
  have hEtop : E ≠ ⊤ := ne_top_of_le_ne_top (energy_lt_top hyp hf).ne (energy_regF_le hyp hf n)
  have hKL := klDiv_Qreg_gibbs_eq hyp hf hfm n hent
  have hKLtop := klDiv_Qreg_gibbs_ne_top hyp hf hfm n
  have hFI := fisher_Qreg_eq hyp hf hfm hw hgm n
  set ent2 := ent (gibbs V W N) (fun X => regF n f X ^ 2) with hent2
  -- `Ent = Z H`
  have hentZ : ent2 = ENNReal.ofReal Z * klDiv ν (gibbs V W N) := by
    rw [hKL, ← mul_assoc, ← ENNReal.ofReal_mul hZ0.le, mul_inv_cancel₀ hZ0.ne', ENNReal.ofReal_one,
      one_mul]
  have hentTop : ent2 ≠ ⊤ := by
    rw [hentZ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKLtop
  have hI : (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2) ∂ν).toReal = 4 / Z * E.toReal := by
    rw [hFI, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [hI] at hbound
  -- the real inequality `Ent ≤ (2/r) E + (K/(2r)) Z`
  have hreal : ent2.toReal ≤ 2 / r * E.toReal + K / (2 * r) * Z := by
    have e1 : ent2.toReal = Z * (klDiv ν (gibbs V W N)).toReal := by
      rw [hentZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hZ0.le]
    rw [e1]
    have h2r : 0 < 2 * r := by positivity
    have : (klDiv ν (gibbs V W N)).toReal ≤ (4 / Z * E.toReal + K) / (2 * r) := by
      rw [le_div_iff₀ h2r]; linarith
    calc Z * (klDiv ν (gibbs V W N)).toReal ≤ Z * ((4 / Z * E.toReal + K) / (2 * r)) :=
          mul_le_mul_of_nonneg_left this hZ0.le
      _ = 2 / r * E.toReal + K / (2 * r) * Z := by first | (field_simp; done) | (field_simp; ring)
  have hZint : ENNReal.ofReal Z = ∫⁻ X, ENNReal.ofReal (regF n f X ^ 2) ∂gibbs V W N := by
    have hm : Measurable fun X => regF n f X ^ 2 :=
      ((contDiff_psiReg n).continuous.measurable.comp hfm).pow_const 2
    have hi : Integrable (fun X => regF n f X ^ 2) (gibbs V W N) :=
      Integrable.of_bound hm.aestronglyMeasurable (((n : ℝ) + 2) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simp only [regF]; rw [← psiSqR_eq]; exact (psiSqR_bounds n (f X)).2)
    rw [hZdef, Zreg_eq hyp hf n, ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun X => sq_nonneg _)]
  have h2r : (0 : ℝ) ≤ 2 / r := div_nonneg zero_le_two hr0.le
  have hKr : (0 : ℝ) ≤ K / (2 * r) := div_nonneg hK0 (by positivity)
  rw [← ENNReal.ofReal_toReal hentTop, ← ENNReal.ofReal_toReal hEtop, ← hZint,
    ← ENNReal.ofReal_mul h2r, ← ENNReal.ofReal_mul hKr,
    ← ENNReal.ofReal_add (mul_nonneg h2r ENNReal.toReal_nonneg) (mul_nonneg hKr hZ0.le)]
  exact ENNReal.ofReal_le_ofReal hreal

end final

/-- **Proposition 2.2**, conditional on Lemma 4.2. -/
theorem prop_defective_of (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (hco : ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ → MFCoercive V W μ) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rStar V W →
      ∃ B : NNReal, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ,
        MemH1C (gibbs V W N) f → IsSymmetric f →
          ent (gibbs V W N) (fun X => f X ^ 2) ≤
            ENNReal.ofReal (2 / r) * energy V W N f +
              (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
  intro r hr0 hrr
  obtain ⟨μ, hμ⟩ := (exists_minimizer hyp).1
  obtain ⟨N₀, K, hK⟩ := large_N_reg hd hyp hμ (hco μ hμ) hr0 hrr
  have hη : 0 < 2 / r := by positivity
  have hsmall : ∀ N : ℕ, ∃ B : ℝ, ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := fun N =>
    fixedN_defective hyp hη
  choose Bs hBs using hsmall
  set K' := max K 0
  set Bsm := ∑ N ∈ Finset.range N₀, max (Bs N) 0
  have hBsm0 : 0 ≤ Bsm := Finset.sum_nonneg fun N _ => le_max_right _ _
  have hK'0 : 0 ≤ K' := le_max_right _ _
  refine ⟨Real.toNNReal (Bsm + K' / (2 * r)), fun N hN f hf hsym => ?_⟩
  have hBcoe : ((Real.toNNReal (Bsm + K' / (2 * r)) : ℝ≥0∞)) = ENNReal.ofReal (Bsm + K' / (2 * r)) := rfl
  rw [hBcoe]
  by_cases hNs : N < N₀
  · refine (hBs N f hf).trans (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
    have h1 : Bs N ≤ max (Bs N) 0 := le_max_left _ _
    have h2 : max (Bs N) 0 ≤ Bsm := Finset.single_le_sum (f := fun N => max (Bs N) 0)
      (fun N _ => le_max_right _ _) (Finset.mem_range.mpr hNs)
    have h3 : 0 ≤ K' / (2 * r) := by positivity
    linarith
  · push_neg at hNs
    haveI := gibbs_isProbabilityMeasure hyp N
    -- a measurable symmetric representative
    obtain ⟨f', hf'm, hf'ae, hf'sym⟩ := exists_measurable_rep hyp (memLp_of_memH1C hyp hf).aestronglyMeasurable
    obtain ⟨hf'H1, hE'⟩ := memH1C_congr_ae hyp hf hf'ae.symm
    have hent' : ent (gibbs V W N) (fun X => f X ^ 2) = ent (gibbs V W N) (fun X => f' X ^ 2) :=
      ent_congr_ae (hf'ae.mono fun X hX => by simp only [hX])
    have hint' : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N =
        ∫⁻ X, ENNReal.ofReal (f' X ^ 2) ∂gibbs V W N :=
      lintegral_congr_ae (hf'ae.mono fun X hX => by simp only [hX])
    rw [hent', hint', ← hE']
    obtain ⟨g, hw, hgm, hg2, -⟩ := exists_measurable_grad hyp hf'H1
    have hreg := fun n => regF_defective_of_bound hyp hf'H1 hf'm hw hgm n hr0 hK'0
      ((hK N hNs hN f' hf'm hf'H1 (hf'sym hsym) g hw hgm hg2 n).trans
        (add_le_add le_rfl (le_max_left _ _)))
    refine (defective_of_regF hyp hf'H1 hreg).trans
      (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
    linarith

end SharpLSI
