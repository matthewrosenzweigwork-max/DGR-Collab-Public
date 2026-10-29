import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Paper.Defective29

/-!
# Large-N assembly I: from the large-N bound to the defective inequality
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 9. L7: the final assembly -/

/-- **From the large-`N` bound to the defective inequality** (pure assembly; no minimizer, no
`rStar`): the copy of `Defective29.prop_defective_of` after `large_N_reg` has been used, with `IsSymmetric`
removed.  Proof (verbatim from Defective29 lines 87-135): `fixedN_defective hyp (η := 2/r)` for each
`N < N₀` (`choose`, finite sum `Bsm`), and for `N ≥ N₀`: `exists_measurable_rep hyp (memLp_of_memH1C hyp hf)
.aestronglyMeasurable` (we ignore its symmetry clause), `memH1C_congr_ae`, `ent_congr_ae`,
`exists_measurable_grad hyp hf'H1`, `regF_defective_of_bound hyp hf'H1 hf'm hw hgm n hr0 hK0 (hK …)`,
`defective_of_regF hyp hf'H1`.  ~60 lines. -/
theorem prop_defective_all_of (hyp : Hyp V W KV KW) {r : ℝ} (hr0 : 0 < r) {N₀ : ℕ} {K : ℝ}
    (hK : ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → ∀ f : Config N d → ℝ, Measurable f →
      MemH1C (gibbs V W N) f →
      ∀ g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ, IsWeakGrad (f ∘ unflat) g →
      (∀ p, Measurable fun y => g y p) → (∀ p, MemLp (fun y => g y p) 2 volume) → ∀ n : ℕ,
      2 * r * (klDiv ((volume : Measure (Config N d)).withDensity
          fun X => ENNReal.ofReal (Qreg V W n f X)) (gibbs V W N)).toReal ≤
        (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
          ∂((volume : Measure (Config N d)).withDensity
            fun X => ENNReal.ofReal (Qreg V W n f X))).toReal + K) :
    ∃ B : NNReal, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤
        ENNReal.ofReal (2 / r) * energy V W N f +
          (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
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
  refine ⟨Real.toNNReal (Bsm + K' / (2 * r)), fun N hN f hf => ?_⟩
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
    obtain ⟨f', hf'm, hf'ae, -⟩ := exists_measurable_rep hyp (memLp_of_memH1C hyp hf).aestronglyMeasurable
    obtain ⟨hf'H1, hE'⟩ := memH1C_congr_ae hyp hf hf'ae.symm
    have hent' : ent (gibbs V W N) (fun X => f X ^ 2) = ent (gibbs V W N) (fun X => f' X ^ 2) :=
      ent_congr_ae (hf'ae.mono fun X hX => by simp only [hX])
    have hint' : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N =
        ∫⁻ X, ENNReal.ofReal (f' X ^ 2) ∂gibbs V W N :=
      lintegral_congr_ae (hf'ae.mono fun X hX => by simp only [hX])
    rw [hent', hint', ← hE']
    obtain ⟨g, hw, hgm, hg2, -⟩ := exists_measurable_grad hyp hf'H1
    have hreg := fun n => regF_defective_of_bound hyp hf'H1 hf'm hw hgm n hr0 hK'0
      ((hK N hNs hN f' hf'm hf'H1 g hw hgm hg2 n).trans
        (add_le_add le_rfl (le_max_left _ _)))
    refine (defective_of_regF hyp hf'H1 hreg).trans
      (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
    linarith

end SharpLSI.FL
