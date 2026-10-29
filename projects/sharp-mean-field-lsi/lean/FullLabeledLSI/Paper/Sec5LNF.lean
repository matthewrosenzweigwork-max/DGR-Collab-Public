import FullLabeledLSI.Paper.Sec5LNDefs

/-!
# Large-N assembly F: L4 and the entropy chain in real form
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 6. L4: the interaction term, and the entropy chain in real form -/

/-- `∫ empiricalTensor 2 (Bk W μ) dν = (∫ U_N dν)/N` (`N ≥ 1`).  Pointwise `mul_empiricalTensor_two`
(`N · emp = U_N`), then `integral_div`.  ~15 lines.  (PROVED in `Defective28` inline as `hempU`.) -/
theorem integral_empiricalTensor_Bk (μ : Measure (Torus d)) {N : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Config N d)) :
    ∫ X, empiricalTensor 2 (Bk W μ) X ∂ν = (∫ X, Ucentered W μ N X ∂ν) / N := by
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have := SharpLSI.mul_empiricalTensor_two (N := N) (centeredKernel W μ) X
  unfold Bk
  rw [eq_div_iff hNpos.ne', mul_comm, this]
  rfl

/-- **L4.**  `Σ_{j<ℓ} E_S E_ν J(ρ̄_S) = (ℓ/N) E_ν U_N + O(1 + √H₀)`, for all `ν` (no smoothness):
`random_products_aux 2 τ hτ (Bk W μ)` (measurability from `measurable_centeredKernel`, boundedness
from `centeredKernel_bdd`) + `integral_empiricalTensor_Bk`.  ~30 lines. -/
theorem products_J (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (N M : ℕ), 2 ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
        klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
        |∑ j ∈ Finset.range (N - M), condMeanS ν 2 (Bk W μ) j -
            ((N - M : ℕ) : ℝ) / N * ∫ X, Ucentered W μ N X ∂ν| ≤
          C * (1 + Real.sqrt (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal) := by
  have hA : Measurable (Bk W μ) := by
    unfold Bk
    have hm : Measurable fun z : Fin 2 → Torus d => (z 0, z 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    exact ((measurable_centeredKernel hyp μ).comp hm).div_const 2
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μ
  obtain ⟨C, hC⟩ := random_products_aux 2 τ hτ (Bk W μ) hA ⟨B / 2, fun z => by
    unfold Bk
    rw [abs_div, abs_two]
    have := hB (z 0) (z 1)
    linarith⟩
  refine ⟨C, fun N M hM hMN hτM ν _ hH => ?_⟩
  have hN : 1 ≤ N := by omega
  have h := hC N M hM hMN hτM μ ν hH
  rw [integral_empiricalTensor_Bk μ hN ν] at h
  have e : ((N - M : ℕ) : ℝ) * ((∫ X, Ucentered W μ N X ∂ν) / N) =
      ((N - M : ℕ) : ℝ) / N * ∫ X, Ucentered W μ N X ∂ν := by ring
  rwa [e] at h

/-- **Entropy chain, real form** (S20 for general `ν`; `chain_sum`, `chain_step` of Sec5Chain need no
smoothness, unlike the statement-file versions `random_chain_*`).  With `h_j = (hRev ν μ j).toReal` and
`H₀ = (klDiv ν μ^{⊗N}).toReal`: all `h_j` are finite (`Σ h_j = H₀ < ⊤`), nondecreasing for `j + 1 < N`
(`chain_step`: `h_{j+1} = h_j + d_{j,2}`), so by `sum_Ico_le_of_mono`,
`H₀ - M h_{N-1} ≤ Σ_{j<N-M} h_j`.  ~50 lines. -/
theorem chain_lower {N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {M : ℕ} (hMN : M ≤ N) :
    (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal - M * (hRev ν μ (N - 1)).toReal ≤
      ∑ j ∈ Finset.range (N - M), (hRev ν μ j).toReal := by
  set h : ℕ → ℝ := fun j => (hRev ν μ j).toReal with hh
  have hsum := chain_sum ν μ
  have hfin : ∀ j ∈ Finset.range N, hRev ν μ j ≠ ⊤ := fun j hj =>
    ne_top_of_le_ne_top hH (hsum ▸ Finset.single_le_sum (f := fun j => hRev ν μ j)
      (fun _ _ => bot_le) hj)
  have hH0 : (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal = ∑ j ∈ Finset.range N, h j := by
    rw [← hsum, ENNReal.toReal_sum hfin]
  have hmono : ∀ j, j + 1 < N → h j ≤ h (j + 1) := fun j hj =>
    ENNReal.toReal_mono (hfin (j + 1) (Finset.mem_range.2 hj)) (hRev_mono ν μ (by omega))
  have hIco := SharpLSI.sum_Ico_le_of_mono (h := h) (N := N) (ℓ := N - M) (by omega) hmono
  have hsplit := Finset.sum_range_add_sum_Ico h (show N - M ≤ N by omega)
  have hc : (N - (N - M) : ℕ) = M := by omega
  rw [hc] at hIco
  show _ ≤ ∑ j ∈ Finset.range (N - M), h j
  linarith


end SharpLSI.FL
