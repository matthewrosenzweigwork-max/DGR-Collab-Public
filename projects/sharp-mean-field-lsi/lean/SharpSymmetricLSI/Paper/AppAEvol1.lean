import SharpSymmetricLSI.Paper.AppAStab5
import SharpSymmetricLSI.Paper.Gibbs

/-!
# Lemma A.1: the drift bounds hold under (1.2); uniqueness of mild solutions

Under (1.2), `‖∇V‖_∞` and `‖∇₁W‖_∞` are finite (Lipschitz representatives), so the bounds of
(A.3) hold for some `B₀`, `L₀`; uniqueness of mild solutions is (A.3) with `ρ₀ = η₀`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memLp_top_sqrt_sqNorm_weakGrad_V (hyp : Hyp V W KV KW) :
    MemLp (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d) := by
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hw := appA_isWeakGrad_weakGrad (⟨_, hVw⟩ : HasWeakGrad V)
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad V x))) (haar d) := by
    refine Real.continuous_sqrt.comp_aestronglyMeasurable ?_
    unfold sqNorm
    exact Finset.aestronglyMeasurable_fun_sum _ fun k _ => (appA_aestronglyMeasurable_grad hw k).pow 2
  refine MemLp.of_bound hm (Real.sqrt (Fintype.card (Fin d) * LV ^ 2)) ?_
  filter_upwards [appA_weakGrad_ae_eq hVw] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
  refine Real.sqrt_le_sqrt ?_
  unfold sqNorm
  calc ∑ k, lipGrad V x k ^ 2 ≤ ∑ _k : Fin d, LV ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hLV x k) 2
    _ = _ := by simp

theorem vec2_self {α : Type*} (X : Fin 2 → α) : ![X 0, X 1] = X := by
  funext i; fin_cases i <;> rfl

theorem memLp_top_sqrt_sqNorm_grad1W (hyp : Hyp V W KV KW) :
    MemLp (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume := by
  have hWw := isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp)
  have hw := appA_isWeakGrad_weakGrad (⟨_, hWw⟩ : HasWeakGrad (W2 W))
  set LW : ℝ := ((Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) : NNReal) : ℝ)
  have hLW : ∀ Y k, |lipGrad (W2 W) Y k| ≤ LW := fun Y k => abs_lipGrad_le (lipschitz_W2 hyp) Y k
  set G : UnitAddTorus (Fin 2 × Fin d) → ℝ :=
    fun Y => Real.sqrt (sqNorm fun k : Fin d => weakGrad (W2 W) Y (0, k)) with hG
  have h2 : MeasurePreserving (flat : Config 2 d → UnitAddTorus (Fin 2 × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume 2⟩
  have e : (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) = G ∘ flat := by
    funext X
    simp only [Function.comp, hG]
    congr 2
    funext k
    rw [grad1W_eq_weakGrad_W2]
    simp only [pairFlat, vec2_self]
  have hGm : AEStronglyMeasurable G volume := by
    refine Real.continuous_sqrt.comp_aestronglyMeasurable ?_
    unfold sqNorm
    exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (appA_aestronglyMeasurable_grad hw (0, k)).pow 2
  have hGb : ∀ᵐ Y ∂(volume : Measure (UnitAddTorus (Fin 2 × Fin d))),
      ‖G Y‖ ≤ Real.sqrt (Fintype.card (Fin d) * LW ^ 2) := by
    filter_upwards [appA_weakGrad_ae_eq hWw] with Y hY
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [hY]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    calc ∑ k : Fin d, lipGrad (W2 W) Y (0, k) ^ 2 ≤ ∑ _k : Fin d, LW ^ 2 :=
          Finset.sum_le_sum fun k _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hLW Y (0, k)) 2
      _ = _ := by simp
  rw [e]
  exact MemLp.of_bound (hGm.comp_measurePreserving h2) _ (h2.quasiMeasurePreserving.ae hGb)

/-- Under (1.2) the drift bounds of (A.3) hold for some `B₀`, `L₀`. -/
theorem exists_driftBounds (hyp : Hyp V W KV KW) :
    ∃ B₀ L₀ : ℝ,
      eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d) +
          eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
        ENNReal.ofReal B₀ ∧
      eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
        ENNReal.ofReal L₀ := by
  have hV := (memLp_top_sqrt_sqNorm_weakGrad_V hyp).eLpNorm_lt_top.ne
  have hW := (memLp_top_sqrt_sqNorm_grad1W hyp).eLpNorm_lt_top.ne
  refine ⟨(eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d) +
      eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume).toReal,
    (eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume).toReal,
    ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨hV, hW⟩)]
  · rw [ENNReal.ofReal_toReal hW]

/-- **Uniqueness** of mild solutions. -/
theorem appAMild_unique (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} {ρ η : ℝ → Torus d → ℝ}
    (hρ : AppAMild V W ρ₀ ρ) (hη : AppAMild V W ρ₀ η) {t : ℝ} (ht : 0 ≤ t) :
    ρ t =ᵐ[haar d] η t := by
  obtain ⟨B₀, L₀, hDB⟩ := exists_driftBounds hyp
  obtain ⟨C, hC⟩ := flow_stability_aux d t B₀ L₀
  have h := hC V W KV KW hyp hDB ρ₀ ρ₀ ρ η hρ hη t ⟨ht, le_rfl⟩
  simp only [sub_self, eLpNorm_fun_zero, mul_zero, nonpos_iff_eq_zero] at h
  rw [eLpNorm_eq_zero_iff one_ne_zero] at h
  filter_upwards [h] with x hx
  simpa [sub_eq_zero] using hx

end SharpLSI
