import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Paper.AppAFisher
import SharpSymmetricLSI.Statements.R06_Upper_Bound

/-!
# Lemma A.1, flux bounds (4.x): `|a_ρ| ≤ B₀`, `|a_ρ - a_η| ≤ L₀ ‖ρ - η‖₁`

From the essential-supremum bounds `DriftBounds` on `∇V` and `∇₁W`, componentwise and almost
everywhere: `|∇ₖV| ≤ B_V`, `|∂ₖ(W*ρ)| ≤ B_W ∫|ρ|`, with `B_V + B_W ≤ B₀⁺`, `B_W ≤ L₀⁺`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem ae_le_of_eLpNorm_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : eLpNorm f ⊤ μ ≠ ⊤) : ∀ᵐ x ∂μ, |f x| ≤ (eLpNorm f ⊤ μ).toReal := by
  have hle : eLpNormEssSup f μ ≤ eLpNorm f ⊤ μ := eLpNormEssSup_le_eLpNorm_top
  have hf' : eLpNormEssSup f μ ≠ ⊤ := ne_top_of_le_ne_top hf hle
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  have h2 : ENNReal.ofReal |f x| ≤ eLpNormEssSup f μ := by
    rw [← Real.norm_eq_abs, ofReal_norm]; exact hx
  exact ((ENNReal.ofReal_le_iff_le_toReal hf').1 h2).trans (ENNReal.toReal_mono hf hle)

theorem appA_abs_le_sqrt_sqNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) (k : ι) :
    |v k| ≤ Real.sqrt (sqNorm v) := by
  refine Real.abs_le_sqrt ?_
  unfold sqNorm
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k)

theorem grad1W_eq_weakGrad_W2 (x y : Torus d) (k : Fin d) :
    grad1W W x y k = weakGrad (W2 W) (pairFlat (x, y)) (0, k) := rfl

/-- **The drift bounds.** -/
theorem drift_bounds (hyp : Hyp V W KV KW) {B₀ L₀ : ℝ}
    (hDB : eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d) +
        eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
      ENNReal.ofReal B₀ ∧
      eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
        ENNReal.ofReal L₀) :
    ∃ BV BW : ℝ, 0 ≤ BV ∧ 0 ≤ BW ∧ BV + BW ≤ max B₀ 0 ∧ BW ≤ max L₀ 0 ∧
      (∀ᵐ x ∂haar d, ∀ k, |weakGrad V x k| ≤ BV) ∧
      (∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW) := by
  obtain ⟨h1, h2⟩ := hDB
  set eV := eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d)
  set eW := eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume
  have hVt : eV ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans h1)
  have hWt : eW ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  refine ⟨eV.toReal, eW.toReal, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_, ?_, ?_, ?_⟩
  · rw [← ENNReal.toReal_add hVt hWt]
    exact (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (h1.trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  · exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (h2.trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  · filter_upwards [ae_le_of_eLpNorm_top hVt] with x hx k
    refine (appA_abs_le_sqrt_sqNorm _ k).trans ?_
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at hx
  · -- transfer from `Config 2 d` to pairs, then identify `grad1W` with `bGrad`
    have hmp := (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure (Torus d))))
    have hW := ae_le_of_eLpNorm_top hWt
    have hW' : ∀ᵐ p ∂(haar d).prod (haar d),
        Real.sqrt (sqNorm (grad1W W p.1 p.2)) ≤ eW.toReal := by
      have := hmp.symm.quasiMeasurePreserving.ae hW
      refine this.mono fun p hp => ?_
      rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hp
      simpa [MeasurableEquiv.piFinTwo] using hp
    have hlip := isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp)
    have hae := appA_weakGrad_ae_eq hlip
    have hae' : ∀ᵐ p ∂(haar d).prod (haar d),
        weakGrad (W2 W) (pairFlat p) = lipGrad (W2 W) (pairFlat p) :=
      measurePreserving_pairFlat.quasiMeasurePreserving.ae hae
    filter_upwards [hW', hae'] with p hp1 hp2 k
    have e : bGrad W p.1 p.2 k = grad1W W p.1 p.2 k := by
      rw [grad1W_eq_weakGrad_W2, show ((p.1, p.2) : Torus d × Torus d) = p from rfl, hp2]
      rfl
    rw [e]
    exact (appA_abs_le_sqrt_sqNorm _ k).trans hp1

/-- `|∫ bGrad(x,y) h(y) dy| ≤ B_W ∫|h|` for a.e. `x`. -/
theorem bForceL_bound {BW : ℝ} (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {h : Torus d → ℝ} (hh : Integrable h (haar d)) :
    ∀ᵐ x ∂haar d, ∀ k, |bForceL W h x k| ≤ BW * ∫ y, |h y| ∂haar d := by
  filter_upwards [Measure.ae_ae_of_ae_prod hBW] with x hx k
  unfold bForceL
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hh.abs.const_mul BW) ?_).trans
    (le_of_eq (integral_const_mul _ _))
  filter_upwards [hx] with y hy
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hy k) (abs_nonneg _)

theorem integrable_bGrad_mul {BW : ℝ}
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    (hyp : Hyp V W KV KW) {h : Torus d → ℝ} (hh : Integrable h (haar d)) :
    ∀ᵐ x ∂haar d, ∀ k, Integrable (fun y => bGrad W x y k * h y) (haar d) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hBW] with x hx k
  refine hh.bdd_mul (c := BW) ?_ ?_
  · exact ((measurable_bGrad hyp k).comp measurable_prodMk_left).aestronglyMeasurable
  · filter_upwards [hx] with y hy
    rw [Real.norm_eq_abs]; exact hy k

end SharpLSI
