import SharpSymmetricLSI.Paper.ProductFisherSimp
import SharpSymmetricLSI.Paper.ProductExpect

/-!
# (2.11): identification of the weak gradients (Phase 3, lane D; R6)

`∇V = lipGrad V` and `∇log ρ = gLog ρ` a.e.; `∇₁W(x,y) = bGrad W x y` for a.e. `(x,y)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem vec2_eq (x y : Torus d) :
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Torus d)).symm (x, y) = ![x, y] := by
  funext i; fin_cases i <;> rfl

/-- `(x,y) ↦ (x,y)` flattened to `𝕋^{2×d}`. -/
def pairFlat (p : Torus d × Torus d) : UnitAddTorus (Fin 2 × Fin d) := flat ![p.1, p.2]

theorem measurePreserving_pairFlat :
    MeasurePreserving (pairFlat (d := d)) ((haar d).prod (haar d)) volume := by
  have h1 := (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure (Torus d)))).symm
  have h2 : MeasurePreserving (flat : Config 2 d → UnitAddTorus (Fin 2 × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume 2⟩
  have h := h2.comp h1
  have e : (flat ∘ (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Torus d)).symm) = pairFlat := by
    funext p; simp only [Function.comp, pairFlat]; rw [vec2_eq]
  rw [e] at h
  exact h

/-- The first-variable weak gradient `∇₁W(x,y)` (unfolded form of `grad1W`). -/
noncomputable def g1W (W : Torus d → Torus d → ℝ) (x y : Torus d) (k : Fin d) : ℝ :=
  weakGradC (fun X : Config 2 d => W (X 0) (X 1)) ![x, y] 0 k

/-- `b_ρ` (unfolded form of `forceDens`). -/
noncomputable def fDens (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (x : Torus d) (k : Fin d) :
    ℝ :=
  ∫ y, g1W W x y k * ρ y ∂haar d

theorem g1W_eq (x y : Torus d) (k : Fin d) :
    g1W W x y k = weakGrad (W2 W) (pairFlat (x, y)) (0, k) := rfl

theorem ae_g1W (hyp : Hyp V W KV KW) :
    ∀ᵐ p ∂((haar d).prod (haar d)), ∀ k, g1W W p.1 p.2 k = bGrad W p.1 p.2 k := by
  have hw := weakGrad_ae_eq (isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp))
  have := measurePreserving_pairFlat.quasiMeasurePreserving.ae_eq_comp hw
  filter_upwards [this] with p hp k
  rw [g1W_eq, bGrad]
  exact congrFun hp (0, k)

theorem ae_weakGrad_V (hyp : Hyp V W KV KW) : weakGrad V =ᵐ[haar d] lipGrad V :=
  weakGrad_ae_eq (isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp))

theorem ae_weakGrad_log {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    weakGrad (fun y => Real.log (ρ y)) =ᵐ[haar d] gLog ρ :=
  weakGrad_ae_eq (isWeakGrad_of_contDiff ((contDiff_logD hs hpos).of_le (by simp)) :
    IsWeakGrad (logD ρ) (gLog ρ))

theorem measurable_bGrad (hyp : Hyp V W KV KW) (k : Fin d) :
    Measurable (Function.uncurry fun x y => bGrad W x y k) := by
  have hpf : Measurable (pairFlat (d := d)) := measurePreserving_pairFlat.measurable
  exact (measurable_lipGrad (continuous_W2 hyp) (0, k)).comp hpf

theorem measurable_aGrad (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (k : Fin d) : Measurable fun x => aGrad V ρ x k :=
  (measurable_lipGrad hyp.continuous_V k).add (measurable_smoothGrad (contDiff_logD hs hpos) k)

theorem bGrad_bdd (hyp : Hyp V W KV KW) : ∃ C, ∀ x y k, |bGrad W x y k| ≤ C :=
  ⟨_, fun x y k => abs_lipGrad_le (lipschitz_W2 hyp) _ _⟩

theorem aGrad_bdd (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) : ∃ C, ∀ x k, |aGrad V ρ x k| ≤ C := by
  obtain ⟨CL, hCL⟩ := gLog_bdd hs hpos
  exact ⟨_ + CL, fun x k => (abs_add_le _ _).trans
    (add_le_add (abs_lipGrad_le (lipschitz_V hyp) x k) (hCL x k))⟩

end SharpLSI
