import SharpSymmetricLSI.Paper.AppAStab1
import SharpSymmetricLSI.Paper.AppAFisher2

/-!
# Lemma A.1, flux bounds (4.x)

With `a_ρ = ∇V + ∇(W*ρ)` (`appADrift`, definitionally the `driftField` of R36), for probability
densities `ρ, η`, almost everywhere and componentwise:
`|a_ρ| ≤ B_V + B_W`, `|a_ρ - a_η| ≤ B_W ‖ρ - η‖₁`, hence
`‖ρ a_ρ - η a_η‖₁ ≤ (B_V + 2 B_W) ‖ρ - η‖₁`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The drift `a_ρ = ∇V + ∇(W*ρ)` (the `driftField` of R36). -/
noncomputable def appADrift (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ)
    (x : Torus d) (k : Fin d) : ℝ :=
  weakGrad V x k + weakGrad (convDens W ρ) x k

/-- A probability density, up to null sets. -/
structure IsProbDens (ρ : Torus d → ℝ) : Prop where
  int : Integrable ρ (haar d)
  nonneg : ∀ᵐ x ∂haar d, 0 ≤ ρ x
  one : ∫ x, ρ x ∂haar d = 1

theorem IsProbDens.integral_abs {ρ : Torus d → ℝ} (h : IsProbDens ρ) :
    ∫ x, |ρ x| ∂haar d = 1 := by
  exact (integral_congr_ae (h.nonneg.mono fun x hx => abs_of_nonneg hx)).trans h.one

theorem weakGrad_convDens_ae (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ : Integrable ρ (haar d)) :
    weakGrad (convDens W ρ) =ᵐ[haar d] bForceL W ρ :=
  appA_weakGrad_ae_eq (isWeakGrad_convDens' hyp hρ)

theorem bForceL_sub_ae {BW : ℝ}
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    (hyp : Hyp V W KV KW) {ρ η : Torus d → ℝ} (hρ : Integrable ρ (haar d))
    (hη : Integrable η (haar d)) :
    ∀ᵐ x ∂haar d, ∀ k, bForceL W ρ x k - bForceL W η x k = bForceL W (fun y => ρ y - η y) x k := by
  filter_upwards [integrable_bGrad_mul hBW hyp hρ, integrable_bGrad_mul hBW hyp hη] with x h1 h2 k
  unfold bForceL
  rw [← integral_sub (h1 k) (h2 k)]
  congr 1; funext y; ring

/-- **`|a_ρ| ≤ B_V + B_W`.** -/
theorem abs_appADrift_le (hyp : Hyp V W KV KW) {BV BW : ℝ}
    (hBV : ∀ᵐ x ∂haar d, ∀ k, |weakGrad V x k| ≤ BV)
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {ρ : Torus d → ℝ} (hρ : IsProbDens ρ) :
    ∀ᵐ x ∂haar d, ∀ k, |appADrift V W ρ x k| ≤ BV + BW := by
  filter_upwards [hBV, weakGrad_convDens_ae hyp hρ.int, bForceL_bound hBW hρ.int] with x h1 h2 h3 k
  unfold appADrift
  rw [h2]
  have := h3 k
  rw [hρ.integral_abs, mul_one] at this
  exact (abs_add_le _ _).trans (add_le_add (h1 k) this)

/-- **`|a_ρ - a_η| ≤ B_W ‖ρ - η‖₁`.** -/
theorem abs_appADrift_sub_le (hyp : Hyp V W KV KW) {BW : ℝ}
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {ρ η : Torus d → ℝ} (hρ : Integrable ρ (haar d)) (hη : Integrable η (haar d)) :
    ∀ᵐ x ∂haar d, ∀ k, |appADrift V W ρ x k - appADrift V W η x k| ≤
      BW * ∫ y, |ρ y - η y| ∂haar d := by
  filter_upwards [weakGrad_convDens_ae hyp hρ, weakGrad_convDens_ae hyp hη,
    bForceL_sub_ae hBW hyp hρ hη, bForceL_bound hBW (hρ.sub hη)] with x h1 h2 h3 h4 k
  unfold appADrift
  rw [h1, h2, add_sub_add_left_eq_sub, h3]
  exact h4 k

/-- The flux `ρ a_ρ`, componentwise. -/
noncomputable def appAFlux (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ)
    (x : Torus d) (k : Fin d) : ℝ :=
  ρ x * appADrift V W ρ x k

theorem aestronglyMeasurable_appADrift (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ}
    (hρ : Integrable ρ (haar d)) (k : Fin d) :
    AEStronglyMeasurable (fun x => appADrift V W ρ x k) (haar d) := by
  have hV : HasWeakGrad V :=
    ⟨_, isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))⟩
  exact (appA_aestronglyMeasurable_grad (appA_isWeakGrad_weakGrad hV) k).add
    (appA_aestronglyMeasurable_grad (appA_isWeakGrad_weakGrad ⟨_, isWeakGrad_convDens' hyp hρ⟩) k)

/-- **Flux `L¹` Lipschitz bound.** -/
theorem lintegral_appAFlux_sub_le (hyp : Hyp V W KV KW) {BV BW : ℝ} (hBV0 : 0 ≤ BV)
    (hBW0 : 0 ≤ BW)
    (hBV : ∀ᵐ x ∂haar d, ∀ k, |weakGrad V x k| ≤ BV)
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {ρ η : Torus d → ℝ} (hρ : IsProbDens ρ) (hη : IsProbDens η) (k : Fin d) :
    ∫⁻ x, ‖appAFlux V W ρ x k - appAFlux V W η x k‖ₑ ∂haar d ≤
      ENNReal.ofReal (BV + 2 * BW) * ∫⁻ x, ‖ρ x - η x‖ₑ ∂haar d := by
  set δ := ∫ y, |ρ y - η y| ∂haar d with hδ
  have hδ' : ENNReal.ofReal δ = ∫⁻ x, ‖ρ x - η x‖ₑ ∂haar d := by
    rw [hδ, ofReal_integral_eq_lintegral_ofReal (f := fun y => |ρ y - η y|)
      (hρ.int.sub hη.int).abs (Eventually.of_forall fun _ => abs_nonneg _)]
    exact lintegral_congr fun x => by rw [← Real.norm_eq_abs, ofReal_norm]
  have hpt : ∀ᵐ x ∂haar d, ‖appAFlux V W ρ x k - appAFlux V W η x k‖ₑ ≤
      ENNReal.ofReal ((BV + BW) * |ρ x - η x| + BW * δ * |η x|) := by
    filter_upwards [abs_appADrift_le hyp hBV hBW hρ, abs_appADrift_sub_le hyp hBW hρ.int hη.int]
      with x h1 h2
    rw [← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold appAFlux
    have e : ρ x * appADrift V W ρ x k - η x * appADrift V W η x k =
        (ρ x - η x) * appADrift V W ρ x k +
          η x * (appADrift V W ρ x k - appADrift V W η x k) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := h1 k
    have := h2 k
    nlinarith [abs_nonneg (ρ x - η x), abs_nonneg (η x),
      abs_nonneg (appADrift V W ρ x k - appADrift V W η x k)]
  refine (lintegral_mono_ae hpt).trans ?_
  have hint : Integrable (fun x => (BV + BW) * |ρ x - η x| + BW * δ * |η x|) (haar d) :=
    ((hρ.int.sub hη.int).abs.const_mul _).add (hη.int.abs.const_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity),
    integral_add (f := fun x => (BV + BW) * |ρ x - η x|) (g := fun x => BW * δ * |η x|)
      ((hρ.int.sub hη.int).abs.const_mul _) (hη.int.abs.const_mul _),
    integral_const_mul, integral_const_mul, hη.integral_abs, ← hδ, ← hδ',
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

end SharpLSI
