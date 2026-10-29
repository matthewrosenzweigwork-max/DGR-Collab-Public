import SharpSymmetricLSI.Paper.AppAPos9

/-!
# Lemma A.1, existence (6): the modified solution is a probability solution of (4.7)

The Picard solution of the modified equation is a linear mild solution with `|N| ≤ A|ρ|`
(`modMild_linMild`), hence nonnegative (positivity) with conserved mass (`LinMild.integral_eq`), so
`P(ρ_t) = ρ_t` and its flux is `ρ_t a_{ρ_t}` up to null sets (`modFlux_ae_eq`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Mass conservation for linear mild solutions. -/
theorem LinMild.integral_eq {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {N : ℝ → Torus d → Fin d → ℝ}
    {A : ℝ} (h : LinMild ρ₀ ρ N A) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ρ t x ∂haar d = ∫ x, ρ₀ x ∂haar d := by
  obtain ⟨K, hK0, hK⟩ := h.bdd t
  have hm := h.cf_eq_mode hK0 hK 0 ⟨ht, le_rfl⟩
  have hB : modeB N t (0 : Fin d → ℤ) = fun _ => 0 := by
    funext u; unfold modeB; split_ifs <;> simp
  have hl : lamN (0 : Fin d → ℤ) = 0 := by simp [lamN]
  rw [hB, hl] at hm
  simp only [modeD, mul_zero, zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    integral_zero, add_zero] at hm
  simp only [cf, mFourierCoeff_eq_integral, neg_zero, mFourier_zero, ContinuousMap.one_apply,
    one_smul, integral_complex_ofReal] at hm
  exact_mod_cast hm

/-- For a probability density, `P(ρ) = ρ` a.e. -/
theorem posNorm_ae_eq {f : Torus d → ℝ} (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x)
    (h1 : ∫ x, f x ∂haar d = 1) : posNorm f =ᵐ[haar d] f := by
  have hmax : (fun x => max (f x) 0) =ᵐ[haar d] f := h0.mono fun x hx => max_eq_left hx
  have hint : ∫ z, max (f z) 0 ∂haar d = 1 := by rw [integral_congr_ae hmax, h1]
  filter_upwards [hmax] with x hx
  unfold posNorm
  rw [hint, max_self, div_one, hx]

/-- The modified flux is the true flux for a probability density. -/
theorem modFlux_ae_eq (hyp : Hyp V W KV KW) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1) (k : Fin d) :
    (fun y => modFlux V W f y k) =ᵐ[haar d] fun y => f y * appADrift V W f y k := by
  have hb : bForceL W (posNorm f) = bForceL W f := bForceL_congr_ae (posNorm_ae_eq h0 h1)
  have hV := appA_weakGrad_ae_eq (isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W)))
  filter_upwards [hV, weakGrad_convDens_ae hyp hf] with y h1 h2
  unfold modFlux appADrift
  rw [hb, h1, h2]

/-- The Picard solution is a linear mild solution with `|N| ≤ A|ρ|`. -/
theorem modMild_linMild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hρ₀ : Measurable ρ₀) {M : ℝ}
    (hM : ∀ x, |ρ₀ x| ≤ M) :
    ∃ ρ : ℝ → Torus d → ℝ, ∃ A : ℝ,
      LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A := by
  obtain ⟨ρ, hρm, hρ0, μ, hμ, hb, hfix⟩ := exists_modMild hyp hρ₀ hM
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨ρ, LV + Cb, ⟨hρm, fun k => measurable_modFlux hyp hρm k, hρ₀, hρ0, fun T => ?_,
    add_nonneg hLV0 hCb0, fun u hu y k => ?_, fun t ht x => ?_⟩⟩
  · refine ⟨2 * M * Real.exp (μ * |T|), by positivity, fun t ht x => (hb t ht.1 x).trans ?_⟩
    gcongr
    exact ht.2.trans (le_abs_self T)
  · have hbu : ∀ y, |ρ u y| ≤ 2 * M * Real.exp (μ * u) := hb u hu
    exact abs_modFlux_le hLV hCb hyp (appA_integrable_of_abs_le (section_measurable hρm u) hbu) y k
  · rw [hfix t ht x]
    unfold picardMap
    rw [if_pos ht]

end SharpLSI
