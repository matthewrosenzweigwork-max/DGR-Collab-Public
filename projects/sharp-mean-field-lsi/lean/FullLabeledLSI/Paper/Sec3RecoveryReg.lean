import FullLabeledLSI.Paper.Sec3RecoveryApprox
import FullLabeledLSI.Paper.Sec3RecSmooth

/-!
# Proposition 3.2: regularization of an admissible family

Componentwise smooth approximation (`approx_species`) with the weights fixed; the `L¹`
convergence of the species densities gives convergence of the mean density and hence of the
potential and interaction energies and of the force terms.
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem lintegral_bar_sub_le {q : ℕ} (θ : Fin q → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (f g : Fin q → Torus d → ℝ) (hf : ∀ a, Integrable (f a) (haar d))
    (hg : ∀ a, Integrable (g a) (haar d)) :
    ∫⁻ x, ‖∑ a, θ a * f a x - ∑ a, θ a * g a x‖ₑ ∂haar d ≤
      ∑ a, ENNReal.ofReal (θ a) * ∫⁻ x, ‖f a x - g a x‖ₑ ∂haar d := by
  have hpt : ∀ x, ‖∑ a, θ a * f a x - ∑ a, θ a * g a x‖ₑ ≤
      ∑ a, ENNReal.ofReal (θ a) * ‖f a x - g a x‖ₑ := fun x => by
    rw [← Finset.sum_sub_distrib]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [← mul_sub, enorm_mul, Real.enorm_eq_ofReal (hθ a)]
  calc _ ≤ ∫⁻ x, ∑ a, ENNReal.ofReal (θ a) * ‖f a x - g a x‖ₑ ∂haar d := lintegral_mono hpt
    _ = ∑ a, ∫⁻ x, ENNReal.ofReal (θ a) * ‖f a x - g a x‖ₑ ∂haar d :=
        lintegral_finsetSum' _ fun a _ =>
          (((hf a).sub (hg a)).aemeasurable.enorm).const_mul _
    _ = _ := Finset.sum_congr rfl fun a _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Componentwise regularization of an admissible family** (manuscript, after (1.13)): there are
families of smooth positive probability densities with the same weights whose `G_θ` and `D_θ`
converge to those of the given family. -/
theorem family_regularization (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    ∃ Fs : ℕ → Family d,
      (∀ n, (∀ s, 0 ≤ (Fs n).θ s) ∧ ∑ s, (Fs n).θ s = 1 ∧
        ∀ s, IsSmoothT ((Fs n).ρ s) ∧ (∀ x, 0 < (Fs n).ρ s x) ∧
          ∫ x, (Fs n).ρ s x ∂haar d = 1) ∧
      Tendsto (fun n => (msGap V W (Fs n)).toENNReal) atTop (𝓝 (msGap V W F).toENNReal) ∧
      Tendsto (fun n => msDiss V W (Fs n)) atTop (𝓝 (msDiss V W F)) := by
  obtain ⟨q, θ, ρ⟩ := F
  obtain ⟨hθpos, hθ1, hρ⟩ := hF
  have hθ0 : ∀ a, 0 ≤ θ a := fun a => (hθpos a).le
  have hap := fun a => approx_species (V := V) (W := W) hyp (hρ a).1 (hρ a).2.1 (hρ a).2.2
  choose ρs hρs hL1 hae hD hent using hap
  have hρi : ∀ a, Integrable (ρ a) (haar d) := fun a => integrable_of_integral_eq_one' (hρ a).2.1
  have hρsi : ∀ a n, Integrable (ρs a n) (haar d) := fun a n =>
    integrable_of_integral_eq_one' (hρs a n).2.2
  -- the mean densities
  set bs : ℕ → Torus d → ℝ := fun n x => ∑ a, θ a * ρs a n x with hbs
  set b : Torus d → ℝ := fun x => ∑ a, θ a * ρ a x with hb
  have hb0 : ∀ x, 0 ≤ b x := fun x => Finset.sum_nonneg fun a _ =>
    mul_nonneg (hθ0 a) ((hρ a).1 x)
  have hbs0 : ∀ n x, 0 ≤ bs n x := fun n x => Finset.sum_nonneg fun a _ =>
    mul_nonneg (hθ0 a) ((hρs a n).2.1 x).le
  have hb1 : ∫ x, b x ∂haar d = 1 := by
    simp only [hb]
    rw [integral_finsetSum _ fun a _ => (hρi a).const_mul _]
    simp_rw [integral_const_mul, (hρ _).2.1]
    simpa using hθ1
  have hbs1 : ∀ n, ∫ x, bs n x ∂haar d = 1 := fun n => by
    simp only [hbs]
    rw [integral_finsetSum _ fun a _ => (hρsi a n).const_mul _]
    simp_rw [integral_const_mul, (hρs _ n).2.2]
    simpa using hθ1
  have hLb : Tendsto (fun n => ∫⁻ x, ‖bs n x - b x‖ₑ ∂haar d) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
      (fun n => lintegral_bar_sub_le θ hθ0 (fun a => ρs a n) ρ (fun a => hρsi a n) hρi)
    have := tendsto_finsetSum Finset.univ fun a (_ : a ∈ Finset.univ) =>
      ENNReal.Tendsto.const_mul (hL1 a) (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (θ a))
    simpa using this
  refine ⟨fun n => ⟨q, θ, fun a => ρs a n⟩, fun n => ⟨hθ0, hθ1, fun a => hρs a n⟩, ?_, ?_⟩
  · have hSt : ∀ n : ℕ, ∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρs a n)) (haar d) =
        ∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρs a n)) (haar d) := fun _ => rfl
    have hS : Tendsto (fun n => ∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρs a n)) (haar d))
        atTop (𝓝 (∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρ a)) (haar d))) :=
      tendsto_finsetSum _ fun a _ =>
        ENNReal.Tendsto.const_mul (hent a) (Or.inr ENNReal.ofReal_ne_top)
    have hS0 : (∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρ a)) (haar d)) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (klDiv_ne_top_of_H1 (hρ a).1 (hρ a).2.1 (hρ a).2.2)
    have hSev : ∀ᶠ n in atTop, (∑ a, ENNReal.ofReal (θ a) *
        klDiv (densMeasure (ρs a n)) (haar d)) ≠ ⊤ :=
      (hS.eventually (eventually_lt_nhds (lt_top_iff_ne_top.2 hS0))).mono fun n hn => ne_of_lt hn
    have hP := potE_tendsto hyp hb0 hb1 hbs0 hbs1 hLb
    have hI := interE_tendsto (W := W) hyp hb0 hb1 hbs0 hbs1 hLb
    have hR := hP.add (hI.div_const 2)
    have hFs : Fstar V W = (((Fstar V W).toReal : ℝ) : EReal) := Fstar_eq_coe hyp
    set c : ℝ := (Fstar V W).toReal
    have hform : ∀ (G : Family d) (R : ℝ), G.q = q → True := fun _ _ _ => trivial
    have hmsG : ∀ (σ : Fin q → Torus d → ℝ) (R : ℝ),
        (∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (σ a)) (haar d)) ≠ ⊤ →
        R = potE V (densMeasure (fun x => ∑ a, θ a * σ a x)) +
          interE W (densMeasure (fun x => ∑ a, θ a * σ a x))
            (densMeasure (fun x => ∑ a, θ a * σ a x)) / 2 →
        (msGap V W ⟨q, θ, σ⟩).toENNReal = ENNReal.ofReal
          ((∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (σ a)) (haar d)).toReal + R - c) := by
      intro σ R hSne hR
      have : msGap V W ⟨q, θ, σ⟩ = ((((∑ a, ENNReal.ofReal (θ a) *
          klDiv (densMeasure (σ a)) (haar d)).toReal + R - c : ℝ)) : EReal) := by
        unfold msGap
        rw [hFs, ← EReal.coe_ennreal_toReal hSne]
        simp only [Family.bar, hR]
        simp [EReal.coe_add, EReal.coe_sub] <;> rfl
      rw [this, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    have hlim : Tendsto (fun n => ENNReal.ofReal
        ((∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρs a n)) (haar d)).toReal +
          (potE V (densMeasure (bs n)) + interE W (densMeasure (bs n)) (densMeasure (bs n)) / 2)
          - c)) atTop (𝓝 (ENNReal.ofReal
        ((∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρ a)) (haar d)).toReal +
          (potE V (densMeasure b) + interE W (densMeasure b) (densMeasure b) / 2) - c))) := by
      refine ENNReal.tendsto_ofReal ?_
      exact (((ENNReal.tendsto_toReal hS0).comp hS).add hR).sub_const c
    rw [hmsG ρ _ hS0 rfl]
    refine hlim.congr' ?_
    filter_upwards [hSev] with n hn
    exact (hmsG (fun a => ρs a n) _ hn rfl).symm
  · -- dissipation
    have hTD : ∀ a, Tendsto (fun n => speciesDiss V W (ρs a n) (bs n)) atTop
        (𝓝 (speciesDiss V W (ρ a) b)) := fun a => hD a bs b hbs0 hbs1 hb0 hb1 hLb
    have := tendsto_finsetSum Finset.univ fun a (_ : a ∈ Finset.univ) =>
      ENNReal.Tendsto.const_mul (hTD a) (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (θ a))
    exact this

end SharpLSI.FL
