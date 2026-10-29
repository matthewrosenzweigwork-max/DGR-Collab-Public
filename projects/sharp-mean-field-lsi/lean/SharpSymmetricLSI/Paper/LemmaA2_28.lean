import SharpSymmetricLSI.Paper.LemmaA2_27

/-!
# R25 Lemma A.2, part 28: generic tools for the final assembly

* `eLpNorm_top_le_of_ae`: an a.e. bound bounds the `L^∞` norm;
* `measurable_slice_lipGrad`: slice gradients of a continuous Lipschitz kernel are jointly
  measurable;
* `ae_eq_on_config`: if `f = g` a.e. on the torus then the corresponding product functions agree
  `μ^{⊗2}`-a.e. and Lebesgue-a.e. on the flattened torus.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem eLpNorm_top_le_of_ae {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g ν) (hfg : ∀ᵐ x ∂ν, f x = g x) (h : ∀ᵐ x ∂ν, |g x| ≤ C) :
    eLpNorm f ⊤ ν ≤ ENNReal.ofReal C := by
  rw [eLpNorm_congr_ae (hfg : f =ᵐ[ν] g), eLpNorm_exponent_top hg]
  exact eLpNormEssSup_le_of_ae_bound (h.mono fun x hx => by rwa [Real.norm_eq_abs])

theorem measurable_pair_flat :
    Measurable fun p : Torus d × Torus d => flat (![p.1, p.2] : Config 2 d) := by
  refine measurable_flat.comp (measurable_pi_iff.mpr fun i => ?_)
  fin_cases i
  · exact measurable_fst
  · exact measurable_snd

theorem continuous_kerC2 {G : Torus d → Torus d → ℝ} (hG : Continuous (Function.uncurry G)) :
    Continuous (kerC2 G) := by
  have h : Continuous fun X : Config 2 d => (X 0, X 1) :=
    (continuous_apply (0 : Fin 2)).prodMk (continuous_apply (1 : Fin 2))
  exact hG.comp h

theorem measurable_config_pair : Measurable fun X : Config 2 d => (X 0, X 1) :=
  (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)

theorem measurable_slice_lipGrad {G : Torus d → Torus d → ℝ} (hG : Continuous (Function.uncurry G))
    (k : Fin d) :
    Measurable (fun p : Torus d × Torus d => lipGrad (fun x => G x p.2) p.1 k) ∧
    Measurable (fun p : Torus d × Torus d => lipGrad (fun y => G p.1 y) p.2 k) := by
  have hc := continuous_kerC2_unflat hG
  constructor
  · have := (measurable_lipGrad hc ((0 : Fin 2), k)).comp measurable_pair_flat
    convert this using 1
    funext p
    simp only [Function.comp]
    rw [lipGrad_kerC_zero]; rfl
  · have := (measurable_lipGrad hc ((1 : Fin 2), k)).comp measurable_pair_flat
    convert this using 1
    funext p
    simp only [Function.comp]
    rw [lipGrad_kerC_one]; rfl

/-- A torus a.e. property in each coordinate holds `μ^{⊗2}`-a.e. -/
theorem ae_pi_two_coord {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {p : Torus d → Prop}
    (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ), p (X 0) ∧ p (X 1) := by
  have h0 := (measurePreserving_eval (fun _ : Fin 2 => μ) 0).quasiMeasurePreserving.ae h
  have h1 := (measurePreserving_eval (fun _ : Fin 2 => μ) 1).quasiMeasurePreserving.ae h
  filter_upwards [h0, h1] with X hX0 hX1
  exact ⟨hX0, hX1⟩

/-- A torus a.e. property in each block holds a.e. on the flattened torus. -/
theorem ae_flat_two_coord {p : Torus d → Prop} (h : ∀ᵐ x ∂(volume : Measure (Torus d)), p x) :
    ∀ᵐ Y ∂(volume : Measure (UnitAddTorus (Fin 2 × Fin d))), p (unflat Y 0) ∧ p (unflat Y 1) := by
  have hv : ∀ᵐ X ∂(volume : Measure (Config 2 d)), p (X 0) ∧ p (X 1) := by
    have h0 := (measurePreserving_eval (fun _ : Fin 2 => (volume : Measure (Torus d))) 0).quasiMeasurePreserving.ae h
    have h1 := (measurePreserving_eval (fun _ : Fin 2 => (volume : Measure (Torus d))) 1).quasiMeasurePreserving.ae h
    filter_upwards [h0, h1] with X hX0 hX1
    exact ⟨hX0, hX1⟩
  rw [← map_flat_volume 2]
  exact measurableEmbedding_flat.ae_map_iff.mpr (hv.mono fun X hX => hX)

end SharpLSI
