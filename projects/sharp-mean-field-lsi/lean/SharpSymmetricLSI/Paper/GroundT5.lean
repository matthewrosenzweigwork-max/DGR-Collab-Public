import SharpSymmetricLSI.Paper.GroundT4

/-!
# R30: the ground-state transform `Ψ_N = f_N √p_N` ((7.6)–(7.7)), pointwise part

`Ψ = (√K_N)⁻¹ f e^{-U_N/2}` has the weak gradient `(√K_N)⁻¹ ((∇f) e^{-U_N/2} - ½ f e^{-U_N/2} ∇U_N)`,
so `|∇Ψ|² ≤ 2 p_N |∇f|² + ½ p_N f² |∇U_N|²` a.e.
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N)

include hyp in
theorem centeredPartition_pos (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    0 < centeredPartition W μ N := by
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μ N
  have hK : rexp (-BU) ≤ centeredPartition W μ N := by
    unfold centeredPartition
    have := integral_mono (μ := Measure.pi fun _ : Fin N => μ) (integrable_const (rexp (-BU)))
      (Integrable.of_bound ((measurable_Ucentered hyp μ N).neg.exp).aestronglyMeasurable (rexp BU)
        (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.2 (by
            have := hBU X; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith)))
      (fun X => Real.exp_le_exp.2 (by
        have := hBU X; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith))
    simpa using this
  exact (Real.exp_pos _).trans_le hK

theorem sqrt_dens_eq (μ : Measure (Torus d)) (X : Config N d) :
    Real.sqrt (rexp (-Ucentered W μ N X) / centeredPartition W μ N) =
      (Real.sqrt (centeredPartition W μ N))⁻¹ * gsE W μ N (flat X) := by
  rw [Real.sqrt_div (Real.exp_pos _).le, ← Real.exp_half, div_eq_inv_mul]
  rfl

include hyp hμ in
theorem ae_pi_of_ae_volume {p : UnitAddTorus (Fin N × Fin d) → Prop}
    (h : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))), p y) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))), p (flat X) := by
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  exact (pi_ac_volume (minimizer_ac hyp hμ) N).ae_le (hmp.quasiMeasurePreserving.ae h)

include hyp hμ in
theorem pi_map_flat_ac :
    (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))).map flat ≪
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  rw [← map_flat_volume N]
  exact (pi_ac_volume (minimizer_ac hyp hμ) N).map measurable_flat

include hyp hμ in
theorem lintegral_gibbs_eq (g : Config N d → ℝ≥0∞) :
    ∫⁻ X, g X ∂gibbs V W N = ∫⁻ X, ENNReal.ofReal (rexp (-Ucentered W μ N X) /
      centeredPartition W μ N) * g X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  rw [gibbs_eq_centered_aux hyp hμ N]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (ENNReal.measurable_ofReal.comp (((measurable_Ucentered hyp _ N).neg.exp).div_const _))
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g

/-- The weak gradient of `Ψ ∘ unflat`. -/
noncomputable def gsPsiG (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ)
    (f : Config N d → ℝ) (y : UnitAddTorus (Fin N × Fin d)) (k : Fin N × Fin d) : ℝ :=
  (Real.sqrt (centeredPartition W μ N))⁻¹ * (weakGrad (f ∘ unflat) y k * gsE W μ N y +
    (f ∘ unflat) y * (-(1 / 2) * gsE W μ N y * gsG W μ N y k))

include hyp hμ hN in
theorem isWeakGrad_psi {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    IsWeakGrad ((fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / centeredPartition W μ N))
      ∘ unflat) (gsPsiG W μ N f) := by
  obtain ⟨hFw, hFi, hgFi⟩ := memH1C_data hyp hf
  have h := (isWeakGrad_mul_gsE hyp (minimizer_ac hyp hμ) hN hFw hFi hgFi).cmul
    (Real.sqrt (centeredPartition W μ N))⁻¹
  convert h using 1
  · funext y
    simp only [Function.comp_apply, sqrt_dens_eq]
    rw [show flat (unflat y) = y from rfl]
    ring
  · rfl

/-- `|∇Ψ|²` bound, pointwise in the explicit gradient. -/
theorem sqNorm_gsPsiG_le (f : Config N d → ℝ) (μ : Measure (Torus d)) (hK : 0 < centeredPartition W μ N)
    (y : UnitAddTorus (Fin N × Fin d)) :
    sqNorm (gsPsiG W μ N f y) ≤
      2 * (rexp (-Ucentered W μ N (unflat y)) / centeredPartition W μ N) *
          sqNorm (weakGrad (f ∘ unflat) y) +
        1 / 2 * (rexp (-Ucentered W μ N (unflat y)) / centeredPartition W μ N) *
          (f (unflat y)) ^ 2 * sqNorm (gsG W μ N y) := by
  have he : gsE W μ N y ^ 2 = rexp (-Ucentered W μ N (unflat y)) := by
    rw [gsE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hs : ((Real.sqrt (centeredPartition W μ N))⁻¹) ^ 2 = (centeredPartition W μ N)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hK.le]
  unfold sqNorm gsPsiG
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  set a := weakGrad (f ∘ unflat) y k * gsE W μ N y
  set b := (f ∘ unflat) y * (-(1 / 2) * gsE W μ N y * gsG W μ N y k)
  have h2 : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have ha : a ^ 2 = rexp (-Ucentered W μ N (unflat y)) * weakGrad (f ∘ unflat) y k ^ 2 := by
    simp only [a]; rw [mul_pow, he]; ring
  have hb : 2 * b ^ 2 = 1 / 2 * rexp (-Ucentered W μ N (unflat y)) * (f (unflat y)) ^ 2 *
      gsG W μ N y k ^ 2 := by
    simp only [b, Function.comp_apply]; rw [show (f (unflat y) * (-(1 / 2) * gsE W μ N y *
      gsG W μ N y k)) ^ 2 = 1 / 4 * gsE W μ N y ^ 2 * f (unflat y) ^ 2 * gsG W μ N y k ^ 2 by ring,
      he]; ring
  rw [mul_pow, hs]
  have hK' : 0 ≤ (centeredPartition W μ N)⁻¹ := inv_nonneg.2 hK.le
  calc (centeredPartition W μ N)⁻¹ * (a + b) ^ 2 ≤ (centeredPartition W μ N)⁻¹ * (2 * a ^ 2 + 2 * b ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hK'
    _ = _ := by rw [mul_add, hb, ha]; field_simp

end

end SharpLSI
