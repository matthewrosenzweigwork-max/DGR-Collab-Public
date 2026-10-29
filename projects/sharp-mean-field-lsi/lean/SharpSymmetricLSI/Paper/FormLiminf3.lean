import SharpSymmetricLSI.Paper.FormLiminf2
import SharpSymmetricLSI.Paper.GibbsVariational
import SharpSymmetricLSI.Paper.ELEquation

/-!
# R33 (8.20) groundwork: the eigenvalue equation in one particle variable (Sobolev case)

For `Φ ∈ W^{1,1}(𝕋^{N×d})` with weak gradient `G`,
`∫ G_{(l,·)}(X) · ∇e_i(X_l) dμ^{⊗N} = λ_i ∫ e_i(X_l) Φ dμ^{⊗N}`,
by mollification (`exists_smooth_approx`), the smooth case, and `μ^{⊗N} ≤ C·vol`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- `μ^{⊗N} ≤ C · vol`. -/
theorem pi_le_smul_volume (N : ℕ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C • (volume : Measure (Config N d)) := by
  obtain ⟨c, Cu, L, hc, hbd⟩ := elDensity_bounds hyp
  obtain ⟨hb, -⟩ := hbd (μ : Measure (Torus d)) inferInstance
  set p := elDens V W (μ : Measure (Torus d))
  have hp0 : ∀ x, 0 ≤ p x := fun x => hc.le.trans (hb x).1
  have hpm : Measurable p := (elDensity_props hyp (μ : Measure (Torus d))).1
  have hpi : Integrable p (haar d) := integrable_of_bdd hpm (C := Cu) fun x => by
    rw [abs_of_nonneg (hp0 x)]; exact (hb x).2
  have hμp : (μ : Measure (Torus d)) = (haar d).withDensity (fun x => ENNReal.ofReal (p x)) :=
    minimizer_eq_elDensity hyp hμ
  refine ⟨ENNReal.ofReal (Cu ^ N), ENNReal.ofReal_ne_top, ?_⟩
  rw [hμp, pi_withDensity_ofReal hpm hp0 hpi, ← withDensity_const]
  refine withDensity_mono (Eventually.of_forall fun X => ENNReal.ofReal_le_ofReal ?_)
  calc ∏ i, p (X i) ≤ ∏ _i : Fin N, Cu := by
        exact Finset.prod_le_prod₀ (fun i _ => hp0 _) (fun i _ => (hb _).2)
    _ = Cu ^ N := by simp

theorem integrable_pi_comp {N : ℕ} {B : UnitAddTorus (Fin N × Fin d) → ℝ} (hB : Integrable B volume)
    {c : Config N d → ℝ} (hc : Measurable c) {Cc : ℝ} (hCc : ∀ X, |c X| ≤ Cc) :
    Integrable (fun X => B (flat X) * c X) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  obtain ⟨C, hC, hle⟩ := pi_le_smul_volume hyp hμ N
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have h1 : Integrable (fun X => B (flat X)) (volume : Measure (Config N d)) :=
    (hmp.integrable_comp hB.aestronglyMeasurable).2 hB
  have h2 := (h1.smul_measure hC).mono_measure hle
  exact h2.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs]; exact hCc X)

/-- Transfer of `L¹(vol)` convergence on `𝕋^{N×d}` to integrals under `μ^{⊗N}` against bounded
weights. -/
theorem tendsto_integral_pi_of_L1 {N : ℕ} {A : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ}
    {A0 : UnitAddTorus (Fin N × Fin d) → ℝ} (hA : ∀ n, Integrable (A n) volume)
    (hA0 : Integrable A0 volume) (hlim : Tendsto (fun n => ∫⁻ y, ‖A n y - A0 y‖ₑ) atTop (𝓝 0))
    {c : Config N d → ℝ} (hc : Measurable c) {Cc : ℝ} (hCc : ∀ X, |c X| ≤ Cc) :
    Tendsto (fun n => ∫ X, A n (flat X) * c X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))
      atTop (𝓝 (∫ X, A0 (flat X) * c X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))) := by
  obtain ⟨C, hC, hle⟩ := pi_le_smul_volume hyp hμ N
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have hint : ∀ {B : UnitAddTorus (Fin N × Fin d) → ℝ}, Integrable B volume →
      Integrable (fun X => B (flat X) * c X) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) :=
    fun {B} hB => by
      have h1 : Integrable (fun X => B (flat X)) (volume : Measure (Config N d)) :=
        (hmp.integrable_comp hB.aestronglyMeasurable).2 hB
      have h2 := (h1.smul_measure hC).mono_measure hle
      exact h2.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hCc X)
  refine tendsto_integral_of_L1 _ (hint hA0).aestronglyMeasurable (Eventually.of_forall fun n => hint (hA n)) ?_
  have hCc0 : 0 ≤ Cc := (abs_nonneg _).trans (hCc 0)
  have hbound : ∀ n, ∫⁻ X, ‖A n (flat X) * c X - A0 (flat X) * c X‖ₑ
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
      C * ENNReal.ofReal Cc * ∫⁻ y, ‖A n y - A0 y‖ₑ := fun n => by
    calc ∫⁻ X, ‖A n (flat X) * c X - A0 (flat X) * c X‖ₑ
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))
        ≤ ∫⁻ X, ENNReal.ofReal Cc * ‖A n (flat X) - A0 (flat X)‖ₑ
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
          refine lintegral_mono fun X => ?_
          rw [← sub_mul, enorm_mul, mul_comm]
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hCc X)
      _ ≤ ∫⁻ X, ENNReal.ofReal Cc * ‖A n (flat X) - A0 (flat X)‖ₑ ∂(C • volume) :=
          lintegral_mono' hle le_rfl
      _ = C * (ENNReal.ofReal Cc * ∫⁻ X, ‖A n (flat X) - A0 (flat X)‖ₑ ∂volume) := by
          rw [lintegral_smul_measure, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul]
      _ = C * ENNReal.ofReal Cc * ∫⁻ y, ‖A n y - A0 y‖ₑ := by
          rw [mul_assoc, hmp.lintegral_comp_emb (flatEquiv N d).measurableEmbedding
            (fun y => ‖A n y - A0 y‖ₑ)]
  have h0 : Tendsto (fun n => C * ENNReal.ofReal Cc * ∫⁻ y, ‖A n y - A0 y‖ₑ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := C * ENNReal.ofReal Cc) hlim
      (Or.inr (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top))
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hbound

end

end SharpLSI
