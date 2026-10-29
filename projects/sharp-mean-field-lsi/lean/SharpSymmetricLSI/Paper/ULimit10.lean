import SharpSymmetricLSI.Paper.ULimit9

/-!
# R26 assembly: (6.6)–(6.9) (Phase 3, lane D)
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section assembly
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

/-- The kernel data with a measurable modification of the eigenbasis. -/
theorem kerData_mk :
    KerData (μ : Measure (Torus d)) (centeredKernel W μ)
      (fun i => (he.memLp i).aestronglyMeasurable.mk (e i)) (Tmat W μ e) := by
  set μm := (μ : Measure (Torus d))
  set e' : ℕ → Torus d → ℝ := fun i => (he.memLp i).aestronglyMeasurable.mk (e i)
  have hae : ∀ i, e i =ᵐ[μm] e' i := fun i => (he.memLp i).aestronglyMeasurable.ae_eq_mk
  refine ⟨measurable_centeredKernel hyp μm, centeredKernel_bdd hyp μm, centeredKernel_symm' hyp μ,
    fun w => ?_, fun i => (he.memLp i).aestronglyMeasurable.stronglyMeasurable_mk.measurable,
    fun i => (he.memLp i).ae_eq (hae i), fun i j => ?_, fun i => ?_, fun a b => ?_,
    hasSum_Tmat_sq hyp hμ he⟩
  · simp_rw [centeredKernel_symm' hyp μ _ w]; exact integral_centeredKernel hyp _ w
  · rw [← he.orthonormal i j]
    refine integral_congr_ae ?_
    filter_upwards [hae i, hae j] with x h1 h2
    rw [h1, h2]
  · have h := he.orthonormal (i + 1) 0
    simp only [he.zero, mul_one, Nat.add_one_ne_zero, if_false] at h
    rw [← h]
    exact integral_congr_ae (hae (i + 1)).symm
  · unfold Tmat
    refine integral_congr_ae ?_
    filter_upwards [hae (a + 1)] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hae (b + 1)] with y hy
    rw [hx, hy]

theorem fluct_ae_eq (N J : ℕ) :
    (fun X : Config N d => fun n : Fin J => fluct e N n X) =ᵐ[Measure.pi fun _ : Fin N =>
      (μ : Measure (Torus d))]
      fun X => fun n : Fin J => zSum (fun i => (he.memLp i).aestronglyMeasurable.mk (e i)) N n X := by
  set μm := (μ : Measure (Torus d))
  set e' : ℕ → Torus d → ℝ := fun i => (he.memLp i).aestronglyMeasurable.mk (e i)
  have hae : ∀ i, e i =ᵐ[μm] e' i := fun i => (he.memLp i).aestronglyMeasurable.ae_eq_mk
  have hcomp : ∀ (i : ℕ) (l : Fin N), ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μm), e i (X l) = e' i (X l) :=
    fun i l => by
      have hmp := measurePreserving_eval (fun _ : Fin N => μm) l
      exact hmp.quasiMeasurePreserving.ae_eq (hae i)
  have hall : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μm), ∀ (n : Fin J) (l : Fin N),
      e (n + 1) (X l) = e' (n + 1) (X l) := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro l; exact hcomp _ l
  filter_upwards [hall] with X hX
  funext n
  unfold fluct zSum
  rw [Real.rpow_neg (Nat.cast_nonneg N), ← Real.sqrt_eq_rpow]
  congr 1
  exact Finset.sum_congr rfl fun l _ => hX n l

/-- **(6.6)–(6.9).** -/
theorem U_limit_aux :
    (∀ N : ℕ, 1 ≤ N → ∀ X : Config N d, Ucentered W μ N X =
      (N : ℝ)⁻¹ * (∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0) +
        (2 * (N : ℝ))⁻¹ * ∑ i, centeredKernel W μ (X i) (X i)) ∧
    (∀ N : ℕ, 1 ≤ N →
      ∫ X, ((N : ℝ)⁻¹ * ∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0) ^ 2
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        ((N : ℝ) - 1) / (2 * N) * ∫ x, ∫ y, centeredKernel W μ x y ^ 2
          ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d))) ∧
    (∃ Q, IsSecondChaos (Tmat W μ e) Q) ∧
    ∀ Q, IsSecondChaos (Tmat W μ e) Q → ∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (Ucentered W μ N X, fun n => fluct e N n X)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, g (Uinf W μ Q z, fun n => z n) ∂gammaRef)) := by
  refine ⟨fun N _ X => Ucentered_decomp hyp μ X, fun N hN => integral_offdiag_centered_sq hyp μ hN,
    exists_secondChaos_Tmat hyp hμ he, fun Q hQ J g => ?_⟩
  set μm := (μ : Measure (Torus d))
  set e' : ℕ → Torus d → ℝ := fun i => (he.memLp i).aestronglyMeasurable.mk (e i)
  have hD := kerData_mk hyp hμ he
  have h := TendstoInDistribution.tendsto_integral_bcf (tendstoInDistribution_Ugen hD J hQ) g
  refine h.congr fun N => ?_
  have hrm : Measurable fun (ω : ℕ → Torus d) (i : Fin N) => ω i := by fun_prop
  have hFm : Measurable fun X : Config N d =>
      g (Ugen (centeredKernel W μ) N X, fun n : Fin J => zSum e' N n X) := by
    refine g.continuous.measurable.comp (Measurable.prodMk ?_ ?_)
    · unfold Ugen
      exact (Finset.measurable_sum (f := fun (i : Fin N) (X : Config N d) =>
          ∑ j : Fin N, centeredKernel W μ (X i) (X j)) _
        fun i _ => Finset.measurable_sum (f := fun (j : Fin N) (X : Config N d) =>
          centeredKernel W μ (X i) (X j)) _
        fun j _ => hD.meas.comp (f := fun X : Config N d => (X i, X j))
          ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).const_mul _
    · refine measurable_pi_iff.mpr fun n => ?_
      unfold zSum
      exact (Finset.measurable_sum (f := fun (l : Fin N) (X : Config N d) => e' (n + 1) (X l)) _
        fun l _ => (hD.emeas _).comp (measurable_pi_apply l)).const_mul _
  have e1 := integral_map (μ := Measure.infinitePi fun _ : ℕ => μm) hrm.aemeasurable
    hFm.aestronglyMeasurable
  rw [infinitePi_map_fin μm N] at e1
  rw [← e1]
  refine integral_congr_ae ?_
  filter_upwards [fluct_ae_eq hyp hμ he N J] with X hX
  rw [hX]
  rfl

end assembly

end SharpLSI
