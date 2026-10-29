import SharpSymmetricLSI.Paper.GaussForm3

/-!
# R33 groundwork: finite-dimensional marginals of a centered Gaussian with covariance `C`

Two probabilities `γ, γ'` on `ℝ^ℕ` that are both `IsCenteredGaussianCov _ C` have the same law of
`(z_0, …, z_{N-1})` (characteristic functions), hence the same integrals of cylinder functions.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix WithLp Complex
open scoped NNReal ENNReal RealInnerProductSpace

namespace SharpLSI

variable {C : ℕ → ℕ → ℝ}

theorem charFun_map_toLp_block {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) {N : ℕ}
    (t : EuclideanSpace ℝ (Fin N)) :
    charFun ((γ.map (zBlock N)).map (WithLp.toLp 2)) t =
      charFun (gaussianReal 0 (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        extVec (ofLp t) i * C i j * extVec (ofLp t) j).toNNReal) 1 := by
  rw [charFun_apply, integral_map (measurable_toLp 2 _).aemeasurable (by fun_prop),
    integral_map (measurable_zBlock N).aemeasurable (by fun_prop)]
  set tt : Fin N → ℝ := ofLp t
  have hlin : ∀ z : ℕ → ℝ, ⟪toLp 2 (zBlock N z), t⟫ = ∑ i ∈ Finset.range N, extVec tt i * z i := by
    intro z
    rw [sum_range_extVec, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zBlock, tt, mul_comm]
  simp_rw [hlin]
  have hm : Measurable fun z : ℕ → ℝ => ∑ i ∈ Finset.range N, extVec tt i * z i :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  rw [← hγ.2 (Finset.range N) (extVec tt), charFun_apply,
    integral_map hm.aemeasurable (by fun_prop)]
  simp

theorem map_zBlock_eq_of_cov {γ γ' : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hγ' : IsCenteredGaussianCov γ' C) (N : ℕ) : γ.map (zBlock N) = γ'.map (zBlock N) := by
  have := hγ.1; have := hγ'.1
  have key : (γ.map (zBlock N)).map (WithLp.toLp 2) = (γ'.map (zBlock N)).map (WithLp.toLp 2) :=
    Measure.ext_of_charFun (funext fun t => by
      rw [charFun_map_toLp_block hγ, charFun_map_toLp_block hγ'])
  have hinv : ∀ ν : Measure (Fin N → ℝ), (ν.map (WithLp.toLp 2)).map (WithLp.ofLp) = ν := by
    intro ν
    rw [Measure.map_map (measurable_ofLp 2 _) (measurable_toLp 2 _)]
    exact Measure.map_id
  rw [← hinv (γ.map _), key, hinv]

/-- Cylinder integrals agree. -/
theorem integral_cyl_eq_of_cov {γ γ' : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hγ' : IsCenteredGaussianCov γ' C) {J : ℕ} {g : (Fin J → ℝ) → ℝ} (hg : Measurable g) :
    ∫ z, g (fun n => z n) ∂γ = ∫ z, g (fun n => z n) ∂γ' := by
  have h1 : ∫ z, g (fun n => z n) ∂γ = ∫ y, g y ∂(γ.map (zBlock J)) :=
    (integral_map (measurable_zBlock J).aemeasurable hg.aestronglyMeasurable).symm
  have h2 : ∫ z, g (fun n => z n) ∂γ' = ∫ y, g y ∂(γ'.map (zBlock J)) :=
    (integral_map (measurable_zBlock J).aemeasurable hg.aestronglyMeasurable).symm
  rw [h1, h2, map_zBlock_eq_of_cov hγ hγ' J]

theorem lintegral_cyl_eq_of_cov {γ γ' : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hγ' : IsCenteredGaussianCov γ' C) {J : ℕ} {g : (Fin J → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (fun n => z n) ∂γ = ∫⁻ z, g (fun n => z n) ∂γ' := by
  have h1 : ∫⁻ z, g (fun n => z n) ∂γ = ∫⁻ y, g y ∂(γ.map (zBlock J)) :=
    (lintegral_map hg (measurable_zBlock J)).symm
  have h2 : ∫⁻ z, g (fun n => z n) ∂γ' = ∫⁻ y, g y ∂(γ'.map (zBlock J)) :=
    (lintegral_map hg (measurable_zBlock J)).symm
  rw [h1, h2, map_zBlock_eq_of_cov hγ hγ' J]

/-- **Uniqueness**: a centered Gaussian on `ℝ^ℕ` is determined by its covariance (cylinder sets). -/
theorem eq_of_isCenteredGaussianCov {γ γ' : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hγ' : IsCenteredGaussianCov γ' C) : γ = γ' := by
  have := hγ.1; have := hγ'.1
  refine ext_of_generate_finite (measurableCylinders fun _ : ℕ => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun t ht => ?_)
    (by simp)
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  obtain ⟨N, hN⟩ : ∃ N, N = s.sup id + 1 := ⟨_, rfl⟩
  have hlt : ∀ i ∈ s, i < N := fun i hi => by
    rw [hN]; exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  let R : (Fin N → ℝ) → (s → ℝ) := fun y i => y ⟨i, hlt i i.2⟩
  have hR : Measurable R := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hcyl : cylinder s S = zBlock N ⁻¹' (R ⁻¹' S) := by ext f; rfl
  rw [hcyl, ← Measure.map_apply (measurable_zBlock N) (hR hS),
    ← Measure.map_apply (measurable_zBlock N) (hR hS), map_zBlock_eq_of_cov hγ hγ' N]

end SharpLSI
