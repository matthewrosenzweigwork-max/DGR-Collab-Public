import SharpSymmetricLSI.Paper.Occ14
import SharpSymmetricLSI.Paper.Occ8
import SharpSymmetricLSI.Paper.Moser5

/-!
# R28 assembly (Phase 3, lane D)

The reference eigenfunctions are essentially bounded (Moser iteration with the Nash inequality on
`𝕋^d`, `Paper/Moser1-5.lean`), which gives the uniform moments; all clauses of Section 7.1.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section bdd
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- `μ ≤ C m` for the minimizer. -/
theorem minimizer_le_smul_haar : ∃ C : ℝ, 0 < C ∧
    (μ : Measure (Torus d)) ≤ ENNReal.ofReal C • haar d := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  have hμp := minimizer_eq_elDensity hyp hμ
  have hC : 0 < C := lt_of_lt_of_le hc
    (((hb (μ : Measure (Torus d)) inferInstance).1 0).1.trans
      ((hb (μ : Measure (Torus d)) inferInstance).1 0).2)
  refine ⟨C, hC, Measure.le_iff.mpr fun s hs => ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, hμp, densMeasure, withDensity_apply _ hs,
    ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    ((hb (μ : Measure (Torus d)) inferInstance).1 x).2

/-- **The reference eigenfunctions are essentially bounded.** -/
theorem refEigen_bounded {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (j : ℕ) :
    ∃ C, ∀ᵐ x ∂(μ : Measure (Torus d)), |e j x| ≤ C := by
  obtain ⟨a, ha⟩ := haar_le_smul_minimizer hyp hμ (d := d)
  obtain ⟨b, hb0, hb⟩ := minimizer_le_smul_haar hyp hμ
  -- `a > 0`
  have ha0 : 0 < a := by
    by_contra h
    push Not at h
    have h1 := ha.trans (le_of_eq (by rw [ENNReal.ofReal_of_nonpos h, zero_smul]))
    have := measure_univ (μ := haar d)
    have h2 : haar d Set.univ ≤ 0 := by simpa using h1 Set.univ
    rw [this] at h2
    exact absurd h2 (by norm_num)
  have hlam : 0 ≤ lam j := by
    have h := he.eigen j (e j) (he.memH1 j)
    simp only [he.orthonormal j j, ↓reduceIte, mul_one] at h
    rw [← h]
    exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  refine ⟨_, (ac_of_le_smul hb).ae_le (ae_abs_le_moser ha0 hb0 ha hb (he.memH1 j) hlam
    (he.eigen j))⟩

/-- **Section 7.1, all clauses.** -/
theorem occupation_basis_aux {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    (∀ N : ℕ, ∀ α β : ℕ →₀ ℕ, occSize α ≤ N → occSize β ≤ N →
      IsSymmetric (occBasis e α N) ∧
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (occBasis e α N) ∧
      ∫ X, occBasis e α N X * occBasis e β N X
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) = (if α = β then 1 else 0) ∧
      ∫ X, ∑ i, ∑ k, weakGradC (occBasis e α N) X i k * weakGradC (occBasis e β N) X i k
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        (if α = β then occEnergy lam α else 0)) ∧
    (∀ N : ℕ, ∀ f : Config N d → ℝ,
      MemLp f 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) → IsSymmetric f →
      (∀ α : ℕ →₀ ℕ, occSize α ≤ N → ∫ X, f X * occBasis e α N X
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) = 0) →
      f =ᵐ[Measure.pi fun _ : Fin N => (μ : Measure (Torus d))] 0) ∧
    (∀ α β : ℕ →₀ ℕ, ∫ z, hermiteBasis α z * hermiteBasis β z ∂gammaRef =
      if α = β then 1 else 0) ∧
    (∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 gammaRef → (∀ α, ∫ z, F z * hermiteBasis α z ∂gammaRef = 0) →
      F =ᵐ[gammaRef] 0) ∧
    (∀ (A : Finset (ℕ →₀ ℕ)) (J : ℕ) (g : (A → ℝ) × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (fun α => occBasis e α N X, fun n => fluct e N n X)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, g (fun α => hermiteBasis α z, fun n => z n) ∂gammaRef))) ∧
    ∀ (α : ℕ →₀ ℕ) (p : ℕ), ∃ C : ℝ, ∀ N : ℕ, occSize α ≤ N →
      ∫ X, |occBasis e α N X| ^ p ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C :=
  ⟨fun N α β hα hβ => ⟨occBasis_symmetric e α N, memH1C_occBasis hyp hμ he α N,
      integral_occBasis_mul he.memLp he.orthonormal hα hβ, dirichlet_occBasis hyp hμ he hα hβ⟩,
    fun N f hf hfs horth => occBasis_complete he f hf hfs horth,
    integral_hermiteBasis_mul,
    fun F hF horth => hermiteBasis_complete hF horth,
    fun A J g => tendsto_occBasis_joint he A J g,
    occBasis_moments_of_bdd he (refEigen_bounded hyp hμ he)⟩

end bdd

end SharpLSI
