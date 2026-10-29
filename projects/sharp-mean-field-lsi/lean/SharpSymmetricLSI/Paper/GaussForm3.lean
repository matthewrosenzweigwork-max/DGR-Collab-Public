import SharpSymmetricLSI.Paper.GaussForm2
import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# R32 (A3): finite blocks of `γ` and Stein's lemma under `γ`

If `γ` is centered Gaussian with covariance `C` (`IsCenteredGaussianCov`) and the zBlock
`S = (C_{ij})_{i,j<N}` is positive semidefinite, the law of `(z_0, …, z_{N-1})` is the image of
the standard Gaussian under `√S` (`map_block_eq`), hence
`∫ z_k g(z_{<N}) dγ = ∑_l C_{kl} ∫ ∂_l g(z_{<N}) dγ` (`stein_gamma`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix WithLp Complex
open scoped NNReal MatrixOrder RealInnerProductSpace

namespace SharpLSI

/-- The zBlock `(C_{ij})_{i,j<N}`. -/
def blockMat (C : ℕ → ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => C i j

/-- The first `N` coordinates. -/
def zBlock (N : ℕ) (z : ℕ → ℝ) : Fin N → ℝ := fun i => z i

theorem measurable_zBlock (N : ℕ) : Measurable (zBlock N) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply _

/-- The extension by zero of a vector on `Fin N`. -/
def extVec {N : ℕ} (t : Fin N → ℝ) (i : ℕ) : ℝ := if h : i < N then t ⟨i, h⟩ else 0

theorem sum_range_extVec {N : ℕ} (t : Fin N → ℝ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range N, extVec t i * f i = ∑ i : Fin N, t i * f i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => extVec t i * f i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [extVec, i.isLt]

theorem quad_extVec {N : ℕ} (t : Fin N → ℝ) (C : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, extVec t i * C i j * extVec t j =
      t ⬝ᵥ blockMat C N *ᵥ t := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range N, extVec t i * C i j * extVec t j)]
  simp only [dotProduct, mulVec, blockMat, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => extVec t i * C i j * extVec t j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [extVec, i.isLt, j.isLt]; ring

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

/-- The law of the zBlock, in `EuclideanSpace`, is `N(0, S)`. -/
theorem map_toLp_block (hγ : IsCenteredGaussianCov γ C) {N : ℕ} (hS : (blockMat C N).PosSemidef) :
    (γ.map (zBlock N)).map (WithLp.toLp 2) = multivariateGaussian 0 (blockMat C N) := by
  haveI := hγ.1
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hS, charFun_apply,
    integral_map (measurable_toLp 2 _).aemeasurable (by fun_prop),
    integral_map (measurable_zBlock N).aemeasurable (by fun_prop)]
  set tt : Fin N → ℝ := ofLp t
  have hlin : ∀ z : ℕ → ℝ, ⟪toLp 2 (zBlock N z), t⟫ = ∑ i ∈ Finset.range N, extVec tt i * z i := by
    intro z
    rw [sum_range_extVec, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zBlock, tt, mul_comm]
  simp_rw [hlin]
  have h1 := hγ.2 (Finset.range N) (extVec tt)
  have h2 : ∫ z, cexp (↑(∑ i ∈ Finset.range N, extVec tt i * z i) * I) ∂γ =
      charFun (γ.map fun z => ∑ i ∈ Finset.range N, extVec tt i * z i) 1 := by
    have hm : Measurable fun z : ℕ → ℝ => ∑ i ∈ Finset.range N, extVec tt i * z i :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
    rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
    simp
  rw [h2, h1, charFun_gaussianReal, quad_extVec]
  have hq : 0 ≤ tt ⬝ᵥ blockMat C N *ᵥ tt := by
    have := hS.dotProduct_mulVec_nonneg tt
    simpa using this
  simp [Real.coe_toNNReal _ hq, tt]

/-- **The law of the zBlock** is the image of the standard Gaussian under `√S`. -/
theorem map_block_eq (hγ : IsCenteredGaussianCov γ C) {N : ℕ} (hS : (blockMat C N).PosSemidef) :
    γ.map (zBlock N) = (Measure.pi fun _ : Fin N => gaussianReal 0 1).map
      (fun y => CFC.sqrt (blockMat C N) *ᵥ y) := by
  set A := CFC.sqrt (blockMat C N)
  have hR : ((Measure.pi fun _ : Fin N => gaussianReal 0 1).map (fun y => A *ᵥ y)).map
      (WithLp.toLp 2) = multivariateGaussian 0 (blockMat C N) := by
    have hAm : Measurable fun y : Fin N → ℝ => A *ᵥ y := (matCLM A).continuous.measurable
    rw [Measure.map_map (measurable_toLp 2 _) hAm, multivariateGaussian,
      ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (measurable_toLp 2 _)]
    congr 1
    funext y
    simp [A]
  have h := (map_toLp_block hγ hS).trans hR.symm
  have hinj := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin N)) => ν.map (WithLp.ofLp)) h
  simp only at hinj
  rw [Measure.map_map (measurable_ofLp 2 _) (measurable_toLp 2 _),
    Measure.map_map (measurable_ofLp 2 _) (measurable_toLp 2 _)] at hinj
  have hid : (WithLp.ofLp ∘ WithLp.toLp 2 : (Fin N → ℝ) → Fin N → ℝ) = id := rfl
  rwa [hid, Measure.map_id, Measure.map_id] at hinj

theorem sqrt_mul_transpose {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S)ᵀ = S := by
  have hsa : IsSelfAdjoint (CFC.sqrt S) := (CFC.sqrt_nonneg S).isSelfAdjoint
  have ht : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [ht]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

/-- **Stein's lemma under `γ`** for functions of the first `N` coordinates. -/
theorem stein_gamma (hγ : IsCenteredGaussianCov γ C) {N : ℕ} (hS : (blockMat C N).PosSemidef)
    {g : (Fin N → ℝ) → ℝ} (hg : Differentiable ℝ g) (hgc : Continuous fun y => fderiv ℝ g y)
    {B : ℝ} (hgB : ∀ y, |g y| ≤ B) (hdB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (k : Fin N) :
    ∫ z, z k * g (zBlock N z) ∂γ =
      ∑ l : Fin N, C k l * ∫ z, fderiv ℝ g (zBlock N z) (Pi.single l 1) ∂γ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := k.isLt; omega⟩
  set A := CFC.sqrt (blockMat C (n + 1))
  set P := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
  have hAm : Measurable fun y : Fin (n + 1) → ℝ => A *ᵥ y := (matCLM A).continuous.measurable
  have hmap := map_block_eq hγ hS
  have htr : ∀ G : (Fin (n + 1) → ℝ) → ℝ, Continuous G →
      ∫ z, G (zBlock (n + 1) z) ∂γ = ∫ y, G (A *ᵥ y) ∂P := fun G hG => by
    rw [← integral_map (measurable_zBlock _).aemeasurable hG.aestronglyMeasurable, hmap,
      integral_map hAm.aemeasurable hG.aestronglyMeasurable]
  have hD : ∀ l : Fin (n + 1), Continuous fun y => fderiv ℝ g y (Pi.single l 1) := fun l =>
    hgc.clm_apply continuous_const
  have e1 : ∫ z, z k * g (zBlock (n + 1) z) ∂γ = ∫ y, (A *ᵥ y) k * g (A *ᵥ y) ∂P :=
    htr (fun x => x k * g x) ((continuous_apply k).mul hg.continuous)
  rw [e1, stein_matrix A hg hgc hgB hdB k, sqrt_mul_transpose hS]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [htr _ (hD l)]
  rfl

end SharpLSI
