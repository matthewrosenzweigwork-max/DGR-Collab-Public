/- Development: arbitrary centered L2 linear observable adjoined to the finite
quadratic statistic on the SAME full indexed Gaussian process. -/
import DGRHS.CLT.FiniteJointChaosCLT
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma inner_finiteEigenFeature_coord {j E : Type*} [Fintype j]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ) (x : S) (l : j) :
    inner ℝ (b l) (finiteEigenFeature b e x) = e l x := by
  classical
  unfold finiteEigenFeature
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Genuine finite particle joint law. Only actual L2 observables and their
centers are required; no fourth spatial moment or favorable Gaussian law. -/
theorem finiteParticleJointReadoutCLT {j ι : Type*} [Fintype j] [Countable ι]
    (a : j → ℝ) (e : j → Lp ℝ 2 μ) (he : ∀ i, (∫ x, e i x ∂μ) = 0)
    (v : Lp ℝ 2 μ) (hv : (∫ x, v x ∂μ) = 0)
    (h : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (f : ι → ℕ) (hf : Function.Injective f) :
    TendstoInDistribution
      (fun N (x : Fin N → S) =>
        ((Real.sqrt N)⁻¹ * ∑ i : Fin N, v (x i),
          DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel a e) x)) atTop
      (fun ω => (DGRHS.Gaussian.indexedGaussianIsometry h f hf v ω,
        ∑ i, a i * ((DGRHS.Gaussian.indexedGaussianIsometry h f hf (e i) ω)^2 - ‖e i‖^2)))
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  let J := Unit ⊕ j
  let B : HilbertBasis J ℝ (EuclideanSpace ℝ J) := (EuclideanSpace.basisFun J ℝ).toHilbertBasis
  let A : J → ℝ := Sum.elim (fun _ => 0) a
  let E : J → Lp ℝ 2 μ := Sum.elim (fun _ => v) e
  have hE : ∀ l, (∫ x, E l x ∂μ) = 0 := by
    intro l
    cases l with
    | inl u => exact hv
    | inr i => exact he i
  have hc := finiteParticleJointChaosCLT A B E hE h f hf
  have hk : finiteSpectralKernel A E = finiteSpectralKernel a e := by
    funext p
    unfold finiteSpectralKernel
    change (∑ l : Unit ⊕ j, A l * E l p.1 * E l p.2) = _
    rw [Fintype.sum_sum_type]
    simp [A, E]
  let P : (EuclideanSpace ℝ J) × ℝ → ℝ × ℝ :=
    fun p => (inner ℝ (B (Sum.inl ())) p.1,p.2)
  have ht := hc.continuous_comp (g := P) (by dsimp [P]; fun_prop)
  apply ht.congr
  · intro N
    filter_upwards [] with x
    change (inner ℝ (B (Sum.inl ())) ((Real.sqrt N)⁻¹ • ∑ i : Fin N, finiteEigenFeature B E (x i)),
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel A E) x) = _
    rw [hk, inner_smul_right, inner_sum]
    simp only [inner_finiteEigenFeature_coord, E, Sum.elim_inl, smul_eq_mul]
  · filter_upwards [] with ω
    change (inner ℝ (B (Sum.inl ())) (finiteEigenFeature B
      (fun l => DGRHS.Gaussian.indexedGaussianIsometry h f hf (E l)) ω),
      finiteSpectralQuadratic A B (finiteEigenFeature B
        (fun l => DGRHS.Gaussian.indexedGaussianIsometry h f hf (E l)) ω) -
        ∑ l, A l * ‖E l‖^2) = _
    rw [inner_finiteEigenFeature_coord]
    apply Prod.ext
    · rfl
    · unfold finiteSpectralQuadratic
      simp only [inner_finiteEigenFeature_coord]
      rw [← Finset.sum_sub_distrib]
      change (∑ l : Unit ⊕ j, (A l *
        (DGRHS.Gaussian.indexedGaussianIsometry h f hf (E l) ω)^2 - A l * ‖E l‖^2)) = _
      rw [Fintype.sum_sum_type]
      simp only [A, E, Sum.elim_inl, Sum.elim_inr, zero_mul,
        sub_self, Finset.sum_const_zero, zero_add]
      exact Finset.sum_congr rfl (fun i _ => by ring)
end DGRHS.CLT
#print axioms DGRHS.CLT.inner_finiteEigenFeature_coord
#print axioms DGRHS.CLT.finiteParticleJointReadoutCLT
#check @DGRHS.CLT.finiteParticleJointReadoutCLT
