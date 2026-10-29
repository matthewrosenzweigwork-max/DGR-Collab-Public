import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.FeatureMoments
import DGPS.Equilibrium.Hessian

/-!
# Density Hessian of the rough example at Haar measure (RUF028)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.6 (3.10).

At `m = haar 1` with the interaction `W = κ (1 - U ⊗ U)` the centered kernel is `-κ U ⊗ U`, so
`⟨h, H h⟩ = ‖h‖² - κ |∫ U h|²` on `L²_0(m)`.  By Bessel for the orthonormal system `√2 U₁, √2 U₂`
one has `|∫ U h|² ≤ ‖h‖²/2`, hence `⟨h, H h⟩ ≥ (1 - κ/2) ‖h‖² = ‖h‖²/12`.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

namespace DGPS.Examples.RoughBoundary.FreeEnergy

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.Model (modelData modelW kappa)

/-- The `i`-th coordinate of the feature, as a bounded continuous function. -/
noncomputable def UcompBCF {L : ℝ} (hL : 0 < L) (ε : ℝ) (i : Fin 2) : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => Ufeat L ε y i, (EuclideanSpace.proj i).continuous.comp (continuous_Ufeat hL ε)⟩

lemma inner_toLp_left (g : Torus 1 →ᵇ ℝ) (h : Lp ℝ 2 (haar 1)) :
    inner ℝ (BoundedContinuousFunction.toLp 2 (haar 1) ℝ g) h = ∫ y, g y * h y ∂(haar 1) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (haar 1) ℝ g] with y hy
  rw [hy]; simp [mul_comm]

lemma integrable_comp_mul {L : ℝ} (hL : 0 < L) (ε : ℝ) (i : Fin 2) (h : Lp ℝ 2 (haar 1)) :
    Integrable (fun y => Ufeat L ε y i * h y) (haar 1) := by
  have hc : Continuous (fun y => Ufeat L ε y i) :=
    (EuclideanSpace.proj i).continuous.comp (continuous_Ufeat hL ε)
  refine (Lp.memLp h).integrable (by norm_num) |>.bdd_mul (c := 1) hc.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  calc ‖Ufeat L ε y i‖ ≤ ‖Ufeat L ε y‖ := PiLp.norm_apply_le _ _
    _ = 1 := norm_Ufeat L ε y

/-- Bessel: `Σ_i (∫ U_i h)² ≤ ‖h‖² / 2`. -/
lemma bessel_feature {L : ℝ} (hL : 0 < L) (ε : ℝ) (h : Lp ℝ 2 (haar 1)) :
    ∑ i : Fin 2, (∫ y, Ufeat L ε y i * h y ∂(haar 1)) ^ 2 ≤ ‖h‖ ^ 2 / 2 := by
  set u : Fin 2 → Lp ℝ 2 (haar 1) :=
    fun i => Real.sqrt 2 • BoundedContinuousFunction.toLp 2 (haar 1) ℝ (UcompBCF hL ε i) with hu
  have hmom := (exact_shift_symmetries_and_feature_moments hL ε).1.2.2.2
  have hon : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hu, inner_smul_left, inner_smul_right, inner_toLp_left]
    have e : ∫ y, UcompBCF hL ε i y *
        (BoundedContinuousFunction.toLp 2 (haar 1) ℝ (UcompBCF hL ε j)) y ∂(haar 1) =
        ∫ y, Ufeat L ε y i * Ufeat L ε y j ∂(haar 1) := by
      refine integral_congr_ae ?_
      filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (haar 1) ℝ (UcompBCF hL ε j)]
        with y hy
      rw [hy]; rfl
    rw [e, hmom i j]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    by_cases hij : i = j
    · simp [hij]; nlinarith [h2]
    · simp [hij]
  have hb := hon.sum_inner_products_le h (s := Finset.univ)
  have hin : ∀ i, inner ℝ (u i) h = Real.sqrt 2 * ∫ y, Ufeat L ε y i * h y ∂(haar 1) := by
    intro i
    simp only [hu, inner_smul_left, conj_trivial]
    rw [inner_toLp_left]; rfl
  simp only [hin, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hb
  rw [← Finset.mul_sum] at hb
  linarith

/-- **RUF028.**  At Haar measure the density Hessian of the rough example satisfies, for every
centered `h ∈ L²_0(m)`, `⟨h, H h⟩ = ‖h‖² - κ |∫ U h dm|² ≥ (1 - κ/2) ‖h‖² = ‖h‖²/12`; in particular
it is coercive. -/
theorem rough_example_density_hessian {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    (1 - kappa / 2 = 1 / 12) ∧
    (∀ f : centeredL2 (haarProbability 1),
      inner ℝ f (densityHessian (modelData hL ε) (haarProbability 1) f) =
        ‖f‖ ^ 2 - kappa * ‖∫ y, ((f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) y) • Ufeat L ε y ∂(haar 1)‖ ^ 2 ∧
      (1 - kappa / 2) * ‖f‖ ^ 2 ≤
        ‖f‖ ^ 2 - kappa * ‖∫ y, ((f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) y) • Ufeat L ε y ∂(haar 1)‖ ^ 2 ∧
      ‖f‖ ^ 2 / 12 ≤
        inner ℝ f (densityHessian (modelData hL ε) (haarProbability 1) f)) ∧
    IsCoerciveDensityHessian (modelData hL ε) (haarProbability 1) := by
  have hk : 1 - kappa / 2 = 1 / 12 := by unfold kappa; norm_num
  have main : ∀ f : centeredL2 (haarProbability 1),
      inner ℝ f (densityHessian (modelData hL ε) (haarProbability 1) f) =
        ‖f‖ ^ 2 - kappa * ‖∫ y, ((f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) y) • Ufeat L ε y ∂(haar 1)‖ ^ 2 ∧
      ‖∫ y, ((f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) y) • Ufeat L ε y ∂(haar 1)‖ ^ 2 ≤ ‖f‖ ^ 2 / 2 := by
    intro f
    set φ : Torus 1 → ℝ := ((f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) : Torus 1 → ℝ) with hφ
    have hf0 : ∫ x, φ x ∂(haar 1) = 0 := f.2
    have hfi : Integrable φ (haar 1) := integrable_lp (haarProbability 1) _
    have hg : ∀ i : Fin 2, Integrable (fun y => Ufeat L ε y i * φ y) (haar 1) :=
      fun i => integrable_comp_mul hL ε i (f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
    set a : Fin 2 → ℝ := fun i => ∫ y, Ufeat L ε y i * φ y ∂(haar 1) with ha
    have hvi : Integrable (fun y => φ y • Ufeat L ε y) (haar 1) :=
      hfi.smul_bdd 1 (continuous_Ufeat hL ε).aestronglyMeasurable
        (ae_of_all _ fun y => by rw [norm_Ufeat])
    have hvec : ‖∫ y, φ y • Ufeat L ε y ∂(haar 1)‖ ^ 2 = ∑ i, a i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) i) hvi
      have : (∫ y, φ y • Ufeat L ε y ∂(haar 1)) i = a i := by
        rw [ha]
        have hc' : ∫ y, (φ y • Ufeat L ε y) i ∂(haar 1) = (∫ y, φ y • Ufeat L ε y ∂(haar 1)) i := hc
        refine hc'.symm.trans (integral_congr_ae (ae_of_all _ fun y => ?_))
        simp [mul_comm]
      rw [this, Real.norm_eq_abs, sq_abs]
    have hW : ∫ p, (modelData hL ε).W p.1 p.2 * (φ p.1 * φ p.2) ∂((haar 1).prod (haar 1)) =
        - kappa * ∑ i, a i ^ 2 := by
      have e : ∀ p : Torus 1 × Torus 1, (modelData hL ε).W p.1 p.2 * (φ p.1 * φ p.2) =
          kappa * (φ p.1 * φ p.2) -
            kappa * ∑ i, ((Ufeat L ε p.1 i * φ p.1) * (Ufeat L ε p.2 i * φ p.2)) := by
        intro p
        simp only [modelData, modelW, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
          conj_trivial]
        ring
      simp_rw [e]
      have i1 : Integrable (fun p : Torus 1 × Torus 1 => kappa * (φ p.1 * φ p.2))
          ((haar 1).prod (haar 1)) := (hfi.mul_prod hfi).const_mul _
      have i2 : Integrable (fun p : Torus 1 × Torus 1 =>
          kappa * ∑ i, ((Ufeat L ε p.1 i * φ p.1) * (Ufeat L ε p.2 i * φ p.2)))
          ((haar 1).prod (haar 1)) :=
        (integrable_finsetSum _ fun i _ => (hg i).mul_prod (hg i)).const_mul _
      rw [integral_sub i1 i2, integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun i _ => (hg i).mul_prod (hg i), integral_prod_mul φ φ, hf0]
      simp only [mul_zero, zero_sub, neg_mul]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      have := integral_prod_mul (μ := haar 1) (ν := haar 1)
        (fun y => Ufeat L ε y i * φ y) (fun y => Ufeat L ε y i * φ y)
      rw [this, ha]; ring
    have hH := inner_densityHessian (modelData hL ε) (haarProbability 1) f
    have hbes := bessel_feature hL ε (f : Lp ℝ 2 ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
    refine ⟨?_, ?_⟩
    · rw [hH]
      exact (congrArg (‖f‖ ^ 2 + ·) hW).trans (by rw [hvec]; ring)
    · rw [hvec]
      exact hbes
  refine ⟨hk, fun f => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := main f
    have hkp : 0 < kappa := by unfold kappa; norm_num
    refine ⟨h1, ?_, ?_⟩
    · nlinarith [hk]
    · rw [h1]; unfold kappa at *; nlinarith
  · refine ⟨1 / 12, by norm_num, fun f => ?_⟩
    obtain ⟨h1, h2⟩ := main f
    rw [h1]; unfold kappa at *; nlinarith

end DGPS.Examples.RoughBoundary.FreeEnergy
