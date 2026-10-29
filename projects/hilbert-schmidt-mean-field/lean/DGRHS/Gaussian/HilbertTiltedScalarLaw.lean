/- Actual normalized SAME-process tilted readout law. The resolvent and all
mixed exponential integrals are constructed upstream, not assumed as the final
paper's desired Gaussian covariance or law. -/
import DGRHS.Gaussian.HilbertTiltedResolvent
import DGRHS.Gaussian.MGFUniqueness
import DGRHS.CLT.NativeTiltAdapter
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Gaussian
variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

lemma tilted_resolvent_quadratic_nonneg (b : HilbertBasis ι ℝ H)
    (β : ℝ) (a : ι → ℝ) (hm : ∀ i, 0 < 1+β*a i) (R : H →L[ℝ] H)
    (hR : ∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i) (v : H) :
    0 ≤ inner ℝ v (R v) := by
  rw [← tilted_basis_coeff_tsum_eq_inner b β a R hR v]
  exact tsum_nonneg (fun i => div_nonneg (sq_nonneg _) (hm i).le)

lemma map_hilbert_tilted_readout (b : HilbertBasis ι ℝ H) (β : ℝ)
    (a : ι → ℝ) (ha : Summable (fun i => (a i)^2))
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f)
    (R : H →L[ℝ] H)
    (hR : ∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i)
    (htransform : ∀ v, Integrable (fun ω => Real.exp (indexedGaussianIsometry b f hf v ω-
        (β/2)*centeredGaussianChaos a f ω)) IsonormalProcess.iidStdGaussian ∧
      (∫ ω, Real.exp (indexedGaussianIsometry b f hf v ω-
        (β/2)*centeredGaussianChaos a f ω) ∂IsonormalProcess.iidStdGaussian) =
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ *
          Real.exp (inner ℝ v (R v)/2)) (v : H) :
    (IsonormalProcess.iidStdGaussian.tilted
      (fun ω => -(β/2)*centeredGaussianChaos a f ω)).map
        (indexedGaussianIsometry b f hf v) =
      gaussianReal 0 (Real.toNNReal (inner ℝ v (R v))) := by
  let P := IsonormalProcess.iidStdGaussian
  let Y : (ℕ → ℝ) → ℝ := fun ω => -(β/2)*centeredGaussianChaos a f ω
  let W := indexedGaussianIsometry b f hf
  have hbase := integral_exp_signed_centeredGaussianChaos_weak_margin β a hm ha f hf
  have hiY : Integrable (fun ω => Real.exp (Y ω)) P := hbase.1
  letI : IsProbabilityMeasure (P.tilted Y) := isProbabilityMeasure_tilted hiY
  have hWa : AEMeasurable (W v) (P.tilted Y) :=
    (Lp.aestronglyMeasurable (W v)).aemeasurable.mono_ac (tilted_absolutelyContinuous P Y)
  have hden : (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ ≠ 0 := by
    rw [← hbase.2]
    exact (integral_exp_pos hbase.1).ne'
  have htw : ∀ t : ℝ, (fun ω => W (t • v) ω) =ᵐ[P] fun ω => t*W v ω := by
    intro t
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul t (W v)] with ω hω
    rw [hω]
    rfl
  have hmix : ∀ t : ℝ, Integrable (fun ω => Real.exp (Y ω+t*W v ω)) P ∧
      (∫ ω, Real.exp (Y ω+t*W v ω) ∂P) =
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ *
          Real.exp (inner ℝ v (R v)*t^2/2) := by
    intro t
    have heq : (fun ω => Real.exp (W (t • v) ω-(β/2)*centeredGaussianChaos a f ω))
        =ᵐ[P] fun ω => Real.exp (Y ω+t*W v ω) := by
      filter_upwards [htw t] with ω hω
      rw [hω]
      congr 1
      dsimp [Y]
      ring
    have ht := htransform (t • v)
    refine ⟨ht.1.congr heq, ?_⟩
    rw [← integral_congr_ae heq, ht.2]
    congr 2
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  apply map_eq_gaussianReal_of_all_real_mgf (P.tilted Y) (W v) hWa
    (inner ℝ v (R v)) (tilted_resolvent_quadratic_nonneg b β a hm R hR v)
  · intro t
    apply (integrable_tilted_iff hiY _).mpr
    apply (hmix t).1.congr
    filter_upwards [] with ω
    simp only [Real.exp_add, smul_eq_mul]
  · intro t
    unfold mgf
    rw [integral_exp_tilted]
    change (∫ ω, Real.exp (Y ω+t*W v ω) ∂P)/(∫ ω, Real.exp (Y ω) ∂P) = _
    rw [(hmix t).2, hbase.2]
    exact mul_div_cancel_left₀ _ hden

/-- The true inverse and each true scalar law under the normalized SAME quadratic
chaos tilt. Square summability and the single strict factor margin suffice. -/
theorem exists_hilbert_tilted_gaussian_readouts (T : H →L[ℝ] H)
    (hT : T.toLinearMap.IsSymmetric) (b : HilbertBasis ι ℝ H) (a : ι → ℝ)
    (he : ∀ i, T (b i) = a i • b i) (β : ℝ) (ha : Summable (fun i => (a i)^2))
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f) :
    ∃ R : H →L[ℝ] H,
      (∀ v, R v + β • T (R v) = v) ∧
      (∀ v, R (v + β • T v) = v) ∧
      (∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i) ∧
      ∀ v, (IsonormalProcess.iidStdGaussian.tilted
        (fun ω => -(β/2)*centeredGaussianChaos a f ω)).map
          (indexedGaussianIsometry b f hf v) =
        gaussianReal 0 (Real.toNNReal (inner ℝ v (R v))) := by
  obtain ⟨R,hR1,hR2,hRc,ht⟩ := exists_hilbert_tilt_resolvent T hT b a he β ha hm f hf
  exact ⟨R,hR1,hR2,hRc,fun v => map_hilbert_tilted_readout b β a ha hm f hf R hRc ht v⟩
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.tilted_resolvent_quadratic_nonneg
#print axioms DGRHS.Gaussian.map_hilbert_tilted_readout
#print axioms DGRHS.Gaussian.exists_hilbert_tilted_gaussian_readouts
#check @DGRHS.Gaussian.exists_hilbert_tilted_gaussian_readouts
