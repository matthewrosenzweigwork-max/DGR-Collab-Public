/- Proper moments and the actual covariance of the SAME process under its
normalized quadratic tilt. No covariance identity is supplied as a premise. -/
import DGRHS.Gaussian.HilbertTiltedTupleLaw
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Gaussian
variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

lemma repr_diagonal_inner_symmetry (b : HilbertBasis ι ℝ H) (c : ι → ℝ)
    (R : H →L[ℝ] H) (hc : ∀ v i, b.repr (R v) i = c i*b.repr v i) (v w : H) :
    inner ℝ v (R w) = inner ℝ w (R v) := by
  rw [← b.tsum_inner_mul_inner v (R w),← b.tsum_inner_mul_inner w (R v)]
  apply tsum_congr
  intro i
  rw [← real_inner_comm v (b i),← real_inner_comm w (b i)]
  simp only [← b.repr_apply_apply,hc]
  ring

lemma tilted_readout_mean_square (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (P : Measure (ℕ → ℝ))
    (hac : P ≪ IsonormalProcess.iidStdGaussian) (R : H →L[ℝ] H)
    (hn : ∀ v, 0 ≤ inner ℝ v (R v))
    (hmap : ∀ v, P.map (indexedGaussianIsometry b f hf v) = gaussianReal 0 (Real.toNNReal (inner ℝ v (R v))))
    (v : H) :
    MemLp (indexedGaussianIsometry b f hf v : (ℕ → ℝ) → ℝ) 2 P ∧
    (∫ ω, indexedGaussianIsometry b f hf v ω ∂P) = 0 ∧
    (∫ ω, (indexedGaussianIsometry b f hf v ω)^2 ∂P) = inner ℝ v (R v) := by
  have hl : HasLaw (indexedGaussianIsometry b f hf v : (ℕ → ℝ) → ℝ)
      (gaussianReal 0 (Real.toNNReal (inner ℝ v (R v)))) P :=
    ⟨(Lp.aestronglyMeasurable _).aemeasurable.mono_ac hac,hmap v⟩
  have hmean : (∫ ω, indexedGaussianIsometry b f hf v ω ∂P) = 0 := by
    rw [hl.integral_eq,integral_id_gaussianReal]
  refine ⟨hl.hasGaussianLaw.memLp_two,hmean,?_⟩
  have hv := hl.variance_eq
  rw [variance_id_gaussianReal,Real.coe_toNNReal _ (hn v)] at hv
  rw [variance_eq_integral hl.aemeasurable,hmean] at hv
  simpa only [sub_zero] using hv

lemma tilted_readout_covariance (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (P : Measure (ℕ → ℝ))
    (hac : P ≪ IsonormalProcess.iidStdGaussian) (R : H →L[ℝ] H)
    (hn : ∀ v, 0 ≤ inner ℝ v (R v))
    (hsym : ∀ v w, inner ℝ v (R w) = inner ℝ w (R v))
    (hmap : ∀ v, P.map (indexedGaussianIsometry b f hf v) = gaussianReal 0 (Real.toNNReal (inner ℝ v (R v))))
    (v w : H) :
    Integrable (fun ω => indexedGaussianIsometry b f hf v ω*indexedGaussianIsometry b f hf w ω) P ∧
    (∫ ω, indexedGaussianIsometry b f hf v ω*indexedGaussianIsometry b f hf w ω ∂P) = inner ℝ v (R w) := by
  let W := indexedGaussianIsometry b f hf
  have hv := tilted_readout_mean_square b f hf P hac R hn hmap v
  have hw := tilted_readout_mean_square b f hf P hac R hn hmap w
  have hsum := tilted_readout_mean_square b f hf P hac R hn hmap (v+w)
  have hprod : Integrable (fun ω => W v ω*W w ω) P := by
    apply (hv.1.integrable_mul hw.1).congr
    filter_upwards [] with ω
    rfl
  have hscaled : Integrable (fun ω => 2*(W v ω*W w ω)) P := by
    simpa only [Pi.mul_apply] using hprod.const_mul 2
  refine ⟨hprod,?_⟩
  have ha : (fun ω => W (v+w) ω) =ᵐ[P] fun ω => W v ω+W w ω := by
    rw [map_add]
    filter_upwards [hac.ae_le (Lp.coeFn_add (W v) (W w))] with ω hω
    rw [hω]
    rfl
  have he : (∫ ω, (W (v+w) ω)^2 ∂P) =
      (∫ ω, (W v ω)^2 ∂P)+2*(∫ ω, W v ω*W w ω ∂P)+(∫ ω, (W w ω)^2 ∂P) := by
    calc
      _ = ∫ ω, (W v ω)^2+2*(W v ω*W w ω)+(W w ω)^2 ∂P := by
        apply integral_congr_ae
        filter_upwards [ha] with ω hω
        rw [hω]
        ring
      _ = _ := by
        rw [integral_add (f := fun ω => (W v ω)^2+2*(W v ω*W w ω))
          (g := fun ω => (W w ω)^2) (hv.1.integrable_sq.add hscaled) hw.1.integrable_sq,
          integral_add (f := fun ω => (W v ω)^2)
            (g := fun ω => 2*(W v ω*W w ω)) hv.1.integrable_sq hscaled,integral_const_mul]
  rw [hsum.2.2,hv.2.2,hw.2.2] at he
  have hq : inner ℝ (v+w) (R (v+w)) =
      inner ℝ v (R v)+2*inner ℝ v (R w)+inner ℝ w (R w) := by
    rw [map_add,inner_add_left,inner_add_right,inner_add_right,← hsym v w]
    ring
  rw [hq] at he
  linarith

/-- All proper scalar moments, true covariance, and inverse from the original
symmetric HS operator. The full basis includes all zero eigenvalue modes. -/
theorem exists_hilbert_tilted_covariance (T : H →L[ℝ] H)
    (hT : T.toLinearMap.IsSymmetric) (b : HilbertBasis ι ℝ H) (a : ι → ℝ)
    (he : ∀ i, T (b i) = a i • b i) (β : ℝ) (ha : Summable (fun i => (a i)^2))
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f) :
    ∃ R : H →L[ℝ] H,
      (∀ v, R v + β • T (R v) = v) ∧ (∀ v, R (v + β • T v) = v) ∧
      (∀ v, (IsonormalProcess.iidStdGaussian.tilted
        (fun ω => -(β/2)*centeredGaussianChaos a f ω)).map
          (indexedGaussianIsometry b f hf v) = gaussianReal 0 (Real.toNNReal (inner ℝ v (R v)))) ∧
      ∀ v w, Integrable (fun ω => indexedGaussianIsometry b f hf v ω*indexedGaussianIsometry b f hf w ω)
          (IsonormalProcess.iidStdGaussian.tilted (fun ω => -(β/2)*centeredGaussianChaos a f ω)) ∧
        (∫ ω, indexedGaussianIsometry b f hf v ω*indexedGaussianIsometry b f hf w ω
          ∂IsonormalProcess.iidStdGaussian.tilted (fun ω => -(β/2)*centeredGaussianChaos a f ω)) = inner ℝ v (R w) := by
  obtain ⟨R,hR1,hR2,hRc,hmap⟩ := exists_hilbert_tilted_gaussian_readouts T hT b a he β ha hm f hf
  refine ⟨R,hR1,hR2,hmap,fun v w => ?_⟩
  exact tilted_readout_covariance b f hf _ (tilted_absolutelyContinuous _ _) R
    (tilted_resolvent_quadratic_nonneg b β a hm R hRc)
    (repr_diagonal_inner_symmetry b (fun i => (1+β*a i)⁻¹) R hRc) hmap v w
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.repr_diagonal_inner_symmetry
#print axioms DGRHS.Gaussian.tilted_readout_mean_square
#print axioms DGRHS.Gaussian.tilted_readout_covariance
#print axioms DGRHS.Gaussian.exists_hilbert_tilted_covariance
#check @DGRHS.Gaussian.exists_hilbert_tilted_covariance
