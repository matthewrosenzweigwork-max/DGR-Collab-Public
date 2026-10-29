import DGRHS.Gaussian.IndexedIsonormal
import DGRHS.Gaussian.Imported.GaussianL2Closure

/-!
Scalar Gaussianity and exact laws for the constructed countable-index map.
Finite Lp readout identification is adapted from the licensed StatLean
IsonormalProcess coeFn_lp_partialSum proof (revision
86b3823f77fc2b0f5a9923f85b588a4f8a65f94c; upstream SHA-256
eab89af1820ec44fc960b1a702a99f4267ba6f182759504d4b585dcc0bc6c5fa).
See Imported/LICENSE. The actual jointly measurable full feature representative
is still a separate product-L2 obligation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace

namespace DGRHS.Gaussian

noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def indexedLpPartialSum (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (h : H) (s : Finset ι) : Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
  ∑ i ∈ s, b.repr h i • indexedGaussianCoords f i

/-- Honest finite coordinate sums identify the finite Lp sums almost everywhere. -/
theorem coeFn_indexedLpPartialSum (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (h : H) (s : Finset ι) :
    (indexedLpPartialSum b f h s : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedPartialEvaluation b f (fun _ : Unit => h) s () := by
  classical
  unfold indexedLpPartialSum
  induction s using Finset.induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
      (μ := IsonormalProcess.iidStdGaussian)] with ω hω
    simp only [Finset.sum_empty] at *
    rw [hω]
    simp [indexedPartialEvaluation]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hadd := Lp.coeFn_add (b.repr h a • indexedGaussianCoords f a)
      (∑ i ∈ s, b.repr h i • indexedGaussianCoords f i)
    have hsmul := Lp.coeFn_smul (b.repr h a) (indexedGaussianCoords f a)
    have hea : (indexedGaussianCoords f a : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
        IsonormalProcess.coord (f a) := by
      change (IsonormalProcess.e (f a) : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
        IsonormalProcess.coord (f a)
      exact (IsonormalProcess.memLp_coord (f a)).coeFn_toLp
    filter_upwards [hadd, hsmul, hea, ih] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]
    simp only [indexedPartialEvaluation, Finset.sum_insert ha, smul_eq_mul]

theorem hasGaussianLaw_indexedLpPartialSum (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (h : H) (s : Finset ι) :
    HasGaussianLaw (indexedLpPartialSum b f h s : (ℕ → ℝ) → ℝ)
      IsonormalProcess.iidStdGaussian :=
  (hasGaussianLaw_indexedPartialEvaluation b f hf (fun _ : Unit => h) s ()).congr
    (coeFn_indexedLpPartialSum b f h s).symm

theorem integral_indexedLpPartialSum_eq_zero (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (h : H) (s : Finset ι) :
    ∫ ω, indexedLpPartialSum b f h s ω ∂IsonormalProcess.iidStdGaussian = 0 := by
  rw [integral_congr_ae (coeFn_indexedLpPartialSum b f h s)]
  exact integral_indexedPartialEvaluation_eq_zero b f (fun _ : Unit => h) s ()

theorem tendsto_indexedLpPartialSum (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (h : H) {ss : ℕ → Finset ι}
    (hss : Tendsto ss atTop atTop) :
    Tendsto (fun n => indexedLpPartialSum b f h (ss n)) atTop
      (𝓝 (indexedGaussianIsometry b f hf h)) := by
  have ht : Tendsto (fun s : Finset ι => indexedLpPartialSum b f h s) atTop
      (𝓝 (indexedGaussianIsometry b f hf h)) := hasSum_indexedGaussianIsometry b f hf h
  exact ht.comp hss

/-- Pointwise feature fibers converge in probability to the constructed map. -/
theorem tendstoInMeasure_indexedPartialEvaluation {X : Type*}
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (k : X → H)
    (x : X) {ss : ℕ → Finset ι} (hss : Tendsto ss atTop atTop) :
    TendstoInMeasure IsonormalProcess.iidStdGaussian
      (fun n ω => indexedPartialEvaluation b f k (ss n) x ω) atTop
      (indexedGaussianIsometry b f hf (k x)) := by
  have ht := tendstoInMeasure_of_tendsto_Lp
    (tendsto_indexedLpPartialSum b f hf (k x) hss)
  apply ht.congr_left
  intro n
  exact coeFn_indexedLpPartialSum b f (k x) (ss n)

/-- The full map has an actual scalar Gaussian law for every countable basis index. -/
theorem hasGaussianLaw_indexedGaussianIsometry [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (h : H) :
    HasGaussianLaw (indexedGaussianIsometry b f hf h : (ℕ → ℝ) → ℝ)
      IsonormalProcess.iidStdGaussian := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  exact hasGaussianLaw_of_centered_tendsto_L2 IsonormalProcess.iidStdGaussian
    (fun n => indexedLpPartialSum b f h (ss n)) (indexedGaussianIsometry b f hf h)
    (fun n => hasGaussianLaw_indexedLpPartialSum b f hf h (ss n))
    (fun n => integral_indexedLpPartialSum_eq_zero b f h (ss n))
    (tendsto_indexedLpPartialSum b f hf h hss)

/-- Full-limit zero mean and variance normalization are encoded in the exact law. -/
theorem map_indexedGaussianIsometry_eq_gaussianReal [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (h : H) :
    IsonormalProcess.iidStdGaussian.map (indexedGaussianIsometry b f hf h) =
      gaussianReal 0 (Real.toNNReal (‖h‖ ^ 2)) := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  have hm := map_eq_gaussianReal_of_centered_tendsto_L2 IsonormalProcess.iidStdGaussian
    (fun n => indexedLpPartialSum b f h (ss n)) (indexedGaussianIsometry b f hf h)
    (fun n => hasGaussianLaw_indexedLpPartialSum b f hf h (ss n))
    (fun n => integral_indexedLpPartialSum_eq_zero b f h (ss n))
    (tendsto_indexedLpPartialSum b f hf h hss)
  rwa [indexedGaussianIsometry_norm] at hm

theorem integral_indexedGaussianIsometry_eq_zero [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (h : H) :
    ∫ ω, indexedGaussianIsometry b f hf h ω ∂IsonormalProcess.iidStdGaussian = 0 := by
  have hi := integral_map (Lp.aestronglyMeasurable (indexedGaussianIsometry b f hf h)).aemeasurable
    aestronglyMeasurable_id
  rw [map_indexedGaussianIsometry_eq_gaussianReal b f hf h] at hi
  change (∫ y : ℝ, y ∂gaussianReal 0 (Real.toNNReal (‖h‖ ^ 2))) =
    (∫ ω, indexedGaussianIsometry b f hf h ω ∂IsonormalProcess.iidStdGaussian) at hi
  rw [integral_id_gaussianReal] at hi
  exact hi.symm

theorem map_countableGaussianIsometry_eq_gaussianReal [Countable ι]
    (b : HilbertBasis ι ℝ H) (h : H) :
    IsonormalProcess.iidStdGaussian.map (countableGaussianIsometry b h) =
      gaussianReal 0 (Real.toNNReal (‖h‖ ^ 2)) :=
  map_indexedGaussianIsometry_eq_gaussianReal b _ _ h

/-- Actual scalar Gaussian laws and second moments for every separable complete
real Hilbert space, including finite and zero dimensions. -/
theorem exists_separableGaussianProcess [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] :
    ∃ W : H →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian,
      (∀ h : H, IsonormalProcess.iidStdGaussian.map (W h) =
        gaussianReal 0 (Real.toNNReal (‖h‖ ^ 2))) ∧
      ∀ h h' : H, (∫ ω, W h ω * W h' ω ∂IsonormalProcess.iidStdGaussian) =
        inner ℝ h h' := by
  classical
  obtain ⟨s, b, hb⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  exact ⟨countableGaussianIsometry b, map_countableGaussianIsometry_eq_gaussianReal b,
    countableGaussianIsometry_cov b⟩

end

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.indexedLpPartialSum
#check DGRHS.Gaussian.indexedLpPartialSum
#print axioms DGRHS.Gaussian.coeFn_indexedLpPartialSum
#check DGRHS.Gaussian.coeFn_indexedLpPartialSum
#print axioms DGRHS.Gaussian.hasGaussianLaw_indexedLpPartialSum
#check DGRHS.Gaussian.hasGaussianLaw_indexedLpPartialSum
#print axioms DGRHS.Gaussian.integral_indexedLpPartialSum_eq_zero
#check DGRHS.Gaussian.integral_indexedLpPartialSum_eq_zero
#print axioms DGRHS.Gaussian.tendsto_indexedLpPartialSum
#check DGRHS.Gaussian.tendsto_indexedLpPartialSum
#print axioms DGRHS.Gaussian.tendstoInMeasure_indexedPartialEvaluation
#check DGRHS.Gaussian.tendstoInMeasure_indexedPartialEvaluation
#print axioms DGRHS.Gaussian.hasGaussianLaw_indexedGaussianIsometry
#check DGRHS.Gaussian.hasGaussianLaw_indexedGaussianIsometry
#print axioms DGRHS.Gaussian.map_indexedGaussianIsometry_eq_gaussianReal
#check DGRHS.Gaussian.map_indexedGaussianIsometry_eq_gaussianReal
#print axioms DGRHS.Gaussian.integral_indexedGaussianIsometry_eq_zero
#check DGRHS.Gaussian.integral_indexedGaussianIsometry_eq_zero
#print axioms DGRHS.Gaussian.map_countableGaussianIsometry_eq_gaussianReal
#check DGRHS.Gaussian.map_countableGaussianIsometry_eq_gaussianReal
#print axioms DGRHS.Gaussian.exists_separableGaussianProcess
#check DGRHS.Gaussian.exists_separableGaussianProcess
