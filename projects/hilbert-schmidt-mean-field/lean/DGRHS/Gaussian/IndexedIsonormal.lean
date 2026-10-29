import DGRHS.Gaussian.Imported.IsonormalProcess

/-!
An actual Gaussian-coordinate L2 isometry for any countable Hilbert-basis index,
including empty and finite indices. No infinite-dimensionality assumption on H.
The coordinate family is a subfamily of the existing actual countable product law.
This file proves construction/isometry/covariance/series convergence. Scalar
Gaussianity of its full limit and a jointly measurable feature representative
remain separate obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal BigOperators

namespace DGRHS.Gaussian

noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def indexedGaussianCoords (f : ι → ℕ) (i : ι) : Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
  IsonormalProcess.e (f i)

theorem orthonormal_indexedGaussianCoords (f : ι → ℕ) (hf : Function.Injective f) :
    Orthonormal ℝ (indexedGaussianCoords f) :=
  IsonormalProcess.orthonormal_e.comp f hf

def indexedGaussianFromCoeffs (f : ι → ℕ) (hf : Function.Injective f) :
    lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
  (orthonormal_indexedGaussianCoords f hf).orthogonalFamily.linearIsometry

def indexedGaussianIsometry (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) : H →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
  (indexedGaussianFromCoeffs f hf).comp b.repr.toLinearIsometry

theorem indexedGaussianIsometry_norm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (h : H) :
    ‖indexedGaussianIsometry b f hf h‖ = ‖h‖ :=
  (indexedGaussianIsometry b f hf).norm_map h

/-- The second-moment integral follows from the constructed isometry.
Full-limit centering and scalar Gaussianity are separate exports. -/
theorem indexedGaussianIsometry_cov (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (h h' : H) :
    (∫ ω, indexedGaussianIsometry b f hf h ω * indexedGaussianIsometry b f hf h' ω
      ∂IsonormalProcess.iidStdGaussian) = inner ℝ h h' := by
  have hi := (indexedGaussianIsometry b f hf).inner_map_map h h'
  rw [← hi, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with ω
  change indexedGaussianIsometry b f hf h ω * indexedGaussianIsometry b f hf h' ω =
    indexedGaussianIsometry b f hf h' ω * indexedGaussianIsometry b f hf h ω
  ring

theorem hasSum_indexedGaussianIsometry (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (h : H) :
    HasSum (fun i => b.repr h i • indexedGaussianCoords f i)
      (indexedGaussianIsometry b f hf h) := by
  have hs := (orthonormal_indexedGaussianCoords f hf).orthogonalFamily.hasSum_linearIsometry
    (b.repr h)
  rw [indexedGaussianIsometry, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, indexedGaussianFromCoeffs]
  refine hs.congr_fun ?_
  intro i
  simp only [LinearIsometry.toSpanSingleton_apply]

def countableGaussianIndex [Countable ι] : ι ↪ ℕ := by
  letI : Encodable ι := Encodable.ofCountable ι
  exact ⟨Encodable.encode, Encodable.encode_injective⟩

def countableGaussianIsometry [Countable ι] (b : HilbertBasis ι ℝ H) :
    H →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
  indexedGaussianIsometry b countableGaussianIndex countableGaussianIndex.injective

theorem countableGaussianIsometry_cov [Countable ι] (b : HilbertBasis ι ℝ H) (h h' : H) :
    (∫ ω, countableGaussianIsometry b h ω * countableGaussianIsometry b h' ω
      ∂IsonormalProcess.iidStdGaussian) = inner ℝ h h' :=
  indexedGaussianIsometry_cov b _ _ h h'

/-- Separable Hilbert spaces admit this constructed isometry even in finite or
zero dimension. The basis comes from Mathlib and its countability is proved. -/
theorem exists_separableGaussianIsometry [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] :
    ∃ W : H →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian,
      ∀ h h' : H, (∫ ω, W h ω * W h' ω ∂IsonormalProcess.iidStdGaussian) =
        inner ℝ h h' := by
  classical
  obtain ⟨s, b, hb⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  exact ⟨countableGaussianIsometry b, countableGaussianIsometry_cov b⟩

/-- Honest finite readout on the same actual countable Gaussian sample space. -/
def indexedPartialEvaluation {X : Type*} (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (k : X → H) (s : Finset ι) (x : X) (ω : ℕ → ℝ) : ℝ :=
  ∑ i ∈ s, b.repr (k x) i * IsonormalProcess.coord (f i) ω

/-- Joint measurability is proved at every finite truncation. -/
theorem measurable_indexedPartialEvaluation {X : Type*} [MeasurableSpace X]
    [MeasurableSpace H] [BorelSpace H] (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : Measurable k) (s : Finset ι) :
    Measurable (fun p : X × (ℕ → ℝ) => indexedPartialEvaluation b f k s p.1 p.2) := by
  classical
  unfold indexedPartialEvaluation
  apply Finset.measurable_sum
  intro i _
  have hi : Measurable (fun x => b.repr (k x) i) := by
    have he : (fun x => b.repr (k x) i) =
        (fun v : H => inner ℝ (b i) v) ∘ k := by
      funext x
      simp only [b.repr_apply_apply, Function.comp_apply]
    rw [he]
    exact (continuous_const.inner continuous_id).measurable.comp hk
  exact (hi.comp measurable_fst).mul ((IsonormalProcess.measurable_coord (f i)).comp
    measurable_snd)

/-- Independent actual coordinates give the finite readout a Gaussian law. -/
theorem hasGaussianLaw_indexedPartialEvaluation {X : Type*}
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (s : Finset ι) (x : X) :
    HasGaussianLaw (indexedPartialEvaluation b f k s x)
      IsonormalProcess.iidStdGaussian := by
  classical
  let Y : ↥s → (ℕ → ℝ) → ℝ := fun i ω => b.repr (k x) i *
    IsonormalProcess.coord (f i) ω
  have hGauss : ∀ i : ↥s, HasGaussianLaw (Y i) IsonormalProcess.iidStdGaussian := by
    intro i
    simpa only [Y, smul_eq_mul] using
      (IsonormalProcess.hasGaussianLaw_coord (f i)).fun_smul (b.repr (k x) i)
  have hIndep : iIndepFun Y IsonormalProcess.iidStdGaussian := by
    have hsub : iIndepFun (fun i : ↥s => IsonormalProcess.coord (f i))
        IsonormalProcess.iidStdGaussian :=
      IsonormalProcess.iIndepFun_coord.precomp (hf.comp Subtype.val_injective)
    exact hsub.comp (fun i : ↥s => fun t : ℝ => b.repr (k x) i * t)
      (fun _ => by fun_prop)
  have hs := hIndep.hasGaussianLaw_fun_sum hGauss
  have he : (fun ω => ∑ i : ↥s, Y i ω) = indexedPartialEvaluation b f k s x := by
    funext ω
    rw [indexedPartialEvaluation, ← Finset.sum_attach s
      (fun i => b.repr (k x) i * IsonormalProcess.coord (f i) ω)]
    rfl
  rwa [he] at hs

/-- Finite readouts are integrable under the actual countable product law. -/
theorem integrable_indexedPartialEvaluation {X : Type*}
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (s : Finset ι) (x : X) :
    Integrable (indexedPartialEvaluation b f k s x) IsonormalProcess.iidStdGaussian :=
  (hasGaussianLaw_indexedPartialEvaluation b f hf k s x).integrable

/-- Finite readouts have zero Gaussian-sample mean. -/
theorem integral_indexedPartialEvaluation_eq_zero {X : Type*}
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (k : X → H) (s : Finset ι) (x : X) :
    ∫ ω, indexedPartialEvaluation b f k s x ω ∂IsonormalProcess.iidStdGaussian = 0 := by
  classical
  unfold indexedPartialEvaluation
  rw [integral_finsetSum _ (fun i _ =>
    ((IsonormalProcess.memLp_coord (f i)).integrable (by norm_num)).const_mul
      (b.repr (k x) i))]
  simp_rw [integral_const_mul, IsonormalProcess.integral_coord, mul_zero]
  simp

end

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.indexedGaussianIsometry
#print axioms DGRHS.Gaussian.indexedGaussianIsometry_cov
#print axioms DGRHS.Gaussian.hasSum_indexedGaussianIsometry
#print axioms DGRHS.Gaussian.countableGaussianIsometry_cov

#print axioms DGRHS.Gaussian.measurable_indexedPartialEvaluation
#print axioms DGRHS.Gaussian.hasGaussianLaw_indexedPartialEvaluation

#print axioms DGRHS.Gaussian.exists_separableGaussianIsometry

#print axioms DGRHS.Gaussian.integrable_indexedPartialEvaluation
#print axioms DGRHS.Gaussian.integral_indexedPartialEvaluation_eq_zero

#check DGRHS.Gaussian.indexedGaussianCoords
#check DGRHS.Gaussian.orthonormal_indexedGaussianCoords
#check DGRHS.Gaussian.indexedGaussianFromCoeffs
#check DGRHS.Gaussian.indexedGaussianIsometry
#check DGRHS.Gaussian.indexedGaussianIsometry_norm
#check DGRHS.Gaussian.indexedGaussianIsometry_cov
#check DGRHS.Gaussian.hasSum_indexedGaussianIsometry
#check DGRHS.Gaussian.countableGaussianIndex
#check DGRHS.Gaussian.countableGaussianIsometry
#check DGRHS.Gaussian.countableGaussianIsometry_cov
#check DGRHS.Gaussian.exists_separableGaussianIsometry
#check DGRHS.Gaussian.indexedPartialEvaluation
#check DGRHS.Gaussian.measurable_indexedPartialEvaluation
#check DGRHS.Gaussian.hasGaussianLaw_indexedPartialEvaluation
#check DGRHS.Gaussian.integrable_indexedPartialEvaluation
#check DGRHS.Gaussian.integral_indexedPartialEvaluation_eq_zero

#print axioms DGRHS.Gaussian.indexedGaussianIsometry_norm
#print axioms DGRHS.Gaussian.orthonormal_indexedGaussianCoords
