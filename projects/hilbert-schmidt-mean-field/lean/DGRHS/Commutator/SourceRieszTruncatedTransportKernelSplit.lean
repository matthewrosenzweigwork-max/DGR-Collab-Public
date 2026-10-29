import DGRHS.Commutator.SourceRieszTruncatedTransportKernelLongMeasurable

/-! Genuine derivative-level full/short/long Gaussian Riesz decomposition.
All derivatives and Bochner integrals are actual checked objects. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


lemma sourceRieszPotential_iteratedFDeriv_full_short_long (n : ℕ) (s η : ℝ)
    (hs : 0<s) (hη : 0<η) {z : E} (hz : z≠0) :
    iteratedFDeriv ℝ n (sourceRieszPotential s) z =
      iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) z+
      iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) z := by
  let c := DGRHS.Gaussian.gaussianRieszSourceCoefficient s
  have he : (sourceRieszPotential s : E→ℝ) =ᶠ[𝓝 z]
      (fun y : E=>c*(∫ t in Ioi 0,t^(-s-1)*sourceRieszGaussianScale t y)) := by
    apply (eventually_ne_nhds hz).mono
    intro y hy
    exact (DGRHS.Gaussian.gaussianRieszEuclidean_full_scale s hs y hy).symm
  have hD := (he.iteratedFDeriv ℝ n).eq_of_nhds
  rw [hD,sourceRieszGaussian_iteratedFDeriv_scale_integral n c s (Ioi 0)
    measurableSet_Ioi (Subset.refl _) hs hz,
    sourceRieszShortRange_iteratedFDeriv_formula n s η hs hz,
    sourceRieszLongRange_iteratedFDeriv_formula n s η hs hη hz]
  have hi := integrable_sourceRieszGaussian_scale_on n s (Ioi 0) measurableSet_Ioi (Subset.refl _) hs hz
  have hiLong := integrable_sourceRieszGaussian_scale_on n s (Ioi η) measurableSet_Ioi (Ioi_subset_Ioi hη.le) hs hz
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hiLong
  rw [intervalIntegral.integral_of_le hη.le] at hsplit
  rw [←smul_add,hsplit]

lemma sourceRieszTransportKernel_full_short_long (n : ℕ) (s η : ℝ)
    (hs : 0<s) (hη : 0<η) (v : E→E) (p : E×E) :
    sourceRieszTransportKernel n s v p =
      sourceRieszShortTransportKernel n s η v p+sourceRieszLongTransportKernel n s η v p := by
  classical
  unfold sourceRieszTransportKernel sourceRieszShortTransportKernel sourceRieszLongTransportKernel
  split_ifs with hp
  · simp
  · rw [sourceRieszPotential_iteratedFDeriv_full_short_long n s η hs hη (sub_ne_zero.mpr hp)]
    rfl
end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszPotential_iteratedFDeriv_full_short_long
#print axioms DGRHS.Commutator.sourceRieszPotential_iteratedFDeriv_full_short_long
#check DGRHS.Commutator.sourceRieszTransportKernel_full_short_long
#print axioms DGRHS.Commutator.sourceRieszTransportKernel_full_short_long
