/- Adaptation of coordinator uncompiled Reflection draft (original SHA256 b814545a4b967dfdc201c08c74c46c65c3ee31e654a448312079dfe7b2513e1e).
Own isolated-check candidate: actual countable Gaussian reflection and SAME-g
parity infrastructure. Original draft is preserved in records/gaussian/rate-provenance.
No acceptance is inferred from that draft. -/
import DGRHS.Gaussian.FeatureProductL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace DGRHS.Gaussian

def gaussianReflection (ω : ℕ → ℝ) : ℕ → ℝ := fun n => -ω n

lemma measurable_gaussianReflection : Measurable gaussianReflection := by
  unfold gaussianReflection
  fun_prop

lemma measurePreserving_gaussianReflection :
    MeasurePreserving gaussianReflection IsonormalProcess.iidStdGaussian
      IsonormalProcess.iidStdGaussian := by
  refine ⟨measurable_gaussianReflection, ?_⟩
  unfold gaussianReflection IsonormalProcess.iidStdGaussian
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => gaussianReal 0 1) (fun _ => measurable_neg)]
  simp only [gaussianReal_map_neg, neg_zero]

lemma gaussianReflection_involutive : Function.Involutive gaussianReflection := by
  intro ω
  funext n
  simp [gaussianReflection]

lemma compReflection_indexedGaussianCoords {ι : Type*} (f : ι → ℕ) (i : ι) :
    Lp.compMeasurePreserving gaussianReflection measurePreserving_gaussianReflection
      (indexedGaussianCoords f i) = -indexedGaussianCoords f i := by
  apply Lp.ext
  have hc : (indexedGaussianCoords f i : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      IsonormalProcess.coord (f i) := (IsonormalProcess.memLp_coord (f i)).coeFn_toLp
  filter_upwards [Lp.coeFn_compMeasurePreserving (indexedGaussianCoords f i)
    measurePreserving_gaussianReflection,
    Lp.coeFn_neg (indexedGaussianCoords f i), hc,
    measurePreserving_gaussianReflection.quasiMeasurePreserving.ae hc]
      with ω h1 h2 h3 h4
  rw [h1, h2]
  simpa only [Function.comp_apply, Pi.neg_apply, h3, h4, gaussianReflection,
    IsonormalProcess.coord] using (rfl : -ω (f i) = -ω (f i))

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma compReflection_indexedGaussianIsometry
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (v : H) :
    Lp.compMeasurePreserving gaussianReflection measurePreserving_gaussianReflection
      (indexedGaussianIsometry b f hf v) = -indexedGaussianIsometry b f hf v := by
  let C := Lp.compMeasurePreservingₗᵢ ℝ gaussianReflection
    measurePreserving_gaussianReflection (E := ℝ) (p := 2)
  have hs := hasSum_indexedGaussianIsometry b f hf v
  have h1 := C.continuous.continuousAt.tendsto.comp hs
  have h2 := hs.neg
  change Tendsto (fun s : Finset ι => C (∑ i ∈ s, b.repr v i • indexedGaussianCoords f i))
    _ (𝓝 (C (indexedGaussianIsometry b f hf v))) at h1
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, -(b.repr v i • indexedGaussianCoords f i))
    _ (𝓝 (-indexedGaussianIsometry b f hf v)) at h2
  simp only [Finset.sum_neg_distrib] at h2
  have he : (fun s : Finset ι => C (∑ i ∈ s, b.repr v i • indexedGaussianCoords f i)) =
      (fun s : Finset ι => -(∑ i ∈ s, b.repr v i • indexedGaussianCoords f i)) := by
    funext s
    simp only [map_sum, map_smul]
    change (∑ i ∈ s, b.repr v i • Lp.compMeasurePreserving gaussianReflection
      measurePreserving_gaussianReflection (indexedGaussianCoords f i)) = _
    simp only [compReflection_indexedGaussianCoords,
      smul_neg, Finset.sum_neg_distrib]
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

lemma ae_reflection_indexedGaussianIsometry
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (v : H) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      indexedGaussianIsometry b f hf v (gaussianReflection ω) =
        -indexedGaussianIsometry b f hf v ω := by
  have he := compReflection_indexedGaussianIsometry b f hf v
  have hc := Lp.coeFn_compMeasurePreserving (indexedGaussianIsometry b f hf v)
    measurePreserving_gaussianReflection
  have hn := Lp.coeFn_neg (indexedGaussianIsometry b f hf v)
  rw [he] at hc
  exact hc.symm.trans hn

/-- Oddness is transported to the exact chosen field through its actual
isonormal fiber witness. No unrelated field with the same scalar laws is used. -/
lemma ae_featureGaussian_reflection {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ, ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      g (x, gaussianReflection ω) = -g (x, ω) := by
  filter_upwards [hW] with x hx
  filter_upwards [hx, measurePreserving_gaussianReflection.quasiMeasurePreserving.ae hx,
    ae_reflection_indexedGaussianIsometry b f hf (k x)] with ω h1 h2 h3
  exact h2.trans (h3.trans (congrArg Neg.neg h1.symm))

/-- Concrete measurable involution of the actual Gaussian sample space. -/
def gaussianReflectionEquiv : (ℕ → ℝ) ≃ᵐ (ℕ → ℝ) where
  toFun := gaussianReflection
  invFun := gaussianReflection
  left_inv := gaussianReflection_involutive
  right_inv := gaussianReflection_involutive
  measurable_toFun := measurable_gaussianReflection
  measurable_invFun := measurable_gaussianReflection

/-- Reverse Fubini transfers oddness to spatial sections of the SAME joint field. -/
lemma ae_featureGaussian_reflection_sections {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, ∀ᵐ x ∂μ,
      g (x, gaussianReflection ω) = -g (x, ω) := by
  have hm : Measurable (fun p : X × (ℕ → ℝ) => g (p.1, gaussianReflection p.2)) :=
    hg.measurable.comp (measurable_fst.prodMk (measurable_gaussianReflection.comp measurable_snd))
  have hset : MeasurableSet {p : X × (ℕ → ℝ) |
      g (p.1, gaussianReflection p.2) = -g (p.1, p.2)} :=
    measurableSet_eq_fun hm hg.measurable.neg
  exact (Measure.ae_ae_comm hset).1
    (ae_featureGaussian_reflection b f hf k g hW)

/-- Actual expectation cancellation under the concrete reflection. Integrability
is retained so the conclusion refers to a proper expectation. -/
lemma integral_zero_of_gaussianReflection_odd (z : (ℕ → ℝ) → ℝ)
    (hz : Integrable z IsonormalProcess.iidStdGaussian)
    (ho : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      z (gaussianReflection ω) = -z ω) :
    (∫ ω, z ω ∂IsonormalProcess.iidStdGaussian) = 0 := by
  have hp := measurePreserving_gaussianReflection.integral_comp
    gaussianReflectionEquiv.measurableEmbedding z
  have hn := integral_congr_ae ho
  rw [integral_neg] at hn
  linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.measurePreserving_gaussianReflection
#print axioms DGRHS.Gaussian.compReflection_indexedGaussianIsometry
#print axioms DGRHS.Gaussian.ae_featureGaussian_reflection

#check DGRHS.Gaussian.gaussianReflection
#print axioms DGRHS.Gaussian.gaussianReflection

#check DGRHS.Gaussian.measurable_gaussianReflection
#print axioms DGRHS.Gaussian.measurable_gaussianReflection

#check DGRHS.Gaussian.measurePreserving_gaussianReflection
#print axioms DGRHS.Gaussian.measurePreserving_gaussianReflection

#check DGRHS.Gaussian.gaussianReflection_involutive
#print axioms DGRHS.Gaussian.gaussianReflection_involutive

#check DGRHS.Gaussian.compReflection_indexedGaussianCoords
#print axioms DGRHS.Gaussian.compReflection_indexedGaussianCoords

#check DGRHS.Gaussian.compReflection_indexedGaussianIsometry
#print axioms DGRHS.Gaussian.compReflection_indexedGaussianIsometry

#check DGRHS.Gaussian.ae_reflection_indexedGaussianIsometry
#print axioms DGRHS.Gaussian.ae_reflection_indexedGaussianIsometry

#check DGRHS.Gaussian.ae_featureGaussian_reflection
#print axioms DGRHS.Gaussian.ae_featureGaussian_reflection

#check DGRHS.Gaussian.gaussianReflectionEquiv
#print axioms DGRHS.Gaussian.gaussianReflectionEquiv

#check DGRHS.Gaussian.ae_featureGaussian_reflection_sections
#print axioms DGRHS.Gaussian.ae_featureGaussian_reflection_sections

#check DGRHS.Gaussian.integral_zero_of_gaussianReflection_odd
#print axioms DGRHS.Gaussian.integral_zero_of_gaussianReflection_odd
