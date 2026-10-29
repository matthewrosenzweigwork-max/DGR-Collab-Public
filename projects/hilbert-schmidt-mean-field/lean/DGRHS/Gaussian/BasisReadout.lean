/- UNCHECKED outside frozen proof. The fixed constructed process reads the
actual chosen Hilbert basis as its selected Gaussian coordinates. This identity
must be retained when spectral truncations vary; marginal laws alone do not
identify the joint process. -/
import DGRHS.Gaussian.IndexedGaussianLaw
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma indexedGaussianIsometry_basis (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (i : ι) :
    indexedGaussianIsometry b f hf (b i) = indexedGaussianCoords f i := by
  classical
  simp only [indexedGaussianIsometry, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, b.repr_self, indexedGaussianFromCoeffs]
  rw [(orthonormal_indexedGaussianCoords f hf).orthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, one_smul]

lemma indexedGaussianIsometry_basis_ae (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (i : ι) :
    (⇑(indexedGaussianIsometry b f hf (b i)) : (ℕ → ℝ) → ℝ)
      =ᵐ[IsonormalProcess.iidStdGaussian] fun ω => ω (f i) := by
  rw [indexedGaussianIsometry_basis]
  exact (IsonormalProcess.memLp_coord (f i)).coeFn_toLp

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.indexedGaussianIsometry_basis
#print axioms DGRHS.Gaussian.indexedGaussianIsometry_basis_ae
