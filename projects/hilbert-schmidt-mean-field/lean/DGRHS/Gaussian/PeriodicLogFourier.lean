import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Actual d-dimensional periodic logarithmic L2 kernel with the original
normalization. Native Mathlib torus Fourier basis and lattice summability,
Apache2; generalization of read-only local square-torus GreenFourier (hash and
provenance in records/PERIODIC_NATIVE_REUSE_20261002.md). No pointwise singular
representative, heat comparison or partition conclusion is assumed here. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal lp
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

abbrev PeriodicTorus (ι : Type u) := ι → UnitAddCircle
abbrev PeriodicFrequency (ι : Type u) := ι → ℤ

def periodicHaar (ι : Type u) [Fintype ι] : Measure (PeriodicTorus ι) :=
  Measure.pi fun _ => AddCircle.haarAddCircle
instance : IsProbabilityMeasure (periodicHaar ι) := by
  unfold periodicHaar
  infer_instance

def periodicFrequencyVector (k : PeriodicFrequency ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun j => (k j : ℝ)
omit [Fintype ι] [Nonempty ι] in
@[simp] lemma periodicFrequencyVector_apply (k : PeriodicFrequency ι) (j : ι) :
    periodicFrequencyVector k j = (k j : ℝ) := rfl
omit [Fintype ι] [Nonempty ι] in
@[simp] lemma periodicFrequencyVector_zero : periodicFrequencyVector (0 : PeriodicFrequency ι) = 0 := by
  ext j
  simp
lemma periodicFrequencyVector_injective : Function.Injective (periodicFrequencyVector : PeriodicFrequency ι → EuclideanSpace ℝ ι) := by
  intro k l h
  funext j
  exact Int.cast_injective (congrArg (fun v : EuclideanSpace ℝ ι => v j) h)

abbrev periodicFrequencyBasis := (EuclideanSpace.basisFun ι ℝ).toBasis
abbrev periodicFrequencyLattice : Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (periodicFrequencyBasis (ι := ι)))
def periodicFrequencyLatticePoint (k : PeriodicFrequency ι) : periodicFrequencyLattice (ι := ι) :=
  ⟨periodicFrequencyVector k,by
    apply ((periodicFrequencyBasis (ι := ι)).mem_span_iff_repr_mem ℤ (periodicFrequencyVector k)).2
    intro j
    refine ⟨k j,?_⟩
    simp [periodicFrequencyBasis]⟩
lemma periodicFrequencyLatticePoint_injective :
    Function.Injective (periodicFrequencyLatticePoint : PeriodicFrequency ι → periodicFrequencyLattice (ι := ι)) := by
  intro k l h
  exact periodicFrequencyVector_injective (congrArg Subtype.val h)

lemma summable_periodicFrequency_inv_doubleDimension :
    Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖⁻¹ ^ (2*Fintype.card ι)) := by
  have hdim : Module.finrank ℤ (periodicFrequencyLattice (ι := ι)) = Fintype.card ι := by
    rw [ZLattice.rank ℝ (periodicFrequencyLattice (ι := ι))]
    exact finrank_euclideanSpace
  have hd : 0 < Fintype.card ι := Fintype.card_pos
  have hs := ZLattice.summable_norm_pow_inv (periodicFrequencyLattice (ι := ι)) (2*Fintype.card ι) (by
    rw [hdim]
    omega)
  have hp := hs.comp_injective periodicFrequencyLatticePoint_injective
  change Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖⁻¹ ^ (2*Fintype.card ι)) at hp
  exact hp

def periodicLogConstant (ι : Type u) [Fintype ι] : ℝ :=
  Real.Gamma ((Fintype.card ι:ℝ)/2) * (4*Real.pi)^((Fintype.card ι:ℝ)/2) / 2

def periodicStabilityThreshold (ι : Type u) [Fintype ι] : ℝ :=
  (2*Real.pi)^(Fintype.card ι) / periodicLogConstant ι

def periodicLogFourierCoeff (k : PeriodicFrequency ι) : ℂ :=
  if k = 0 then 0 else
    ((periodicLogConstant ι / (2*Real.pi)^(Fintype.card ι) *
      (‖periodicFrequencyVector k‖⁻¹)^(Fintype.card ι) : ℝ) : ℂ)
omit [Nonempty ι] in
@[simp] lemma periodicLogFourierCoeff_zero : periodicLogFourierCoeff (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicLogFourierCoeff]
lemma norm_periodicLogFourierCoeff_sq (k : PeriodicFrequency ι) :
    ‖periodicLogFourierCoeff k‖^2 =
      (periodicLogConstant ι/(2*Real.pi)^(Fintype.card ι))^2 *
      ‖periodicFrequencyVector k‖⁻¹^(2*Fintype.card ι) := by
  by_cases hk : k = 0
  · subst k
    have hd : 2*Fintype.card ι ≠ 0 := by have := Fintype.card_pos (α := ι); omega
    simp [hd]
  · simp only [periodicLogFourierCoeff,hk,ite_false,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]
    rw [← pow_mul]
    congr 1
    congr 1
    omega
lemma summable_periodicLogFourierCoeff_sq :
    Summable (fun k : PeriodicFrequency ι => ‖periodicLogFourierCoeff k‖^2) := by
  exact (summable_periodicFrequency_inv_doubleDimension.mul_left
    ((periodicLogConstant ι/(2*Real.pi)^(Fintype.card ι))^2)).congr
      fun k => (norm_periodicLogFourierCoeff_sq k).symm
lemma periodicLogFourierCoeff_memℓp : Memℓp (@periodicLogFourierCoeff ι _) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).2
  simpa using (summable_periodicLogFourierCoeff_sq (ι := ι))
def periodicLogCoefficientVector : ℓ²(PeriodicFrequency ι,ℂ) :=
  ⟨periodicLogFourierCoeff,periodicLogFourierCoeff_memℓp⟩

local instance periodicCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
def periodicFourierBasis : HilbertBasis (PeriodicFrequency ι) ℂ (Lp ℂ 2 (periodicHaar ι)) :=
  UnitAddTorus.mFourierBasis (d := ι)
omit [Nonempty ι] in
lemma periodicFourierBasis_repr (f : Lp ℂ 2 (periodicHaar ι)) (k : PeriodicFrequency ι) :
    (periodicFourierBasis (ι := ι)).repr f k = UnitAddTorus.mFourierCoeff f k :=
  UnitAddTorus.mFourierBasis_repr f k

def periodicLogL2 : Lp ℂ 2 (periodicHaar ι) :=
  (periodicFourierBasis (ι := ι)).repr.symm periodicLogCoefficientVector
lemma periodicLogL2_fourierCoeff (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (periodicLogL2 (ι := ι)) k = periodicLogFourierCoeff k := by
  rw [← periodicFourierBasis_repr]
  simp [periodicLogL2,periodicLogCoefficientVector]
lemma periodicLogL2_unique (f : Lp ℂ 2 (periodicHaar ι))
    (hf : ∀ k : PeriodicFrequency ι,UnitAddTorus.mFourierCoeff f k = periodicLogFourierCoeff k) :
    f = periodicLogL2 := by
  apply (periodicFourierBasis (ι := ι)).repr.injective
  apply lp.ext
  funext k
  simpa only [periodicFourierBasis_repr,periodicLogL2_fourierCoeff] using hf k
lemma periodicLogL2_integrable : Integrable (periodicLogL2 (ι := ι) : PeriodicTorus ι → ℂ) (periodicHaar ι) :=
  MemLp.integrable (by norm_num) (Lp.memLp _)
lemma periodicLogL2_integral_zero : (∫ x,periodicLogL2 (ι := ι) x ∂periodicHaar ι) = 0 := by
  simpa only [UnitAddTorus.mFourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_smul,periodicLogFourierCoeff_zero] using!
      periodicLogL2_fourierCoeff (0 : PeriodicFrequency ι)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogL2_fourierCoeff
#print axioms DGRHS.Periodic.periodicLogL2_integral_zero
#check @DGRHS.Periodic.periodicLogL2_fourierCoeff
