import DGRHS.Gaussian.PeriodicResidualTiltJensen

/-! Genuine finite first-shell Gaussian spatial tilt. Proper normalization,
strict positivity and bounded density are derived for each actual field;
no favorable Gaussian field or exponential moment is supplied. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
attribute [local fun_prop] periodicFirstShellMode_continuous

def periodicFirstShellField (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∑ q : ι × Bool,(t*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*z q)*periodicFirstShellMode q x

def periodicFirstShellFieldBound (t : ℝ) (z : ι × Bool → ℝ) : ℝ :=
  ∑ q : ι × Bool,|t*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*z q|

def periodicFirstShellWeight (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) : ℝ :=
  Real.exp (periodicFirstShellField t z x)

def periodicFirstShellNormalizer (t : ℝ) (z : ι × Bool → ℝ) : ℝ :=
  ∫ x,periodicFirstShellWeight t z x ∂periodicHaar ι

def periodicFirstShellTiltDensity (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicFirstShellWeight t z x/periodicFirstShellNormalizer t z

lemma periodicFirstShellField_abs_le (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) :
    |periodicFirstShellField t z x|≤periodicFirstShellFieldBound t z := by
  unfold periodicFirstShellField periodicFirstShellFieldBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (periodicFirstShellMode_abs_le_one q x) (abs_nonneg _)).trans_eq (mul_one _)

lemma periodicFirstShellWeight_continuous (t : ℝ) (z : ι × Bool → ℝ) :
    Continuous (periodicFirstShellWeight t z) := by unfold periodicFirstShellWeight periodicFirstShellField;fun_prop

lemma periodicFirstShellWeight_integrable (t : ℝ) (z : ι × Bool → ℝ) :
    Integrable (periodicFirstShellWeight t z) (periodicHaar ι) :=
  (periodicFirstShellWeight_continuous t z).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma periodicFirstShellWeight_bounds (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) :
    Real.exp (-periodicFirstShellFieldBound t z)≤periodicFirstShellWeight t z x ∧
      periodicFirstShellWeight t z x≤Real.exp (periodicFirstShellFieldBound t z) := by
  have h := abs_le.mp (periodicFirstShellField_abs_le t z x)
  exact ⟨Real.exp_le_exp.mpr h.1,Real.exp_le_exp.mpr h.2⟩

lemma periodicFirstShellNormalizer_pos (t : ℝ) (z : ι × Bool → ℝ) :
    0<periodicFirstShellNormalizer t z := by
  have h := integral_mono (integrable_const (Real.exp (-periodicFirstShellFieldBound t z)))
    (periodicFirstShellWeight_integrable t z) (fun x => (periodicFirstShellWeight_bounds t z x).1)
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at h
  exact (Real.exp_pos _).trans_le h

lemma periodicFirstShellTiltDensity_measurable (t : ℝ) (z : ι × Bool → ℝ) :
    Measurable (periodicFirstShellTiltDensity t z) :=
  (periodicFirstShellWeight_continuous t z).measurable.div_const _

lemma periodicFirstShellTiltDensity_pos (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) :
    0<periodicFirstShellTiltDensity t z x :=
  div_pos (Real.exp_pos _) (periodicFirstShellNormalizer_pos t z)

lemma periodicFirstShellTiltDensity_bound (t : ℝ) (z : ι × Bool → ℝ) (x : PeriodicTorus ι) :
    ‖periodicFirstShellTiltDensity t z x‖≤
      Real.exp (periodicFirstShellFieldBound t z)/periodicFirstShellNormalizer t z := by
  rw [Real.norm_eq_abs,abs_of_pos (periodicFirstShellTiltDensity_pos t z x)]
  exact div_le_div_of_nonneg_right (periodicFirstShellWeight_bounds t z x).2
    (periodicFirstShellNormalizer_pos t z).le

lemma periodicFirstShellTiltDensity_integral (t : ℝ) (z : ι × Bool → ℝ) :
    (∫ x,periodicFirstShellTiltDensity t z x ∂periodicHaar ι)=1 := by
  unfold periodicFirstShellTiltDensity
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ (periodicFirstShellNormalizer_pos t z).ne'

/-- Genuine residual lower bound for the actually constructed first-shell
Gaussian spatial tilt, for every fixed field and every N>=1. -/
theorem periodic_firstShell_tilt_residual_lower (t : ℝ) (z : ι × Bool → ℝ)
    (β : ℝ) (hβ : 0≤β) (N : ℕ) (hN : 1≤N) :
    (1:ℝ≥0∞) ≤ ∫⁻ x : Fin N → PeriodicTorus ι,
      ENNReal.ofReal (Real.exp (β/(2*(N:ℝ))*∑ i,∑ j,
        if i=j then 0 else periodicFirstShellResidualPair (x i,x j)))
      ∂Measure.pi (fun _ => periodicBoundedDensityLaw (periodicFirstShellTiltDensity t z)) :=
  periodic_residual_tilt_extended_lower (periodicFirstShellTiltDensity t z)
    (periodicFirstShellTiltDensity_measurable t z) (fun x => (periodicFirstShellTiltDensity_pos t z x).le)
    _ (periodicFirstShellTiltDensity_bound t z) (periodicFirstShellTiltDensity_integral t z) β hβ N hN

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellField_abs_le
#print axioms DGRHS.Periodic.periodicFirstShellWeight_integrable
#print axioms DGRHS.Periodic.periodicFirstShellNormalizer_pos
#print axioms DGRHS.Periodic.periodicFirstShellTiltDensity_measurable
#print axioms DGRHS.Periodic.periodicFirstShellTiltDensity_pos
#print axioms DGRHS.Periodic.periodicFirstShellTiltDensity_bound
#print axioms DGRHS.Periodic.periodicFirstShellTiltDensity_integral
#print axioms DGRHS.Periodic.periodic_firstShell_tilt_residual_lower
#check @DGRHS.Periodic.periodic_firstShell_tilt_residual_lower
