import DGRHS.Concentration.MasterTail

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Concentration

def masterCutoffValues {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ → Ω × Ω → ℝ) (m : ℝ → ℝ) (u₀ : ℝ) : Set ℝ :=
  {s | ∃ u, u₀ ≤ u ∧ min u (m u)*(1+(eLpNormEssSup (q u) (μ.prod μ)).toReal) = s}

def masterCutoffSize {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ → Ω × Ω → ℝ) (m : ℝ → ℝ) (u₀ : ℝ) : ℝ := sSup (masterCutoffValues μ q m u₀)

lemma masterCutoffSize_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ → Ω × Ω → ℝ) (m : ℝ → ℝ) (u₀ : ℝ)
    (hFinite : BddAbove (masterCutoffValues μ q m u₀)) (u : ℝ) (hu : u₀ ≤ u) :
    min u (m u)*(1+(eLpNormEssSup (q u) (μ.prod μ)).toReal) ≤ masterCutoffSize μ q m u₀ :=
  le_csSup hFinite ⟨u,hu,rfl⟩

lemma masterCutoffSize_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ → Ω × Ω → ℝ) (m : ℝ → ℝ) (u₀ : ℝ)
    (hFinite : BddAbove (masterCutoffValues μ q m u₀)) (hu₀ : 0 ≤ u₀) (hm : 0 ≤ m u₀) :
    0 ≤ masterCutoffSize μ q m u₀ :=
  (mul_nonneg (le_min hu₀ hm) (by positivity)).trans (masterCutoffSize_bound μ q m u₀ hFinite u₀ le_rfl)

/-- Branch-local source master hypotheses. These are actual cutoff kernels,
comparison/cap events, moments, and the exact accepted integral operator;
no tail, exponential-integrability, or concentration conclusion is a field. -/
structure MasterCutoffData {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : (Fin n → Ω) → ℝ) (u₀ : ℝ) where
  kernel : ℝ → Ω × Ω → ℝ
  cap : ℝ → ℝ
  measurable : ∀ u, u₀ ≤ u → Measurable (kernel u)
  memLp : ∀ u, u₀ ≤ u → MemLp (kernel u) ∞ (μ.prod μ)
  symmetric : ∀ u, u₀ ≤ u → ∀ x y, kernel u (x,y) = kernel u (y,x)
  canonical : ∀ u, u₀ ≤ u → ∀ᵐ x ∂μ, ∫ y,kernel u (x,y) ∂μ = 0
  cap_pos : ∀ u, u₀ ≤ u → 0 < cap u
  compare : ∀ u, u₀ ≤ u → ∀ᵐ ω ∂Measure.pi (fun _ : Fin n ↦ μ), u ≤ X ω → u ≤ iidNegativeStatistic n (kernel u) ω
  capped : ∀ u, u₀ ≤ u → ∀ᵐ ω ∂Measure.pi (fun _ : Fin n ↦ μ), iidNegativeStatistic n (kernel u) ω ≤ cap u
  row : ∀ u, u₀ ≤ u → ∀ᵐ x ∂μ, (∫ y,(kernel u (x,y))^2 ∂μ) ≤ 1/glzUniversalTailConstant
  joint : ∀ u, u₀ ≤ u → (∫ p,(kernel u p)^2 ∂μ.prod μ) ≤ 1/glzUniversalTailConstant
  operator : ∀ u (hu : u₀ ≤ u), ‖DGRHS.Kernel.integralOperator (kernel u) ((memLp u hu).mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ≤ 1/glzUniversalTailConstant
  size_finite : BddAbove (masterCutoffValues μ kernel cap u₀)

/-- The large-N master partition/control endpoint from actual cutoff data and
source growth. The tail and exponential integrability are derived. -/
theorem master_exponential_moment_large {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (X : (Fin n → Ω) → ℝ)
    (hX : AEMeasurable X (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀) (d : MasterCutoffData μ n X u₀)
    (hGrowth : 2*glzUniversalTailConstant^2*masterCutoffSize μ d.kernel d.cap u₀ ≤ (n : ℝ)) :
    Integrable (fun ω ↦ Real.exp (X ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp (X ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ Real.exp u₀+glzUniversalTailConstant := by
  let π := Measure.pi (fun _ : Fin n ↦ μ)
  have hL := glzUniversalTailConstant_pos
  have hTail : ∀ u, u₀ < u → π {ω | u ≤ X ω} ≤ ENNReal.ofReal (glzUniversalTailConstant*Real.exp (-2*u)) := by
    intro u hu
    have hu0 := hu.le
    by_cases hm : u ≤ d.cap u
    · let a := (eLpNormEssSup (d.kernel u) (μ.prod μ)).toReal
      have hsz := masterCutoffSize_bound μ d.kernel d.cap u₀ d.size_finite u hu0
      rw [min_eq_left hm] at hsz
      have hg : 2*glzUniversalTailConstant^2*u*(1+a) ≤ (n : ℝ) := by
        calc
          _ = 2*glzUniversalTailConstant^2*(u*(1+a)) := by ring
          _ ≤ 2*glzUniversalTailConstant^2*masterCutoffSize μ d.kernel d.cap u₀ := mul_le_mul_of_nonneg_left hsz (by positivity)
          _ ≤ _ := hGrowth
      have ht := iid_master_tail μ n hn (d.kernel u) (d.measurable u hu0) (d.memLp u hu0)
        (d.symmetric u hu0) (d.canonical u hu0) a u ENNReal.toReal_nonneg (hu₀.trans hu0)
        (ae_absolute_le_essSup_toReal (μ.prod μ) (d.kernel u) (d.memLp u hu0))
        (d.row u hu0) (d.joint u hu0) (d.operator u hu0) hg
      have hi := measure_mono_ae (d.compare u hu0)
      have hr := ENNReal.toReal_mono (measure_ne_top π {ω | u ≤ iidNegativeStatistic n (d.kernel u) ω}) hi
      have hreal := hr.trans ht
      have hh := ENNReal.ofReal_le_ofReal hreal
      change ENNReal.ofReal (π {ω | u ≤ X ω}).toReal ≤ ENNReal.ofReal (glzUniversalTailConstant*Real.exp (-2*u)) at hh
      rw [ENNReal.ofReal_toReal (measure_ne_top π {ω | u ≤ X ω})] at hh
      exact hh
    · have hzero : π {ω | u ≤ X ω} = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [d.compare u hu0,d.capped u hu0] with ω hcmp hcap
        intro hω
        exact hm ((hcmp hω).trans hcap)
      rw [hzero]
      exact zero_le
  obtain ⟨hi,hb⟩ := exponential_integrable_of_tail π X hX u₀ glzUniversalTailConstant hL.le hTail
  refine ⟨hi,hb.trans ?_⟩
  apply add_le_add le_rfl
  have he : Real.exp (-u₀) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -u₀ ≤ 0)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hL.le

/-- The small-N master endpoint uses the same actual size supremum and cap,
with rational heights accounting for all height-dependent null sets. -/
theorem master_exponential_moment_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : (Fin n → Ω) → ℝ)
    (hX : AEMeasurable X (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 0 ≤ u₀) (d : MasterCutoffData μ n X u₀) :
    Integrable (fun ω ↦ Real.exp (X ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp (X ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ Real.exp (u₀+masterCutoffSize μ d.kernel d.cap u₀) := by
  have hb := master_bounded_branch (Measure.pi (fun _ : Fin n ↦ μ)) X hX
    (fun u ↦ iidNegativeStatistic n (d.kernel u)) d.cap
    (fun u ↦ (eLpNormEssSup (d.kernel u) (μ.prod μ)).toReal) u₀ (masterCutoffSize μ d.kernel d.cap u₀)
    hu₀ (masterCutoffSize_nonneg μ d.kernel d.cap u₀ d.size_finite hu₀ (d.cap_pos u₀ le_rfl).le)
    (fun _ _ ↦ ENNReal.toReal_nonneg) d.compare d.capped
    (fun u hu ↦ masterCutoffSize_bound μ d.kernel d.cap u₀ d.size_finite u hu)
  exact hb.2

#print axioms DGRHS.Concentration.master_exponential_moment_large
#print axioms DGRHS.Concentration.master_exponential_moment_bounded
#check @DGRHS.Concentration.master_exponential_moment_large
#check @DGRHS.Concentration.master_exponential_moment_bounded
end DGRHS.Concentration
