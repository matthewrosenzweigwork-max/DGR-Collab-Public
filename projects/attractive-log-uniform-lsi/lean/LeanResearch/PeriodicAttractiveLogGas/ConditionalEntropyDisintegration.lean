import LeanResearch.PeriodicAttractiveLogGas.RelativeEntropyVariational
import LeanResearch.PeriodicAttractiveLogGas.PositiveProductConditionals
import LeanResearch.PeriodicAttractiveLogGas.ReferenceConditionalNormalization
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Bounded density tilts and conditional entropy in source 2699–2708.
Zero section mass is handled explicitly. The actual extended entropy and
actual density measures are retained throughout. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace PeriodicAttractiveLogGas.ConditionalEntropyDisintegration

variable {α : Type*} [MeasurableSpace α] {P : Measure α} {F : α → ℝ}

def normalizedTilt (P : Measure α) (F : α → ℝ) : Measure α :=
  P.withDensity (fun x => ENNReal.ofReal (F x / ∫ y, F y ∂P))

theorem normalizedTilt_zero_mass (hM : ∫ x, F x ∂P = 0) :
    normalizedTilt P F = 0 := by
  simp only [normalizedTilt, hM, div_zero, ENNReal.ofReal_zero]
  exact MeasureTheory.withDensity_zero

theorem normalizedTilt_probability [IsProbabilityMeasure P]
    (hF0 : ∀ᵐ x ∂P, 0 ≤ F x) (hi : Integrable F P)
    (hM : 0 < ∫ x, F x ∂P) : IsProbabilityMeasure (normalizedTilt P F) := by
  constructor
  rw [normalizedTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (hF0.mono fun x hx => div_nonneg hx hM.le), integral_div, div_self hM.ne', ENNReal.ofReal_one]

/-- Algebra at density zeros is part of the identity, rather than a
positivity hypothesis on the test function. -/
theorem normalized_log_density {u m : ℝ} (hm : m ≠ 0) :
    (u / m) * Real.log (u / m) = (u * Real.log u - u * Real.log m) / m := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [Real.log_div hu hm]
    ring

theorem zero_mass_entropy [IsProbabilityMeasure P] (hF : Measurable F)
    {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ F x ∧ F x ≤ K) (hM : ∫ x, F x ∂P = 0) :
    F =ᵐ[P] 0 ∧ entropy P F = 0 := by
  have hI := (RelativeEntropyVariational.bounded_density_integrable hF hb).1
  have hz : F =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae (hb.mono fun _ hx => hx.1) hI).mp hM
  exact ⟨hz, (entropy_congr_ae hz).trans (entropy_zero P)⟩

/-- Exact source normalization identity, with finite log integral proved,
including the zero-mass branch. -/
theorem entropy_normalizedTilt [IsProbabilityMeasure P] (hF : Measurable F)
    {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ F x ∧ F x ≤ K) :
    Integrable (fun x => Real.log (F x / ∫ y, F y ∂P)) (normalizedTilt P F) ∧
      entropy P F =
        (((∫ x, F x ∂P) * ∫ x, Real.log (F x / ∫ y, F y ∂P) ∂normalizedTilt P F : ℝ) : EReal) := by
  obtain ⟨hI, hlog⟩ := RelativeEntropyVariational.bounded_density_integrable hF hb
  have hF0 := hb.mono fun _ hx => hx.1
  have hM0 : 0 ≤ ∫ x, F x ∂P := integral_nonneg_of_ae hF0
  by_cases hM : ∫ x, F x ∂P = 0
  · rw [normalizedTilt_zero_mass hM]
    refine ⟨integrable_zero_measure, ?_⟩
    rw [(zero_mass_entropy hF hb hM).2, hM]
    simp
  · have hMp : 0 < ∫ x, F x ∂P := lt_of_le_of_ne hM0 (Ne.symm hM)
    let _ := normalizedTilt_probability hF0 hI hMp
    have hq : Measurable (fun x => F x / ∫ y, F y ∂P) := hF.div_const _
    have hq0 : ∀ᵐ x ∂P, 0 ≤ F x / ∫ y, F y ∂P := hF0.mono fun _ hx => div_nonneg hx hM0
    have hqb : ∀ᵐ x ∂P, 0 ≤ F x / ∫ y, F y ∂P ∧
        F x / ∫ y, F y ∂P ≤ K / ∫ y, F y ∂P := by
      filter_upwards [hb] with x hx
      exact ⟨div_nonneg hx.1 hM0, div_le_div_of_nonneg_right hx.2 hM0⟩
    have he := RelativeEntropyVariational.bounded_tilt_entropy_eq
      (P := P) (Q := normalizedTilt P F) rfl hq hqb
    refine ⟨he.1, ?_⟩
    rw [entropy_eq_integral hF0 hlog,
      DensityMoments.integral_density (μ := P) (ν := normalizedTilt P F) rfl hq hq0]
    congr 1
    have hp : (fun x => (F x / ∫ y, F y ∂P) * Real.log (F x / ∫ y, F y ∂P)) =
        fun x => (F x * Real.log (F x) - F x * Real.log (∫ y, F y ∂P)) / ∫ y, F y ∂P := by
      funext x
      exact normalized_log_density hM
    rw [hp, integral_div, integral_sub hlog (hI.mul_const _), integral_mul_const]
    field_simp

theorem normalizedTilt_log_integral [IsProbabilityMeasure P] (hF : Measurable F)
    {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ F x ∧ F x ≤ K) :
    (∫ x, Real.log (F x / ∫ y, F y ∂P) ∂normalizedTilt P F) =
      ((∫ x, F x * Real.log (F x) ∂P) -
        (∫ x, F x ∂P) * Real.log (∫ x, F x ∂P)) / ∫ x, F x ∂P := by
  by_cases hM : ∫ x, F x ∂P = 0
  · rw [normalizedTilt_zero_mass hM, hM]
    simp
  · have he := (entropy_normalizedTilt hF hb).2
    rw [entropy_eq_integral (hb.mono fun _ hx => hx.1)
      (RelativeEntropyVariational.bounded_density_integrable hF hb).2] at he
    apply (eq_div_iff hM).mpr
    have hh : (∫ x, F x * Real.log (F x) ∂P) -
        (∫ x, F x ∂P) * Real.log (∫ x, F x ∂P) =
        (∫ x, F x ∂P) * ∫ x, Real.log (F x / ∫ y, F y ∂P) ∂normalizedTilt P F := by
      exact_mod_cast he
    simpa only [mul_comm] using hh.symm

/-- Normalization commutes with an actual measurable pushforward when
the density is pulled back along that same map. -/
theorem normalizedTilt_map {γ : Type*} [MeasurableSpace γ] (P : Measure α)
    (φ : α → γ) (hφ : Measurable φ) {G : γ → ℝ} (hG : Measurable G) :
    Measure.map φ (normalizedTilt P (G ∘ φ)) = normalizedTilt (Measure.map φ P) G := by
  have hm : (∫ y, G y ∂Measure.map φ P) = ∫ x, G (φ x) ∂P :=
    integral_map_of_stronglyMeasurable hφ hG.stronglyMeasurable
  unfold normalizedTilt
  rw [hm]
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH hφ]
  have hq : Measurable (fun x => ENNReal.ofReal ((G ∘ φ) x / ∫ y, (G ∘ φ) y ∂P)) :=
    ((hG.comp hφ).div_const _).ennreal_ofReal
  have hh : Measurable (fun x => H (φ x)) := hH.comp hφ
  rw [lintegral_withDensity_eq_lintegral_mul P hq hh,
    lintegral_withDensity_eq_lintegral_mul (Measure.map φ P) (hG.div_const _).ennreal_ofReal hH,
    lintegral_map ((hG.div_const _).ennreal_ofReal.mul hH) hφ]
  rfl

section Kernels

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (κ : Kernel A B) [IsMarkovKernel κ] {F : A × B → ℝ}

def sectionMass (F : A × B → ℝ) (x : A) : ℝ := ∫ y, F (x, y) ∂κ x

/-- The literal conditional relative entropy of the normalized section tilt.
At zero section mass the measure and this integral are both zero. -/
def conditionalLogEntropy (F : A × B → ℝ) (x : A) : ℝ :=
  ∫ y, Real.log (F (x, y) / sectionMass κ F x)
    ∂normalizedTilt (κ x) (fun y => F (x, y))

/-- The finite real value of the existing extended entropy. The equality
with that entropy is proved below, so this does not change its definition. -/
def conditionalEntropyValue (F : A × B → ℝ) (x : A) : ℝ :=
  (∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) -
    sectionMass κ F x * Real.log (sectionMass κ F x)

theorem measurable_sectionMass (hF : Measurable F) : Measurable (sectionMass κ F) :=
  hF.stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem measurable_conditionalEntropyValue (hF : Measurable F) :
    Measurable (conditionalEntropyValue κ F) := by
  have hL := Real.continuous_mul_log.measurable.comp hF
  exact hL.stronglyMeasurable.integral_kernel_prod_right'.measurable.sub
    (Real.continuous_mul_log.measurable.comp (measurable_sectionMass κ hF))

theorem conditionalEntropyValue_eq_entropy (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) (x : A) :
    (conditionalEntropyValue κ F x : EReal) = entropy (κ x) (fun y => F (x, y)) := by
  exact (entropy_eq_integral (Eventually.of_forall fun y => (hb x y).1)
    (RelativeEntropyVariational.bounded_density_integrable (hF.comp measurable_prodMk_left)
      (Eventually.of_forall (hb x))).2).symm

theorem sectionMass_bounds (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) (x : A) :
    0 ≤ sectionMass κ F x ∧ sectionMass κ F x ≤ K := by
  have hf : Measurable (fun y => F (x, y)) := hF.comp measurable_prodMk_left
  have hi := (RelativeEntropyVariational.bounded_density_integrable (P := κ x) hf
    (Eventually.of_forall (hb x))).1
  refine ⟨integral_nonneg fun y => (hb x y).1, ?_⟩
  have hh := integral_mono_ae hi (integrable_const K)
    (Eventually.of_forall fun y => (hb x y).2)
  simpa only [sectionMass, integral_const, probReal_univ, one_smul] using! hh

theorem conditionalLogEntropy_formula (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) (x : A) :
    conditionalLogEntropy κ F x =
      ((∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) -
        sectionMass κ F x * Real.log (sectionMass κ F x)) / sectionMass κ F x :=
  normalizedTilt_log_integral (hF.comp measurable_prodMk_left) (Eventually.of_forall (hb x))

theorem measurable_conditionalLogEntropy (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) :
    Measurable (conditionalLogEntropy κ F) := by
  have hm := measurable_sectionMass κ hF
  have hL : Measurable (fun p => F p * Real.log (F p)) :=
    Real.continuous_mul_log.measurable.comp hF
  have hA : Measurable (fun x => ∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) :=
    hL.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have he : conditionalLogEntropy κ F = fun x =>
      ((∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) -
        sectionMass κ F x * Real.log (sectionMass κ F x)) / sectionMass κ F x :=
    funext (conditionalLogEntropy_formula κ hF hb)
  rw [he]
  exact (hA.sub (Real.continuous_mul_log.measurable.comp hm)).div hm

/-- Multiplication by the true section mass cancels the normalization even
where the test function has zero conditional mass. -/
theorem sectionMass_mul_conditionalLogEntropy (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) (x : A) :
    sectionMass κ F x * conditionalLogEntropy κ F x =
      (∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) -
        sectionMass κ F x * Real.log (sectionMass κ F x) := by
  have hf : Measurable (fun y => F (x, y)) := hF.comp measurable_prodMk_left
  have he := (entropy_normalizedTilt (P := κ x) hf (Eventually.of_forall (hb x))).2
  rw [entropy_eq_integral (Eventually.of_forall fun y => (hb x y).1)
    (RelativeEntropyVariational.bounded_density_integrable hf (Eventually.of_forall (hb x))).2] at he
  exact_mod_cast he.symm

theorem integrable_mass_mul_conditionalLogEntropy (ρ : Measure A) [IsFiniteMeasure ρ]
    (hF : Measurable F) {K : ℝ} (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) :
    Integrable (fun x => sectionMass κ F x * conditionalLogEntropy κ F x) ρ := by
  have hm := measurable_sectionMass κ hF
  have hmlog := (RelativeEntropyVariational.bounded_density_integrable (P := ρ) hm
    (Eventually.of_forall (sectionMass_bounds κ hF hb))).2
  have hL : Measurable (fun p => F p * Real.log (F p)) :=
    Real.continuous_mul_log.measurable.comp hF
  have hA : Measurable (fun x => ∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) :=
    hL.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hAi : Integrable (fun x => ∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) ρ := by
    apply Integrable.of_bound hA.aestronglyMeasurable (1 + K ^ 2)
    apply Eventually.of_forall
    intro x
    have hi := (RelativeEntropyVariational.bounded_density_integrable (P := κ x)
      (hF.comp measurable_prodMk_left) (Eventually.of_forall (hb x))).2
    calc
      _ ≤ ∫ y, ‖F (x, y) * Real.log (F (x, y))‖ ∂κ x := norm_integral_le_integral_norm _
      _ ≤ ∫ _y, (1 + K ^ 2 : ℝ) ∂κ x := by
        apply integral_mono_ae hi.norm (integrable_const _)
        apply Eventually.of_forall
        intro y
        change ‖F (x, y) * Real.log (F (x, y))‖ ≤ 1 + K ^ 2
        rw [Real.norm_eq_abs]
        have hh := hb x y
        exact (RelativeEntropyVariational.abs_mul_log_le_one_add_sq hh.1).trans
          (by nlinarith [mul_nonneg hh.1 (sub_nonneg.mpr hh.2)])
      _ = _ := by simp
  have he : (fun x => sectionMass κ F x * conditionalLogEntropy κ F x) = fun x =>
      (∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) -
        sectionMass κ F x * Real.log (sectionMass κ F x) :=
    funext (sectionMass_mul_conditionalLogEntropy κ hF hb)
  rw [he]
  exact hAi.sub hmlog

/-- Exact averaged conditional entropy identity under the actual tilted
outside measure. Its logarithmic entropy is integrable as a conclusion. -/
theorem averaged_conditional_entropy (ρ : Measure A) [IsProbabilityMeasure ρ]
    (hF : Measurable F) {K : ℝ} (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K)
    (hS : 0 < ∫ x, sectionMass κ F x ∂ρ) :
    Integrable (conditionalLogEntropy κ F) (normalizedTilt ρ (sectionMass κ F)) ∧
      (∫ x, sectionMass κ F x ∂ρ) *
        ∫ x, conditionalLogEntropy κ F x ∂normalizedTilt ρ (sectionMass κ F) =
      ∫ x, (∫ y, F (x, y) * Real.log (F (x, y)) ∂κ x) -
        sectionMass κ F x * Real.log (sectionMass κ F x) ∂ρ := by
  let S := ∫ x, sectionMass κ F x ∂ρ
  have hm := measurable_sectionMass κ hF
  have hm0 : ∀ᵐ x ∂ρ, 0 ≤ sectionMass κ F x :=
    Eventually.of_forall fun x => (sectionMass_bounds κ hF hb x).1
  have hq0 : ∀ᵐ x ∂ρ, 0 ≤ sectionMass κ F x / S := hm0.mono fun _ hx => div_nonneg hx hS.le
  have hi := integrable_mass_mul_conditionalLogEntropy κ ρ hF hb
  have hid (x : A) : (sectionMass κ F x / S) * conditionalLogEntropy κ F x =
      (sectionMass κ F x * conditionalLogEntropy κ F x) / S := by ring
  have hqi : Integrable (fun x => (sectionMass κ F x / S) * conditionalLogEntropy κ F x) ρ := by
    simp_rw [hid]
    exact hi.div_const _
  refine ⟨(RelativeEntropyVariational.integrable_density_iff rfl (hm.div_const S) hq0).mpr hqi, ?_⟩
  rw [DensityMoments.integral_density (μ := ρ) (ν := normalizedTilt ρ (sectionMass κ F)) rfl (hm.div_const S) hq0]
  change S * (∫ x, (sectionMass κ F x / S) * conditionalLogEntropy κ F x ∂ρ) = _
  simp_rw [hid, sectionMass_mul_conditionalLogEntropy κ hF hb]
  rw [integral_div]
  change S * (_ / S) = _
  field_simp [show S ≠ 0 from hS.ne']

/-- The actual section tilt. A zero-mass section is the zero measure; that
section has zero mass for the tilted outside law as well. -/
def sectionTiltKernel (F : A × B → ℝ) : Kernel A B :=
  κ.withDensity (fun x y => ENNReal.ofReal (F (x, y) / sectionMass κ F x))

theorem measurable_sectionDensity (hF : Measurable F) :
    Measurable (fun p : A × B => ENNReal.ofReal (F p / sectionMass κ F p.1)) :=
  (hF.div ((measurable_sectionMass κ hF).comp measurable_fst)).ennreal_ofReal

instance sectionTiltKernel_sfinite : IsSFiniteKernel (sectionTiltKernel κ F) :=
  Kernel.IsSFiniteKernel.withDensity κ (fun _ _ => ENNReal.ofReal_ne_top)

theorem sectionTiltKernel_apply (hF : Measurable F) (x : A) :
    sectionTiltKernel κ F x = normalizedTilt (κ x) (fun y => F (x, y)) :=
  Kernel.withDensity_apply κ
    (f := fun x y => ENNReal.ofReal (F (x, y) / sectionMass κ F x))
    (measurable_sectionDensity κ hF) x

/-- Disintegration of the actual tilted joint law. Cancellation at a
zero-mass section uses nonnegativity and zero integral, rather than an
unjustified division by its mass. -/
theorem normalizedTilt_compProd (ρ : Measure A) [IsProbabilityMeasure ρ]
    (hF : Measurable F) {K : ℝ} (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K)
    (hS : 0 < ∫ x, sectionMass κ F x ∂ρ) :
    normalizedTilt (ρ ⊗ₘ κ) F =
      normalizedTilt ρ (sectionMass κ F) ⊗ₘ sectionTiltKernel κ F := by
  have hm := measurable_sectionMass κ hF
  have hi := (RelativeEntropyVariational.bounded_density_integrable (P := ρ ⊗ₘ κ) hF
    (Eventually.of_forall fun p => hb p.1 p.2)).1
  have hmass : (∫ p, F p ∂(ρ ⊗ₘ κ)) = ∫ x, sectionMass κ F x ∂ρ :=
    Measure.integral_compProd hi
  let : IsSFiniteKernel (κ.withDensity
      (fun x y => ENNReal.ofReal (F (x, y) / sectionMass κ F x))) :=
    sectionTiltKernel_sfinite κ
  unfold normalizedTilt sectionTiltKernel
  rw [Measure.withDensity_compProd_withDensity (hm.div_const _).ennreal_ofReal
    (measurable_sectionDensity κ hF), hmass]
  apply withDensity_congr_ae
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun (hF.div_const _).ennreal_ofReal
      (((hm.div_const _).ennreal_ofReal.comp measurable_fst).mul
        (measurable_sectionDensity κ hF)))
  apply Eventually.of_forall
  intro x
  by_cases hz : sectionMass κ F x = 0
  · have hfz := (zero_mass_entropy (P := κ x) (hF.comp measurable_prodMk_left)
      (Eventually.of_forall (hb x)) hz).1
    filter_upwards [hfz] with y hy
    dsimp only [Pi.mul_apply, Function.comp_apply, Prod.fst] at *
    simp only [hy, Pi.zero_apply, zero_div, ENNReal.ofReal_zero, hz, zero_mul]
  · apply Eventually.of_forall
    intro y
    have hm0 := (sectionMass_bounds κ hF hb x).1
    dsimp only [Pi.mul_apply, Function.comp_apply, Prod.fst]
    rw [← ENNReal.ofReal_mul (div_nonneg hm0 hS.le)]
    congr 1
    field_simp [hz]

/-- An everywhere Markov version of the tilted conditional law. On a
zero-mass section its value is irrelevant to the tilted joint law. -/
def conditionalTiltKernel (F : A × B → ℝ) (hF : Measurable F) {K : ℝ}
    (_hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) : Kernel A B :=
  Kernel.piecewise (measurableSet_eq_fun (measurable_sectionMass κ hF)
    (measurable_const (a := (0 : ℝ)))) κ (sectionTiltKernel κ F)

theorem conditionalTiltKernel_apply (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) (x : A)
    (hx : sectionMass κ F x ≠ 0) :
    conditionalTiltKernel κ F hF hb x = normalizedTilt (κ x) (fun y => F (x, y)) := by
  simp only [conditionalTiltKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hx, ite_false]
  exact sectionTiltKernel_apply κ hF x

instance conditionalTiltKernel_markov (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) :
    IsMarkovKernel (conditionalTiltKernel κ F hF hb) := by
  constructor
  intro x
  by_cases hx : sectionMass κ F x = 0
  · simp only [conditionalTiltKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hx, ite_true]
    infer_instance
  · rw [conditionalTiltKernel_apply κ hF hb x hx]
    exact normalizedTilt_probability (Eventually.of_forall fun y => (hb x y).1)
      (RelativeEntropyVariational.bounded_density_integrable (P := κ x)
        (hF.comp measurable_prodMk_left) (Eventually.of_forall (hb x))).1
      (lt_of_le_of_ne (sectionMass_bounds κ hF hb x).1 (Ne.symm hx))

theorem conditionalTiltKernel_ae_eq (ρ : Measure A) (hF : Measurable F) {K : ℝ}
    (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K) :
    conditionalTiltKernel κ F hF hb =ᵐ[normalizedTilt ρ (sectionMass κ F)] sectionTiltKernel κ F := by
  apply (ae_withDensity_iff ((measurable_sectionMass κ hF).div_const _).ennreal_ofReal).mpr
  apply Eventually.of_forall
  intro x hx
  have hm : sectionMass κ F x ≠ 0 := by
    intro hz
    exact hx (by simp only [hz, zero_div, ENNReal.ofReal_zero])
  rw [conditionalTiltKernel_apply κ hF hb x hm, sectionTiltKernel_apply κ hF x]

theorem normalizedTilt_disintegration (ρ : Measure A) [IsProbabilityMeasure ρ]
    (hF : Measurable F) {K : ℝ} (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K)
    (hS : 0 < ∫ x, sectionMass κ F x ∂ρ) :
    normalizedTilt (ρ ⊗ₘ κ) F =
      normalizedTilt ρ (sectionMass κ F) ⊗ₘ conditionalTiltKernel κ F hF hb := by
  rw [normalizedTilt_compProd κ ρ hF hb hS]
  exact Measure.compProd_congr (conditionalTiltKernel_ae_eq κ ρ hF hb).symm

theorem normalizedTilt_outside_marginal (ρ : Measure A) [IsProbabilityMeasure ρ]
    (hF : Measurable F) {K : ℝ} (hb : ∀ x y, 0 ≤ F (x, y) ∧ F (x, y) ≤ K)
    (hS : 0 < ∫ x, sectionMass κ F x ∂ρ) :
    (normalizedTilt (ρ ⊗ₘ κ) F).fst = normalizedTilt ρ (sectionMass κ F) := by
  have hm := measurable_sectionMass κ hF
  have hmb : ∀ᵐ x ∂ρ, 0 ≤ sectionMass κ F x ∧ sectionMass κ F x ≤ K :=
    Eventually.of_forall (sectionMass_bounds κ hF hb)
  let : IsProbabilityMeasure (normalizedTilt ρ (sectionMass κ F)) :=
    normalizedTilt_probability (hmb.mono fun _ hx => hx.1)
      (RelativeEntropyVariational.bounded_density_integrable hm hmb).1 hS
  rw [normalizedTilt_disintegration κ ρ hF hb hS, Measure.fst_compProd]

end Kernels

section SplitLaw

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem normalizedTilt_equiv (e : α ≃ᵐ A × B) (hF : Measurable F) :
    Measure.map e (normalizedTilt P F) =
      normalizedTilt (Measure.map e P) (F ∘ e.symm) := by
  simpa only [Function.comp_def, e.symm_apply_apply] using
    normalizedTilt_map P e e.measurable (hF.comp e.symm.measurable)

/-- The exact averaged identity transported back through the actual
coordinate split. The outside law is the pushforward of the tilted
original law, not a separately chosen law. -/
theorem entropy_disintegration_equiv (e : α ≃ᵐ A × B)
    (ρ : Measure A) [IsProbabilityMeasure ρ] (κ : Kernel A B) [IsMarkovKernel κ]
    (hsplit : Measure.map e P = ρ ⊗ₘ κ) (hF : Measurable F)
    {K : ℝ} (hb : ∀ x, 0 ≤ F x ∧ F x ≤ K) (hS : 0 < ∫ x, F x ∂P) :
    Integrable (fun x => conditionalLogEntropy κ (F ∘ e.symm) (e x).1) (normalizedTilt P F) ∧
    (∫ x, F x ∂P) *
      (∫ x, conditionalLogEntropy κ (F ∘ e.symm) (e x).1 ∂normalizedTilt P F) =
      ∫ a, (∫ b, F (e.symm (a, b)) * Real.log (F (e.symm (a, b))) ∂κ a) -
        sectionMass κ (F ∘ e.symm) a * Real.log (sectionMass κ (F ∘ e.symm) a) ∂ρ := by
  have hf : Measurable (F ∘ e.symm) := hF.comp e.symm.measurable
  have hfb : ∀ a b, 0 ≤ (F ∘ e.symm) (a, b) ∧ (F ∘ e.symm) (a, b) ≤ K :=
    fun a b => hb (e.symm (a, b))
  have hi := (RelativeEntropyVariational.bounded_density_integrable (P := ρ ⊗ₘ κ) hf
    (Eventually.of_forall fun p => hfb p.1 p.2)).1
  have hmass : (∫ a, sectionMass κ (F ∘ e.symm) a ∂ρ) = ∫ x, F x ∂P := by
    simp only [sectionMass]
    rw [← Measure.integral_compProd hi, ← hsplit,
      integral_map_of_stronglyMeasurable e.measurable hf.stronglyMeasurable]
    simp only [Function.comp_apply, e.symm_apply_apply]
  have hS' : 0 < ∫ a, sectionMass κ (F ∘ e.symm) a ∂ρ := by rw [hmass]; exact hS
  have hmap := normalizedTilt_equiv (P := P) e hF
  rw [hsplit] at hmap
  have hout : Measure.map (fun x => (e x).1) (normalizedTilt P F) =
      normalizedTilt ρ (sectionMass κ (F ∘ e.symm)) := by
    calc
      _ = (Measure.map e (normalizedTilt P F)).fst := by
        rw [Measure.fst, Measure.map_map measurable_fst e.measurable]
        rfl
      _ = _ := by rw [hmap, normalizedTilt_outside_marginal κ ρ hf hfb hS']
  have hav := averaged_conditional_entropy κ ρ hf hfb hS'
  have hm := measurable_conditionalLogEntropy κ hf hfb
  have hφ : Measurable (fun x => (e x).1) := measurable_fst.comp e.measurable
  rw [← hout] at hav
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable hφ.aemeasurable).mp hav.1, ?_⟩
  rw [hmass, integral_map_of_stronglyMeasurable hφ hm.stronglyMeasurable] at hav
  exact hav.2

end SplitLaw

section ActualGibbsLaw

open OneCoordinateConditionals MeshCells CellRestrictions LabelOccupations
  ReferenceDensityChange ReferenceSelfTerms

/-- The existing coordinate equivalence, with the outside coordinates first. -/
def configurationSplit {n : ℕ} (i : Fin (n + 1)) :
    Configuration (n + 1) ≃ᵐ Configuration n × Torus :=
  (siteEquiv i).trans MeasurableEquiv.prodComm

@[simp] theorem configurationSplit_apply {n : ℕ} (i : Fin (n + 1))
    (X : Configuration (n + 1)) : configurationSplit i X = (removeSite i X, X i) := rfl

@[simp] theorem configurationSplit_symm_apply {n : ℕ} (i : Fin (n + 1))
    (p : Configuration n × Torus) :
    (configurationSplit i).symm p = insertSite i p.2 p.1 := rfl

@[simp] theorem configurationSplit_insertSite {n : ℕ} (i : Fin (n + 1))
    (Y : Configuration n) (z : Torus) : configurationSplit i (insertSite i z Y) = (Y, z) := by
  simp only [configurationSplit_apply, removeSite_insertSite, insertSite_self]

theorem split_law_of_lintegral {n : ℕ} (i : Fin (n + 1))
    (P : Measure (Configuration (n + 1))) [IsProbabilityMeasure P]
    (κ : Kernel (Configuration n) Torus) [IsMarkovKernel κ]
    (hdis : ∀ G : Configuration (n + 1) → ℝ≥0∞, Measurable G →
      (∫⁻ X, G X ∂P) = ∫⁻ Y, ∫⁻ z, G (insertSite i z Y) ∂κ Y
        ∂Measure.map (removeSite i) P) :
    Measure.map (configurationSplit i) P = (Measure.map (removeSite i) P) ⊗ₘ κ := by
  apply Measure.ext_of_lintegral
  intro G hG
  rw [lintegral_map hG (configurationSplit i).measurable, Measure.lintegral_compProd hG]
  have hh := hdis (G ∘ configurationSplit i) (hG.comp (configurationSplit i).measurable)
  simpa only [Function.comp_apply, configurationSplit_insertSite] using hh

/-- The supplied source identity for the actual prescribed-cell Gibbs law.
The chosen source reference family is an earlier mathematical dependency;
no entropy or disintegration conclusion is assumed here. -/
theorem source_entropy_disintegration {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (i : Fin (n + 1)) {F : Configuration (n + 1) → ℝ}
    (hF : Measurable F) {K : ℝ} (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    let F' := fun p : Configuration n × Torus => F (insertSite i p.2 p.1)
    Integrable (fun X => conditionalLogEntropy κ F' (removeSite i X))
        (normalizedTilt (labelGibbsMeasure hJ η β) F) ∧
      (∫ X, F X ∂labelGibbsMeasure hJ η β) *
        (∫ X, conditionalLogEntropy κ F' (removeSite i X)
          ∂normalizedTilt (labelGibbsMeasure hJ η β) F) =
        ∫ Y, (∫ z, F (insertSite i z Y) * Real.log (F (insertSite i z Y)) ∂κ Y) -
          sectionMass κ F' Y * Real.log (sectionMass κ F' Y)
          ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) := by
  let P := labelGibbsMeasure hJ η β
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let : IsProbabilityMeasure P := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  let : IsMarkovKernel κ := PositiveProductConditionals.isMarkovKernel_conditionalKernel
    (μ (η i)) (referenceTilt μ η β) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  have hsplit : Measure.map (configurationSplit i) P = (Measure.map (removeSite i) P) ⊗ₘ κ := by
    apply split_law_of_lintegral
    intro G hG
    exact ReferenceConditionalNormalization.reference_lintegral_disintegrate
      hJ hN μ η hβ hsub hformula i hG
  simpa only [Function.comp_def, configurationSplit_symm_apply, configurationSplit_apply] using!
    entropy_disintegration_equiv (P := P) (configurationSplit i) (Measure.map (removeSite i) P)
      κ hsplit hF hb hS

/-- The exact summed identity used in the defective LSI proof. Both
expectations are taken under the literal original and tilted Gibbs laws. -/
theorem source_sum_entropy_disintegration {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    {F : Configuration (n + 1) → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K) (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) :
    let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    let F' := fun i (p : Configuration n × Torus) => F (insertSite i p.2 p.1)
    (∫ X, F X ∂labelGibbsMeasure hJ η β) *
      (∑ i, ∫ X, conditionalLogEntropy (κ i) (F' i) (removeSite i X)
        ∂normalizedTilt (labelGibbsMeasure hJ η β) F) =
      ∑ i, ∫ X, conditionalEntropyValue (κ i) (F' i) (removeSite i X)
        ∂labelGibbsMeasure hJ η β := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let : IsMarkovKernel (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i) :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  have hh := (source_entropy_disintegration hJ hN μ η hβ hsub hformula i hF hb hS).2
  have hf : Measurable (fun p : Configuration n × Torus => F (insertSite i p.2 p.1)) :=
    hF.comp ((measurable_insertSite i).comp measurable_swap)
  have hm := measurable_conditionalEntropyValue
    (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i) hf
  change _ = ∫ X, conditionalEntropyValue _ _ (removeSite i X) ∂labelGibbsMeasure hJ η β
  rw [← integral_map_of_stronglyMeasurable (measurable_removeSite i) hm.stronglyMeasurable]
  exact hh

end ActualGibbsLaw

end PeriodicAttractiveLogGas.ConditionalEntropyDisintegration
