import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Defs.D09_ParticleRates
import DGPS.SingularCounterexample.BarrierGeometry
import DGPS.SingularCounterexample.Particle.EnergyUpper
import DGPS.SingularCounterexample.Particle.MassLower
import DGPS.SingularCounterexample.Particle.TestFunction

/-!
# Support lower bound for the frozen particle entropy

The affine-minorant argument is the one used for
`DGPS.Examples.RoughBoundary.Bottleneck.entropy_lower_by_support_RUF047`.
Here the input need not be bounded, and the conclusion uses `SharpLSI.ent` directly.
-/

open MeasureTheory InformationTheory
open Filter
open scoped ENNReal

namespace DGPS.SingularCounterexample

private lemma mul_log_lower_affine {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    t * Real.log s + t - s ≤ t * Real.log t := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · rw [← hzero]
    simp only [zero_mul, add_zero, zero_sub]
    exact neg_nonpos.mpr hs.le
  · have hnn := mul_nonneg hs.le (klFun_nonneg (div_nonneg ht hs.le))
    have hid : s * klFun (t / s) =
        t * Real.log t - t * Real.log s + s - t := by
      rw [klFun_apply, Real.log_div hpos.ne' hs.ne']
      field_simp
    rw [hid] at hnn
    linarith

/-- SLC-N024: a nonnegative input supported on a measurable event has entropy at least its
mass times the logarithm of the reciprocal event probability. The bound also holds when the
event has probability one, and no finite-entropy assumption is required. -/
theorem entropy_support_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) {u : Ω → ℝ} (hu0 : ∀ x, 0 ≤ u x)
    (hu : Integrable u P)
    (hsupp : ∀ x, x ∉ A → u x = 0) (hm : 0 < ∫ x, u x ∂P) :
    ENNReal.ofReal ((∫ x, u x ∂P) * Real.log (1 / P.real A)) ≤ SharpLSI.ent P u := by
  by_cases hent : SharpLSI.ent P u = ⊤
  · simp [hent]
  have hlog : Integrable (fun x => u x * Real.log (u x)) P := by
    let m := ∫ x, u x ∂P
    have hm0 : 0 < m := hm
    have hpt : ∀ x, m * klFun (u x / m) =
        u x * Real.log (u x) - u x * Real.log m + m - u x := by
      intro x
      unfold klFun
      rcases (hu0 x).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [Real.log_div h.ne' hm0.ne']; field_simp
    have hmeas : AEStronglyMeasurable (fun x => m * klFun (u x / m)) P :=
      (continuous_klFun.comp_aestronglyMeasurable
        (hu.div_const m).aestronglyMeasurable).const_mul m
    have hnonneg : 0 ≤ᵐ[P] fun x => m * klFun (u x / m) :=
      Eventually.of_forall fun x => mul_nonneg hm0.le (klFun_nonneg (div_nonneg (hu0 x) hm0.le))
    have hkl : Integrable (fun x => m * klFun (u x / m)) P :=
      (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp (by
        simpa only [SharpLSI.ent, hu, ↓reduceIte] using hent)
    refine (((hkl.add (hu.mul_const (Real.log m))).sub (integrable_const m)).add hu).congr ?_
    filter_upwards [] with x
    change m * klFun (u x / m) + u x * Real.log m - m + u x = u x * Real.log (u x)
    rw [hpt]
    ring
  have hp : 0 < P.real A := by
    by_contra! hnonpos
    have hzero : P.real A = 0 := le_antisymm hnonpos measureReal_nonneg
    have hAzero : P A = 0 := (measureReal_eq_zero_iff (μ := P) (s := A)).mp hzero
    have hu_ae : u =ᵐ[P] 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hAzero] with x hx
      exact hsupp x hx
    exact hm.ne' (integral_eq_zero_of_ae hu_ae)
  set m := ∫ x, u x ∂P with hm_def
  set s := m / P.real A with hs_def
  have hs : 0 < s := div_pos hm hp
  have hsp : s * P.real A = m := by rw [hs_def]; field_simp
  have hlogratio : Real.log s - Real.log m = Real.log (1 / P.real A) := by
    rw [← Real.log_div hs.ne' hm.ne']
    congr 1
    rw [hs_def]
    field_simp
  have hind : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hg : Integrable (fun x => u x * Real.log s + u x -
      s * A.indicator (fun _ => (1 : ℝ)) x) P :=
    ((hu.mul_const _).add hu).sub (hind.const_mul s)
  have hpoint : ∀ x, u x * Real.log s + u x -
      s * A.indicator (fun _ => (1 : ℝ)) x ≤ u x * Real.log (u x) := by
    intro x
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx, mul_one] using
        mul_log_lower_affine hs (hu0 x)
    · simp [Set.indicator_of_notMem hx, hsupp x hx]
  have hint := integral_mono hg hlog hpoint
  have hcomp : ∫ x, (u x * Real.log s + u x -
      s * A.indicator (fun _ => (1 : ℝ)) x) ∂P = m * Real.log s := by
    have hi1 : Integrable (fun x => u x * Real.log s + u x) P :=
      (hu.mul_const (Real.log s)).add hu
    have hi2 : Integrable (fun x => s * A.indicator (fun _ => (1 : ℝ)) x) P :=
      hind.const_mul s
    rw [integral_sub hi1 hi2,
      integral_add (hu.mul_const (Real.log s)) hu, integral_mul_const, integral_const_mul,
      integral_indicator_const _ hA]
    simp only [smul_eq_mul, mul_one, ← hm_def]
    rw [hsp]
    ring
  rw [hcomp] at hint
  rw [SharpLSI.ent_eq_formula P u hu0 hu hlog]
  apply ENNReal.ofReal_le_ofReal
  change m * Real.log (1 / P.real A) ≤
    (∫ x, u x * Real.log (u x) ∂P) - m * Real.log m
  rw [← hlogratio]
  nlinarith

/-- If the support probability is at most `exp (-1)`, the support lower bound controls the
second moment itself. This form is convenient when the support probabilities tend to zero. -/
theorem entropy_ge_second_moment_of_small_support {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) {u : Ω → ℝ} (hu0 : ∀ x, 0 ≤ u x)
    (hu : Integrable u P) (hlog : Integrable (fun x => u x * Real.log (u x)) P)
    (hsupp : ∀ x, x ∉ A → u x = 0) (hm : 0 < ∫ x, u x ∂P)
    (hAprob : P.real A ≤ Real.exp (-1)) :
    ENNReal.ofReal (∫ x, u x ∂P) ≤ SharpLSI.ent P u := by
  clear hlog
  have hp : 0 < P.real A := by
    by_contra! hnonpos
    have hzero : P.real A = 0 := le_antisymm hnonpos measureReal_nonneg
    have hAzero : P A = 0 := (measureReal_eq_zero_iff (μ := P) (s := A)).mp hzero
    have hu_ae : u =ᵐ[P] 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hAzero] with x hx
      exact hsupp x hx
    exact hm.ne' (integral_eq_zero_of_ae hu_ae)
  have hprod : Real.exp 1 * P.real A ≤ 1 := by
    calc
      Real.exp 1 * P.real A ≤ Real.exp 1 * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hAprob (Real.exp_pos 1).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have hrecip : Real.exp 1 ≤ 1 / P.real A := (le_div_iff₀ hp).2 (by simpa using hprod)
  have hlogrecip : 1 ≤ Real.log (1 / P.real A) :=
    (Real.le_log_iff_exp_le (div_pos one_pos hp)).2 hrecip
  have hsupport := entropy_support_lower_bound hA hu0 hu hsupp hm
  apply le_trans ?_ hsupport
  apply ENNReal.ofReal_le_ofReal
  have hm_nonneg : 0 ≤ ∫ x, u x ∂P := hm.le
  nlinarith

/-- If a sequence of supports has probability tending to zero and its nonnegative inputs
have positive mass eventually, their entropies eventually dominate their masses. -/
theorem entropy_ge_mass_eventually_of_support_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : ℕ → Set Ω) (u : ℕ → Ω → ℝ)
    (hA : ∀ n, MeasurableSet (A n)) (hu0 : ∀ n x, 0 ≤ u n x)
    (hu : ∀ n, Integrable (u n) P)
    (hlog : ∀ n, Integrable (fun x => u n x * Real.log (u n x)) P)
    (hsupp : ∀ n x, x ∉ A n → u n x = 0)
    (hm : ∀ᶠ n in atTop, 0 < ∫ x, u n x ∂P)
    (hprob : Tendsto (fun n => P.real (A n)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, ENNReal.ofReal (∫ x, u n x ∂P) ≤ SharpLSI.ent P (u n) := by
  have hsmall : ∀ᶠ n in atTop, P.real (A n) ≤ Real.exp (-1) := by
    filter_upwards [hprob.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.exp (-1)))]
      with n hn
    exact hn.le
  filter_upwards [hm, hsmall] with n hmn hAn
  exact entropy_ge_second_moment_of_small_support (hA n) (hu0 n) (hu n) (hlog n)
    (hsupp n) hmn hAn

/-- A frozen infimum is zero when a sequence of admissible quotients tends to zero. -/
private theorem eq_zero_of_le_seq_tendsto_zero {q : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (hle : ∀ n, a ≤ q n) (hq : Tendsto q atTop (nhds 0)) : a = 0 := by
  have hconst : Tendsto (fun _ : ℕ => a) atTop (nhds 0) :=
    ENNReal.tendsto_atTop_zero.mpr (by
      intro ε hε
      obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hq ε hε
      exact ⟨N, fun n hn => le_trans (hle n) (hN n hn)⟩)
  exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm

/-- Package the nested `iInf` convention used by the frozen rates. -/
private theorem nested_iInf_eq_zero_of_admissible_sequence {α : Type*}
    (admissible : α → Prop) (quotient : α → ℝ≥0∞) (f : ℕ → α)
    (hf : ∀ n, admissible (f n))
    (hq : Tendsto (fun n => quotient (f n)) atTop (nhds 0)) :
    (⨅ g, ⨅ (_ : admissible g), quotient g) = 0 := by
  apply eq_zero_of_le_seq_tendsto_zero
  · intro n
    exact le_trans (iInf_le (fun g => ⨅ (_ : admissible g), quotient g) (f n))
      (iInf_le (fun _ : admissible (f n) => quotient (f n)) (hf n))
  · exact hq

/-- A lower-order exponent error can be absorbed into the factorial barrier in the numerator.
This form is set up for later substitution of the valley cost divided by `height`. -/
theorem inverse_width_separation_exp_height_error_tendsto_zero {c : ℝ} (hc : 0 < c)
    (e : ℕ → ℝ) (he : Tendsto (fun n => e n / height n) atTop (nhds 0)) :
    Tendsto (fun n => (width n * separation n)⁻¹ *
      Real.exp (e n - c * height n)) atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n => (width n)⁻¹ * Real.exp (-(c / 2) * height n) * (separation n)⁻¹)
      atTop (nhds 0) :=
    inverse_width_separation_exp_tendsto_zero (c := c / 2) (by positivity)
  have hbase' : Tendsto
      (fun n => (width n * separation n)⁻¹ * Real.exp (-(c / 2) * height n))
      atTop (nhds 0) := by
    simpa only [mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
  have habsorb : ∀ᶠ n in atTop, e n / height n < c / 2 :=
    he.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 2))
  have hbound : ∀ᶠ n in atTop,
      (width n * separation n)⁻¹ * Real.exp (e n - c * height n) ≤
        (width n * separation n)⁻¹ * Real.exp (-(c / 2) * height n) := by
    filter_upwards [habsorb] with n hn
    have herror : e n < (c / 2) * height n :=
      (div_lt_iff₀ (height_pos n)).mp hn
    have hexp : e n - c * height n ≤ -(c / 2) * height n := by nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
      (inv_nonneg.mpr (mul_nonneg (width_pos n).le (separation_pos n).le))
  have hnonneg (n : ℕ) :
      0 ≤ (width n * separation n)⁻¹ * Real.exp (e n - c * height n) :=
    mul_nonneg (inv_nonneg.mpr (mul_nonneg (width_pos n).le (separation_pos n).le))
      (Real.exp_pos _).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbase'
    (Filter.Eventually.of_forall hnonneg) hbound

/-- A constant partition-function loss plus any fixed multiple of the valley cost is still
negligible relative to the factorial barrier height. -/
theorem barrier_cost_error_ratio_tendsto_zero (C κ : ℝ) :
    Tendsto (fun n => (C + κ * valleyCost n) / height n) atTop (nhds 0) := by
  have hC : Tendsto (fun n => C / height n) atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall fun _ : ℕ => le_rfl)
      (Filter.Eventually.of_forall fun _ : ℕ => le_rfl)
      height_tendsto_atTop
  have hκ : Tendsto (fun n => κ * valleyCost n / height n) atTop (nhds 0) := by
    simpa [mul_div_assoc] using
      tendsto_const_nhds.mul valleyCost_ratio_tendsto_zero
  simpa [add_div] using hC.add hκ

/-- Convert eventual real-scale energy and mass bounds into convergence of the frozen
`ℝ≥0∞` quotient.  The denominator lower bound is strictly positive, so the comparison uses
the actual ENNReal division convention without an endpoint exception. -/
theorem ennreal_quotient_tendsto_zero_of_barrier_bounds
    {E M : ℕ → ℝ≥0∞} {C D c : ℝ} (_hC : 0 ≤ C) (hD : 0 < D) (hc : 0 < c)
    (e : ℕ → ℝ) (he : Tendsto (fun n => e n / height n) atTop (nhds 0))
    (hE : ∀ᶠ n in atTop,
      E n ≤ ENNReal.ofReal (C / width n * Real.exp (-c * height n)))
    (hM : ∀ᶠ n in atTop,
      ENNReal.ofReal (D * separation n * Real.exp (-e n)) ≤ M n) :
    Tendsto (fun n => E n / M n) atTop (nhds 0) := by
  have hAbsorb := inverse_width_separation_exp_height_error_tendsto_zero hc e he
  have hReal : Tendsto
      (fun n => C / D *
        ((width n * separation n)⁻¹ * Real.exp (e n - c * height n)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hAbsorb
  have hENN : Tendsto
      (fun n => ENNReal.ofReal (C / D *
        ((width n * separation n)⁻¹ * Real.exp (e n - c * height n))))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hReal
  have hquot : ∀ᶠ n in atTop,
      E n / M n ≤ ENNReal.ofReal (C / D *
        ((width n * separation n)⁻¹ * Real.exp (e n - c * height n))) := by
    filter_upwards [hE, hM] with n hEn hMn
    have hden : 0 < D * separation n * Real.exp (-e n) :=
      mul_pos (mul_pos hD (separation_pos n)) (Real.exp_pos _)
    have hwidth : width n ≠ 0 := (width_pos n).ne'
    have hseparation : separation n ≠ 0 := (separation_pos n).ne'
    have hexp : Real.exp (-e n) ≠ 0 := (Real.exp_pos _).ne'
    have hratio :
        (C / width n * Real.exp (-c * height n)) /
            (D * separation n * Real.exp (-e n)) =
          C / D * ((width n * separation n)⁻¹ *
            Real.exp (e n - c * height n)) := by
      have hexpRatio : Real.exp (-c * height n) / Real.exp (-e n) =
          Real.exp (e n - c * height n) := by
        calc
          Real.exp (-c * height n) / Real.exp (-e n) =
              Real.exp (-c * height n - -e n) := by rw [← Real.exp_sub]
          _ = Real.exp (e n - c * height n) := by congr 1; ring
      calc
        (C / width n * Real.exp (-c * height n)) /
            (D * separation n * Real.exp (-e n)) =
          C / D * (width n * separation n)⁻¹ *
            (Real.exp (-c * height n) / Real.exp (-e n)) := by
          field_simp [hwidth, hseparation, hD.ne', hexp]
        _ = C / D * ((width n * separation n)⁻¹ *
            Real.exp (e n - c * height n)) := by rw [hexpRatio]; ring
    calc
      E n / M n ≤
          ENNReal.ofReal (C / width n * Real.exp (-c * height n)) /
            ENNReal.ofReal (D * separation n * Real.exp (-e n)) :=
        ENNReal.div_le_div hEn hMn
      _ = ENNReal.ofReal
          ((C / width n * Real.exp (-c * height n)) /
            (D * separation n * Real.exp (-e n))) :=
        (ENNReal.ofReal_div_of_pos hden).symm
      _ = ENNReal.ofReal (C / D *
          ((width n * separation n)⁻¹ * Real.exp (e n - c * height n))) := by
        rw [hratio]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hENN ε hε
  have hbound : ∀ᶠ n in atTop,
      ENNReal.ofReal (C / D *
        ((width n * separation n)⁻¹ * Real.exp (e n - c * height n))) ≤ ε :=
    Filter.eventually_atTop.2 ⟨N, hN⟩
  have hfinal : ∀ᶠ n in atTop, E n / M n ≤ ε := by
    filter_upwards [hquot, hbound] with n hn hεn
    exact le_trans hn hεn
  exact Filter.eventually_atTop.mp hfinal

/-- A symmetric admissible sequence with vanishing Poincare quotients forces the frozen
symmetric Poincare rate to vanish. -/
theorem lamSym_zero_of_admissible_sequence {d N : ℕ}
    {V : SharpLSI.Torus d → ℝ} {W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ}
    (f : ℕ → SharpLSI.Config N d → ℝ)
    (hmem : ∀ n, SharpLSI.MemH1C (SharpLSI.gibbs V W N) (f n))
    (hsym : ∀ n, SharpLSI.IsSymmetric (f n))
    (hvar : ∀ n, 0 < SharpLSI.var (SharpLSI.gibbs V W N) (f n))
    (hq : Tendsto (fun n => SharpLSI.energy V W N (f n) /
      SharpLSI.var (SharpLSI.gibbs V W N) (f n)) atTop (nhds 0)) :
    SharpLSI.lamSym V W N = 0 := by
  simp only [SharpLSI.lamSym, Set.mem_ofPred_eq]
  exact nested_iInf_eq_zero_of_admissible_sequence
    (fun g => SharpLSI.MemH1C (SharpLSI.gibbs V W N) g ∧
      SharpLSI.IsSymmetric g ∧ 0 < SharpLSI.var (SharpLSI.gibbs V W N) g)
    (fun g => SharpLSI.energy V W N g / SharpLSI.var (SharpLSI.gibbs V W N) g)
    f (fun n => ⟨hmem n, hsym n, hvar n⟩) hq

/-- An admissible sequence with vanishing Poincare quotients forces the frozen full Poincare
rate to vanish. -/
theorem lamAll_zero_of_admissible_sequence {d N : ℕ}
    {V : SharpLSI.Torus d → ℝ} {W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ}
    (f : ℕ → SharpLSI.Config N d → ℝ)
    (hmem : ∀ n, SharpLSI.MemH1C (SharpLSI.gibbs V W N) (f n))
    (hvar : ∀ n, 0 < SharpLSI.var (SharpLSI.gibbs V W N) (f n))
    (hq : Tendsto (fun n => SharpLSI.energy V W N (f n) /
      SharpLSI.var (SharpLSI.gibbs V W N) (f n)) atTop (nhds 0)) :
    SharpLSI.lamAll V W N = 0 := by
  simp only [SharpLSI.lamAll, Set.mem_ofPred_eq]
  exact nested_iInf_eq_zero_of_admissible_sequence
    (fun g => SharpLSI.MemH1C (SharpLSI.gibbs V W N) g ∧
      0 < SharpLSI.var (SharpLSI.gibbs V W N) g)
    (fun g => SharpLSI.energy V W N g / SharpLSI.var (SharpLSI.gibbs V W N) g)
    f (fun n => ⟨hmem n, hvar n⟩) hq

/-- A symmetric admissible sequence with vanishing entropy quotients forces the frozen
symmetric logarithmic Sobolev rate to vanish. -/
theorem rSym_zero_of_admissible_sequence {d N : ℕ}
    {V : SharpLSI.Torus d → ℝ} {W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ}
    (f : ℕ → SharpLSI.Config N d → ℝ)
    (hmem : ∀ n, SharpLSI.MemH1C (SharpLSI.gibbs V W N) (f n))
    (hsym : ∀ n, SharpLSI.IsSymmetric (f n))
    (hent : ∀ n, 0 < SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => (f n X) ^ 2))
    (hq : Tendsto (fun n => 2 * SharpLSI.energy V W N (f n) /
      SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => (f n X) ^ 2)) atTop (nhds 0)) :
    SharpLSI.rSym V W N = 0 := by
  simp only [SharpLSI.rSym, Set.mem_ofPred_eq]
  exact nested_iInf_eq_zero_of_admissible_sequence
    (fun g => SharpLSI.MemH1C (SharpLSI.gibbs V W N) g ∧
      SharpLSI.IsSymmetric g ∧
      0 < SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => g X ^ 2))
    (fun g => 2 * SharpLSI.energy V W N g /
      SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => g X ^ 2))
    f (fun n => ⟨hmem n, hsym n, hent n⟩) hq

/-- An admissible sequence with vanishing entropy quotients forces the frozen full logarithmic
Sobolev rate to vanish. -/
theorem rAll_zero_of_admissible_sequence {d N : ℕ}
    {V : SharpLSI.Torus d → ℝ} {W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ}
    (f : ℕ → SharpLSI.Config N d → ℝ)
    (hmem : ∀ n, SharpLSI.MemH1C (SharpLSI.gibbs V W N) (f n))
    (hent : ∀ n, 0 < SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => (f n X) ^ 2))
    (hq : Tendsto (fun n => 2 * SharpLSI.energy V W N (f n) /
      SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => (f n X) ^ 2)) atTop (nhds 0)) :
    SharpLSI.rAll V W N = 0 := by
  simp only [SharpLSI.rAll, Set.mem_ofPred_eq]
  exact nested_iInf_eq_zero_of_admissible_sequence
    (fun g => SharpLSI.MemH1C (SharpLSI.gibbs V W N) g ∧
      0 < SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => g X ^ 2))
    (fun g => 2 * SharpLSI.energy V W N g /
      SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => g X ^ 2))
    f (fun n => ⟨hmem n, hent n⟩) hq

/-- Removing the symmetry constraint can only decrease either frozen rate. -/
theorem lamAll_le_lamSym {d N : ℕ}
    (V : SharpLSI.Torus d → ℝ) (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ) :
    SharpLSI.lamAll V W N ≤ SharpLSI.lamSym V W N := by
  simp only [SharpLSI.lamAll, SharpLSI.lamSym, Set.mem_ofPred_eq]
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  have hfAll : SharpLSI.MemH1C (SharpLSI.gibbs V W N) f ∧
      0 < SharpLSI.var (SharpLSI.gibbs V W N) f := ⟨hf.1, hf.2.2⟩
  exact le_trans (iInf_le _ f) (iInf_le _ hfAll)

/-- Removing the symmetry constraint can only decrease either frozen rate. -/
theorem rAll_le_rSym {d N : ℕ}
    (V : SharpLSI.Torus d → ℝ) (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ) :
    SharpLSI.rAll V W N ≤ SharpLSI.rSym V W N := by
  simp only [SharpLSI.rAll, SharpLSI.rSym, Set.mem_ofPred_eq]
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  have hfAll : SharpLSI.MemH1C (SharpLSI.gibbs V W N) f ∧
      0 < SharpLSI.ent (SharpLSI.gibbs V W N) (fun X => f X ^ 2) :=
    ⟨hf.1, hf.2.2⟩
  exact le_trans (iInf_le _ f) (iInf_le _ hfAll)

/-- The full Poincare rate is zero whenever the symmetric Poincare rate is zero. -/
theorem lamAll_eq_zero_of_lamSym_eq_zero {d N : ℕ}
    {V : SharpLSI.Torus d → ℝ} {W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ}
    (h : SharpLSI.lamSym V W N = 0) : SharpLSI.lamAll V W N = 0 := by
  apply le_antisymm
  · calc
      SharpLSI.lamAll V W N ≤ SharpLSI.lamSym V W N := lamAll_le_lamSym V W
      _ = 0 := h
  · exact bot_le

/-- The full logarithmic Sobolev rate is zero whenever the symmetric rate is zero. -/
theorem rAll_eq_zero_of_rSym_eq_zero {d N : ℕ}
    {V : SharpLSI.Torus d → ℝ} {W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ}
    (h : SharpLSI.rSym V W N = 0) : SharpLSI.rAll V W N = 0 := by
  apply le_antisymm
  · calc
      SharpLSI.rAll V W N ≤ SharpLSI.rSym V W N := rAll_le_rSym V W
      _ = 0 := h
  · exact bot_le

/-- The concrete particle cutoff tests are admissible for the frozen Gibbs law and are
symmetric. -/
theorem particleTest_admissible {N : ℕ} (n : ℕ)
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y) :
    SharpLSI.MemH1C
        (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N)
        (particleTest n : SharpLSI.Config N 1 → ℝ) ∧
      SharpLSI.IsSymmetric (particleTest n : SharpLSI.Config N 1 → ℝ) := by
  exact ⟨particleTest_memH1C (N := N) n W hWmeas hWlower,
    particleTest_isSymmetric (N := N) n⟩

/-- The bounded measurable particle tests have integrable second moment and entropy integrand
under the singular Gibbs law.  The logarithmic integrand is bounded on the compact range of
`particleTest n ^ 2` by continuity of `x * log x`, including at zero. -/
theorem particleTest_square_entropy_integrable {N : ℕ} (n : ℕ)
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y) :
    Integrable (fun X : SharpLSI.Config N 1 => (particleTest n X) ^ 2)
        (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) ∧
      Integrable (fun X : SharpLSI.Config N 1 =>
        (particleTest n X) ^ 2 * Real.log ((particleTest n X) ^ 2))
        (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) := by
  obtain ⟨a, ha⟩ := hWlower
  have hHmeas := zero_hamiltonian_measurable (d := 1) (N := N) W hWmeas
  have hHlower : ∀ X : SharpLSI.Config N 1,
      1 / (2 * (N : ℝ)) * (∑ _i : Fin N, ∑ _j : Fin N, a) ≤
        SharpLSI.hamiltonian (fun _ : SharpLSI.Torus 1 => 0) W N X :=
    fun X => zero_hamiltonian_lower_bound (d := 1) (N := N) W ha X
  letI hprob : IsProbabilityMeasure
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) :=
    gibbs_probability_of_hamiltonian_lower_bound (d := 1) (N := N)
      (fun _ : SharpLSI.Torus 1 => 0) W hHmeas hHlower
  let K : ℝ := (N : ℝ) ^ 2 / 2
  have hK : 0 ≤ K := by positivity
  have hfmeas : Measurable (particleTest n : SharpLSI.Config N 1 → ℝ) :=
    particleTest_measurable n
  have hfbound : ∀ X : SharpLSI.Config N 1,
      0 ≤ particleTest n X ∧ particleTest n X ≤ K := by
    intro X
    exact ⟨particleTest_nonneg n X, by simpa [K] using particleTest_le n X⟩
  have hsqmeas : Measurable (fun X : SharpLSI.Config N 1 => (particleTest n X) ^ 2) :=
    hfmeas.pow_const 2
  have hsq : Integrable (fun X : SharpLSI.Config N 1 => (particleTest n X) ^ 2)
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) := by
    refine Integrable.of_bound hsqmeas.aestronglyMeasurable (K ^ 2) ?_
    filter_upwards [] with X
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hfbound X).1 (hfbound X).2 2
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := K ^ 2)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlogmeas : Measurable (fun X : SharpLSI.Config N 1 =>
      (particleTest n X) ^ 2 * Real.log ((particleTest n X) ^ 2)) :=
    Real.continuous_mul_log.measurable.comp hsqmeas
  have hlog : Integrable (fun X : SharpLSI.Config N 1 =>
      (particleTest n X) ^ 2 * Real.log ((particleTest n X) ^ 2))
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) := by
    refine Integrable.of_bound hlogmeas.aestronglyMeasurable B ?_
    filter_upwards [] with X
    exact hB ((particleTest n X) ^ 2)
      ⟨sq_nonneg _, pow_le_pow_left₀ (hfbound X).1 (hfbound X).2 2⟩
  exact ⟨hsq, hlog⟩

/-- The actual particle cutoff sequence has vanishing frozen Poincare and logarithmic
Sobolev quotients. The mass exponent retains the complete valley cost; the scale lemma
absorbs it against the factorial height. -/
private theorem particleTest_actual_quotient_data {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (fun n => SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0)
      (perturbedInteraction B β η) N (particleTest n) /
        SharpLSI.var (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N)
          (particleTest n)) atTop (nhds 0) ∧
    (∀ᶠ n in atTop, 0 < SharpLSI.var
      (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N) (particleTest n)) ∧
    Tendsto (fun n => 2 * SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0)
      (perturbedInteraction B β η) N (particleTest n) /
        SharpLSI.ent (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N)
          (fun X => (particleTest n X) ^ 2)) atTop (nhds 0) ∧
    (∀ᶠ n in atTop, 0 < SharpLSI.ent
      (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N)
        (fun X => (particleTest n X) ^ 2)) := by
  obtain ⟨G, _hG0, hG⟩ := B.bounded_g
  obtain ⟨Cenergy, hCenergy, hEnergy⟩ :=
    particleTest_energy_upper_bound B hβ hη G hG hN
  obtain ⟨Cmass, d, hCmass, hd, hMoment⟩ :=
    particle_favorable_box_second_moment_lower hN B hβ hη
  let P := SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0)
    (perturbedInteraction B β η) N
  letI : IsProbabilityMeasure P :=
    singular_gibbs_isProbabilityMeasure B hβ hη (by omega)
  let κ : ℝ := (N : ℝ) / 2 * β * η
  let e : ℕ → ℝ := fun n => Cmass + κ * valleyCost n
  let rate : ℝ := β * η / (65 * (N : ℝ))
  let dVar : ℝ := d / 2
  have hdVar : 0 < dVar := by dsimp [dVar]; positivity
  have he : Tendsto (fun n => e n / height n) atTop (nhds 0) := by
    simpa [e, κ] using barrier_cost_error_ratio_tendsto_zero Cmass κ
  have hrate : 0 < rate := by dsimp [rate]; positivity
  have hMoment' (n : ℕ) :
      d * separation n * Real.exp (-e n) ≤
        ∫ X, (particleTest n X) ^ 2 ∂P := by
    simpa [e, κ, P] using hMoment n
  have hVarianceLower : ∀ᶠ n in atTop,
      ENNReal.ofReal (dVar * separation n * Real.exp (-e n)) ≤
        SharpLSI.var P (particleTest n) := by
    filter_upwards [particleTest_variance_eventually_lower B hβ hη
      (by omega : 0 < N)] with n hn
    have hhalf : dVar * separation n * Real.exp (-e n) ≤
        (1 / 2 : ℝ) * ∫ X, (particleTest n X) ^ 2 ∂P := by
      calc
        dVar * separation n * Real.exp (-e n) =
            (1 / 2 : ℝ) * (d * separation n * Real.exp (-e n)) := by
          simp only [dVar]
          ring
        _ ≤ (1 / 2 : ℝ) * ∫ X, (particleTest n X) ^ 2 ∂P :=
          mul_le_mul_of_nonneg_left (hMoment' n) (by norm_num)
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) *
          ∫ X, (particleTest n X) ^ 2 ∂P) := ENNReal.ofReal_le_ofReal hhalf
      _ ≤ SharpLSI.var P (particleTest n) := by simpa [P] using hn
  have hVariancePositive : ∀ᶠ n in atTop, 0 < SharpLSI.var P (particleTest n) := by
    filter_upwards [hVarianceLower] with n hn
    exact lt_of_lt_of_le
      (ENNReal.ofReal_pos.mpr
        (mul_pos (mul_pos hdVar (separation_pos n)) (Real.exp_pos _))) hn
  let W := perturbedInteraction B β η
  rcases perturbedInteraction_borel_lower_bound B hβ hη with ⟨hWmeas, ⟨a, hWlower⟩⟩
  obtain ⟨Csupport, hCsupport, hSupport⟩ :=
    particleTest_support_probability_upper B hβ hη (by omega : 0 < N)
  have hSupportReal : ∀ n : ℕ,
      P.real {X : SharpLSI.Config N 1 | particleTest n X ≠ 0} ≤
        Csupport * separation n := by
    intro n
    rw [Measure.real_def]
    have hENN : P {X : SharpLSI.Config N 1 | particleTest n X ≠ 0} ≤
        ENNReal.ofReal (Csupport * separation n) := by
      simpa [P] using hSupport n
    have htoReal := ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top) hENN
    rw [ENNReal.toReal_ofReal
      (mul_nonneg hCsupport.le (separation_pos n).le)] at htoReal
    exact htoReal
  have hSupportRealTendsto : Tendsto
      (fun n : ℕ => P.real {X : SharpLSI.Config N 1 | particleTest n X ≠ 0})
      atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ => Csupport * separation n) atTop (nhds 0) := by
      simpa [mul_comm] using separation_tendsto_zero.const_mul Csupport
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => measureReal_nonneg)
      hSupportReal
  have hEntropyMass : ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ X, (particleTest n X) ^ 2 ∂P) ≤
        SharpLSI.ent P (fun X => (particleTest n X) ^ 2) := by
    apply entropy_ge_mass_eventually_of_support_tendsto_zero
      (P := P)
      (A := fun n => {X : SharpLSI.Config N 1 | particleTest n X ≠ 0})
      (u := fun n X => (particleTest n X) ^ 2)
    · intro n
      exact ((measurableSet_singleton (0 : ℝ)).preimage (particleTest_measurable n)).compl
    · intro n X
      exact sq_nonneg _
    · intro n
      exact (particleTest_square_entropy_integrable n W hWmeas ⟨-a, hWlower⟩).1
    · intro n
      exact (particleTest_square_entropy_integrable n W hWmeas ⟨-a, hWlower⟩).2
    · intro n X hX
      have hzero : particleTest n X = 0 := by
        by_contra hne
        exact hX hne
      simp [hzero]
    · filter_upwards [] with n
      have hpos : 0 < d * separation n * Real.exp (-e n) :=
        mul_pos (mul_pos hd (separation_pos n)) (Real.exp_pos _)
      exact lt_of_lt_of_le hpos (hMoment' n)
    · exact hSupportRealTendsto
  have hEntropyLower : ∀ᶠ n in atTop,
      ENNReal.ofReal (d * separation n * Real.exp (-e n)) ≤
        SharpLSI.ent P (fun X => (particleTest n X) ^ 2) := by
    filter_upwards [hEntropyMass] with n hn
    exact (ENNReal.ofReal_le_ofReal (hMoment' n)).trans hn
  have hEntropyPositive : ∀ᶠ n in atTop,
      0 < SharpLSI.ent P (fun X => (particleTest n X) ^ 2) := by
    filter_upwards [hEntropyLower] with n hn
    exact lt_of_lt_of_le
      (ENNReal.ofReal_pos.mpr (mul_pos (mul_pos hd (separation_pos n)) (Real.exp_pos _))) hn
  have hqVar := ennreal_quotient_tendsto_zero_of_barrier_bounds
    (E := fun n => SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N (particleTest n))
    (M := fun n => SharpLSI.var P (particleTest n))
    (C := Cenergy) (D := dVar) (c := rate) (e := e)
    hCenergy.le hdVar hrate he
    (Filter.Eventually.of_forall fun n => by simpa [W, rate] using hEnergy n)
    hVarianceLower
  have hEnergyTwice : ∀ᶠ n in atTop,
      (2 : ℝ≥0∞) * SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N
          (particleTest n) ≤
        ENNReal.ofReal ((2 * Cenergy) / width n * Real.exp (-rate * height n)) := by
    filter_upwards [Filter.Eventually.of_forall hEnergy] with n hn
    calc
      (2 : ℝ≥0∞) * SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N
          (particleTest n) ≤
        2 * ENNReal.ofReal (Cenergy / width n * Real.exp (-(rate * height n))) :=
          mul_le_mul_of_nonneg_left (by simpa [W, rate, neg_mul] using hn) (by norm_num)
      _ = ENNReal.ofReal
          (2 * (Cenergy / width n * Real.exp (-(rate * height n)))) := by
        calc
          _ = ENNReal.ofReal (2 : ℝ) *
              ENNReal.ofReal (Cenergy / width n * Real.exp (-(rate * height n))) := by
            norm_num
          _ = ENNReal.ofReal
              (2 * (Cenergy / width n * Real.exp (-(rate * height n)))) :=
            (ENNReal.ofReal_mul (p := 2)
              (q := Cenergy / width n * Real.exp (-(rate * height n)))
              (by norm_num : (0 : ℝ) ≤ 2)).symm
      _ = ENNReal.ofReal
          ((2 * Cenergy) / width n * Real.exp (-rate * height n)) := by
        congr 1
        rw [neg_mul]
        ring
  have hqEnt := ennreal_quotient_tendsto_zero_of_barrier_bounds
    (E := fun n => (2 : ℝ≥0∞) *
      SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N (particleTest n))
    (M := fun n => SharpLSI.ent P (fun X => (particleTest n X) ^ 2))
    (C := 2 * Cenergy) (D := d) (c := rate) (e := e)
    (by positivity) hd hrate he
    hEnergyTwice hEntropyLower
  exact ⟨by simpa [P, W] using hqVar, hVariancePositive,
    by simpa [P, W] using hqEnt, hEntropyPositive⟩

/-- The singular particle model has zero symmetric Poincare rate for every fixed `N ≥ 2`
and every positive pair of perturbation parameters. -/
theorem particleTest_lamSym_zero {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    SharpLSI.lamSym (fun _ : SharpLSI.Torus 1 => 0) (perturbedInteraction B β η) N = 0 := by
  obtain ⟨hq, hpos, _, _⟩ := particleTest_actual_quotient_data hN B hβ hη
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hpos
  let W := perturbedInteraction B β η
  let P := SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N
  rcases perturbedInteraction_borel_lower_bound B hβ hη with ⟨hWmeas, ⟨a, hWlower⟩⟩
  let f : ℕ → SharpLSI.Config N 1 → ℝ := fun n => particleTest (n + n₀)
  have hmem : ∀ n, SharpLSI.MemH1C P (f n) := by
    intro n
    exact (particleTest_admissible (n + n₀) W hWmeas ⟨-a, hWlower⟩).1
  have hsym : ∀ n, SharpLSI.IsSymmetric (f n) := by
    intro n
    exact (particleTest_admissible (n + n₀) W hWmeas ⟨-a, hWlower⟩).2
  have hvar : ∀ n, 0 < SharpLSI.var P (f n) := by
    intro n
    exact hn₀ (n + n₀) (by omega)
  have hq : Tendsto (fun n => SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N (f n) /
      SharpLSI.var P (f n)) atTop (nhds 0) := by
    convert hq.comp (tendsto_add_atTop_nat n₀) using 1
    funext n
    rfl
  exact lamSym_zero_of_admissible_sequence f hmem hsym hvar hq

/-- The full Poincare rate vanishes because it is bounded above by the symmetric rate. -/
theorem particleTest_lamAll_zero {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    SharpLSI.lamAll (fun _ : SharpLSI.Torus 1 => 0) (perturbedInteraction B β η) N = 0 :=
  lamAll_eq_zero_of_lamSym_eq_zero (particleTest_lamSym_zero hN B hβ hη)

/-- The singular particle model has zero symmetric logarithmic Sobolev rate for every fixed
`N ≥ 2` and every positive pair of perturbation parameters. -/
theorem particleTest_rSym_zero {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    SharpLSI.rSym (fun _ : SharpLSI.Torus 1 => 0) (perturbedInteraction B β η) N = 0 := by
  obtain ⟨_, _, hq, hpos⟩ := particleTest_actual_quotient_data hN B hβ hη
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hpos
  let W := perturbedInteraction B β η
  let P := SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N
  rcases perturbedInteraction_borel_lower_bound B hβ hη with ⟨hWmeas, ⟨a, hWlower⟩⟩
  let f : ℕ → SharpLSI.Config N 1 → ℝ := fun n => particleTest (n + n₀)
  have hmem : ∀ n, SharpLSI.MemH1C P (f n) := by
    intro n
    exact (particleTest_admissible (n + n₀) W hWmeas ⟨-a, hWlower⟩).1
  have hsym : ∀ n, SharpLSI.IsSymmetric (f n) := by
    intro n
    exact (particleTest_admissible (n + n₀) W hWmeas ⟨-a, hWlower⟩).2
  have hent : ∀ n, 0 < SharpLSI.ent P (fun X => (f n X) ^ 2) := by
    intro n
    exact hn₀ (n + n₀) (by omega)
  have hq : Tendsto (fun n => 2 * SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N (f n) /
      SharpLSI.ent P (fun X => (f n X) ^ 2)) atTop (nhds 0) := by
    convert hq.comp (tendsto_add_atTop_nat n₀) using 1
    funext n
    rfl
  exact rSym_zero_of_admissible_sequence f hmem hsym hent hq

/-- The full logarithmic Sobolev rate vanishes because it is bounded above by the symmetric
rate. -/
theorem particleTest_rAll_zero {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    SharpLSI.rAll (fun _ : SharpLSI.Torus 1 => 0) (perturbedInteraction B β η) N = 0 :=
  rAll_eq_zero_of_rSym_eq_zero (particleTest_rSym_zero hN B hβ hη)

/-- Once the concrete cutoff-test variance is positive and its frozen quotient tends to zero,
the symmetric Poincare rate vanishes. -/
theorem lamSym_zero_of_particleTest_quotient_tendsto {N : ℕ}
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y)
    (hvar : ∀ n, 0 < SharpLSI.var
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) (particleTest n))
    (hq : Tendsto (fun n => SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N
        (particleTest n) /
      SharpLSI.var (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) (particleTest n))
      atTop (nhds 0)) :
    SharpLSI.lamSym (fun _ : SharpLSI.Torus 1 => 0) W N = 0 := by
  apply lamSym_zero_of_admissible_sequence (f := fun n => particleTest n)
  · exact fun n => (particleTest_admissible n W hWmeas hWlower).1
  · exact fun n => (particleTest_admissible n W hWmeas hWlower).2
  · exact hvar
  · exact hq

/-- Once the concrete cutoff-test variance is positive and its frozen quotient tends to zero,
the full Poincare rate vanishes. -/
theorem lamAll_zero_of_particleTest_quotient_tendsto {N : ℕ}
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y)
    (hvar : ∀ n, 0 < SharpLSI.var
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) (particleTest n))
    (hq : Tendsto (fun n => SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N
        (particleTest n) /
      SharpLSI.var (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) (particleTest n))
      atTop (nhds 0)) :
    SharpLSI.lamAll (fun _ : SharpLSI.Torus 1 => 0) W N = 0 := by
  apply lamAll_zero_of_admissible_sequence (f := fun n => particleTest n)
  · exact fun n => (particleTest_admissible n W hWmeas hWlower).1
  · exact hvar
  · exact hq

/-- Once the concrete cutoff-test entropy is positive and its frozen quotient tends to zero,
the symmetric logarithmic Sobolev rate vanishes. -/
theorem rSym_zero_of_particleTest_quotient_tendsto {N : ℕ}
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y)
    (hent : ∀ n, 0 < SharpLSI.ent
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N)
      (fun X => (particleTest n X) ^ 2))
    (hq : Tendsto (fun n => 2 * SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N
        (particleTest n) /
      SharpLSI.ent (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N)
        (fun X => (particleTest n X) ^ 2)) atTop (nhds 0)) :
    SharpLSI.rSym (fun _ : SharpLSI.Torus 1 => 0) W N = 0 := by
  apply rSym_zero_of_admissible_sequence (f := fun n => particleTest n)
  · exact fun n => (particleTest_admissible n W hWmeas hWlower).1
  · exact fun n => (particleTest_admissible n W hWmeas hWlower).2
  · exact hent
  · exact hq

/-- Once the concrete cutoff-test entropy is positive and its frozen quotient tends to zero,
the full logarithmic Sobolev rate vanishes. -/
theorem rAll_zero_of_particleTest_quotient_tendsto {N : ℕ}
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y)
    (hent : ∀ n, 0 < SharpLSI.ent
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N)
      (fun X => (particleTest n X) ^ 2))
    (hq : Tendsto (fun n => 2 * SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0) W N
        (particleTest n) /
      SharpLSI.ent (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N)
        (fun X => (particleTest n X) ^ 2)) atTop (nhds 0)) :
    SharpLSI.rAll (fun _ : SharpLSI.Torus 1 => 0) W N = 0 := by
  apply rAll_zero_of_admissible_sequence (f := fun n => particleTest n)
  · exact fun n => (particleTest_admissible n W hWmeas hWlower).1
  · exact hent
  · exact hq

end DGPS.SingularCounterexample
