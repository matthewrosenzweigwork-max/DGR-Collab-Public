import DGRHS.CLT.BoundedLinearWeightMoments
import DGRHS.Commutator.SourceRieszLocalEmpirical
import DGRHS.Dynamics.BoundedRawProductLinearMGF
import DGRHS.Entropy.AbsoluteExponentialTransfer

/-!
Packet P11c, unit 2 (part 1): kernel-generic ingredients of the torus Lemma 8.1
(`lem:dynamicEntropyTransfers`, TeX 3771-3794), valid on any measurable space `X` (here the torus):

* the raw fluctuation `dynRawFluctuation μ q N ω = N^{-1/2} Σ_i (q(ω_i) - ∫ q dμ)` and the empirical
  difference `dynEmpiricalDifference μ q N ω = ∫ q dμ_N - ∫ q dμ` (the torus analogues of
  `sourceRieszDynamicRawFluctuation` and `sourceRieszDynamicEmpiricalDifference`);
* Lemma 8.1(iii) core: for a Gibbs law `Q = μ^{⊗N}.tilted u` with a partition lower bound `Zlow` and a
  doubled partition bound `C₂`, every bounded measurable `q` of oscillation `≤ L` has `Q`-exponential
  moments of both signs bounded by `C = √(e^{L²/2}) √C₂ / Zlow` and hence, for every `ν` of finite
  relative entropy `≤ H`, `∫ |raw fluctuation| dν ≤ max(H + log(2C), 0)`;
* Lemma 8.1(ii) core: absolute expectation of a scaled transport energy under finite relative entropy
  from two-sign exponential moments;
* the elementary interpolation `e^{a t} ≤ 1 + e^{b t}` for `0 ≤ a ≤ b`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Periodic

section Generic
variable {X : Type*} [MeasurableSpace X]

/-- The raw fluctuation `N^{-1/2} Σ_i (q(ω_i) - ∫ q dμ)`. -/
def dynRawFluctuation (μ : Measure X) (q : X → ℝ) (N : ℕ) (ω : Fin N → X) : ℝ :=
  (Real.sqrt N)⁻¹ * ∑ i : Fin N, (q (ω i) - ∫ y, q y ∂μ)

lemma measurable_dynRawFluctuation (μ : Measure X) (q : X → ℝ) (hq : Measurable q) (N : ℕ) :
    Measurable (dynRawFluctuation μ q N) := by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact (hq.comp (measurable_pi_apply i)).sub_const _

/-- The empirical difference `∫ q dμ_N - ∫ q dμ`. -/
def dynEmpiricalDifference [MeasurableSingletonClass X] (μ : Measure X) (q : X → ℝ) (N : ℕ)
    (ω : Fin N → X) : ℝ :=
  (∫ x, q x ∂DGRHS.Commutator.sourceRieszLocalEmpiricalLaw N ω) - ∫ x, q x ∂μ

lemma dynEmpiricalDifference_eq [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → ℝ) (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → X) :
    dynEmpiricalDifference μ q N ω = (Real.sqrt N)⁻¹ * dynRawFluctuation μ q N ω := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq := Real.sq_sqrt hn.le
  unfold dynEmpiricalDifference dynRawFluctuation
  rw [DGRHS.Commutator.integral_sourceRieszLocalEmpiricalLaw]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hi : (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv_rev, ← pow_two, hsq]
  rw [← mul_assoc, hi]
  field_simp

lemma measurable_dynEmpiricalDifference [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (q : X → ℝ) (hq : Measurable q) (N : ℕ) (hN : 1 ≤ N) :
    Measurable (dynEmpiricalDifference μ q N) := by
  have : dynEmpiricalDifference μ q N = fun ω => (Real.sqrt N)⁻¹ * dynRawFluctuation μ q N ω :=
    funext (dynEmpiricalDifference_eq μ q N hN)
  rw [this]
  exact (measurable_dynRawFluctuation μ q hq N).const_mul _

lemma measurable_dynEmpiricalDifference_all [MeasurableSingletonClass X] (μ : Measure X)
    (q : X → ℝ) (hq : Measurable q) (N : ℕ) : Measurable (dynEmpiricalDifference μ q N) := by
  unfold dynEmpiricalDifference
  simp_rw [DGRHS.Commutator.integral_sourceRieszLocalEmpiricalLaw]
  exact (((Finset.measurable_sum _ fun i _ => hq.comp (measurable_pi_apply i)).const_mul _)).sub
    measurable_const

/-- Lemma 8.1(iii) core: two-sign Gibbs moments of the raw fluctuation. -/
theorem dynLinear_gibbs_two_signs (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ)
    (u : (Fin N → X) → ℝ) (hu : Measurable u)
    (hu1 : Integrable (fun ω => Real.exp (u ω)) (Measure.pi (fun _ : Fin N => μ)))
    (hu2 : Integrable (fun ω => Real.exp (2 * u ω)) (Measure.pi (fun _ : Fin N => μ)))
    (Zlow C₂ : ℝ) (hZ : 0 < Zlow)
    (hZlow : Zlow ≤ ∫ ω, Real.exp (u ω) ∂Measure.pi (fun _ : Fin N => μ))
    (hC₂ : (∫ ω, Real.exp (2 * u ω) ∂Measure.pi (fun _ : Fin N => μ)) ≤ C₂)
    (q : X → ℝ) (hq : Measurable q) (a b : ℝ) (hqbound : ∀ x, q x ∈ Set.Icc a b) (L : ℝ)
    (hwidth : ‖b - a‖ ≤ L) (σ : ℝ) (hσ : |σ| = 1) :
    Integrable (fun ω => Real.exp (σ * dynRawFluctuation μ q N ω))
      ((Measure.pi (fun _ : Fin N => μ)).tilted u) ∧
    (∫ ω, Real.exp (σ * dynRawFluctuation μ q N ω) ∂(Measure.pi (fun _ : Fin N => μ)).tilted u) ≤
      Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let S := dynRawFluctuation μ q N
  let Y := fun ω => σ * S ω
  have hY : Measurable Y := (measurable_dynRawFluctuation μ q hq N).const_mul σ
  obtain ⟨hYi, hYB⟩ := DGRHS.Dynamics.boundedRawProductLinearMGF (μ := μ) q hq a b hqbound (2 * σ) N
  have hcoef : ((((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = (‖b - a‖ / 2) ^ 2 := by simp
  have hsq : σ ^ 2 = 1 := by nlinarith [sq_abs σ]
  have hw : ‖b - a‖ ^ 2 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - ‖b - a‖), norm_nonneg (b - a)]
  have hYY (ω : Fin N → X) : 2 * Y ω = (2 * σ) * dynRawFluctuation μ q N ω := by
    dsimp [Y, S]; ring
  have hYproper : Integrable (fun ω => Real.exp (2 * Y ω)) P := by
    simpa only [hYY, dynRawFluctuation] using hYi
  have hYbound : (∫ ω, Real.exp (2 * Y ω) ∂P) ≤ Real.exp (L ^ 2 / 2) := by
    simp_rw [hYY]
    apply hYB.trans
    apply Real.exp_le_exp.mpr
    rw [hcoef]
    nlinarith
  obtain ⟨hNum, hNumB⟩ := DGRHS.CLT.exponential_sum_integral_cs u Y hu.aemeasurable hY.aemeasurable
    hu2 hYproper
  have hNB : (∫ ω, Real.exp (u ω + Y ω) ∂P) ≤ Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ := by
    have h := hNumB.trans (mul_le_mul (Real.sqrt_le_sqrt hC₂) (Real.sqrt_le_sqrt hYbound)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    simpa only [mul_comm] using h
  have hProper : Integrable (fun ω => Real.exp (Y ω)) (P.tilted u) := by
    apply (integrable_tilted_iff hu1 _).mpr
    apply hNum.congr
    exact ae_of_all _ fun ω => by
      change Real.exp (u ω + Y ω) = Real.exp (u ω) * Real.exp (Y ω)
      rw [Real.exp_add]
  refine ⟨hProper, ?_⟩
  change (∫ ω, Real.exp (Y ω) ∂P.tilted u) ≤ _
  rw [integral_exp_tilted]
  have hZ' : 0 < (∫ ω, Real.exp (u ω) ∂P) := lt_of_lt_of_le hZ hZlow
  apply (div_le_iff₀ hZ').mpr
  have hnn : 0 ≤ Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (∫ ω, Real.exp (u ω + Y ω) ∂P) ≤ Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ := hNB
    _ = (Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow) * Zlow := by field_simp
    _ ≤ (Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow) * (∫ ω, Real.exp (u ω) ∂P) :=
      mul_le_mul_of_nonneg_left hZlow (div_nonneg hnn hZ.le)

/-- Lemma 8.1(iii) core: absolute raw fluctuation under finite relative entropy. -/
theorem dynLinear_absolute_bound (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ)
    (u : (Fin N → X) → ℝ) (hu : Measurable u)
    (hu1 : Integrable (fun ω => Real.exp (u ω)) (Measure.pi (fun _ : Fin N => μ)))
    (hu2 : Integrable (fun ω => Real.exp (2 * u ω)) (Measure.pi (fun _ : Fin N => μ)))
    (Zlow C₂ : ℝ) (hZ : 0 < Zlow)
    (hZlow : Zlow ≤ ∫ ω, Real.exp (u ω) ∂Measure.pi (fun _ : Fin N => μ))
    (hC₂ : (∫ ω, Real.exp (2 * u ω) ∂Measure.pi (fun _ : Fin N => μ)) ≤ C₂)
    (q : X → ℝ) (hq : Measurable q) (a b : ℝ) (hqbound : ∀ x, q x ∈ Set.Icc a b) (L : ℝ)
    (hwidth : ‖b - a‖ ≤ L)
    (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν ((Measure.pi (fun _ : Fin N => μ)).tilted u) ≠ ∞) (H : ℝ)
    (hH : (klDiv ν ((Measure.pi (fun _ : Fin N => μ)).tilted u)).toReal ≤ H) :
    Integrable (dynRawFluctuation μ q N) ν ∧
    (∫ ω, |dynRawFluctuation μ q N ω| ∂ν) ≤
      max (H + Real.log (2 * (Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow))) 0 := by
  let P := Measure.pi (fun _ : Fin N => μ)
  haveI : IsProbabilityMeasure (P.tilted u) := isProbabilityMeasure_tilted hu1
  let C := Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow
  have hS : StronglyMeasurable (dynRawFluctuation μ q N) :=
    (measurable_dynRawFluctuation μ q hq N).stronglyMeasurable
  have hp := dynLinear_gibbs_two_signs μ N u hu hu1 hu2 Zlow C₂ hZ hZlow hC₂ q hq a b hqbound L
    hwidth 1 (by norm_num)
  have hm := dynLinear_gibbs_two_signs μ N u hu hu1 hu2 Zlow C₂ hZ hZlow hC₂ q hq a b hqbound L
    hwidth (-1) (by norm_num)
  obtain ⟨hi, hb⟩ := DGRHS.Entropy.entropy_absolute_expectation_scaled_of_two_exponential_bounds
    (P.tilted u) ν (dynRawFluctuation μ q N) hS 1 (by norm_num)
    (by simpa only [one_mul] using hp.1) (by simpa only [neg_one_mul, one_mul] using hm.1) hKL C
    (by simpa only [one_mul] using hp.2) (by simpa only [neg_one_mul, one_mul] using hm.2)
  refine ⟨hi, ?_⟩
  simp only [inv_one, one_mul] at hb
  exact (hb.trans (add_le_add hH le_rfl)).trans (le_max_left _ _)

/-- Lemma 8.1(iii) core for the empirical difference. -/
theorem dynEmpirical_absolute_bound [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N)
    (u : (Fin N → X) → ℝ) (hu : Measurable u)
    (hu1 : Integrable (fun ω => Real.exp (u ω)) (Measure.pi (fun _ : Fin N => μ)))
    (hu2 : Integrable (fun ω => Real.exp (2 * u ω)) (Measure.pi (fun _ : Fin N => μ)))
    (Zlow C₂ : ℝ) (hZ : 0 < Zlow)
    (hZlow : Zlow ≤ ∫ ω, Real.exp (u ω) ∂Measure.pi (fun _ : Fin N => μ))
    (hC₂ : (∫ ω, Real.exp (2 * u ω) ∂Measure.pi (fun _ : Fin N => μ)) ≤ C₂)
    (q : X → ℝ) (hq : Measurable q) (a b : ℝ) (hqbound : ∀ x, q x ∈ Set.Icc a b) (L : ℝ)
    (hwidth : ‖b - a‖ ≤ L)
    (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν ((Measure.pi (fun _ : Fin N => μ)).tilted u) ≠ ∞) (H : ℝ)
    (hH : (klDiv ν ((Measure.pi (fun _ : Fin N => μ)).tilted u)).toReal ≤ H) :
    Integrable (dynRawFluctuation μ q N) ν ∧ Integrable (dynEmpiricalDifference μ q N) ν ∧
    (∫ ω, |dynEmpiricalDifference μ q N ω| ∂ν) ≤
      max (H + Real.log (2 * (Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow))) 0 /
        Real.sqrt N := by
  obtain ⟨hi, hb⟩ := dynLinear_absolute_bound μ N u hu hu1 hu2 Zlow C₂ hZ hZlow hC₂ q hq a b hqbound
    L hwidth ν hKL H hH
  have heq := funext (dynEmpiricalDifference_eq μ q N hN)
  have hiE : Integrable (dynEmpiricalDifference μ q N) ν := by
    rw [heq]
    exact hi.const_mul _
  refine ⟨hi, hiE, ?_⟩
  simp_rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [integral_const_mul]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Lemma 8.1(ii) core: absolute expectation of the transport energy under finite relative entropy,
from two-sign exponential moments of `ε N a`. -/
theorem dynCommutator_absolute_of_moments {Ω : Type*} [MeasurableSpace Ω] (Q ν : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] (N : ℕ) (hN : 1 ≤ N) (a : Ω → ℝ)
    (ha : StronglyMeasurable (fun ω => (N : ℝ) * a ω)) (ε : ℝ) (hε : 0 < ε)
    (hp : Integrable (fun ω => Real.exp (ε * ((N : ℝ) * a ω))) Q)
    (hm : Integrable (fun ω => Real.exp (-(ε * ((N : ℝ) * a ω)))) Q)
    (hKL : klDiv ν Q ≠ ∞) (H : ℝ) (hH : (klDiv ν Q).toReal ≤ H) (C : ℝ)
    (hbP : (∫ ω, Real.exp (ε * ((N : ℝ) * a ω)) ∂Q) ≤ C)
    (hbM : (∫ ω, Real.exp (-(ε * ((N : ℝ) * a ω))) ∂Q) ≤ C) :
    Integrable a ν ∧
    (∫ ω, |a ω| ∂ν) ≤ max (ε⁻¹ * (H + Real.log (2 * C))) 0 / (N : ℝ) := by
  obtain ⟨hi, hb⟩ := DGRHS.Entropy.entropy_absolute_expectation_scaled_of_two_exponential_bounds Q ν
    (fun ω => (N : ℝ) * a ω) ha ε hε hp hm hKL C hbP hbM
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hai : Integrable a ν := by
    have h := hi.const_mul (N : ℝ)⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using h
  have he : (fun ω => |(N : ℝ) * a ω|) = (fun ω => (N : ℝ) * |a ω|) := by
    funext ω
    rw [abs_mul, abs_of_pos hn]
  rw [he, integral_const_mul] at hb
  have hc := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hε.le)
  have hfinal : (N : ℝ) * (∫ ω, |a ω| ∂ν) ≤ max (ε⁻¹ * (H + Real.log (2 * C))) 0 :=
    (hb.trans (by linarith)).trans (le_max_left _ _)
  exact ⟨hai, (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hfinal)⟩

/-- `e^{a t} ≤ 1 + e^{b t}` for `0 ≤ a ≤ b`. -/
lemma exp_mul_le_one_add_exp_mul {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (t : ℝ) :
    Real.exp (a * t) ≤ 1 + Real.exp (b * t) := by
  by_cases ht : 0 ≤ t
  · have : Real.exp (a * t) ≤ Real.exp (b * t) := Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (b * t)]
  · have : Real.exp (a * t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [not_le.mp ht])
    linarith [Real.exp_pos (b * t)]

end Generic

end DGRHS.Periodic
#print axioms DGRHS.Periodic.dynEmpiricalDifference_eq
#print axioms DGRHS.Periodic.dynLinear_gibbs_two_signs
#print axioms DGRHS.Periodic.dynLinear_absolute_bound
#print axioms DGRHS.Periodic.dynEmpirical_absolute_bound
#print axioms DGRHS.Periodic.dynCommutator_absolute_of_moments
#print axioms DGRHS.Periodic.exp_mul_le_one_add_exp_mul
