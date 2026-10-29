import DGRHS.Commutator.SourceRieszPhaseForcingL1
import DGRHS.Commutator.SourceRieszVolterraComplex

/- DGR source3971--3997, exact finite source phase Ito formula -> comparison.
Conditional analytic interface only: the finite source Ito formula is explicit,
with the SAME actual phase and empirical square H. It is neither terminal duality
nor characteristic factorization/limit. The original Ito-admissibility semantic
review is separate. All complex integrals below are proved proper by phase/caps. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace DGRHS.Commutator

/-- Proper unit-phase extraction of the literal finite source Ito formula.
The coefficient and empirical square caps are on the finite horizon only. -/
theorem sourceRiesz_finite_Ito_volterra {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (T β C : ℝ)
    (hT : 0 ≤ T) (hβ : 0 < β) (hC : 0 ≤ C)
    (A : Ω → ℝ) (hA : Measurable A) (M H : ℝ → Ω → ℝ)
    (hM : Measurable (Function.uncurry M))
    (hH : Measurable (Function.uncurry H))
    (hHb : ∀ r ∈ Icc 0 T, ∀ ω, |H r ω| ≤ C)
    (m : ℝ → ℝ) (hm : Measurable m)
    (hmb : ∀ r ∈ Icc 0 T, 0 ≤ m r ∧ m r ≤ C) :
    let Φ := fun r ω => sourceRieszFinitePhase (A ω + M r ω)
    let chi := fun r => ∫ ω, Φ r ω ∂ν
    let J := fun r ω => (2/β) * (H r ω - m r)
    (∀ r ∈ Icc 0 T, chi r = chi 0 - (1/β:ℝ) •
      (∫ u in 0..r, ∫ ω, Φ u ω * (H u ω : ℂ) ∂ν)) →
    ‖chi T - chi 0 * (Real.exp (-(1/β) * (∫ r in 0..T, m r)) : ℂ)‖ ≤
      Real.exp ((C/β) * T) * (∫ r in Ioc 0 T, ∫ ω, |J r ω| ∂ν) := by
  dsimp only
  let η := volume.restrict (Ioc 0 T)
  let Φ := fun r ω => sourceRieszFinitePhase (A ω + M r ω)
  let chi := fun r => ∫ ω, Φ r ω ∂ν
  let J := fun r ω => (2/β) * (H r ω - m r)
  let F := fun r => (1/2:ℝ) • (∫ ω, Φ r ω * (J r ω : ℂ) ∂ν)
  intro hIto
  have hΦ : Measurable (Function.uncurry Φ) :=
    measurable_sourceRieszFinitePhase.comp ((hA.comp measurable_snd).add hM)
  have hχ : Measurable chi := hΦ.stronglyMeasurable.integral_prod_right'.measurable
  have hiΦ (r : ℝ) : Integrable (Φ r) ν := by
    apply (integrable_const (1:ℝ)).mono'
      (hΦ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => (norm_sourceRieszFinitePhase _).le
  have hχb (r : ℝ) : ‖chi r‖ ≤ 1 := by
    have hh : ∀ᵐ ω ∂ν, ‖Φ r ω‖ ≤ 1 :=
      Filter.Eventually.of_forall fun ω => (norm_sourceRieszFinitePhase _).le
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ:=ν) hh
  have hiM : Integrable m η := by
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hmb r ⟨hr.1.le,hr.2⟩).1]
    exact (hmb r ⟨hr.1.le,hr.2⟩).2
  have hip : Integrable (fun r => ((m r/β:ℝ):ℂ) * chi r) η := by
    apply (hiM.abs.div_const β).mono'
      ((Complex.continuous_ofReal.measurable.comp (hm.div_const β)).mul hχ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change ‖((m r/β:ℝ):ℂ) * chi r‖ ≤ |m r|/β
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hβ]
    exact mul_le_of_le_one_right (by positivity) (hχb r)
  have hJ : Measurable (Function.uncurry J) :=
    (hH.sub (hm.comp measurable_fst)).const_mul _
  have hJb (r : ℝ) (hr : r ∈ Icc 0 T) (ω : Ω) : |J r ω| ≤ (2/β)*(C+C) := by
    dsimp [J]
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hβ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (abs_sub _ _).trans (add_le_add (hHb r hr ω)
      (by rw [abs_of_nonneg (hmb r hr).1]; exact (hmb r hr).2))
  have hiJ : Integrable (Function.uncurry J) (η.prod ν) := by
    apply (integrable_const ((2/β)*(C+C))).mono' hJ.aestronglyMeasurable
    have ht : ∀ᵐ p : ℝ×Ω ∂η.prod ν, p.1 ∈ Ioc 0 T := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact Filter.Eventually.of_forall fun _ => hr
    filter_upwards [ht] with p hp
    change |J p.1 p.2| ≤ _
    exact hJb p.1 ⟨hp.1.le,hp.2⟩ p.2
  obtain ⟨_,hiF,hFb⟩ := sourceRiesz_phase_forcing_L1 ν η A hA M J hM hJ hiJ
  have hraw (r : ℝ) (hr : r ∈ Icc 0 T) :
      ((m r/β:ℝ):ℂ) * chi r + F r =
        (1/β:ℝ) • (∫ ω, Φ r ω * (H r ω : ℂ) ∂ν) := by
    have hiPH : Integrable (fun ω => Φ r ω * (H r ω : ℂ)) ν := by
      apply (integrable_const C).mono'
        ((hΦ.comp (measurable_const.prodMk measurable_id)).mul
          (Complex.continuous_ofReal.measurable.comp
            (hH.comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        change ‖sourceRieszFinitePhase (A ω+M r ω) * (H r ω:ℂ)‖ ≤ C
        rw [norm_mul, norm_sourceRieszFinitePhase, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hHb r hr ω
    have hG : (∫ ω, Φ r ω * (J r ω : ℂ) ∂ν) =
        (2/β:ℝ) • ((∫ ω, Φ r ω * (H r ω : ℂ) ∂ν) - chi r * (m r : ℂ)) := by
      calc
        _ = ∫ ω, (2/β:ℝ) • (Φ r ω * (H r ω : ℂ) - Φ r ω * (m r : ℂ)) ∂ν := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            simp only [J, Complex.ofReal_mul, Complex.ofReal_sub, Complex.real_smul]
            ring
        _ = _ := by rw [integral_smul, integral_sub hiPH ((hiΦ r).mul_const _),
          integral_mul_const]
    rw [show F r = (1/2:ℝ) • (∫ ω, Φ r ω * (J r ω:ℂ) ∂ν) from rfl, hG, smul_smul]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    norm_num
    ring
  have hmI : IntervalIntegrable (fun r => m r/β) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hiM.div_const β)
  have hpI : IntervalIntegrable (fun r => ((m r/β:ℝ):ℂ)*chi r) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hip
  have hfI : IntervalIntegrable F volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hiF
  have hcoef : ∀ r ∈ Icc 0 T, 0 ≤ m r/β ∧ m r/β ≤ C/β := by
    intro r hr
    exact ⟨div_nonneg (hmb r hr).1 hβ.le, div_le_div_of_nonneg_right (hmb r hr).2 hβ.le⟩
  have hvol : ∀ r ∈ Icc 0 T, chi r = chi 0 -
      ∫ u in 0..r, ((m u/β:ℝ):ℂ)*chi u + F u := by
    intro r hr
    have hIr : chi r = chi 0 - (1/β:ℝ) •
        (∫ u in 0..r, ∫ ω, Φ u ω * (H u ω:ℂ) ∂ν) := hIto r hr
    rw [hIr]
    congr 1
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hr.1] at hu
    exact (hraw u ⟨hu.1,hu.2.trans hr.2⟩).symm
  have hh := sourceRiesz_complex_volterra_comparison hT (div_nonneg hC hβ.le)
    hmI hpI hfI hcoef hvol
  have hexp : (∫ r in 0..T, m r/β) = (1/β)*(∫ r in 0..T, m r) := by
    simp only [div_eq_mul_inv, mul_comm (m _) (β⁻¹), intervalIntegral.integral_const_mul, one_mul]
  rw [hexp] at hh
  rw [intervalIntegral.integral_of_le hT (f:=fun r=>‖F r‖)] at hh
  apply le_trans (by simpa only [neg_mul] using hh)

  have hb := mul_le_mul_of_nonneg_left hFb (by positivity : 0 ≤ 2*Real.exp ((C/β)*T))
  exact hb.trans_eq (by ring)

#check sourceRiesz_finite_Ito_volterra
#print axioms sourceRiesz_finite_Ito_volterra
end DGRHS.Commutator
