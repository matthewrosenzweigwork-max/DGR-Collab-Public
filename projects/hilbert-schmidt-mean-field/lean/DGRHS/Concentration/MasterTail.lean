import DGRHS.Concentration.MasterRate

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Concentration

def iidNegativeStatistic {Ω : Type*} (n : ℕ) (h : Ω × Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  -iidCoupledSum n h ω/(2*(n : ℝ))

lemma glzExtendedTailBound_le_of_rate {t A B C D u : ℝ}
    (hRate : ENNReal.ofReal (2*glzUniversalTailConstant*u) ≤ glzExtendedRate t A B C D) :
    glzExtendedTailBound t A B C D ≤ glzUniversalTailConstant*Real.exp (-2*u) := by
  have hL := glzUniversalTailConstant_pos
  by_cases hz : glzExtendedRate t A B C D = ∞
  · simp only [glzExtendedTailBound,ite_eq_left hz]
    positivity
  · simp only [glzExtendedTailBound,ite_eq_right hz]
    have hr : 2*glzUniversalTailConstant*u ≤ (glzExtendedRate t A B C D).toReal := by
      have hh := ENNReal.toReal_mono hz hRate
      by_cases hu : 0 ≤ u
      · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*glzUniversalTailConstant*u)] using hh
      · exact (by nlinarith [glzUniversalTailConstant_pos] : 2*glzUniversalTailConstant*u ≤ 0).trans ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_left _ glzUniversalTailConstant_pos.le
    apply Real.exp_le_exp.mpr
    have hd : 2*u ≤ (glzExtendedRate t A B C D).toReal/glzUniversalTailConstant := by
      apply (le_div_iff₀ glzUniversalTailConstant_pos).mpr
      nlinarith only [hr]
    simpa only [neg_div,neg_mul] using neg_le_neg hd

/-- A genuine iid negative U-statistic tail from source M3 and growth controls;
all moment, decoupling and source A/B/C/D bridges are instantiated here. -/
theorem iid_master_tail {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (h : Ω × Ω → ℝ) (hm : Measurable h)
    (hh : MemLp h ∞ (μ.prod μ)) (hSym : ∀ x y, h (x,y) = h (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y,h (x,y) ∂μ = 0)
    (a u : ℝ) (ha : 0 ≤ a) (hu : 1 ≤ u)
    (hAbs : ∀ᵐ p ∂μ.prod μ, |h p| ≤ a)
    (hRow : ∀ᵐ x ∂μ, (∫ y,(h (x,y))^2 ∂μ) ≤ 1/glzUniversalTailConstant)
    (hJoint : (∫ p,(h p)^2 ∂μ.prod μ) ≤ 1/glzUniversalTailConstant)
    (hOp : ‖DGRHS.Kernel.integralOperator h (hh.mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ≤ 1/glzUniversalTailConstant)
    (hGrowth : 2*glzUniversalTailConstant^2*u*(1+a) ≤ (n : ℝ)) :
    (Measure.pi (fun _ : Fin n ↦ μ)).real {ω | u ≤ iidNegativeStatistic n h ω} ≤
      glzUniversalTailConstant*Real.exp (-2*u) := by
  let L := glzUniversalTailConstant
  have hL : 0 < L := glzUniversalTailConstant_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hu0 : 0 < u := by linarith
  obtain ⟨hA,hB,hC,hD⟩ := iid_source_scales_nonneg μ n h hh
  obtain ⟨hAb,hBb,hCb⟩ := iidSourceABC_le μ n h (fun x y ↦ hSym y x)
    a (Real.sqrt (1/L)) (Real.sqrt (1/L)) ha (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hAbs
    (by simpa only [Real.sq_sqrt (by positivity : 0 ≤ 1/L)] using hRow)
    (by simpa only [Real.sq_sqrt (by positivity : 0 ≤ 1/L)] using hJoint)
  have hBs : (iidSourceB μ n h)^2 ≤ (n : ℝ)/L := by
    have hp := pow_le_pow_left₀ hB hBb 2
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt (by positivity : 0 ≤ 1/L)] at hp
    convert hp using 1; ring
  have hCs : (iidSourceC μ n h)^2 ≤ (n : ℝ)^2/L := by
    have hp := pow_le_pow_left₀ hC hCb 2
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 1/L)] at hp
    convert hp using 1; ring
  have hDb : iidSourceD μ n h ≤ (n : ℝ)/L := by
    calc
      _ ≤ (n : ℝ)*‖DGRHS.Kernel.integralOperator h (hh.mono_exponent le_top)‖ := iidSourceD_le_integralOperator μ n h _
      _ ≤ (n : ℝ)*(1/L) := mul_le_mul_of_nonneg_left hOp hn0.le
      _ = _ := by ring
  have hRate := master_rate_lower hn0.le hu hL ha hA hB hC hD hAb hBs hCs hDb hGrowth
  have hActual := iid_actual_extended_rate_tail μ n h hm hh hSym hr (2*(n : ℝ)*u) (by positivity)
  have hIncl : {ω | u ≤ iidNegativeStatistic n h ω} ⊆ {ω | 2*(n : ℝ)*u ≤ |iidCoupledSum n h ω|} := by
    intro ω hω
    have he := (le_div_iff₀ (show 0 < 2*(n : ℝ) by positivity)).mp hω
    calc
      _ = u*(2*(n : ℝ)) := by ring
      _ ≤ -iidCoupledSum n h ω := he
      _ ≤ _ := neg_le_abs _
  have hMeasure := ENNReal.toReal_mono
    (measure_ne_top (Measure.pi (fun _ : Fin n ↦ μ)) {ω | 2*(n : ℝ)*u ≤ |iidCoupledSum n h ω|})
    (measure_mono hIncl)
  exact hMeasure.trans (hActual.trans (glzExtendedTailBound_le_of_rate hRate))

#print axioms DGRHS.Concentration.iid_master_tail
#check @DGRHS.Concentration.iid_master_tail
end DGRHS.Concentration
