import LeanResearch.PeriodicAttractiveLogGas.BoundaryCovarianceSplitting

/-! Analytic estimates used in the supplied occupation-field proof,
source `thm:occupation-rates`, lines 1724–1779. These generic lemmas retain
their moment and denominator inputs explicitly; the actual Gibbs-field
instances are separate obligations, not hypotheses of a completed main theorem. -/

noncomputable section
open MeasureTheory Filter

namespace PeriodicAttractiveLogGas.OccupationFieldEstimates

theorem abs_exp_sub_one_bound (u : ℝ) :
    |Real.exp u - 1| ≤ |u| * (1 + Real.exp u) := by
  by_cases hu : 0 ≤ u
  · have he : 1 ≤ Real.exp u := by simpa using Real.exp_le_exp.mpr hu
    have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
    have hc : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    rw [hc] at hm
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonneg hu]
    nlinarith
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have he : Real.exp u ≤ 1 := by simpa using Real.exp_le_exp.mpr hu'
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos hu']
    have h := Real.add_one_le_exp u
    nlinarith [mul_nonneg (neg_nonneg.mpr hu') (Real.exp_pos u).le]

theorem exp_twice (u : ℝ) : Real.exp (2 * u) = Real.exp u ^ 2 := by
  rw [two_mul, Real.exp_add, pow_two]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_exponential_error {D : Ω → ℝ} {β : ℝ}
    (hE : MemLp (fun x => Real.exp (β * D x)) 2 μ) :
    Integrable (fun x => |Real.exp (β * D x) - 1|) μ := by
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using!
    ((hE.integrable (by norm_num)).sub (integrable_const 1)).norm

theorem integral_exponential_error_le {D : Ω → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hD : MemLp D 2 μ) (hE : MemLp (fun x => Real.exp (β * D x)) 2 μ) :
    (∫ x, |Real.exp (β * D x) - 1| ∂μ) ≤
      β * ∫ x, |D x| * (1 + Real.exp (β * D x)) ∂μ := by
  have hA : MemLp (fun x => |D x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using! hD.norm
  have hG : MemLp (fun x => 1 + Real.exp (β * D x)) 2 μ := by
    simpa only [Pi.add_apply] using! (memLp_const (μ := μ) (p := 2) (1 : ℝ)).add hE
  have hP : Integrable (fun x => |D x| * (1 + Real.exp (β * D x))) μ := by
    simpa only [Pi.mul_apply] using! hA.integrable_mul hG
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_exponential_error hE) (hP.const_mul β)
  exact Eventually.of_forall fun x => by
    simpa only [abs_mul, abs_of_nonneg hβ, mul_assoc] using abs_exp_sub_one_bound (β * D x)

theorem integral_one_add_exp_sq_le {D : Ω → ℝ} {β : ℝ}
    (hE : MemLp (fun x => Real.exp (β * D x)) 2 μ) :
    (∫ x, (1 + Real.exp (β * D x)) ^ 2 ∂μ) ≤
      2 * (1 + ∫ x, Real.exp (2 * (β * D x)) ∂μ) := by
  have hG : MemLp (fun x => 1 + Real.exp (β * D x)) 2 μ := by
    simpa only [Pi.add_apply] using! (memLp_const (μ := μ) (p := 2) (1 : ℝ)).add hE
  have heI : Integrable (fun x => Real.exp (2 * (β * D x))) μ := by
    simpa only [exp_twice] using! hE.integrable_sq
  have hm := integral_mono_ae hG.integrable_sq
    ((integrable_const 2).add (heI.const_mul 2))
    (Eventually.of_forall fun x => show (1 + Real.exp (β * D x)) ^ 2 ≤
      2 + 2 * Real.exp (2 * (β * D x)) by
        rw [exp_twice]
        nlinarith [sq_nonneg (Real.exp (β * D x) - 1)])
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_const 2) (heI.const_mul 2), integral_const_mul] at hm
  simpa only [integral_const, probReal_univ, one_smul, mul_add, mul_one] using hm

/-- The supplied Cauchy--Schwarz step, with actual integrability established. -/
theorem exponential_error_squared_le {D : Ω → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hD : MemLp D 2 μ) (hE : MemLp (fun x => Real.exp (β * D x)) 2 μ) :
    Integrable (fun x => |Real.exp (β * D x) - 1|) μ ∧
      (∫ x, |Real.exp (β * D x) - 1| ∂μ) ^ 2 ≤
        2 * β ^ 2 * (∫ x, D x ^ 2 ∂μ) *
          (1 + ∫ x, Real.exp (2 * (β * D x)) ∂μ) := by
  have hA : MemLp (fun x => |D x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using! hD.norm
  have hG : MemLp (fun x => 1 + Real.exp (β * D x)) 2 μ := by
    simpa only [Pi.add_apply] using! (memLp_const (μ := μ) (p := 2) (1 : ℝ)).add hE
  have hnonneg : 0 ≤ ∫ x, |Real.exp (β * D x) - 1| ∂μ :=
    integral_nonneg fun x => abs_nonneg _
  have hs := pow_le_pow_left₀ hnonneg (integral_exponential_error_le hβ hD hE) 2
  rw [mul_pow] at hs
  have hc := BoundaryCovarianceSplitting.integral_mul_squared_le hA hG
  simp only [sq_abs] at hc
  have hgI := integral_one_add_exp_sq_le hE
  refine ⟨integrable_exponential_error hE, hs.trans ?_⟩
  calc
    β ^ 2 * (∫ x, |D x| * (1 + Real.exp (β * D x)) ∂μ) ^ 2 ≤
        β ^ 2 * ((∫ x, D x ^ 2 ∂μ) * (∫ x, (1 + Real.exp (β * D x)) ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg β)
    _ ≤ β ^ 2 * ((∫ x, D x ^ 2 ∂μ) *
        (2 * (1 + ∫ x, Real.exp (2 * (β * D x)) ∂μ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgI (integral_nonneg fun x => sq_nonneg _)) (sq_nonneg β)
    _ = _ := by ring

/-- The source square-root particle rate, with its two moment bounds visible. -/
theorem exponential_error_le_of_moments {D : Ω → ℝ} {β A B n : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 < n)
    (hD : MemLp D 2 μ) (hE : MemLp (fun x => Real.exp (β * D x)) 2 μ)
    (hD2 : (∫ x, D x ^ 2 ∂μ) ≤ A / n)
    (hE2 : (∫ x, Real.exp (2 * (β * D x)) ∂μ) ≤ B) :
    (∫ x, |Real.exp (β * D x) - 1| ∂μ) ≤
      β * Real.sqrt (2 * A * (1 + B)) / Real.sqrt n := by
  have hi0 : 0 ≤ ∫ x, |Real.exp (β * D x) - 1| ∂μ :=
    integral_nonneg fun x => abs_nonneg _
  have he0 : 0 ≤ ∫ x, Real.exp (2 * (β * D x)) ∂μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hs := (exponential_error_squared_le hβ hD hE).2
  have hb : (∫ x, |Real.exp (β * D x) - 1| ∂μ) ^ 2 ≤
      2 * β ^ 2 * (A / n) * (1 + B) := by
    refine hs.trans ?_
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hD2 (by positivity)
    · linarith
    · linarith
    · positivity
  have hr : 0 ≤ 2 * A * (1 + B) := by positivity
  have he : (β * Real.sqrt (2 * A * (1 + B)) / Real.sqrt n) ^ 2 =
      2 * β ^ 2 * (A / n) * (1 + B) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt hn.le]
    ring
  apply (sq_le_sq₀ hi0 (by positivity)).mp
  rw [he]
  exact hb

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem ratio_sub_one_bound {a w c : ℝ} (hc : 0 < c) (hw : c ≤ w) :
    |a / w - 1| ≤ c⁻¹ * (|a - 1| + |w - 1|) := by
  have hw0 : 0 < w := hc.trans_le hw
  have he : a / w - 1 = ((a - 1) - (w - 1)) / w := by field_simp; ring
  rw [he, abs_div, abs_of_pos hw0]
  calc
    _ ≤ (|a - 1| + |w - 1|) / w := div_le_div_of_nonneg_right (abs_sub _ _) hw0.le
    _ ≤ (|a - 1| + |w - 1|) / c := by
      apply (div_le_div_iff₀ hw0 hc).mpr
      exact mul_le_mul_of_nonneg_left hw (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

/-- The random denominator stays inside the expectation. Its positive lower
bound yields the source normalization error without replacing it by its mean. -/
theorem integral_ratio_sub_one_le {a w : Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (ha : Integrable a μ) (hw : Integrable w μ) (hlower : ∀ᵐ x ∂μ, c ≤ w x) :
    Integrable (fun x => |a x / w x - 1|) μ ∧
      (∫ x, |a x / w x - 1| ∂μ) ≤
        c⁻¹ * ((∫ x, |a x - 1| ∂μ) + ∫ x, |w x - 1| ∂μ) := by
  have hA : Integrable (fun x => |a x - 1|) μ := (ha.sub (integrable_const 1)).abs
  have hW : Integrable (fun x => |w x - 1|) μ := (hw.sub (integrable_const 1)).abs
  have hb : Integrable (fun x => c⁻¹ * (|a x - 1| + |w x - 1|)) μ :=
    (hA.add hW).const_mul c⁻¹
  have hi : Integrable (fun x => |a x / w x - 1|) μ := by
    have hm : AEMeasurable (fun x => a x / w x - 1) μ :=
      (ha.aemeasurable.div hw.aemeasurable).sub aemeasurable_const
    have hm' : AEStronglyMeasurable (fun x => |a x / w x - 1|) μ := by
      simpa only [Real.norm_eq_abs] using hm.aestronglyMeasurable.norm
    apply hb.mono' hm'
    filter_upwards [hlower] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using ratio_sub_one_bound hc hx (a := a x)
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi hb (hlower.mono fun x hx => ratio_sub_one_bound hc hx (a := a x))
  rw [integral_const_mul, integral_add hA hW] at he
  exact he

theorem integral_ratio_sub_one_le_of_errors {a w : Ω → ℝ} {c ε : ℝ}
    (hc : 0 < c) (ha : Integrable a μ) (hw : Integrable w μ)
    (hlower : ∀ᵐ x ∂μ, c ≤ w x)
    (haerr : (∫ x, |a x - 1| ∂μ) ≤ ε)
    (hwerr : (∫ x, |w x - 1| ∂μ) ≤ ε) :
    (∫ x, |a x / w x - 1| ∂μ) ≤ 2 * ε / c := by
  refine (integral_ratio_sub_one_le hc ha hw hlower).2.trans ?_
  calc
    c⁻¹ * ((∫ x, |a x - 1| ∂μ) + ∫ x, |w x - 1| ∂μ) ≤ c⁻¹ * (ε + ε) :=
      mul_le_mul_of_nonneg_left (add_le_add haerr hwerr) (inv_nonneg.mpr hc.le)
    _ = _ := by ring

end PeriodicAttractiveLogGas.OccupationFieldEstimates
