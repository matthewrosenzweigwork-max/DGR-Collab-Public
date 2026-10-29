import SharpSymmetricLSI.Paper.AppAFourier1

/-!
# Fourier coefficients of the Duhamel term and of mild solutions

`(∫_{(0,t]} ∇·e^{(t-u)Δ}N_u du)^(n) = ∫_{(0,t]} ∑ₖ 2πi nₖ e^{-4π²|n|²(t-u)} N̂_{u,k}(n) du`
for jointly measurable bounded `N` (`cf_duhamel`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The kernel form of the Duhamel integrand (measurable in `(x, u)`). -/
noncomputable def duhQ (N : ℝ → UnitAddTorus ι → ι → ℝ) (t : ℝ) (p : UnitAddTorus ι × ℝ) : ℝ :=
  if 0 < p.2 ∧ p.2 < t then ∑ k, ∫ y : ι → ℝ, duhKer (t - p.2) y k * N p.2 (p.1 - liftT y) k
  else 0

theorem measurable_duhQ {N : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k) (t : ℝ) :
    Measurable (duhQ N t) := by
  unfold duhQ
  refine Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_const)) ?_ measurable_const
  refine Finset.measurable_sum _ fun k _ => ?_
  have hm : StronglyMeasurable (fun r : (UnitAddTorus ι × ℝ) × (ι → ℝ) =>
      duhKer (t - r.1.2) r.2 k * N r.1.2 (r.1.1 - liftT r.2) k) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((measurable_duhKer k).comp ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk
      measurable_snd)).mul ((hN k).comp ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).sub (measurable_liftT.comp measurable_snd))))
  exact hm.integral_prod_right'.measurable

theorem duhQ_eq {N : ℝ → UnitAddTorus ι → ι → ℝ} {t u : ℝ} (hu : 0 < u ∧ u < t)
    (x : UnitAddTorus ι) : duhQ N t (x, u) = divHeatT (t - u) (N u) x := by
  unfold duhQ
  rw [if_pos hu, divHeatT_eq_duhKer (sub_pos.2 hu.2)]

theorem abs_duhQ_le {N : ℝ → UnitAddTorus ι → ι → ℝ} {t B : ℝ}
    (hB : ∀ u ∈ Ioo 0 t, ∀ y k, |N u y k| ≤ B) (p : UnitAddTorus ι × ℝ) :
    |duhQ N t p| ≤ (Ioo 0 t).indicator (fun u => Fintype.card ι * divConst (t - u) * B) p.2 := by
  by_cases hu : 0 < p.2 ∧ p.2 < t
  · rw [show p = (p.1, p.2) from rfl, duhQ_eq hu, indicator_of_mem (show p.2 ∈ Ioo 0 t from hu)]
    exact abs_divHeatT_le (sub_pos.2 hu.2) (fun k => Eventually.of_forall fun y => hB p.2 hu y k) _
  · unfold duhQ
    rw [if_neg hu, indicator_of_notMem (show p.2 ∉ Ioo 0 t from hu), abs_zero]

theorem duhamel_eq_duhQ (N : ℝ → UnitAddTorus ι → ι → ℝ) (t : ℝ) (x : UnitAddTorus ι) :
    duhamel N t x = ∫ u, duhQ N t (x, u) := by
  rw [duhamel_eq_ker]; rfl

/-- **Coefficients of the Duhamel term.** -/
theorem cf_duhamel {N : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k) {t B : ℝ} (ht : 0 < t)
    (hB0 : 0 ≤ B) (hB : ∀ u ∈ Ioo 0 t, ∀ y k, |N u y k| ≤ B) (n : ι → ℤ) :
    cf (duhamel N t) n = ∫ u in Ioo 0 t,
      ∑ k, 2 * π * I * n k * (heatMult (t - u) n * cf (fun z => N u z k) n) := by
  set g : ℝ → ℝ := (Ioo 0 t).indicator (fun u => Fintype.card ι * divConst (t - u) * B) with hg
  have hgi : Integrable g := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    have := ((integrableOn_divConst ht).const_mul (Fintype.card ι : ℝ)).mul_const B
    exact (IntegrableOn.mono_set this Ioo_subset_Ioc_self).congr_fun (fun u _ => by ring) measurableSet_Ioo
  set H : UnitAddTorus ι × ℝ → ℂ := fun p => mFourier (-n) p.1 * (duhQ N t p : ℂ) with hH
  have hHi : Integrable H (volume.prod volume) := by
    refine ((integrable_const (1 : ℝ)).mul_prod hgi).mono'
      (((mFourier (-n)).continuous.measurable.comp measurable_fst).mul
        (Complex.measurable_ofReal.comp (measurable_duhQ hN t))).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    simp only [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    calc ‖mFourier (-n) p.1‖ * |duhQ N t p| ≤ 1 * g p.2 :=
          mul_le_mul (norm_mFourier_le _ _) (abs_duhQ_le hB p) (abs_nonneg _) zero_le_one
      _ = g p.2 := one_mul _
  simp only [cf]
  rw [mFourierCoeff_eq_integral]
  have e1 : (fun x => mFourier (-n) x • ((duhamel N t x : ℝ) : ℂ)) = fun x => ∫ u, H (x, u) := by
    funext x
    rw [duhamel_eq_duhQ, smul_eq_mul, ← integral_complex_ofReal, ← integral_const_mul]
  rw [e1, integral_integral_swap hHi, ← integral_indicator measurableSet_Ioo]
  congr 1; funext u
  by_cases hu : u ∈ Ioo 0 t
  · rw [indicator_of_mem hu]
    have hd : (fun x => H (x, u)) = fun x => mFourier (-n) x • ((divHeatT (t - u) (N u) x : ℝ) : ℂ) := by
      funext x; simp only [hH, smul_eq_mul]; rw [duhQ_eq hu]
    rw [hd, ← mFourierCoeff_eq_integral]
    exact cf_divHeatT (sub_pos.2 hu.2) (fun k => (hN k).comp measurable_prodMk_left)
      (fun z k => hB u hu z k) n
  · rw [indicator_of_notMem hu]
    have : (fun x => H (x, u)) = fun _ => 0 := by
      funext x; simp only [hH, duhQ, if_neg (show ¬ (0 < u ∧ u < t) from hu)]; simp
    rw [this, integral_zero]

end SharpLSI
