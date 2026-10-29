import SharpSymmetricLSI.Paper.AppAPicard2

/-!
# Lemma A.1, existence (3): bounds and linearity of the Duhamel term

For a jointly measurable field `N` with `|N_u| ≤ K e^{μu}` on `(0,t]`:
`|∫_{(0,t]} ∇·e^{(t-u)Δ}N_u(x) du| ≤ |ι| K e^{μt}/√μ` (`abs_duhamel_le`), and the Duhamel term is
linear in `N` (`duhamel_sub`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Duhamel integrand is measurable in `u` (on `(0,t)` it is the explicit kernel form). -/
theorem aestronglyMeasurable_duhamel_integrand {N : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k) (t : ℝ)
    (x : UnitAddTorus ι) :
    AEStronglyMeasurable (fun u => divHeatT (t - u) (N u) x) (volume.restrict (Ioc 0 t)) := by
  set Q : ℝ → ℝ := fun u => if 0 < u ∧ u < t then
    ∑ k, ∫ y : ι → ℝ, duhKer (t - u) y k * N u (x - liftT y) k else 0 with hQ
  have hQm : Measurable Q := by
    refine Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)) ?_ measurable_const
    refine Finset.measurable_sum _ fun k _ => ?_
    have hm : StronglyMeasurable (fun r : ℝ × (ι → ℝ) =>
        duhKer (t - r.1) r.2 k * N r.1 (x - liftT r.2) k) := by
      refine Measurable.stronglyMeasurable ?_
      exact ((measurable_duhKer k).comp ((measurable_const.sub measurable_fst).prodMk
        measurable_snd)).mul ((hN k).comp (measurable_fst.prodMk
          (measurable_const.sub (measurable_liftT.comp measurable_snd))))
    exact hm.integral_prod_right'.measurable
  refine hQm.aestronglyMeasurable.congr ?_
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by rw [ae_iff]; simp
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hne] with u hu hmem
  have h : 0 < u ∧ u < t := ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩
  simp only [hQ, if_pos h]
  exact (divHeatT_eq_duhKer (sub_pos.2 h.2) _ _).symm

theorem integrableOn_duhamel_integrand {N : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k) {t : ℝ} (ht : 0 < t)
    {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hNb : ∀ u ∈ Ioc 0 t, ∀ y k, |N u y k| ≤ K * Real.exp (μ * u))
    (x : UnitAddTorus ι) :
    IntegrableOn (fun u => divHeatT (t - u) (N u) x) (Ioc 0 t) := by
  have hg : IntegrableOn (fun u => Fintype.card ι * divConst (t - u) * (K * Real.exp (μ * t)))
      (Ioc 0 t) := by
    have := (integrableOn_divConst ht).const_mul (Fintype.card ι : ℝ)
    exact IntegrableOn.congr_fun (this.mul_const (K * Real.exp (μ * t))) (fun u _ => by ring)
      measurableSet_Ioc
  refine hg.mono' (aestronglyMeasurable_duhamel_integrand hN t x) ?_
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by rw [ae_iff]; simp
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hne] with u hu hmem
  rw [Real.norm_eq_abs]
  have hs : 0 < t - u := sub_pos.2 (lt_of_le_of_ne hmem.2 hu)
  refine abs_divHeatT_le hs (fun k => Eventually.of_forall fun y =>
    (hNb u hmem y k).trans ?_) x
  gcongr
  exact hmem.2

theorem integrableOn_divConst_exp {t μ : ℝ} (ht : 0 < t) (hμ : 0 ≤ μ) :
    IntegrableOn (fun u => divConst (t - u) * Real.exp (μ * u)) (Ioc 0 t) := by
  refine ((integrableOn_divConst ht).mul_const (Real.exp (μ * t))).mono'
    ((integrableOn_divConst ht).aestronglyMeasurable.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by rw [ae_iff]; simp
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hne] with u hu hmem
  have hs : 0 < t - u := sub_pos.2 (lt_of_le_of_ne hmem.2 hu)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (divConst_nonneg hs),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hmem.2 hμ))
    (divConst_nonneg hs)

/-- **Bound on the Duhamel term.** -/
theorem abs_duhamel_le {N : ℝ → UnitAddTorus ι → ι → ℝ} {t : ℝ} (ht : 0 < t)
    {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 < μ)
    (hNb : ∀ u ∈ Ioc 0 t, ∀ y k, |N u y k| ≤ K * Real.exp (μ * u)) (x : UnitAddTorus ι) :
    |duhamel N t x| ≤ Fintype.card ι * K * Real.exp (μ * t) / Real.sqrt μ := by
  have hg := (integrableOn_divConst_exp ht hμ.le).const_mul (Fintype.card ι * K)
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by rw [ae_iff]; simp
  unfold duhamel
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg ?_).trans ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with u hu hmem
    have hs : 0 < t - u := sub_pos.2 (lt_of_le_of_ne hmem.2 hu)
    rw [Real.norm_eq_abs]
    refine (abs_divHeatT_le hs (fun k => Eventually.of_forall fun y => hNb u hmem y k) x).trans
      (le_of_eq ?_)
    ring
  · rw [integral_const_mul]
    have := setIntegral_divConst_exp_le ht hμ
    have h0 : (0 : ℝ) ≤ Fintype.card ι * K := by positivity
    calc Fintype.card ι * K * ∫ u in Ioc 0 t, divConst (t - u) * Real.exp (μ * u)
        ≤ Fintype.card ι * K * (Real.exp (μ * t) / Real.sqrt μ) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring

/-- **Linearity of the Duhamel term.** -/
theorem duhamel_sub {N N' : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k)
    (hN' : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N' p.1 p.2 k) {t : ℝ} (ht : 0 < t)
    {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hNb : ∀ u ∈ Ioc 0 t, ∀ y k, |N u y k| ≤ K * Real.exp (μ * u))
    (hNb' : ∀ u ∈ Ioc 0 t, ∀ y k, |N' u y k| ≤ K * Real.exp (μ * u)) (x : UnitAddTorus ι) :
    duhamel N t x - duhamel N' t x = duhamel (fun u y k => N u y k - N' u y k) t x := by
  unfold duhamel
  rw [← integral_sub (integrableOn_duhamel_integrand hN ht hK hμ hNb x)
    (integrableOn_duhamel_integrand hN' ht hK hμ hNb' x)]
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by rw [ae_iff]; simp
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [hne] with u hu hmem
  have hs : 0 < t - u := sub_pos.2 (lt_of_le_of_ne hmem.2 hu)
  have hm : ∀ (G : ℝ → UnitAddTorus ι → ι → ℝ),
      (∀ k, Measurable fun p : ℝ × UnitAddTorus ι => G p.1 p.2 k) →
      ∀ k, AEStronglyMeasurable (fun z => G u z k) volume := fun G hG k =>
    ((hG k).comp measurable_prodMk_left).aestronglyMeasurable
  exact (divHeatT_sub hs (hm N hN) (hm N' hN') (fun k => Eventually.of_forall fun y => hNb u hmem y k)
    (fun k => Eventually.of_forall fun y => hNb' u hmem y k) x).symm

end SharpLSI