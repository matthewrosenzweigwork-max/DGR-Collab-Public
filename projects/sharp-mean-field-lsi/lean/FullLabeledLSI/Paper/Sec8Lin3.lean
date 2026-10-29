import FullLabeledLSI.Paper.Sec8Lin2

/-!
# Section 8.3 (linearization), part 3: weak gradients of `√(p(1 + t h))` and the relative Fisher
information along the perturbation
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

/-- Lipschitz, weak gradient and `H¹` membership of `√(p(1+th))`. -/
theorem pert_weak {p h : Torus d → ℝ} {c C : ℝ} {Lp : ℝ≥0} (hc : 0 < c)
    (hpb : ∀ x, c ≤ p x ∧ p x ≤ C) (hpL : LipschitzWith Lp p)
    (hh : ∃ L : ℝ≥0, LipschitzWith L h) {t : ℝ}
    (hA : ∀ x, 1 / 2 ≤ 1 + t * h x ∧ 1 + t * h x ≤ 3 / 2) :
    (∃ L : ℝ≥0, LipschitzWith L (fun x => p x * (1 + t * h x))) ∧
    (∀ x, c / 2 ≤ p x * (1 + t * h x) ∧ p x * (1 + t * h x) ≤ C * (3 / 2)) ∧
    IsWeakGrad (fun y => Real.sqrt (p y * (1 + t * h y)))
      (fun y k => (lipGrad p y k * (1 + t * h y) + p y * (t * lipGrad h y k)) /
        (2 * Real.sqrt (p y * (1 + t * h y)))) ∧
    MemH1 (haar d) (fun y => Real.sqrt (p y * (1 + t * h y))) := by
  obtain ⟨hch, hwh, ⟨Kh, hKh⟩, hmh⟩ := lip_data hh
  obtain ⟨hcp, hwp, ⟨Kp, hKp⟩, hmp⟩ := lip_data ⟨Lp, hpL⟩
  have hp0 : ∀ x, 0 < p x := fun x => hc.trans_le (hpb x).1
  have hC0 : 0 ≤ C := (hp0 0).le.trans (hpb 0).2
  have hA0 : ∀ x, 0 < 1 + t * h x := fun x => by linarith [(hA x).1]
  have hAL : ∃ L : ℝ≥0, LipschitzWith L (fun x => 1 + t * h x) := lip_add (lip_const 1) (lip_smul t hh)
  have hρL := lip_mul ⟨Lp, hpL⟩ hAL (Bu := C) (Bv := 3 / 2) hC0 (by norm_num)
    (fun x => by rw [abs_of_pos (hp0 x)]; exact (hpb x).2)
    (fun x => by rw [abs_of_pos (hA0 x)]; exact (hA x).2)
  have hρb : ∀ x, c / 2 ≤ p x * (1 + t * h x) ∧ p x * (1 + t * h x) ≤ C * (3 / 2) := fun x => by
    refine ⟨?_, mul_le_mul (hpb x).2 (hA x).2 (hA0 x).le hC0⟩
    have := mul_le_mul (hpb x).1 (hA x).1 (by norm_num) (hp0 x).le
    linarith
  refine ⟨hρL, hρb, ?_, ?_⟩
  · obtain ⟨Lρ, hLρ⟩ := hρL
    have hAcont : Continuous fun x => 1 + t * h x := continuous_const.add (continuous_const.mul hch)
    have hAw : IsWeakGrad (fun x => 1 + t * h x) (fun y k => t * lipGrad h y k) := by
      have := (isWeakGrad_const (ι := Fin d) 1).add (hwh.cmul t)
      convert this using 1
      funext y k; simp
    have hpi : Integrable p volume := integrable_of_bdd hcp.measurable (C := C) fun x => by
      rw [abs_of_pos (hp0 x)]; exact (hpb x).2
    have hgpi : ∀ k, Integrable (fun y => lipGrad p y k) volume := fun k =>
      integrable_of_bdd (hmp k) fun y => hKp y k
    have hρw := IsWeakGrad.mul_lip hwp hpi hgpi hAw hAcont.measurable (B := 3 / 2)
      (fun y => by rw [abs_of_pos (hA0 y)]; exact (hA y).2)
      (fun k => measurable_const.mul (hmh k)) (L := |t| * Kh) (fun y k => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKh y k) (abs_nonneg _))
    have hρc : Continuous fun x => p x * (1 + t * h x) := hcp.mul hAcont
    have hρi : Integrable (fun x => p x * (1 + t * h x)) volume :=
      integrable_of_bdd hρc.measurable (C := C * (3 / 2)) fun x => by
        rw [abs_of_pos (lt_of_lt_of_le (by linarith [hc]) (hρb x).1)]; exact (hρb x).2
    have hgρi : ∀ k, Integrable (fun y => lipGrad p y k * (1 + t * h y) +
        p y * (t * lipGrad h y k)) volume := fun k =>
      integrable_of_bdd (C := Kp * (3 / 2) + C * (|t| * Kh))
        (((hmp k).mul hAcont.measurable).add (hcp.measurable.mul (measurable_const.mul (hmh k))))
        fun y => by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_pos (hA0 y)]
            exact mul_le_mul (hKp y k) (hA y).2 (hA0 y).le ((abs_nonneg _).trans (hKp y k))
          · rw [abs_mul, abs_mul, abs_of_pos (hp0 y)]
            exact mul_le_mul (hpb y).2 (mul_le_mul_of_nonneg_left (hKh y k) (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC0
    exact isWeakGrad_sqrt_of_ge hρw hρi hgρi (c := c / 2) (by positivity) fun x => (hρb x).1
  · obtain ⟨Lρ, hLρ⟩ := hρL
    exact (memH1_sqrt_of_lipschitz (by positivity) hρb hLρ).2

theorem relJ_props {ga gb : Torus d → Fin d → ℝ} {ha hb : Torus d → ℝ} {K t : ℝ}
    (hK0 : 0 ≤ K) (hga : ∀ x k, |ga x k| ≤ K) (hgb : ∀ x k, |gb x k| ≤ K)
    (hA : ∀ x, 1 / 2 ≤ 1 + t * ha x ∧ 1 + t * ha x ≤ 3 / 2)
    (hB : ∀ x, 1 / 2 ≤ 1 + t * hb x ∧ 1 + t * hb x ≤ 3 / 2)
    (hmga : ∀ k, Measurable fun x => ga x k) (hmgb : ∀ k, Measurable fun x => gb x k)
    (hma : Measurable ha) (hmb : Measurable hb) :
    Measurable (relJ ga gb ha hb t) ∧
      ∀ x, 0 ≤ relJ ga gb ha hb t x ∧ relJ ga gb ha hb t x ≤ 24 * d * K ^ 2 := by
  refine ⟨?_, fun x => ?_⟩
  · unfold relJ
    exact (measurable_const.add (measurable_const.mul hma)).mul
      (Finset.measurable_sum _ fun k _ =>
        (((hmga k).div (measurable_const.add (measurable_const.mul hma))).sub
          ((hmgb k).div (measurable_const.add (measurable_const.mul hmb)))).pow_const 2)
  · have hA0 : 0 < 1 + t * ha x := by linarith [(hA x).1]
    have hB0 : 0 < 1 + t * hb x := by linarith [(hB x).1]
    have hq : ∀ k, (ga x k / (1 + t * ha x) - gb x k / (1 + t * hb x)) ^ 2 ≤ (4 * K) ^ 2 :=
      fun k => by
      have h1 : |ga x k / (1 + t * ha x)| ≤ 2 * K := by
        rw [abs_div, abs_of_pos hA0, div_le_iff₀ hA0]; nlinarith [hga x k, (hA x).1]
      have h2 : |gb x k / (1 + t * hb x)| ≤ 2 * K := by
        rw [abs_div, abs_of_pos hB0, div_le_iff₀ hB0]; nlinarith [hgb x k, (hB x).1]
      have h3 : |ga x k / (1 + t * ha x) - gb x k / (1 + t * hb x)| ≤ 4 * K :=
        (abs_sub _ _).trans (by linarith)
      calc _ = |ga x k / (1 + t * ha x) - gb x k / (1 + t * hb x)| ^ 2 := (sq_abs _).symm
        _ ≤ (4 * K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    have hS0 : 0 ≤ ∑ k, (ga x k / (1 + t * ha x) - gb x k / (1 + t * hb x)) ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hS : ∑ k, (ga x k / (1 + t * ha x) - gb x k / (1 + t * hb x)) ^ 2 ≤ d * (4 * K) ^ 2 :=
      (Finset.sum_le_sum fun k _ => hq k).trans (by simp)
    refine ⟨mul_nonneg hA0.le hS0, ?_⟩
    calc relJ ga gb ha hb t x ≤ (3 / 2) * (d * (4 * K) ^ 2) :=
          mul_le_mul (hA x).2 hS hS0 (by norm_num)
      _ = 24 * d * K ^ 2 := by ring

theorem relFisher_pert {p ha hb : Torus d → ℝ} {c C : ℝ} {Lp : ℝ≥0} (hc : 0 < c)
    (hpb : ∀ x, c ≤ p x ∧ p x ≤ C) (hpL : LipschitzWith Lp p)
    (hha : ∃ L : ℝ≥0, LipschitzWith L ha) (hhb : ∃ L : ℝ≥0, LipschitzWith L hb) {t : ℝ}
    (hA : ∀ x, 1 / 2 ≤ 1 + t * ha x ∧ 1 + t * ha x ≤ 3 / 2)
    (hB : ∀ x, 1 / 2 ≤ 1 + t * hb x ∧ 1 + t * hb x ≤ 3 / 2)
    (hac : densMeasure (fun x => p x * (1 + t * ha x)) ≪
      densMeasure (fun x => p x * (1 + t * hb x))) :
    relFisher (fun x => p x * (1 + t * ha x)) (fun x => p x * (1 + t * hb x)) =
      ENNReal.ofReal (t ^ 2 * ∫ x, p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x ∂haar d) := by
  obtain ⟨hca, hwa, ⟨Ka, hKa⟩, hma⟩ := lip_data hha
  obtain ⟨hcb, hwb, ⟨Kb, hKb⟩, hmb⟩ := lip_data hhb
  obtain ⟨hcp, hwp, ⟨Kp, hKp⟩, hmp⟩ := lip_data ⟨Lp, hpL⟩
  have hp0 : ∀ x, 0 < p x := fun x => hc.trans_le (hpb x).1
  have hC0 : 0 ≤ C := (hp0 0).le.trans (hpb 0).2
  have hA0 : ∀ x, 0 < 1 + t * ha x := fun x => by linarith [(hA x).1]
  have hB0 : ∀ x, 0 < 1 + t * hb x := fun x => by linarith [(hB x).1]
  obtain ⟨-, -, hSa, hH1a⟩ := pert_weak hc hpb hpL hha hA
  obtain ⟨-, -, hSb, hH1b⟩ := pert_weak hc hpb hpL hhb hB
  set K := max (max Ka Kb) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  obtain ⟨hJm, hJb⟩ := relJ_props (t := t) hK0
    (fun x k => (hKa x k).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun x k => (hKb x k).trans ((le_max_right _ _).trans (le_max_left _ _))) hA hB hma hmb
    hca.measurable hcb.measurable
  have hint : Integrable (fun x => t ^ 2 * (p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x))
      (haar d) := by
    refine Integrable.const_mul (integrable_of_bdd (C := C * (24 * d * K ^ 2))
      (hcp.measurable.mul hJm) fun x => ?_) _
    show |p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x| ≤ _
    rw [abs_mul, abs_of_pos (hp0 x), abs_of_nonneg (hJb x).1]
    exact mul_le_mul (hpb x).2 (hJb x).2 (hJb x).1 hC0
  have hae : ∀ᵐ x ∂haar d, ∑ k, (2 * weakGrad (fun y => Real.sqrt (p y * (1 + t * ha y))) x k -
      Real.sqrt (p x * (1 + t * ha x)) * score (fun y => p y * (1 + t * hb y)) x k) ^ 2 =
      t ^ 2 * (p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x) := by
    filter_upwards [weakGrad_ae_eq hSa, weakGrad_ae_eq hSb] with x h1 h2
    unfold relJ
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 := congrFun h1 k
    have e2 := congrFun h2 k
    unfold score
    simp only []
    rw [e1, e2]
    exact relFisher_alg (hp0 x) (hA0 x) (hB0 x)
  unfold relFisher
  rw [if_pos ⟨hac, hH1a, hH1b⟩]
  rw [lintegral_congr_ae (hae.mono fun x hx => by rw [hx])]
  have := (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hp0 x).le (hJb x).1))).symm
  rw [integral_const_mul] at this
  exact this


theorem eventually_small {B : ℝ} : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * B ≤ 1 / 2 := by
  have : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => |t| * B := continuous_abs.mul continuous_const
    convert hc.tendsto 0 using 2
    simp
  exact this.eventually (ge_mem_nhds (by norm_num))

theorem bounds_of_small {h : Torus d → ℝ} {B t : ℝ} (hB : ∀ x, |h x| ≤ B) (ht : |t| * B ≤ 1 / 2)
    (x : Torus d) : 1 / 2 ≤ 1 + t * h x ∧ 1 + t * h x ≤ 3 / 2 := by
  have : |t * h x| ≤ 1 / 2 := by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)).trans ht
  constructor <;> linarith [(abs_le.mp this).1, (abs_le.mp this).2]

theorem tendsto_relJ_int {p ha hb : Torus d → ℝ} {c C : ℝ} (hc : 0 < c)
    (hpb : ∀ x, c ≤ p x ∧ p x ≤ C) (hpm : Measurable p)
    (hha : ∃ L : ℝ≥0, LipschitzWith L ha) (hhb : ∃ L : ℝ≥0, LipschitzWith L hb)
    {B : ℝ} (hBa : ∀ x, |ha x| ≤ B) (hBb : ∀ x, |hb x| ≤ B) :
    Tendsto (fun t : ℝ => ∫ x, p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x ∂haar d) (𝓝 0)
      (𝓝 (∫ x, p x * ∑ k, (lipGrad ha x k - lipGrad hb x k) ^ 2 ∂haar d)) := by
  obtain ⟨hca, hwa, ⟨Ka, hKa⟩, hma⟩ := lip_data hha
  obtain ⟨hcb, hwb, ⟨Kb, hKb⟩, hmb⟩ := lip_data hhb
  have hp0 : ∀ x, 0 < p x := fun x => hc.trans_le (hpb x).1
  have hC0 : 0 ≤ C := (hp0 0).le.trans (hpb 0).2
  set K := max (max Ka Kb) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hlim : ∀ x, Tendsto (fun t : ℝ => p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x) (𝓝 0)
      (𝓝 (p x * ∑ k, (lipGrad ha x k - lipGrad hb x k) ^ 2)) := fun x => by
    have hca' : ContinuousAt (fun t : ℝ => 1 + t * ha x) 0 := by fun_prop
    have hcb' : ContinuousAt (fun t : ℝ => 1 + t * hb x) 0 := by fun_prop
    have hk : ∀ k, ContinuousAt (fun t : ℝ => (lipGrad ha x k / (1 + t * ha x) -
        lipGrad hb x k / (1 + t * hb x)) ^ 2) 0 := fun k =>
      ((continuousAt_const.div hca' (by simp)).sub (continuousAt_const.div hcb' (by simp))).pow 2
    have hs : ContinuousAt (fun t : ℝ => ∑ k, (lipGrad ha x k / (1 + t * ha x) -
        lipGrad hb x k / (1 + t * hb x)) ^ 2) 0 :=
      tendsto_finsetSum _ fun k _ => (hk k).tendsto
    have : ContinuousAt (fun t : ℝ => p x * relJ (lipGrad ha) (lipGrad hb) ha hb t x) 0 := by
      unfold relJ
      exact continuousAt_const.mul (hca'.mul hs)
    convert this.tendsto using 2
    simp [relJ]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C * (24 * d * K ^ 2)) ?_ ?_
    (integrable_const _) (Eventually.of_forall hlim)
  · filter_upwards [eventually_small (B := B)] with t ht
    exact (hpm.mul (relJ_props hK0 (fun x k => (hKa x k).trans ((le_max_left _ _).trans (le_max_left _ _)))
      (fun x k => (hKb x k).trans ((le_max_right _ _).trans (le_max_left _ _)))
      (bounds_of_small hBa ht) (bounds_of_small hBb ht) hma hmb hca.measurable
      hcb.measurable).1).aestronglyMeasurable
  · filter_upwards [eventually_small (B := B)] with t ht
    refine Eventually.of_forall fun x => ?_
    obtain ⟨-, hJb⟩ := relJ_props hK0 (fun x k => (hKa x k).trans ((le_max_left _ _).trans (le_max_left _ _)))
      (fun x k => (hKb x k).trans ((le_max_right _ _).trans (le_max_left _ _)))
      (bounds_of_small hBa ht) (bounds_of_small hBb ht) hma hmb hca.measurable hcb.measurable
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hp0 x), abs_of_nonneg (hJb x).1]
    exact mul_le_mul (hpb x).2 (hJb x).2 (hJb x).1 hC0

theorem tendsto_relFisher_toReal {p ha hb : Torus d → ℝ} {c C : ℝ} {Lp : ℝ≥0} (hc : 0 < c)
    (hpb : ∀ x, c ≤ p x ∧ p x ≤ C) (hpL : LipschitzWith Lp p)
    (hha : ∃ L : ℝ≥0, LipschitzWith L ha) (hhb : ∃ L : ℝ≥0, LipschitzWith L hb)
    {B : ℝ} (hBa : ∀ x, |ha x| ≤ B) (hBb : ∀ x, |hb x| ≤ B)
    (hac : ∀ᶠ t in 𝓝[≠] (0 : ℝ), densMeasure (fun x => p x * (1 + t * ha x)) ≪
      densMeasure (fun x => p x * (1 + t * hb x))) :
    Tendsto (fun t : ℝ => (relFisher (fun x => p x * (1 + t * ha x))
        (fun x => p x * (1 + t * hb x))).toReal / t ^ 2) (𝓝[≠] 0)
      (𝓝 (∫ x, p x * ∑ k, (lipGrad ha x k - lipGrad hb x k) ^ 2 ∂haar d)) := by
  obtain ⟨hca, hwa, ⟨Ka, hKa⟩, hma⟩ := lip_data hha
  obtain ⟨hcb, hwb, ⟨Kb, hKb⟩, hmb⟩ := lip_data hhb
  have hp0 : ∀ x, 0 < p x := fun x => hc.trans_le (hpb x).1
  set K := max (max Ka Kb) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hlim := (tendsto_relJ_int hc hpb hpL.continuous.measurable hha hhb hBa hBb).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  refine Tendsto.congr' ?_ hlim
  filter_upwards [hac, self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_small (B := B))]
    with t hac' ht0 ht
  obtain ⟨-, hJb⟩ := relJ_props hK0 (fun x k => (hKa x k).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun x k => (hKb x k).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (bounds_of_small hBa ht) (bounds_of_small hBb ht) hma hmb hca.measurable hcb.measurable
  rw [relFisher_pert hc hpb hpL hha hhb (bounds_of_small hBa ht) (bounds_of_small hBb ht) hac',
    ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) (integral_nonneg fun x =>
      mul_nonneg (hp0 x).le (hJb x).1))]
  have : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  rw [mul_div_cancel_left₀ _ this]

end Sec8
end SharpLSI.FL
