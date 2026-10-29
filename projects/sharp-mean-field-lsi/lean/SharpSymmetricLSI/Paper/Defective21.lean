import SharpSymmetricLSI.Paper.Defective20
import SharpSymmetricLSI.Paper.ReferenceLSI

/-!
# R03 (Proposition 2.2), part 21: the reference LSI for a density bounded below

For the minimizer `μ = q · haar` (`q = e^{-Φ}/Z_q`, `Φ = V + W * μ`) and a probability density `ρ`
bounded above and below with `∇ρ = g ∈ L²`:
`H(ρ|μ) ≤ (c₊/c₋)/2 · ∫ ρ |g/ρ + ∇Φ|²` (`klDiv_le_of_reference_lsi`), from R22 applied to
`w = √(ρ/q)`.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `H(ρ|μ) = Ent_μ(ρ/q)` for densities. -/
theorem klDiv_densMeasure_eq_ent {ρ q : Torus d → ℝ} (hρm : Measurable ρ) (hqm : Measurable q)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hq0 : ∀ x, 0 < q x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hq1 : ∫ x, q x ∂haar d = 1) {B : ℝ} (hB : ∀ x, ρ x / q x ≤ B) :
    klDiv (densMeasure ρ) (densMeasure q) = ent (densMeasure q) (fun x => ρ x / q x) := by
  haveI := isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  haveI := isProbabilityMeasure_densMeasure' hρ0 hρ1
  have hmρq : Measurable fun x => ENNReal.ofReal (ρ x / q x) := (hρm.div hqm).ennreal_ofReal
  have hdq : densMeasure ρ = (densMeasure q).withDensity fun x => ENNReal.ofReal (ρ x / q x) := by
    unfold densMeasure
    rw [← withDensity_mul _ ((hqm).ennreal_ofReal) hmρq]
    congr 1; funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq0 x).le, mul_div_cancel₀ _ (hq0 x).ne']
  have hrn : (densMeasure ρ).rnDeriv (densMeasure q) =ᵐ[densMeasure q] fun x => ENNReal.ofReal (ρ x / q x) := by
    rw [hdq]; exact Measure.rnDeriv_withDensity _ hmρq
  have hac : densMeasure ρ ≪ densMeasure q := by rw [hdq]; exact withDensity_absolutelyContinuous _ _
  have hint : Integrable (fun x => ρ x / q x) (densMeasure q) :=
    Integrable.of_bound (hρm.div hqm).aestronglyMeasurable B (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hρ0 x) (hq0 x).le)]; exact hB x)
  have h1 : ∫ x, ρ x / q x ∂densMeasure q = 1 := by
    rw [integral_densMeasure' (fun x => (hq0 x).le) hq1]
    simp_rw [mul_div_cancel₀ _ (hq0 _).ne']; exact hρ1
  rw [klDiv_eq_lintegral_klFun_of_ac hac, ent_normalized (P := densMeasure q) hint h1]
  refine lintegral_congr_ae ?_
  filter_upwards [hrn] with x hx
  rw [hx, ENNReal.toReal_ofReal (div_nonneg (hρ0 x) (hq0 x).le)]

section refLSI
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

theorem elDens_eq_exp (x : Torus d) : elDens V W (μ : Measure (Torus d)) x =
    Real.exp (-PhiMF V W μ x) / ∫ y, Real.exp (-PhiMF V W μ y) ∂haar d := by
  simp only [elDens, PhiMF, neg_add']

theorem isWeakGrad_elDens :
    IsWeakGrad (elDens V W (μ : Measure (Torus d)))
      (fun x k => -(elDens V W (μ : Measure (Torus d)) x * lipGrad (PhiMF V W μ) x k)) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨B, hB⟩ := exists_bound_of_continuous (continuous_PhiMF hyp (μ := (μ : Measure (Torus d))))
  have h2 := (isWeakGrad_PhiMF hyp hac (μ := (μ : Measure (Torus d)))).cmul 2
  have hi : Integrable (fun x => 2 * PhiMF V W μ x) (haar d) :=
    ((integrable_PhiMF hyp hac).const_mul 2)
  have hgi : ∀ k, Integrable (fun x => 2 * lipGrad (PhiMF V W μ) x k) (haar d) := fun k =>
    (integrable_lipGrad_PhiMF hyp hac k).const_mul 2
  have he := isWeakGrad_exp_neg_half h2 hi hgi (B := 2 * B) fun x => by
    rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (hB x) zero_le_two
  simp only [show ∀ y, -(2 * PhiMF V W μ y) / 2 = -PhiMF V W μ y from fun y => by ring] at he
  have h := he.cmul (1 / ∫ y, Real.exp (-PhiMF V W μ y) ∂haar d)
  convert h using 1
  · funext x; rw [elDens_eq_exp hyp hμ]; ring
  · funext x k; rw [elDens_eq_exp hyp hμ]; ring

theorem isWeakGrad_inv_elDens :
    IsWeakGrad (fun x => 1 / elDens V W (μ : Measure (Torus d)) x)
      (fun x k => 1 / elDens V W (μ : Measure (Torus d)) x * lipGrad (PhiMF V W μ) x k) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨B, hB⟩ := exists_bound_of_continuous (continuous_PhiMF hyp (μ := (μ : Measure (Torus d))))
  have h2 := (isWeakGrad_PhiMF hyp hac (μ := (μ : Measure (Torus d)))).cmul (-2)
  have hi : Integrable (fun x => -2 * PhiMF V W μ x) (haar d) :=
    ((integrable_PhiMF hyp hac).const_mul (-2))
  have hgi : ∀ k, Integrable (fun x => -2 * lipGrad (PhiMF V W μ) x k) (haar d) := fun k =>
    (integrable_lipGrad_PhiMF hyp hac k).const_mul (-2)
  have he := isWeakGrad_exp_neg_half h2 hi hgi (B := 2 * B) fun x => by
    rw [abs_mul, abs_neg, abs_two]; exact mul_le_mul_of_nonneg_left (hB x) zero_le_two
  simp only [show ∀ y, -(-2 * PhiMF V W μ y) / 2 = PhiMF V W μ y from fun y => by ring] at he
  have h := he.cmul (∫ y, Real.exp (-PhiMF V W μ y) ∂haar d)
  convert h using 1
  · funext x; rw [elDens_eq_exp hyp hμ, one_div_div, Real.exp_neg, div_inv_eq_mul]
  · funext x k; rw [elDens_eq_exp hyp hμ, one_div_div, Real.exp_neg, div_inv_eq_mul]; ring

/-- **The reference LSI for a density** (R22 applied to `√(ρ/q)`):
`H(ρ|μ) ≤ A ∫ ρ |g/ρ + ∇Φ|²`, with `A` independent of `ρ`. -/
theorem exists_klDiv_le_reference : ∃ A : ℝ, 0 < A ∧ ∀ {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ},
    Measurable ρ → IsWeakGrad ρ g → (∀ k, Measurable fun x => g x k) →
    (∀ k, MemLp (fun x => g x k) 2 (haar d)) → ∀ {c C : ℝ}, 0 < c → (∀ x, c ≤ ρ x) →
    (∀ x, ρ x ≤ C) → ∫ x, ρ x ∂haar d = 1 →
    klDiv (densMeasure ρ) (μ : Measure (Torus d)) ≤ ENNReal.ofReal A *
      ∫⁻ x, ENNReal.ofReal (ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF V W μ) x k) ^ 2) ∂haar d := by
  obtain ⟨cm, cp, Lq, hcm, hB⟩ := elDensity_bounds hyp
  have hac := minimizer_ac hyp hμ
  obtain ⟨LΦ, hLΦ⟩ := lipschitz_PhiMF hyp hac (μ := (μ : Measure (Torus d)))
  obtain ⟨hqb, hqL⟩ := hB (μ : Measure (Torus d)) inferInstance
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    minimizer_eq_elDensity hyp hμ
  have hq1 : ∫ x, elDens V W (μ : Measure (Torus d)) x ∂haar d = 1 :=
    (elDensity_props hyp (μ : Measure (Torus d))).2.2
  have hiq := isWeakGrad_inv_elDens hyp hμ
  generalize hqdef : elDens V W (μ : Measure (Torus d)) = q at hqb hqL hμq hq1 hiq
  have hcp : 0 < cp := hcm.trans_le ((hqb 0).1.trans (hqb 0).2)
  have hq0 : ∀ x, 0 < q x := fun x => hcm.trans_le (hqb x).1
  have hqc : Continuous q := hqL.continuous
  have hqm : Measurable q := hqc.measurable
  haveI : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  refine ⟨2 / (cm / cp) / 4, by positivity, ?_⟩
  intro ρ g hρm h hgm hg2 c C hc hρc hρC h1
  have hρ0 : ∀ x, 0 < ρ x := fun x => hc.trans_le (hρc x)
  have hρi : Integrable ρ (haar d) := Integrable.of_bound hρm.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_pos (hρ0 x)]; exact hρC x)
  have hgi : ∀ k, Integrable (fun x => g x k) (haar d) := fun k => (hg2 k).integrable one_le_two
  -- `r = ρ / q`
  have hiqm : Measurable fun x => 1 / q x := measurable_const.div hqm
  have hiqB : ∀ x, |1 / q x| ≤ 1 / cm := fun x => by
    rw [abs_of_pos (one_div_pos.mpr (hq0 x))]
    exact one_div_le_one_div_of_le hcm (hqb x).1
  have hgΦm : ∀ k, Measurable fun x => lipGrad (PhiMF V W μ) x k :=
    measurable_lipGrad (continuous_PhiMF hyp)
  have hgΦB : ∀ x k, |lipGrad (PhiMF V W μ) x k| ≤ LΦ := fun x k => abs_lipGrad_le hLΦ x k
  have hr := h.mul_lip hρi hgi hiq hiqm hiqB
    (fun k => hiqm.mul (hgΦm k)) (L := 1 / cm * LΦ) fun x k => by
      rw [abs_mul]
      exact mul_le_mul (hiqB x) (hgΦB x k) (abs_nonneg _) (by positivity)
  set r : Torus d → ℝ := fun x => ρ x * (1 / q x) with hrdef
  set gr : Torus d → Fin d → ℝ := fun x k => g x k * (1 / q x) + ρ x * (1 / q x * lipGrad (PhiMF V W μ) x k)
    with hgrdef
  have hrm : Measurable r := hρm.mul hiqm
  have hrc : ∀ x, c / cp ≤ r x := fun x => by
    simp only [hrdef, mul_one_div]
    exact div_le_div₀ (hρ0 x).le (hρc x) (hq0 x) (hqb x).2
  have hrC : ∀ x, r x ≤ C / cm := fun x => by
    simp only [hrdef, mul_one_div]
    exact div_le_div₀ (hc.le.trans (hρc x) |>.trans (hρC x)) (hρC x) hcm (hqb x).1
  have hri : Integrable r (haar d) := Integrable.of_bound hrm.aestronglyMeasurable (C / cm)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos ((div_pos hc hcp).trans_le (hrc x))]; exact hrC x)
  have hgrm : ∀ k, Measurable fun x => gr x k := fun k =>
    ((hgm k).mul hiqm).add (hρm.mul (hiqm.mul (hgΦm k)))
  have hgr_le : ∀ x k, |gr x k| ≤ 1 / cm * |g x k| + C * (1 / cm * LΦ) := fun x k => by
    simp only [hgrdef]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hiqB x) (abs_nonneg _)
    · rw [abs_mul, abs_mul, abs_of_pos (hρ0 x)]
      exact mul_le_mul (hρC x) (mul_le_mul (hiqB x) (hgΦB x k) (abs_nonneg _) (by positivity))
        (by positivity) (hc.le.trans ((hρc x).trans (hρC x)))
  have hgri : ∀ k, Integrable (fun x => gr x k) (haar d) := fun k =>
    ((((hgi k).abs.const_mul (1 / cm)).add (integrable_const (C * (1 / cm * LΦ)))).mono'
      (hgrm k).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hgr_le x k))
  have hS := isWeakGrad_sqrt_of_ge hr hri hgri (div_pos hc hcp) hrc
  -- the measure `μ = q · haar` is dominated by `cp · haar`
  have hle : densMeasure q ≤ ENNReal.ofReal cp • haar d := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, densMeasure, withDensity_apply _ hs]
    calc ∫⁻ x in s, ENNReal.ofReal (q x) ∂haar d ≤ ∫⁻ _ in s, ENNReal.ofReal cp ∂haar d :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hqb x).2
      _ = ENNReal.ofReal cp * haar d s := by rw [setLIntegral_const]
  have hacq : densMeasure q ≪ haar d := withDensity_absolutelyContinuous _ _
  set w : Torus d → ℝ := fun x => Real.sqrt (r x) with hwdef
  set gw : Torus d → Fin d → ℝ := fun x k => gr x k / (2 * Real.sqrt (r x)) with hgwdef
  have hwm : Measurable w := Real.continuous_sqrt.measurable.comp hrm
  have hmem : MemH1 (densMeasure q) w := by
    refine ⟨⟨_, hS⟩, MemLp.of_bound hwm.aestronglyMeasurable (Real.sqrt (C / cm))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hrC x)), ?_⟩
    have hsc0 : 0 < Real.sqrt (c / cp) := Real.sqrt_pos.mpr (div_pos hc hcp)
    set κ := 1 / (2 * Real.sqrt (c / cp)) with hκ
    have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
    have hC0 : 0 ≤ C := hc.le.trans ((hρc 0).trans (hρC 0))
    have hL : MemLp (fun x => ∑ k, κ * (1 / cm * ‖g x k‖ + C * (1 / cm * LΦ))) 2 (densMeasure q) := by
      refine MemLp.of_measure_le_smul ENNReal.ofReal_ne_top hle ?_
      exact memLp_finsetSum _ fun k _ =>
        ((((hg2 k).norm).const_mul _).add (memLp_const _)).const_mul _
    refine hL.of_le (Real.continuous_sqrt.comp_aestronglyMeasurable
      ((isWeakGrad_weakGrad ⟨_, hS⟩).aestronglyMeasurable_sqNorm.mono_ac hacq)) ?_
    filter_upwards [hacq.ae_le (weakGrad_ae_eq hS)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg hκ0
        (add_nonneg (by positivity) (mul_nonneg hC0 (by positivity)))), hx]
    have hsr : Real.sqrt (c / cp) ≤ Real.sqrt (r x) := Real.sqrt_le_sqrt (hrc x)
    have hpt : ∀ k, |gr x k / (2 * Real.sqrt (r x))| ≤
        κ * (1 / cm * ‖g x k‖ + C * (1 / cm * LΦ)) := fun k => by
      have hd : (0 : ℝ) < 2 * Real.sqrt (r x) := by linarith
      rw [abs_div, abs_of_pos hd, Real.norm_eq_abs, div_eq_mul_one_div, mul_comm]
      exact mul_le_mul (one_div_le_one_div_of_le (by positivity) (by linarith)) (hgr_le x k)
        (abs_nonneg _) hκ0
    calc Real.sqrt (sqNorm fun k => gr x k / (2 * Real.sqrt (r x)))
        ≤ ∑ k, |gr x k / (2 * Real.sqrt (r x))| := by
          rw [Real.sqrt_le_left (Finset.sum_nonneg fun k _ => abs_nonneg _)]
          unfold sqNorm
          calc ∑ k, (gr x k / (2 * Real.sqrt (r x))) ^ 2 = ∑ k, |gr x k / (2 * Real.sqrt (r x))| ^ 2 := by
                simp_rw [sq_abs]
            _ ≤ (∑ k, |gr x k / (2 * Real.sqrt (r x))|) ^ 2 :=
                Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
      _ ≤ _ := Finset.sum_le_sum fun k _ => hpt k
  have hlsi := reference_lsi_aux hcm (fun x => hqb x) hq1 hqm (g := w) hmem
  -- identify both sides
  have hent : ent (densMeasure q) (fun x => w x ^ 2) = ent (densMeasure q) (fun x => ρ x / q x) := by
    congr 1; funext x
    simp only [hwdef, hrdef]
    rw [Real.sq_sqrt (mul_nonneg (hρ0 x).le (one_div_pos.mpr (hq0 x)).le), mul_one_div]
  have hdir : dirichlet (densMeasure q) w = ∫⁻ x, ENNReal.ofReal
      ((ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF V W μ) x k) ^ 2) / 4) ∂haar d := by
    have hgm' : AEMeasurable (fun x => ENNReal.ofReal (sqNorm (weakGrad w x))) (haar d) :=
      (isWeakGrad_weakGrad ⟨_, hS⟩).aestronglyMeasurable_sqNorm.aemeasurable.ennreal_ofReal
    unfold dirichlet densMeasure
    rw [lintegral_withDensity_eq_lintegral_mul₀ (μ := haar d) ((hqm).ennreal_ofReal).aemeasurable hgm']
    refine lintegral_congr_ae ?_
    filter_upwards [weakGrad_ae_eq hS] with x hx
    try simp only [Pi.mul_apply]
    rw [hx, ← ENNReal.ofReal_mul (hq0 x).le]
    congr 1
    unfold sqNorm
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hr0 : 0 < r x := (div_pos hc hcp).trans_le (hrc x)
    have hsq : Real.sqrt (r x) ^ 2 = r x := Real.sq_sqrt hr0.le
    have hs0 : 0 < Real.sqrt (r x) := Real.sqrt_pos.mpr hr0
    have hrx : r x = ρ x / q x := by simp only [hrdef, mul_one_div]
    rw [div_pow, mul_pow, hsq, hrx, hgrdef]
    beta_reduce
    have := (hq0 x).ne'; have := (hρ0 x).ne'
    first | (field_simp; done) | (field_simp; ring)
  have hk : klDiv (densMeasure ρ) (μ : Measure (Torus d)) = klDiv (densMeasure ρ) (densMeasure q) := by
    rw [hμq]
  rw [hk, klDiv_densMeasure_eq_ent hρm hqm (fun x => (hρ0 x).le) hq0 h1 hq1
    (B := C / cm) (fun x => by rw [← mul_one_div]; exact hrC x), ← hent]
  refine hlsi.trans (le_of_eq ?_)
  rw [show ((haar d).withDensity fun x => ENNReal.ofReal (q x)) = densMeasure q from rfl, hdir]
  have e : (fun x => ENNReal.ofReal ((ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF V W μ) x k) ^ 2) / 4)) =
      fun x => ENNReal.ofReal (1 / 4) *
        ENNReal.ofReal (ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF V W μ) x k) ^ 2) := by
    funext x; rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2; ring
end refLSI

end SharpLSI
