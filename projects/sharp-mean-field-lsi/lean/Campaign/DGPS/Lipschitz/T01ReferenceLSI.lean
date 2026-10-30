import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Analysis.RelativeFisher
import DGPS.Variational.FrozenGibbs
import FullLabeledLSI.Paper.Sec5LNE

/-!
# The actual frozen reference LSI for bounded weak densities

The density bounds and weak inverse-density calculation use the direct Lipschitz frozen
potential. The reference entropy/Dirichlet calculation is the assumption-clean proof from
`Defective21`, with its former semiconvex equilibrium wrapper discharged on the actual reference.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL

private theorem actual_isWeakGrad_inv_frozenDensity {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (μ : ProbabilityMeasure (Torus d)) :
    IsWeakGrad (fun x => 1 / frozenDensity J (μ : Measure (Torus d)) x)
      (fun x k => 1 / frozenDensity J (μ : Measure (Torus d)) x *
        lipGrad (PhiMF J.V J.W μ) x k) := by
  obtain ⟨L, hL0, hL⟩ := lipschitz_equilibriumPotential J hJ
  have hΦ : TorusLipschitzWith L (PhiMF J.V J.W μ) := hL (μ : Measure (Torus d))
  have hΦL := DGPS.RelativeFisher.lipschitzWith_comp_lift hΦ
  have hΦc : Continuous (PhiMF J.V J.W μ) := frozenPotential_continuous J μ
  have hw := isWeakGrad_lipGrad hΦc hΦL
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hΦc
  have h2 := hw.cmul (-2)
  have hi : Integrable (fun x => -2 * PhiMF J.V J.W μ x) (haar d) :=
    hΦc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) |>.const_mul (-2)
  have hgi : ∀ k, Integrable (fun x => -2 * lipGrad (PhiMF J.V J.W μ) x k) (haar d) := by
    intro k
    have hi' : Integrable (fun x => lipGrad (PhiMF J.V J.W μ) x k) (haar d) :=
      Integrable.of_bound (measurable_lipGrad hΦc k).aestronglyMeasurable (Real.toNNReal (L * Real.sqrt d))
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_lipGrad_le hΦL x k)
    exact hi'.const_mul (-2)
  have he := isWeakGrad_exp_neg_half h2 hi hgi (B := 2 * B) (fun x => by
    rw [abs_mul, abs_neg, abs_two]
    exact mul_le_mul_of_nonneg_left (hB x) zero_le_two)
  simp only [show ∀ y, -(-2 * PhiMF J.V J.W μ y) / 2 = PhiMF J.V J.W μ y by
    intro y; ring] at he
  have h := he.cmul (frozenPartition J (μ : Measure (Torus d)))
  convert h using 1
  · funext x
    rw [frozenDensity, one_div_div, Real.exp_neg, div_inv_eq_mul]
    change frozenPartition J ↑μ * Real.exp (PhiMF J.V J.W ↑μ x) = _
    rfl
  · funext x k
    rw [frozenDensity, one_div_div, Real.exp_neg, div_inv_eq_mul]
    change frozenPartition J ↑μ * Real.exp (PhiMF J.V J.W ↑μ x) * _ = _
    ring

/-- A direct-Lipschitz fixed point supplies the exact reference LSI used by the last-increment
conditional-entropy argument, on all bounded positive weak densities. -/
theorem exists_actual_refLSI {d : ℕ} (J : InteractionData d) (hJ : LipschitzData J)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs J μ).measure = (μ : Measure (Torus d))) :
    ∃ Aref : ℝ, 0 < Aref ∧ RefLSI J.V J.W (μ : Measure (Torus d)) Aref := by
  obtain ⟨L, hL0, hL⟩ := lipschitz_equilibriumPotential J hJ
  have hΦ : TorusLipschitzWith L (PhiMF J.V J.W μ) := hL (μ : Measure (Torus d))
  let LΦ : ℝ≥0 := Real.toNNReal (L * Real.sqrt d)
  have hLΦ : LipschitzWith LΦ (PhiMF J.V J.W μ ∘ liftT) :=
    DGPS.RelativeFisher.lipschitzWith_comp_lift hΦ
  have hΦc : Continuous (PhiMF J.V J.W μ) := frozenPotential_continuous J μ
  let q := frozenDensity J (μ : Measure (Torus d))
  let cm := Real.exp (-(2 * frozenSupBound J))
  let cp := Real.exp (2 * frozenSupBound J)
  have hcm : 0 < cm := Real.exp_pos _
  have hqb : ∀ x, cm ≤ q x ∧ q x ≤ cp := frozenDensity_bounds J (μ : Measure (Torus d))
  have hμq : (μ : Measure (Torus d)) = densMeasure q := hfix.symm
  have hq1 : ∫ x, q x ∂haar d = 1 := integral_frozenDensity J (μ : Measure (Torus d))
  have hiq := actual_isWeakGrad_inv_frozenDensity J hJ μ
  have hcp : 0 < cp := hcm.trans_le ((hqb 0).1.trans (hqb 0).2)
  have hq0 : ∀ x, 0 < q x := fun x => hcm.trans_le (hqb x).1
  have hqc : Continuous q := frozenDensity_continuous J μ
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
  have hgΦm : ∀ k, Measurable fun x => lipGrad (PhiMF J.V J.W μ) x k :=
    measurable_lipGrad (hΦc)
  have hgΦB : ∀ x k, |lipGrad (PhiMF J.V J.W μ) x k| ≤ LΦ := fun x k => abs_lipGrad_le hLΦ x k
  have hr := h.mul_lip hρi hgi hiq hiqm hiqB
    (fun k => hiqm.mul (hgΦm k)) (L := 1 / cm * LΦ) fun x k => by
      rw [abs_mul]
      exact mul_le_mul (hiqB x) (hgΦB x k) (abs_nonneg _) (by positivity)
  set r : Torus d → ℝ := fun x => ρ x * (1 / q x) with hrdef
  set gr : Torus d → Fin d → ℝ := fun x k => g x k * (1 / q x) + ρ x * (1 / q x * lipGrad (PhiMF J.V J.W μ) x k)
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
  have hmem : SharpLSI.MemH1 (densMeasure q) w := by
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
      ((ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF J.V J.W μ) x k) ^ 2) / 4) ∂haar d := by
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
  have e : (fun x => ENNReal.ofReal ((ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF J.V J.W μ) x k) ^ 2) / 4)) =
      fun x => ENNReal.ofReal (1 / 4) *
        ENNReal.ofReal (ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF J.V J.W μ) x k) ^ 2) := by
    funext x; rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2; ring

end DGPS.Lipschitz
