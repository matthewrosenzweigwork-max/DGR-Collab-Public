import SharpSymmetricLSI.Paper.FormLiminf10

/-!
# R33 (8.20): `ℰ_N(f) ≥ 2 ℰ_N(f, φ_N) - ℰ_N(φ_N)`
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j) {N : ℕ} (hN : 1 ≤ N)
  (c : Cyl)
include hyp hμ he hφ heC hN

theorem gibbs_ac_pi : gibbs V W N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _

/-- `gradZ` of a cylinder is bounded and measurable. -/
theorem gradZ_cyl_props : (∀ p, Measurable fun y => gradZ eC N c.J c.φ y p) ∧
    ∃ L, ∀ y p, |gradZ eC N c.J c.φ y p| ≤ L :=
  gradZ_props hφ (c.smooth.of_le (by simp)) c.compact

/-- **`2ℰ_N(f, φ_N) - ℰ_N(φ_N) ≤ ℰ_N(f)`** (all real). -/
theorem energy_ge_cross {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    2 * crossE (gibbs V W N) f (fun X => c.φ (zC eC N c.J X)) -
        ∫ X, ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2 ∂gibbs V W N ≤
      (energy V W N f).toReal := by
  have hP := gibbs_isProbabilityMeasure hyp N
  have hac := gibbs_ac_pi hyp hμ he hφ heC hN
  obtain ⟨hbm, Lb, hLb⟩ := gradZ_cyl_props hyp hμ he hφ heC hN c
  have hw := isWeakGrad_weakGrad hf.1
  have ham : ∀ l k, AEStronglyMeasurable (fun X => weakGradC f X l k) (gibbs V W N) :=
    fun l k => (aestronglyMeasurable_comp_flat hyp hμ (hw.aestronglyMeasurable_grad (l, k))).mono_ac hac
  have hbm' : ∀ l k, Measurable fun X : Config N d => gradZ eC N c.J c.φ (flat X) (l, k) :=
    fun l k => (hbm (l, k)).comp measurable_flat
  -- `∑ a²` integrable, with integral `ℰ_N(f)`
  have hEf := energy_lt_top hyp hf
  have hsm : AEStronglyMeasurable (fun X => gradSqC f X) (gibbs V W N) :=
    (aemeasurable_gradSqC_pi hyp hμ hf.1).aestronglyMeasurable.mono_ac hac
  have hsi : Integrable (fun X => gradSqC f X) (gibbs V W N) := by
    refine ⟨hsm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun X => gradSqC_nonneg f X)]
    exact hEf
  have hE : (energy V W N f).toReal = ∫ X, gradSqC f X ∂gibbs V W N := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => gradSqC_nonneg f X) hsm]
    rfl
  rw [hE]
  -- the cross term, a.e.
  have hcr : crossE (gibbs V W N) f (fun X => c.φ (zC eC N c.J X)) =
      ∫ X, ∑ l, ∑ k, weakGradC f X l k * gradZ eC N c.J c.φ (flat X) (l, k) ∂gibbs V W N := by
    unfold crossE
    refine integral_congr_ae ?_
    filter_upwards [weakGradC_cyl_ae hyp hμ he hφ heC hN c] with X hX
    simp only [hX]
  rw [hcr]
  have hab : ∀ l k, Integrable (fun X => weakGradC f X l k * gradZ eC N c.J c.φ (flat X) (l, k))
      (gibbs V W N) := fun l k => by
    have ha2 : Integrable (fun X => weakGradC f X l k ^ 2) (gibbs V W N) := by
      refine hsi.mono' ((ham l k).pow 2) (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      unfold gradSqC
      exact (Finset.single_le_sum (f := fun k' => weakGradC f X l k' ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun l' => ∑ k', weakGradC f X l' k' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ l))
    refine (ha2.add (integrable_const (Lb ^ 2))).mono' ((ham l k).mul
      (hbm' l k).aestronglyMeasurable) (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hLb (flat X) (l, k)
    have h2 := abs_nonneg (weakGradC f X l k)
    have h3 := abs_nonneg (gradZ eC N c.J c.φ (flat X) (l, k))
    have h4 : |weakGradC f X l k| * |gradZ eC N c.J c.φ (flat X) (l, k)| ≤
        |weakGradC f X l k| ^ 2 + |gradZ eC N c.J c.φ (flat X) (l, k)| ^ 2 := by nlinarith
    rw [sq_abs, sq_abs] at h4
    have h5 : gradZ eC N c.J c.φ (flat X) (l, k) ^ 2 ≤ Lb ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ h3 h1 2
    simp only [Pi.add_apply]
    linarith
  have hb2 : ∀ l k, Integrable (fun X => gradZ eC N c.J c.φ (flat X) (l, k) ^ 2) (gibbs V W N) :=
    fun l k => integrable_of_bdd ((hbm' l k).pow_const 2) (C := Lb ^ 2) fun X => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hLb _ _) 2
  have iab : Integrable (fun X => ∑ l, ∑ k, weakGradC f X l k * gradZ eC N c.J c.φ (flat X) (l, k))
      (gibbs V W N) := integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => hab l k
  have ib2 : Integrable (fun X => ∑ l, ∑ k, gradZ eC N c.J c.φ (flat X) (l, k) ^ 2) (gibbs V W N) :=
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => hb2 l k
  rw [← integral_const_mul, ← integral_sub (iab.const_mul 2) ib2]
  refine integral_mono (((iab.const_mul 2).sub ib2)) hsi fun X => ?_
  simp only [Pi.sub_apply]
  unfold gradSqC
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  nlinarith [sq_nonneg (weakGradC f X l k - gradZ eC N c.J c.φ (flat X) (l, k))]

end

end SharpLSI
