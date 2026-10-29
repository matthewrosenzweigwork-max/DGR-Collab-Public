import SharpSymmetricLSI.Paper.Defective21

/-!
# R03 (Proposition 2.2), part 22: the mean-field inequality on each conditional law

For `ν = Q · Leb` (the regularized law), `j < N`, `0 ≤ r₀ ≤ r_*` and `ε > 0`:
`E_ν 2r₀ G(ρ_j) ≤ (1+ε) E_ν |s_j|² + (1 + 1/ε) fcTerm j` (`lintegral_two_r_gap_le`).
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `√ρ ∈ H¹` for a density bounded above and below with an `L²` weak gradient. -/
theorem memH1_sqrt_of_ge {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ}
    (hρm : Measurable ρ) (h : IsWeakGrad ρ g) (hg2 : ∀ k, MemLp (fun x => g x k) 2 (haar d))
    {c C : ℝ} (hc : 0 < c) (hρc : ∀ x, c ≤ ρ x) (hρC : ∀ x, ρ x ≤ C) :
    MemH1 (haar d) (fun x => Real.sqrt (ρ x)) := by
  have hρ0 : ∀ x, 0 < ρ x := fun x => hc.trans_le (hρc x)
  have hρi : Integrable ρ (haar d) := Integrable.of_bound hρm.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_pos (hρ0 x)]; exact hρC x)
  have hgi : ∀ k, Integrable (fun x => g x k) (haar d) := fun k => (hg2 k).integrable one_le_two
  have hS := isWeakGrad_sqrt_of_ge h hρi hgi hc hρc
  refine ⟨⟨_, hS⟩, MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
    hρm.aestronglyMeasurable) (Real.sqrt C) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hρC x)), ?_⟩
  have hL : MemLp (fun x => ∑ k, (1 / (2 * Real.sqrt c)) * ‖g x k‖) 2 (haar d) :=
    memLp_finsetSum _ fun k _ => ((hg2 k).norm).const_mul _
  refine hL.of_le (Real.continuous_sqrt.comp_aestronglyMeasurable
    (isWeakGrad_weakGrad ⟨_, hS⟩).aestronglyMeasurable_sqNorm) ?_
  filter_upwards [weakGrad_ae_eq hS] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg fun k _ => by positivity), hx]
  have hsc : Real.sqrt c ≤ Real.sqrt (ρ x) := Real.sqrt_le_sqrt (hρc x)
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hpt : ∀ k, |g x k / (2 * Real.sqrt (ρ x))| ≤ (1 / (2 * Real.sqrt c)) * ‖g x k‖ := fun k => by
    have hd : (0 : ℝ) < 2 * Real.sqrt (ρ x) := by linarith
    rw [abs_div, abs_of_pos hd, Real.norm_eq_abs, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith)
  calc Real.sqrt (sqNorm fun k => g x k / (2 * Real.sqrt (ρ x)))
      ≤ ∑ k, |g x k / (2 * Real.sqrt (ρ x))| := by
        rw [Real.sqrt_le_left (Finset.sum_nonneg fun k _ => abs_nonneg _)]
        unfold sqNorm
        calc ∑ k, (g x k / (2 * Real.sqrt (ρ x))) ^ 2 = ∑ k, |g x k / (2 * Real.sqrt (ρ x))| ^ 2 := by
              simp_rw [sq_abs]
          _ ≤ (∑ k, |g x k / (2 * Real.sqrt (ρ x))|) ^ 2 :=
              Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ ≤ ∑ k, (1 / (2 * Real.sqrt c)) * ‖g x k‖ := Finset.sum_le_sum fun k _ => hpt k

section prob
variable (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f)
  (hfm : Measurable f)
include hyp hf hfm

theorem isProbabilityMeasure_Qreg (n : ℕ) :
    IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Qreg V W n f X)) := by
  haveI := gibbs_isProbabilityMeasure hyp N
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  have hm : Measurable fun X => regF n f X ^ 2 :=
    ((contDiff_psiReg n).continuous.measurable.comp hfm).pow_const 2
  have hi : Integrable (fun X => regF n f X ^ 2) (gibbs V W N) :=
    Integrable.of_bound hm.aestronglyMeasurable (((n : ℝ) + 2) ^ 2) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [regF]; rw [← psiSqR_eq]; exact (psiSqR_bounds n (f X)).2)
  constructor
  rw [← sqMeasure_regF_eq hyp hf hfm n, sqMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (ae_of_all _ fun X => div_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)),
    integral_div, div_self (by rw [← Zreg_eq hyp hf n]; exact hZ0.ne'), ENNReal.ofReal_one]

end prob

section gapj
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)
include hyp hμ hN hfm hf hw hgm hg2 hgi

/-- **`E_ν 2r₀ G(ρ_j) ≤ (1+ε) E_ν |s_j|² + (1+1/ε) fcTerm j`.** -/
theorem lintegral_two_r_gap_le {r₀ ε : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rStar V W)
    (hε : 0 < ε) :
    haveI := isProbabilityMeasure_Qreg hyp hf hfm n
    ∫⁻ X, ENNReal.ofReal (2 * r₀ * (gap V W (condNext ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (Qreg V W n f X)) j hj (past j hj.le X))).toReal)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) ≤
      ENNReal.ofReal (1 + ε) * (∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g ⟨j, hj⟩ k X ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))) +
      ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (fcTerm W μ ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (Qreg V W n f X)) j) := by
  haveI := isProbabilityMeasure_Qreg hyp hf hfm n
  have hac := minimizer_ac hyp hμ
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  have hC : 0 < C := hc.trans_le ((hb (Classical.arbitrary _)).1.trans (hb _).2)
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)
    with hνdef
  have hmap := map_past_eq hj hQm hc hQc hQC
  -- `ρ_j = condDens` and `√condDens ∈ H¹`, a.e. in the past
  have hcn : ∀ᵐ X ∂ν, condNext ν j hj (past j hj.le X) =
      densMeasure (condDens hj (Qreg V W n f) (past j hj.le X)) :=
    ae_of_ae_map (measurable_past hj.le).aemeasurable (condNext_ae_eq hj hQm hc hQc hQC)
  have hH1p : ∀ᵐ p ∂(volume : Measure (Config j d)),
      MemH1 (haar d) (fun x => Real.sqrt (condDens hj (Qreg V W n f) p x)) := by
    filter_upwards [ae_isWeakGrad_condDens hyp hac hN hfm hf hw hgm hg2 hgi n hj,
      ae_memLp_gradMarg hyp hac hN hfm hf hw hgm hg2 hgi n hj] with p hp hp2
    exact memH1_sqrt_of_ge ((measurable_condDens hj hQm).of_uncurry_left)
      hp (fun k => memLp_div_const (hp2 k) _) (div_pos hc hC)
      (fun x => (condDens_bounds hj hQm hc hQc hQC p x).1)
      (fun x => (condDens_bounds hj hQm hc hQc hQC p x).2)
  have hH1 : ∀ᵐ X ∂ν, MemH1 (haar d)
      (fun x => Real.sqrt (condDens hj (Qreg V W n f) (past j hj.le X) x)) := by
    have h1 : ∀ᵐ p ∂(ν.map (past j hj.le)),
        MemH1 (haar d) (fun x => Real.sqrt (condDens hj (Qreg V W n f) p x)) := by
      rw [hmap]; exact withDensity_absolutelyContinuous _ _ |>.ae_le hH1p
    exact ae_of_ae_map (measurable_past hj.le).aemeasurable h1
  calc ∫⁻ X, ENNReal.ofReal (2 * r₀ * (gap V W (condNext ν j hj (past j hj.le X))).toReal) ∂ν
      ≤ ∫⁻ X, dissipation V W (condDens hj (Qreg V W n f) (past j hj.le X)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hcn, hH1] with X h1 h2
        rw [h1]
        exact ofReal_two_r_gap_le hr₀ hrr
          (fun x => (div_pos hc hC).le.trans (condDens_bounds hj hQm hc hQc hQC _ x).1)
          (integral_condDens hj hQm hc hQc hQC _) h2
    _ = _ := lintegral_dissipation_eq_S hyp hac hN hfm hf hw hgm hg2 hgi n hj
    _ ≤ _ := lintegral_scoreS_le hyp hac hN hfm hf hw hgm hg2 hgi n hj hε
    _ = _ := by rw [lintegral_force_eq_fcTerm hyp hμ hN hfm hf hw hgm hg2 hgi n hj]

end gapj

end SharpLSI
