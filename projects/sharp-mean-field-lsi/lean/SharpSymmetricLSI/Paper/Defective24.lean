import SharpSymmetricLSI.Paper.Defective23

/-!
# R03 (Proposition 2.2), part 24: the entropy increments are bounded by the relative scores

`h_j ≤ A E_ν |s_j - G_j|²` (`hCond_le_sG`), from the reference LSI on each `ρ_j`
(`exists_klDiv_le_reference`), the conditional score identity, and conditional Jensen.
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}


section hbound
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)
include hyp hμ hN hfm hf hw hgm hg2 hgi

/-- **`h_j ≤ A E_ν |s_j - G_j|²`**, given the reference LSI with constant `A`. -/
theorem hCond_le_sG {A : ℝ}
    (hA : ∀ {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ}, Measurable ρ → IsWeakGrad ρ g →
      (∀ k, Measurable fun x => g x k) → (∀ k, MemLp (fun x => g x k) 2 (haar d)) →
      ∀ {c C : ℝ}, 0 < c → (∀ x, c ≤ ρ x) → (∀ x, ρ x ≤ C) → ∫ x, ρ x ∂haar d = 1 →
      klDiv (densMeasure ρ) (μ : Measure (Torus d)) ≤ ENNReal.ofReal A *
        ∫⁻ x, ENNReal.ofReal (ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF V W μ) x k) ^ 2) ∂haar d) :
    haveI := isProbabilityMeasure_Qreg hyp hf hfm n
    hCond ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
        (μ : Measure (Torus d)) j hj ≤
      ENNReal.ofReal A * ∫⁻ X, ENNReal.ofReal
        (∑ k, (sfun n f g ⟨j, hj⟩ k X - Gfun W μ ⟨j, hj⟩ k X) ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) := by
  haveI := isProbabilityMeasure_Qreg hyp hf hfm n
  have hac := minimizer_ac hyp hμ
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  have hC : 0 < C := hc.trans_le ((hb (Classical.arbitrary _)).1.trans (hb _).2)
  set Q := Qreg V W n f with hQdef
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X) with hνdef
  have hsm : ∀ k, Measurable (sfun n f g ⟨j, hj⟩ k) := fun k =>
    measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n _ k
  have hGm : ∀ k, Measurable (Gfun W (μ : Measure (Torus d)) ⟨j, hj⟩ k) := fun k =>
    measurable_Gfun hyp hac hN _ k
  set D : Fin d → Config N d → ℝ := fun k X => sfun n f g ⟨j, hj⟩ k X - Gfun W μ ⟨j, hj⟩ k X
    with hDdef
  have hDm : ∀ k, Measurable (D k) := fun k => (hsm k).sub (hGm k)
  set R : Config j d → Torus d → ℝ := fun p x => ∑ k, condRatio hj Q (D k) p x ^ 2 with hRdef
  have hcr : ∀ k, Measurable fun q : Config j d × Torus d => condRatio hj Q (D k) q.1 q.2 := fun k => by
    have h := measurable_condRatio hj hQm (hDm k)
    unfold Function.uncurry at h
    exact h
  have hRm : Measurable (Function.uncurry R) := by
    unfold Function.uncurry
    exact Finset.measurable_sum _ fun k _ => (hcr k).pow_const 2
  have hR0 : ∀ p x, 0 ≤ R p x := fun p x => Finset.sum_nonneg fun k _ => sq_nonneg _
  -- linearity of the conditional ratio, a.e. in `(p, x)`
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_gsG hyp hac (μ := (μ : Measure (Torus d))) (N := N)
  have hslice : ∀ k, ∀ᵐ q ∂((volume : Measure (Config j d)).prod (volume : Measure (Torus d))),
      Integrable (fun z => sfun n f g ⟨j, hj⟩ k (assemble hj q.1 q.2 z) * Q (assemble hj q.1 q.2 z))
        (volume : Measure (Config (N - j - 1) d)) := fun k =>
    ((measurePreserving_assemble (d := d) hj).integrable_comp_of_integrable
      (integrable_sfun_mul_Q hyp hac hN hfm hf hw hgm hg2 hgi n ⟨j, hj⟩ k)).prod_right_ae
  have hlin : ∀ᵐ q ∂((volume : Measure (Config j d)).prod (volume : Measure (Torus d))), ∀ k,
      gradMarg hj (GQreg V W μ n f g) q.1 q.2 k / margQ hj Q q.1 q.2 +
        lipGrad (PhiMF V W μ) q.2 k = condRatio hj Q (D k) q.1 q.2 := by
    filter_upwards [ae_all_iff.mpr fun k => ae_gradMarg_div_eq hyp hac hN hfm hf hw hgm hg2 hgi n hj k,
      ae_all_iff.mpr hslice] with q h1 h2 k
    rw [h1 k]
    have hzm : Measurable fun z : Config (N - j - 1) d => assemble hj q.1 q.2 z :=
      (measurable_assemble hj).comp ((measurable_const (a := q)).prodMk measurable_id)
    have hQi : Integrable (fun z => Q (assemble hj q.1 q.2 z)) (volume : Measure (Config (N - j - 1) d)) :=
      Integrable.of_bound (hQm.comp hzm).aestronglyMeasurable C (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb _).1)]; exact (hb _).2)
    have hGi : Integrable (fun z => Gfun W μ ⟨j, hj⟩ k (assemble hj q.1 q.2 z) *
        Q (assemble hj q.1 q.2 z)) (volume : Measure (Config (N - j - 1) d)) :=
      hQi.bdd_mul ((hGm k).comp hzm).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hCG _ _)
    unfold condRatio
    rw [sub_add_cancel, ← sub_div, ← integral_sub (h2 k) hGi]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    try simp only [hDdef]
    ring
  -- the reference LSI on a.e. slice
  have hp : ∀ᵐ p ∂(volume : Measure (Config j d)),
      klDiv (densMeasure (condDens hj Q p)) (μ : Measure (Torus d)) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (condDens hj Q p x * R p x) ∂haar d := by
    filter_upwards [ae_isWeakGrad_condDens hyp hac hN hfm hf hw hgm hg2 hgi n hj,
      ae_memLp_gradMarg hyp hac hN hfm hf hw hgm hg2 hgi n hj,
      Measure.ae_ae_of_ae_prod hlin] with p hpw hpm hpl
    refine (hA ((measurable_condDens hj hQm).of_uncurry_left) hpw
      (fun k => ((measurable_gradMarg hyp hac hN hfm hf hw hgm hg2 hgi n hj k).of_uncurry_left).div_const _)
      (fun k => memLp_div_const (hpm k) _) (div_pos hc hC)
      (fun x => (condDens_bounds hj hQm hc hQc hQC p x).1)
      (fun x => (condDens_bounds hj hQm hc hQc hQC p x).2)
      (integral_condDens hj hQm hc hQc hQC p)).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hpl] with x hx
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    have hZ0 : 0 < Zc hj Q p := hc.trans_le (Zc_bounds hj hQm hQc hQC p).1
    have hm0 : 0 < margQ hj Q p x := hc.trans_le (margQ_bounds hj hQm hQc hQC p x).1
    rw [← hx k]
    congr 2
    have h1 : Zc hj (Qreg V W n f) p ≠ 0 := hZ0.ne'
    have h2 : margQ hj (Qreg V W n f) p x ≠ 0 := hm0.ne'
    unfold condDens
    simp only [hQdef]
    field_simp
  have hmap := map_past_eq hj hQm hc hQc hQC
  have hpX : ∀ᵐ X ∂ν, klDiv (densMeasure (condDens hj Q (past j hj.le X))) (μ : Measure (Torus d)) ≤
      ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (condDens hj Q (past j hj.le X) x *
        R (past j hj.le X) x) ∂haar d := by
    have h1 : ∀ᵐ p ∂(ν.map (past j hj.le)), klDiv (densMeasure (condDens hj Q p)) (μ : Measure (Torus d)) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (condDens hj Q p x * R p x) ∂haar d := by
      rw [hmap]; exact withDensity_absolutelyContinuous _ _ |>.ae_le hp
    exact ae_of_ae_map (measurable_past hj.le).aemeasurable h1
  have hcn : ∀ᵐ X ∂ν, condNext ν j hj (past j hj.le X) = densMeasure (condDens hj Q (past j hj.le X)) :=
    ae_of_ae_map (measurable_past hj.le).aemeasurable (condNext_ae_eq hj hQm hc hQc hQC)
  calc hCond ν (μ : Measure (Torus d)) j hj
      = ∫⁻ X, klDiv (condNext ν j hj (past j hj.le X)) (μ : Measure (Torus d)) ∂ν := rfl
    _ ≤ ∫⁻ X, ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (condDens hj Q (past j hj.le X) x *
          R (past j hj.le X) x) ∂haar d ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hcn, hpX] with X h1 h2
        rw [h1]; exact h2
    _ = ENNReal.ofReal A * ∫⁻ X, ENNReal.ofReal (R (past j hj.le X) (X ⟨j, hj⟩)) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_condDens_mul_past hj hQm hc hQc hQC hRm hR0]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl ?_
        have hpc : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
          (measurable_past hj.le).prodMk (measurable_pi_apply _)
        have e1 : ∀ X : Config N d, ENNReal.ofReal (R (past j hj.le X) (X ⟨j, hj⟩)) =
            ∑ k, ENNReal.ofReal (condRatio hj Q (D k) (past j hj.le X) (X ⟨j, hj⟩) ^ 2) := fun X =>
          ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _
        have e2 : ∀ X : Config N d, ENNReal.ofReal (∑ k, (sfun n f g ⟨j, hj⟩ k X -
            Gfun W μ ⟨j, hj⟩ k X) ^ 2) = ∑ k, ENNReal.ofReal (D k X ^ 2) := fun X =>
          ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _
        rw [lintegral_congr e1, lintegral_congr e2,
          lintegral_finset_sum _ fun k _ =>
            ((measurable_pastCur_comp hj (measurable_condRatio hj hQm (hDm k))).pow_const 2).ennreal_ofReal,
          lintegral_finset_sum _ fun k _ => ((hDm k).pow_const 2).ennreal_ofReal]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [lintegral_withDensity_eq_lintegral_mul _ ((hQm).ennreal_ofReal)
            (((measurable_pastCur_comp hj (measurable_condRatio hj hQm (hDm k))).pow_const 2).ennreal_ofReal),
          lintegral_withDensity_eq_lintegral_mul _ ((hQm).ennreal_ofReal)
            (((hDm k).pow_const 2).ennreal_ofReal)]
        simp only [Pi.mul_apply]
        simp_rw [mul_comm (ENNReal.ofReal (Q _))]
        exact lintegral_condRatio_sq_le hj hQm hc hQc hQC (hDm k)

end hbound

end SharpLSI
