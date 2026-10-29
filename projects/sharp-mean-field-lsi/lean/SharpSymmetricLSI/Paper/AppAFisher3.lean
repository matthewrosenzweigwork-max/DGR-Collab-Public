import SharpSymmetricLSI.Paper.AppAFisher2

/-!
# Appendix A, (A.1): the statement on `𝕋^d`
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

section General

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem continuous_of_comp_liftT {f : UnitAddTorus ι → ℝ} (h : Continuous (f ∘ liftT)) :
    Continuous f := by
  have hq : Topology.IsQuotientMap (liftT (ι := ι)) :=
    IsOpenQuotientMap.isQuotientMap
      (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  exact hq.continuous_iff.2 h

theorem heatT_sum {t : ℝ} (ht : 0 < t) {κ : Type*} (s : Finset κ)
    {f : κ → UnitAddTorus ι → ℝ} (hf : ∀ k ∈ s, Integrable (f k)) (z : UnitAddTorus ι) :
    heatT t (fun y => ∑ k ∈ s, f k y) z = ∑ k ∈ s, heatT t (f k) z := by
  rw [heatT_eq ht (Finset.aestronglyMeasurable_fun_sum _ fun k hk => (hf k hk).aestronglyMeasurable)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun k hk => ?_]
  · exact Finset.sum_congr rfl fun k hk => (heatT_eq ht (hf k hk).aestronglyMeasurable z).symm
  · obtain ⟨M, hM⟩ := heatP_bdd (ι := ι) ht
    refine ((hf k hk).comp_sub_left z).bdd_mul (c := M)
      (measurable_heatP ht).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs]; exact hM w

end General

variable {d : ℕ}

/-- **(A.1).** -/
theorem heat_fisher_aux {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hρ : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) {t : ℝ} (ht : 0 < t) :
    (∀ᵐ x ∂haar d, sqNorm (weakGrad (heatT t ρ) x) / heatT t ρ x ≤
      4 * heatT t (fun y => sqNorm (weakGrad (fun z => Real.sqrt (ρ z)) y)) x) ∧
    fisherInfo (densMeasure (heatT t ρ)) (haar d) ≤ fisherInfo (densMeasure ρ) (haar d) := by
  set s : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hsdef
  obtain ⟨hw, hs2, hgn⟩ := hρ
  set g := weakGrad s with hgdef
  have hsg : IsWeakGrad s g := appA_isWeakGrad_weakGrad hw
  have hgk : ∀ k, MemLp (fun y => g y k) 2 volume := fun k => by
    refine hgn.mono (appA_aestronglyMeasurable_grad hsg k) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.abs_le_sqrt ?_
    unfold sqNorm
    exact Finset.single_le_sum (f := fun j => g y j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ k)
  have hρs : (fun y => s y ^ 2) = ρ := funext fun y => Real.sq_sqrt (hρ0 y)
  have hρg : IsWeakGrad ρ (fun y k => 2 * s y * g y k) := by
    have := isWeakGrad_sq hsg hs2 hgk
    rwa [hρs] at this
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ1]; exact one_ne_zero)
  have hgi : ∀ k, Integrable fun y => 2 * s y * g y k := fun k =>
    ((hs2.integrable_mul (hgk k)).const_mul 2).congr (Eventually.of_forall fun y => by
      simp only [Pi.mul_apply]; ring)
  have hg2 : ∀ k, Integrable fun y => g y k ^ 2 := fun k => (hgk k).integrable_sq
  have hsq : Integrable fun y => sqNorm (g y) := by
    unfold sqNorm; exact integrable_finsetSum _ fun k _ => hg2 k
  set H := heatT t ρ with hHdef
  have hH := isWeakGrad_heatT ht hρg hρi hgi
  have hHae := appA_weakGrad_ae_eq hH
  obtain ⟨c, hc, hlow⟩ := heatT_lower (ι := Fin d) ht
  have hHpos : ∀ z, 0 < H z := fun z => by
    have := hlow ρ hρi (Eventually.of_forall hρ0) z
    rw [show ∫ y, ρ y = 1 from hρ1, mul_one] at this
    exact lt_of_lt_of_le hc this
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ z, sqNorm (fun k => heatT t (fun y => 2 * s y * g y k) z) ≤
      4 * H z * heatT t (fun y => sqNorm (g y)) z := by
    intro z
    have hA : 0 < heatT t (fun y => s y ^ 2) z := by rw [hρs]; exact hHpos z
    unfold sqNorm
    rw [heatT_sum ht _ fun k _ => hg2 k, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := heatT_sq_le ht hs2 (hgk k) z hA
    rwa [hρs] at this
  have part1 : ∀ᵐ x ∂haar d, sqNorm (weakGrad H x) / H x ≤
      4 * heatT t (fun y => sqNorm (g y)) x := by
    filter_upwards [hHae] with x hx
    rw [hx, div_le_iff₀ (hHpos x)]
    linarith [hpt x]
  refine ⟨part1, ?_⟩
  -- Fisher information of the flow
  have hHs : IsSmoothT H := isSmoothT_heatT ht hρi
  have hHc : Continuous H := continuous_of_comp_liftT hHs.continuous
  set sH : Torus d → ℝ := fun x => Real.sqrt (H x) with hsHdef
  have hsHs : ContDiff ℝ ∞ (sH ∘ liftT) :=
    hHs.sqrt fun x => (hHpos _).ne'
  have hsHw := isWeakGrad_of_contDiff (hsHs.of_le (by simp))
  set gsH := fun (y : Torus d) (k : Fin d) => fderiv ℝ (sH ∘ liftT) (secT y) (Pi.single k 1)
  have hgsH : ∀ y k, gsH y k = fderiv ℝ (H ∘ liftT) (secT y) (Pi.single k 1) / (2 * sH y) := by
    intro y k
    have hd := ((hHs.differentiable (by simp)) (secT y)).hasFDerivAt.sqrt
      (hHpos (liftT (secT y))).ne'
    simp only [gsH]
    rw [show (sH ∘ liftT) = fun x => Real.sqrt ((H ∘ liftT) x) from rfl, hd.fderiv]
    simp only [smul_apply, smul_eq_mul, Function.comp, liftT_secT, sH]
    field_simp
  have hclass := weakGrad_ae_eq_of_contDiff (hHs.of_le (by simp) : ContDiff ℝ 1 (H ∘ liftT))
  have hbound : ∀ᵐ y ∂haar d, sqNorm (gsH y) ≤ heatT t (fun y => sqNorm (g y)) y := by
    filter_upwards [part1, hclass] with y h1 h2
    have e : sqNorm (gsH y) = sqNorm (weakGrad H y) / (4 * H y) := by
      unfold sqNorm
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hgsH, h2]
      have : sH y ^ 2 = H y := Real.sq_sqrt (hHpos y).le
      rw [div_pow, mul_pow, this]; ring
    have hy := hHpos y
    rw [e, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hy] at h1
    linarith
  -- the two square-root densities
  have hrnH : ∀ᵐ x ∂haar d,
      Real.sqrt ((densMeasure H).rnDeriv (haar d) x).toReal = sH x := by
    filter_upwards [Measure.rnDeriv_withDensity (haar d) (hHc.measurable.ennreal_ofReal)]
      with x hx
    rw [densMeasure, hx, ENNReal.toReal_ofReal (hHpos x).le]
  have hHint : Integrable (heatT t fun y => sqNorm (g y)) := integrable_heatT ht hsq
  have hsHc : Continuous sH := hHc.sqrt
  have hsHg := appA_weakGrad_ae_eq hsHw
  have hsqH : Integrable fun y => sqNorm (weakGrad sH y) := by
    refine hHint.mono' (appA_isWeakGrad_weakGrad ⟨_, hsHw⟩ |> fun h => by
      unfold sqNorm
      exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (appA_aestronglyMeasurable_grad h k).pow 2) ?_
    filter_upwards [hsHg, hbound] with y h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold sqNorm; positivity), h1]
    exact h2
  have hsHmem : MemH1 (haar d) sH := by
    refine ⟨⟨_, hsHw⟩, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hsHc.continuousOn
      exact MemLp.of_bound hsHc.aestronglyMeasurable C
        (Eventually.of_forall fun x => hC x (mem_univ x))
    · have hm : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad sH x))) volume :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hsqH.aestronglyMeasurable
      rw [memLp_two_iff_integrable_sq hm]
      refine hsqH.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [Real.sq_sqrt (by unfold sqNorm; positivity)]
  -- the left side
  set rt : Torus d → ℝ := fun x => Real.sqrt ((densMeasure H).rnDeriv (haar d) x).toReal
  have hrt : MemH1 (haar d) rt := by
    obtain ⟨hw', hm2, hg2'⟩ := hsHmem
    have hrw : IsWeakGrad rt (weakGrad sH) :=
      appA_isWeakGrad_congr_ae (appA_isWeakGrad_weakGrad hw') (hrnH.mono fun x hx => hx.symm)
    refine ⟨⟨_, hrw⟩, hm2.ae_eq (hrnH.mono fun x hx => hx.symm), ?_⟩
    refine hg2'.ae_eq ?_
    filter_upwards [appA_weakGrad_ae_eq hrw] with x hx
    rw [hx]
  have hLHS : fisherInfo (densMeasure H) (haar d) ≤
      4 * ∫⁻ y, ENNReal.ofReal (sqNorm (g y)) ∂haar d := by
    have hc : densMeasure H ≪ haar d ∧ MemH1 (haar d) rt :=
      ⟨withDensity_absolutelyContinuous _ _, hrt⟩
    rw [fisherInfo, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    gcongr
    unfold dirichlet
    have hrw : IsWeakGrad rt gsH :=
      appA_isWeakGrad_congr_ae hsHw (hrnH.mono fun x hx => hx.symm)
    calc ∫⁻ x, ENNReal.ofReal (sqNorm (weakGrad rt x)) ∂haar d
        = ∫⁻ x, ENNReal.ofReal (sqNorm (gsH x)) ∂haar d := by
          refine lintegral_congr_ae ?_
          filter_upwards [appA_weakGrad_ae_eq hrw] with x hx
          rw [hx]
      _ ≤ ∫⁻ x, ENNReal.ofReal (heatT t (fun y => sqNorm (g y)) x) ∂haar d := by
          refine lintegral_mono_ae ?_
          filter_upwards [hbound] with x hx
          exact ENNReal.ofReal_le_ofReal hx
      _ = ENNReal.ofReal (∫ x, heatT t (fun y => sqNorm (g y)) x) := by
          rw [ofReal_integral_eq_lintegral_ofReal hHint (Eventually.of_forall fun x => by
            rw [heatT_eq ht hsq.aestronglyMeasurable]
            exact integral_nonneg fun w =>
              mul_nonneg (heatP_pos ht w).le (by unfold sqNorm; positivity))]
      _ = ENNReal.ofReal (∫ x, sqNorm (g x)) := by rw [integral_heatT ht hsq]
      _ = ∫⁻ y, ENNReal.ofReal (sqNorm (g y)) ∂haar d :=
          ofReal_integral_eq_lintegral_ofReal hsq
            (Eventually.of_forall fun x => by unfold sqNorm; positivity)
  -- the right side
  refine hLHS.trans ?_
  unfold fisherInfo
  split_ifs with hcond
  · gcongr
    unfold dirichlet
    set r0 : Torus d → ℝ := fun x => Real.sqrt ((densMeasure ρ).rnDeriv (haar d) x).toReal
    have hr0 : r0 =ᵐ[haar d] s := by
      filter_upwards [Measure.rnDeriv_withDensity₀ (haar d)
        hρi.aemeasurable.ennreal_ofReal] with x hx
      simp only [r0, s]
      rw [densMeasure, hx, ENNReal.toReal_ofReal (hρ0 x)]
    have hrw : IsWeakGrad r0 g := appA_isWeakGrad_congr_ae hsg (hr0.mono fun x hx => hx.symm)
    refine le_of_eq (lintegral_congr_ae ?_)
    filter_upwards [appA_weakGrad_ae_eq hrw] with x hx
    rw [hx]
  · exact le_top

end SharpLSI
