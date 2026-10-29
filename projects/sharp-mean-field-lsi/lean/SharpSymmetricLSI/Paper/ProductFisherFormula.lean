import SharpSymmetricLSI.Paper.ProductFisherId

/-!
# (2.11): the Fisher-information identity (Phase 3, lane D; R6)
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

theorem integrable_bdd' {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    {f : α → ℝ} (hf : AEStronglyMeasurable f m) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f m :=
  Integrable.of_bound hf C (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- The per-component value `F_k` of the Fisher information per particle. -/
noncomputable def fisherComp (μ : Measure (Torus d)) (a : Torus d → ℝ) (B : Torus d → Torus d → ℝ)
    (N : ℕ) : ℝ :=
  ∫ x, a x ^ 2 ∂μ + 2 * (1 / (N : ℝ)) * ((N : ℝ) - 1) * ∫ x, a x * ∫ y, B x y ∂μ ∂μ +
    (1 / (N : ℝ)) ^ 2 * ((N : ℝ) - 1) * ∫ x, ∫ y, B x y ^ 2 ∂μ ∂μ +
    (1 / (N : ℝ)) ^ 2 * (((N : ℝ) - 1) * ((N : ℝ) - 2)) * ∫ x, (∫ y, B x y ∂μ) ^ 2 ∂μ

/-- Step A: `I(ν_N|P_N)/N = ∑ₖ F_k`. -/
theorem fisher_div_eq_sum (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) (hN : 1 ≤ N) :
    (fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)).toReal / N =
      ∑ k, fisherComp (densMeasure ρ) (fun x => aGrad V ρ x k) (fun x y => bGrad W x y k) N := by
  haveI := isProbabilityMeasure_densMeasure' (fun x => (hpos x).le) h1
  set ν := Measure.pi fun _ : Fin N => densMeasure ρ with hν
  obtain ⟨-, -, hF⟩ := fisher_productState (N := N) hyp hs hpos h1
  obtain ⟨Ca, hCa⟩ := aGrad_bdd hyp hs hpos
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i k, ∫ X, gPhi V W ρ N (flat X) (i, k) ^ 2 ∂ν =
      fisherComp (densMeasure ρ) (fun x => aGrad V ρ x k) (fun x y => bGrad W x y k) N := by
    intro i k
    simp_rw [gPhi_flat hyp hN]
    exact expect_sq hN i (measurable_aGrad hyp hs hpos k) (measurable_bGrad hyp k)
      (fun x => hCa x k) (fun x y => hCb x y k) (1 / (N : ℝ))
  have hmeas : ∀ p, AEStronglyMeasurable (fun X : Config N d => gPhi V W ρ N (flat X) p ^ 2) ν := by
    intro p
    obtain ⟨i, k⟩ := p
    simp_rw [gPhi_flat hyp hN]
    refine (Measurable.pow_const ?_ 2).aestronglyMeasurable
    refine ((measurable_aGrad hyp hs hpos k).comp (measurable_pi_apply i)).add
      (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_))
    have := (measurable_bGrad hyp (W := W) k).comp
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j) :
        Measurable fun X : Config N d => (X i, X j))
    exact this
  obtain ⟨Cg, hCg⟩ := gPhi_bdd (N := N) hyp hs hpos
  have hint : ∀ p, Integrable (fun X : Config N d => gPhi V W ρ N (flat X) p ^ 2) ν := fun p =>
    integrable_bdd' (hmeas p) (C := Cg ^ 2) fun X => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg _ p) 2
  rw [hF, ENNReal.toReal_ofReal (integral_nonneg fun X => sqNorm_nonneg _)]
  unfold sqNorm
  rw [integral_finsetSum _ fun p _ => hint p, Fintype.sum_prod_type]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The generic expansion behind step B. -/
theorem rhs_generic {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : Torus d → Fin d → ℝ}
    {B : Torus d → Torus d → Fin d → ℝ} (ham : ∀ k, Measurable fun x => a x k)
    (hBm : ∀ k, Measurable (Function.uncurry fun x y => B x y k)) {Ca Cb : ℝ}
    (hCa : ∀ x k, |a x k| ≤ Ca) (hCb : ∀ x y k, |B x y k| ≤ Cb) (q r : ℝ) :
    (∫ x, ∑ k, (a x k + q * ∫ y, B x y k ∂μ) ^ 2 ∂μ) +
      r * ∫ x, ((∫ y, ∑ k, B x y k ^ 2 ∂μ) - ∑ k, (∫ y, B x y k ∂μ) ^ 2) ∂μ =
    ∑ k, ((∫ x, a x k ^ 2 ∂μ) + 2 * q * (∫ x, a x k * ∫ y, B x y k ∂μ ∂μ) +
      q ^ 2 * (∫ x, (∫ y, B x y k ∂μ) ^ 2 ∂μ) +
      r * ((∫ x, ∫ y, B x y k ^ 2 ∂μ ∂μ) - ∫ x, (∫ y, B x y k ∂μ) ^ 2 ∂μ)) := by
  have hbm : ∀ k, AEStronglyMeasurable (fun x => ∫ y, B x y k ∂μ) μ := fun k =>
    ((hBm k).stronglyMeasurable.integral_prod_right (ν := μ)).aestronglyMeasurable
  have hbb : ∀ x k, |∫ y, B x y k ∂μ| ≤ Cb := fun x k => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |B x y k| ∂μ ≤ ∫ _, Cb ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const Cb)
          (Eventually.of_forall fun y => hCb x y k)
      _ = Cb := by simp
  have hsq : ∀ {u : ℝ} {C : ℝ}, |u| ≤ C → |u ^ 2| ≤ C ^ 2 := fun h => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hB2m : ∀ k, AEStronglyMeasurable (fun x => ∫ y, B x y k ^ 2 ∂μ) μ := fun k =>
    (((hBm k).pow_const 2).stronglyMeasurable.integral_prod_right (ν := μ)
      (f := fun x y => B x y k ^ 2)).aestronglyMeasurable
  have hB2b : ∀ x k, |∫ y, B x y k ^ 2 ∂μ| ≤ Cb ^ 2 := fun x k => by
    rw [abs_of_nonneg (integral_nonneg fun y => sq_nonneg _)]
    calc ∫ y, B x y k ^ 2 ∂μ ≤ ∫ _, Cb ^ 2 ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun _ => sq_nonneg _) (integrable_const _)
          (Eventually.of_forall fun y => (le_abs_self _).trans (hsq (hCb x y k)))
      _ = Cb ^ 2 := by simp
  have ia2 : ∀ k, Integrable (fun x => a x k ^ 2) μ := fun k =>
    integrable_bdd' ((ham k).pow_const 2).aestronglyMeasurable fun x => hsq (hCa x k)
  have iab : ∀ k, Integrable (fun x => a x k * ∫ y, B x y k ∂μ) μ := fun k =>
    integrable_bdd' ((ham k).aestronglyMeasurable.mul (hbm k)) (C := Ca * Cb) fun x => by
      rw [abs_mul]; exact mul_le_mul (hCa x k) (hbb x k) (abs_nonneg _)
        ((abs_nonneg _).trans (hCa x k))
  have ib2 : ∀ k, Integrable (fun x => (∫ y, B x y k ∂μ) ^ 2) μ := fun k =>
    integrable_bdd' ((hbm k).pow 2) fun x => hsq (hbb x k)
  have iB2 : ∀ k, Integrable (fun x => ∫ y, B x y k ^ 2 ∂μ) μ := fun k =>
    integrable_bdd' (hB2m k) (hB2b · k)
  have iB2y : ∀ x k, Integrable (fun y => B x y k ^ 2) μ := fun x k =>
    integrable_bdd' (((hBm k).comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
      fun y => hsq (hCb x y k)
  have hexp : ∀ k, ∫ x, (a x k + q * ∫ y, B x y k ∂μ) ^ 2 ∂μ =
      (∫ x, a x k ^ 2 ∂μ) + 2 * q * (∫ x, a x k * ∫ y, B x y k ∂μ ∂μ) +
        q ^ 2 * (∫ x, (∫ y, B x y k ∂μ) ^ 2 ∂μ) := fun k => by
    have e : (fun x => (a x k + q * ∫ y, B x y k ∂μ) ^ 2) = fun x => a x k ^ 2 +
        2 * q * (a x k * ∫ y, B x y k ∂μ) + q ^ 2 * (∫ y, B x y k ∂μ) ^ 2 := by
      funext x; ring
    rw [e, integral_add (f := fun x => a x k ^ 2 + 2 * q * (a x k * ∫ y, B x y k ∂μ))
      (g := fun x => q ^ 2 * (∫ y, B x y k ∂μ) ^ 2)
      ((ia2 k).add ((iab k).const_mul _)) ((ib2 k).const_mul _),
      integral_add (f := fun x => a x k ^ 2) (g := fun x => 2 * q * (a x k * ∫ y, B x y k ∂μ))
      (ia2 k) ((iab k).const_mul _), integral_const_mul, integral_const_mul]
  have hi1 : ∀ k, Integrable (fun x => (a x k + q * ∫ y, B x y k ∂μ) ^ 2) μ := fun k => by
    have e : (fun x => (a x k + q * ∫ y, B x y k ∂μ) ^ 2) = fun x => a x k ^ 2 +
        2 * q * (a x k * ∫ y, B x y k ∂μ) + q ^ 2 * (∫ y, B x y k ∂μ) ^ 2 := by
      funext x; ring
    rw [e]; exact ((ia2 k).add ((iab k).const_mul _)).add ((ib2 k).const_mul _)
  have hin : ∀ x, ∫ y, ∑ k, B x y k ^ 2 ∂μ = ∑ k, ∫ y, B x y k ^ 2 ∂μ := fun x =>
    integral_finsetSum _ fun k _ => iB2y x k
  simp_rw [hin]
  rw [integral_finsetSum _ fun k _ => hi1 k,
    integral_sub (integrable_finsetSum _ fun k _ => iB2 k) (integrable_finsetSum _ fun k _ => ib2 k),
    integral_finsetSum _ fun k _ => iB2 k, integral_finsetSum _ fun k _ => ib2 k,
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [hexp k]

/-- Step B: the right-hand side of (2.11) equals `∑ₖ F_k`. -/
theorem rhs_eq_sum (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) (hN : 1 ≤ N) :
    (∫ x, sqNorm (fun k => weakGrad (fun y => Real.log (ρ y)) x k + weakGrad V x k +
        ((N : ℝ) - 1) / N * fDens W ρ x k) ∂densMeasure ρ) +
      ((N : ℝ) - 1) / (N : ℝ) ^ 2 *
        ∫ x, ((∫ y, sqNorm (g1W W x y) ∂densMeasure ρ) - sqNorm (fDens W ρ x)) ∂densMeasure ρ =
      ∑ k, fisherComp (densMeasure ρ) (fun x => aGrad V ρ x k) (fun x y => bGrad W x y k) N := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  haveI := isProbabilityMeasure_densMeasure' hρ0 h1
  have μac : densMeasure ρ ≪ haar d := withDensity_absolutelyContinuous _ _
  obtain ⟨Ca, hCa⟩ := aGrad_bdd hyp hs hpos
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hN0 : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                               exact this.ne'
  have hgg := Measure.ae_ae_of_ae_prod (ae_g1W hyp (W := W))
  have hb_eq : ∀ᵐ x ∂densMeasure ρ, ∀ k,
      fDens W ρ x k = ∫ y, bGrad W x y k ∂densMeasure ρ := by
    refine μac.ae_le ?_
    filter_upwards [hgg] with x hx k
    simp only [fDens]
    rw [integral_densMeasure' hρ0 h1]
    refine integral_congr_ae ?_
    filter_upwards [hx] with y hy
    rw [hy k, mul_comm]
  have hg_eq : ∀ᵐ x ∂densMeasure ρ, ∫ y, sqNorm (g1W W x y) ∂densMeasure ρ =
      ∫ y, ∑ k, bGrad W x y k ^ 2 ∂densMeasure ρ := by
    refine μac.ae_le ?_
    filter_upwards [hgg] with x hx
    refine integral_congr_ae (μac.ae_le ?_)
    filter_upwards [hx] with y hy
    simp only [sqNorm]
    exact Finset.sum_congr rfl fun k _ => by rw [hy k]
  have ha_eq : ∀ᵐ x ∂densMeasure ρ, ∀ k,
      weakGrad (fun y => Real.log (ρ y)) x k + weakGrad V x k = aGrad V ρ x k := by
    refine μac.ae_le ?_
    filter_upwards [ae_weakGrad_log hs hpos, ae_weakGrad_V hyp (W := W)] with x h1x h2x k
    rw [h1x, h2x, aGrad, add_comm]
  have e1 : ∫ x, sqNorm (fun k => weakGrad (fun y => Real.log (ρ y)) x k + weakGrad V x k +
      ((N : ℝ) - 1) / N * fDens W ρ x k) ∂densMeasure ρ =
      ∫ x, ∑ k, (aGrad V ρ x k + ((N : ℝ) - 1) / N * ∫ y, bGrad W x y k ∂densMeasure ρ) ^ 2
        ∂densMeasure ρ := by
    refine integral_congr_ae ?_
    filter_upwards [ha_eq, hb_eq] with x hx1 hx2
    simp only [sqNorm]
    exact Finset.sum_congr rfl fun k _ => by rw [hx1 k, hx2 k]
  have e2 : ∫ x, ((∫ y, sqNorm (g1W W x y) ∂densMeasure ρ) - sqNorm (fDens W ρ x)) ∂densMeasure ρ =
      ∫ x, ((∫ y, ∑ k, bGrad W x y k ^ 2 ∂densMeasure ρ) -
        ∑ k, (∫ y, bGrad W x y k ∂densMeasure ρ) ^ 2) ∂densMeasure ρ := by
    refine integral_congr_ae ?_
    filter_upwards [hg_eq, hb_eq] with x hx1 hx2
    rw [hx1]
    simp only [sqNorm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hx2 k]
  rw [e1, e2, rhs_generic (fun k => measurable_aGrad hyp hs hpos k)
    (fun k => measurable_bGrad hyp k) hCa hCb]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [fisherComp]
  field_simp
  ring

end SharpLSI
