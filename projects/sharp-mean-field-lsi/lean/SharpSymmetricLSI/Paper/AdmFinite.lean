import SharpSymmetricLSI.Paper.DensMeasure
import SharpSymmetricLSI.Paper.EntFinite
import SharpSymmetricLSI.Paper.SemiconvexHyp
import SharpSymmetricLSI.Paper.TorusLipschitz
import SharpSymmetricLSI.Infra.SobolevTorus

/-!
# Finite gap and dissipation of admissible densities (D7 sanity lemma)

For `ρ ≥ 0`, `∫ρ = 1`, `√ρ ∈ H¹(m)`:
* `H(ρ|m) < ∞` (torus Sobolev inequality: `ρ ∈ L^p` for some `p > 1`);
* `F_* > -∞` since `V`, `W` are bounded, so `G(ρ) < ∞`;
* `V + W*ρ` is Lipschitz (semiconvexity), so `D(ρ) ≤ 8∫|∇√ρ|² + 2C²∫ρ < ∞`.
This file imports nothing above `D06`, so that `D07` can use it.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `F ≥ -C` on probability measures. -/
theorem freeEnergy_ge (hyp : Hyp V W KV KW) :
    ∃ C : ℝ, ∀ ρ : ProbabilityMeasure (Torus d), ((-C : ℝ) : EReal) ≤ freeEnergy V W ρ := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  refine ⟨BV + BW / 2, fun ρ => ?_⟩
  have h1 : |potE V ρ| ≤ BV := by
    unfold potE
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |V x| ∂(ρ : Measure (Torus d)) ≤ ∫ _x, BV ∂(ρ : Measure (Torus d)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun x => hBV x)
      _ = BV := by simp
  have h2 : |interE W ρ ρ| ≤ BW := by
    unfold interE
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |∫ x, W x y ∂(ρ : Measure (Torus d))| ∂(ρ : Measure (Torus d)) ≤
        ∫ _y, BW ∂(ρ : Measure (Torus d)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun y => ?_)
          refine (abs_integral_le_integral_abs).trans ?_
          calc ∫ x, |W x y| ∂(ρ : Measure (Torus d)) ≤ ∫ _x, BW ∂(ρ : Measure (Torus d)) :=
                integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
                  (integrable_const _) (Eventually.of_forall fun x => hBW (x, y))
            _ = BW := by simp
      _ = BW := by simp
  unfold freeEnergy
  have h3 : ((-(BV + BW / 2) : ℝ) : EReal) ≤ ((potE V ρ + interE W ρ ρ / 2 : ℝ) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    have := neg_abs_le (potE V ρ); have := neg_abs_le (interE W ρ ρ); linarith
  calc ((-(BV + BW / 2) : ℝ) : EReal) = 0 + ((-(BV + BW / 2) : ℝ) : EReal) := by rw [zero_add]
    _ ≤ _ := add_le_add (EReal.coe_ennreal_nonneg _) h3

theorem Fstar_ne_bot (hyp : Hyp V W KV KW) : Fstar V W ≠ ⊥ := by
  obtain ⟨C, hC⟩ := freeEnergy_ge hyp
  have : ((-C : ℝ) : EReal) ≤ Fstar V W := le_iInf hC
  intro h; rw [h] at this; exact (EReal.coe_ne_bot _) (le_bot_iff.mp this)

/-- **`H(ρ|m) < ∞`** for `√ρ ∈ H¹(m)`. -/
theorem klDiv_densMeasure_ne_top_of_memH1 {ρ : Torus d → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) (hH : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    klDiv (densMeasure ρ) (haar d) ≠ ⊤ := by
  rw [klDiv_densMeasure' h0 h1]
  have hρi := integrable_of_integral_eq_one' h1
  rcases isEmpty_or_nonempty (Fin d) with hι | hι
  · -- a one-point space: `ρ ≡ 1`
    have hX : ∀ x y : Torus d, x = y := fun x y => by funext k; exact (hι.false k).elim
    refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal (klFun (ρ 0)) ∂haar d)
      (by simp) (le_of_eq (lintegral_congr fun x => by rw [hX x 0]))
  · set p := sobExp (Fin d)
    have hp : 1 < p := one_lt_sobExp
    obtain ⟨hw, hL2, hgL2⟩ := hH
    set s : Torus d → ℝ := fun x => Real.sqrt (ρ x)
    have hsw := isWeakGrad_weakGrad hw
    have hsi : Integrable s (haar d) := hL2.integrable one_le_two
    have hgi : ∀ k, Integrable (fun y => weakGrad s y k) (haar d) := fun k => by
      refine (hgL2.integrable one_le_two).mono' (hsw.aestronglyMeasurable_grad k)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]; exact abs_le_sqrt_sqNorm _ k
    have hS := lintegral_rpow_le_of_isWeakGrad hsw hsi hgi
    have hfin : ∫⁻ y, ‖s y‖ₑ ^ (2 * p) ∂haar d < ⊤ := by
      refine hS.trans_lt (ENNReal.mul_lt_top sobConst_lt_top (ENNReal.rpow_lt_top_of_nonneg
        (by linarith) ?_))
      refine ENNReal.add_ne_top.mpr ⟨?_, ENNReal.sum_ne_top.mpr fun k _ => ?_⟩
      · have := hL2.integrable_sq.2
        simpa [HasFiniteIntegral, enorm_pow] using this.ne
      · have hk : MemLp (fun y => weakGrad s y k) 2 (haar d) :=
          hgL2.of_le (hsw.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            exact abs_le_sqrt_sqNorm _ k)
        have := hk.integrable_sq.2
        simpa [HasFiniteIntegral, enorm_pow] using this.ne
    -- `klFun ρ ≤ 1 + ρ^p/(p-1)` and `ρ^p = |√ρ|^{2p}`
    have hpt : ∀ x, ENNReal.ofReal (klFun (ρ x)) ≤
        1 + ENNReal.ofReal (1 / (p - 1)) * ‖s x‖ₑ ^ (2 * p) := fun x => by
      have hk := klFun_le_rpow hp (h0 x)
      have e : ‖s x‖ₑ ^ (2 * p) = ENNReal.ofReal (ρ x ^ p) := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by linarith), Real.rpow_mul
            (Real.sqrt_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          Real.sq_sqrt (h0 x)]
      have hp1 : 0 ≤ 1 / (p - 1) := div_nonneg zero_le_one (by linarith)
      rw [e, ← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg hp1 (Real.rpow_nonneg (h0 x) p))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [one_div, inv_mul_eq_div]; exact hk
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [lintegral_add_left' measurable_const.aemeasurable, lintegral_const_mul'' _
      (hsw.aestronglyMeasurable_fun.enorm.pow_const _)]
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne⟩


/-- Lipschitz bound for the slices `x ↦ W(x, y)`, uniformly in `y`. -/
theorem lipschitz_W_left (hyp : Hyp V W KV KW) :
    ∃ L : ℝ≥0, ∀ y : Torus d, LipschitzWith L (fun x : Fin d → ℝ => W (liftT x) y) := by
  have hc : Continuous (W2 W) := by
    have e : W2 W = Function.uncurry W ∘ (fun Y : UnitAddTorus (Fin 2 × Fin d) =>
        ((fun k => Y (0, k) : Torus d), (fun k => Y (1, k) : Torus d))) := rfl
    rw [e]
    exact hyp.continuous_W.comp ((continuous_pi fun k => continuous_apply ((0 : Fin 2), k)).prodMk
      (continuous_pi fun k => continuous_apply ((1 : Fin 2), k)))
  have hL := lipschitz_of_coordSemiconvex hc hyp.KW_nonneg (coordSemiconvex_W2 hyp)
  refine ⟨(KW * Fintype.card (Fin 2 × Fin d) / 2).toNNReal, fun y => ?_⟩
  have hb : ∀ k, ∃ r : ℝ, ((r : UnitAddCircle)) = y k := fun k => QuotientAddGroup.mk_surjective (y k)
  choose b hb using hb
  set emb : (Fin d → ℝ) → (Fin 2 × Fin d → ℝ) := fun x p => if p.1 = 0 then x p.2 else b p.2
  have he : ∀ x, W (liftT x) y = (W2 W ∘ liftT) (emb x) := fun x => by
    have hy : y = liftT b := funext fun k => (hb k).symm
    simp only [Function.comp, W2, unflat, emb, liftT, hy]
    rfl
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [he, he]
  refine (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _))
  refine (dist_pi_le_iff dist_nonneg).mpr fun p => ?_
  simp only [emb]
  split_ifs
  · exact dist_le_pi_dist x x' p.2
  · simp

/-- `W*ρ` lifts to a Lipschitz function. -/
theorem lipschitz_convDens (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρi : Integrable ρ (haar d)) :
    ∃ L : ℝ≥0, LipschitzWith L (convDens W ρ ∘ liftT) := by
  obtain ⟨L, hL⟩ := lipschitz_W_left hyp
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hint : ∀ a : Torus d, Integrable (fun y => W a y * ρ y) (haar d) := fun a =>
    hρi.bdd_mul (c := BW) (hyp.continuous_W.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hBW (a, y))
  refine ⟨L * (∫ y, |ρ y| ∂haar d).toNNReal,
    LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
  simp only [Function.comp, convDens, Real.dist_eq]
  rw [← integral_sub (hint _) (hint _)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |W (liftT x) y * ρ y - W (liftT x') y * ρ y| ∂haar d ≤
      ∫ y, L * dist x x' * |ρ y| ∂haar d := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hρi.abs.const_mul _) (Eventually.of_forall fun y => ?_)
        show |W (liftT x) y * ρ y - W (liftT x') y * ρ y| ≤ L * dist x x' * |ρ y|
        rw [← sub_mul, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have := (hL y).dist_le_mul x x'
        rwa [Real.dist_eq] at this
    _ = _ := by
        rw [integral_const_mul, NNReal.coe_mul,
          Real.coe_toNNReal _ (integral_nonneg fun _ => abs_nonneg _)]
        ring

/-- **`D(ρ) < ∞`** for `√ρ ∈ H¹(m)`. -/
theorem dissipation_lt_top_of_memH1 (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) (hH : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    dissipation V W ρ < ⊤ := by
  have hρi := integrable_of_integral_eq_one' h1
  obtain ⟨LC, hLC⟩ := lipschitz_convDens hyp hρi (W := W)
  have hLV := lipschitz_of_coordSemiconvex hyp.continuous_V hyp.KV_nonneg (coordSemiconvex_V hyp)
  set Φ : Torus d → ℝ := fun x => V x + convDens W ρ x
  have hΦL : LipschitzWith (_ + LC) (Φ ∘ liftT) := hLV.add hLC
  have hΦc : Continuous Φ :=
    hyp.continuous_V.add (lipschitzWith_of_liftT hLC).continuous
  have hΦw := isWeakGrad_lipGrad hΦc hΦL
  set CΦ : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) + LC : ℝ≥0) : ℝ)
  have hΦb : ∀ y k, |lipGrad Φ y k| ≤ CΦ := fun y k => abs_lipGrad_le hΦL y k
  unfold dissipation
  rw [if_pos ⟨hH, ⟨_, hΦw⟩⟩]
  obtain ⟨hw, -, hgL2⟩ := hH
  set g := weakGrad (fun y => Real.sqrt (ρ y))
  have hsq : Integrable (fun x => sqNorm (g x)) (haar d) := by
    refine hgL2.integrable_sq.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.sq_sqrt (sqNorm_nonneg _)]
  set B : Torus d → ℝ := fun x => 8 * sqNorm (g x) + 2 * (Fintype.card (Fin d) * CΦ ^ 2) * ρ x
  have hBi : Integrable B (haar d) := (hsq.const_mul 8).add (hρi.const_mul _)
  have hle : ∀ᵐ x ∂haar d, ENNReal.ofReal (∑ k, (2 * g x k + Real.sqrt (ρ x) * weakGrad Φ x k) ^ 2)
      ≤ ENNReal.ofReal (B x) := by
    filter_upwards [weakGrad_ae_eq hΦw] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hx]
    simp only [B, sqNorm]
    rw [Finset.mul_sum, mul_comm (2 * _ : ℝ) (ρ x)]
    have hcard : (Fintype.card (Fin d) : ℝ) * CΦ ^ 2 = ∑ _k : Fin d, CΦ ^ 2 := by simp
    rw [hcard, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hG : lipGrad Φ x k ^ 2 ≤ CΦ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΦb x k) 2
    have hs : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (h0 x)
    nlinarith [sq_nonneg (2 * g x k - Real.sqrt (ρ x) * lipGrad Φ x k), h0 x,
      mul_le_mul_of_nonneg_left hG (h0 x)]
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂haar d := lintegral_mono_ae hle
    _ < ⊤ := hBi.lintegral_lt_top

/-- **The D7 sanity lemma.** -/
theorem gap_lt_top_aux (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) (hH : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    gap V W (densMeasure ρ) < ⊤ ∧ dissipation V W ρ < ⊤ := by
  refine ⟨?_, dissipation_lt_top_of_memH1 hyp h0 h1 hH⟩
  have hK := klDiv_densMeasure_ne_top_of_memH1 h0 h1 hH
  have hF : freeEnergy V W (densMeasure ρ) ≠ ⊤ := by
    unfold freeEnergy
    refine (EReal.add_lt_top ?_ (EReal.coe_ne_top _)).ne
    exact fun h => hK (EReal.coe_ennreal_eq_top_iff.mp h)
  unfold gap
  rw [sub_eq_add_neg]
  refine EReal.add_lt_top hF ?_
  rw [Ne, EReal.neg_eq_top_iff]
  exact Fstar_ne_bot hyp

end SharpLSI
