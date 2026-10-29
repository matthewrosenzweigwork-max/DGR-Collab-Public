import SharpSymmetricLSI.Paper.Defective19

/-!
# R03 (Proposition 2.2), part 20: the mean-field inequality on the conditional laws

* `ofReal_two_r_gap_le`: for `r₀ ≤ r_*` and any probability density `ρ` with `√ρ ∈ H¹`,
  `2 r₀ G(ρ) ≤ D(ρ)` (definition (1.7) of `r_*`; trivial if `G(ρ) = 0`).
* `lintegral_force_eq_fcTerm`: `E_ν |B_j - E[G_j | ·]|² = fcTerm j` (R21's summand).
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **The definition of `r_*`, applied to one density.** -/
theorem ofReal_two_r_gap_le {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rStar V W)
    {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar d = 1)
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    ENNReal.ofReal (2 * r₀ * (gap V W (densMeasure ρ)).toReal) ≤ dissipation V W ρ := by
  set G := gap V W (densMeasure ρ)
  by_cases hG : 0 < G
  · by_cases hGt : G = ⊤
    · rw [hGt]; simp
    have hadm : Admissible V W ρ := ⟨hρ0, h1, hH1, hG⟩
    have hle : rStar V W ≤ dissipation V W ρ / (2 * G.toENNReal) := iInf₂_le ρ hadm
    have hGe : G.toENNReal = ENNReal.ofReal G.toReal := EReal.toENNReal_of_ne_top hGt
    have hGpos : 0 < G.toReal := EReal.toReal_pos hG hGt
    have h2 : ENNReal.ofReal r₀ ≤ dissipation V W ρ / (2 * ENNReal.ofReal G.toReal) := by
      rw [← hGe]; exact hrr.trans hle
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hGpos]))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))] at h2
    calc ENNReal.ofReal (2 * r₀ * G.toReal) = ENNReal.ofReal r₀ * (2 * ENNReal.ofReal G.toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring
      _ ≤ _ := h2
  · push_neg at hG
    have : G.toReal ≤ 0 := by
      rcases eq_or_ne G ⊥ with h | h
      · rw [h]; simp
      · exact EReal.toReal_nonpos hG
    rw [ENNReal.ofReal_of_nonpos (by nlinarith)]
    exact bot_le

section fc
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)
include hyp hμ hN hfm hf hw hgm hg2 hgi

theorem gfixF_eq_Gfun (X : Config N d) (k : Fin d) :
    GfixF W (μ : Measure (Torus d)) ⟨j, hj⟩ X k = Gfun W (μ : Measure (Torus d)) ⟨j, hj⟩ k X := rfl

/-- **The force term is R21's `fcTerm`.** -/
theorem lintegral_force_eq_fcTerm
    [IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Qreg V W n f X))] :
    ∫⁻ X, ENNReal.ofReal (∑ k,
        (condB W μ hj (Qreg V W n f) (past j hj.le X) (X ⟨j, hj⟩) k -
          condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩)) ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      ENNReal.ofReal (fcTerm W μ ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (Qreg V W n f X)) j) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)
  have hνac : ν ≪ Measure.pi fun _ : Fin N => μm :=
    (withDensity_absolutelyContinuous _ _).trans (volume_ac_pi_minimizer hyp hμ N)
  obtain ⟨hbm, M, hM0, hM, hMβ, -⟩ := bfixF_props hyp hac (μ := μm)
  -- the conditional laws
  have h2 : ∀ᵐ X ∂ν, condNext ν j hj (past j hj.le X) = densMeasure (condDens hj (Qreg V W n f)
      (past j hj.le X)) :=
    ae_of_ae_map (measurable_past hj.le).aemeasurable (condNext_ae_eq hj hQm hc hQc hQC)
  have h1 := condForce_ae_eq hyp hμ ν hνac hj
  have h3 : ∀ k, ν[fun Y => weakGradC (Ucentered W μm N) Y ⟨j, hj⟩ k | pastNextSA j hj] =ᵐ[ν]
      fun X => condRatio hj (Qreg V W n f) (Gfun W μm ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩) := by
    intro k
    have he := condExp_congr_ae (m := pastNextSA (d := d) j hj) (μ := ν)
      ((weakGradC_ae_eq_GfixF hyp hμ ν hνac ⟨j, hj⟩).mono fun X hX => hX k)
    refine he.trans ?_
    have hc' := condRatio_ae_eq_condExp hj hQm hc hQc hQC (F := fun X => GfixF W μm ⟨j, hj⟩ X k)
      (measurable_GfixF hyp hac ⟨j, hj⟩ k) (abs_GfixF_le hM hMβ ⟨j, hj⟩ · k)
    exact hc'.symm
  have h3' := ae_all_iff.mpr h3
  -- the integrand agrees a.e.
  have hint : (fun X => ∑ k, (condForce W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k -
      (ν[fun Y => weakGradC (Ucentered W μm N) Y ⟨j, hj⟩ k | pastNextSA j hj]) X) ^ 2) =ᵐ[ν]
      fun X => ∑ k, (condB W μ hj (Qreg V W n f) (past j hj.le X) (X ⟨j, hj⟩) k -
        condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩)) ^ 2 := by
    filter_upwards [h1, h2, h3'] with X hX1 hX2 hX3
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hX1 k, hX3 k]
    congr 2
    unfold BfixF condB
    rw [hX2, integral_densMeasure' (fun y => le_trans (div_pos hc (hc.trans_le
      ((hQc (Classical.arbitrary _)).trans (hQC _)))).le
      (condDens_bounds hj hQm hc hQc hQC _ y).1) (integral_condDens hj hQm hc hQc hQC _)]
    congr 1; funext y; ring
  -- bounded, hence `ofReal ∫ = ∫⁻ ofReal`
  have hRb : ∀ k p x, |condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) p x| ≤ M := fun k p x =>
    abs_condRatio_le hj hQm hc hQc hQC (measurable_GfixF hyp hac ⟨j, hj⟩ k)
      (abs_GfixF_le hM hMβ ⟨j, hj⟩ · k) p x
  have hBb : ∀ k p x, |condB W μ hj (Qreg V W n f) p x k| ≤ M := fun k p x => by
    unfold condB
    have hρ0 : ∀ y, 0 ≤ condDens hj (Qreg V W n f) p y := fun y => le_trans (div_pos hc (hc.trans_le
      ((hQc (Classical.arbitrary _)).trans (hQC _)))).le (condDens_bounds hj hQm hc hQc hQC p y).1
    calc |∫ y, bfixF W μm x y k * condDens hj (Qreg V W n f) p y ∂haar d|
        ≤ ∫ y, |bfixF W μm x y k * condDens hj (Qreg V W n f) p y| ∂haar d :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, M * condDens hj (Qreg V W n f) p y ∂haar d := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ?_
            (Eventually.of_forall fun y => ?_)
          · exact (Integrable.of_bound ((measurable_condDens hj hQm).of_uncurry_left |>.aestronglyMeasurable) (C / c)
              (Eventually.of_forall fun y => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 y)]
                exact (condDens_bounds hj hQm hc hQc hQC p y).2)).const_mul M
          · dsimp only
            rw [abs_mul, abs_of_nonneg (hρ0 y)]
            exact mul_le_mul_of_nonneg_right (hM x y k) (hρ0 y)
      _ = M := by rw [integral_const_mul, integral_condDens hj hQm hc hQc hQC p, mul_one]
  have hπ : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
    (measurable_past hj.le).prodMk (measurable_pi_apply _)
  have hGm : Measurable fun X => ∑ k, (condB W μ hj (Qreg V W n f) (past j hj.le X) (X ⟨j, hj⟩) k -
      condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩)) ^ 2 := by
    refine Finset.measurable_sum _ fun k _ => Measurable.pow_const (Measurable.sub ?_ ?_) 2
    · exact measurable_pastCur_comp hj (measurable_condB_uncurry hyp hac hj hQm k)
    · exact measurable_pastCur_comp hj (measurable_condRatio hj hQm (measurable_GfixF hyp hac ⟨j, hj⟩ k))
  unfold fcTerm
  rw [dif_pos hj, integral_congr_ae hint, ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_bound hGm.aestronglyMeasurable (Fintype.card (Fin d) * (2 * M) ^ 2)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
        calc _ ≤ ∑ _k : Fin d, (2 * M) ^ 2 := Finset.sum_le_sum fun k _ => by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by
                linarith [hBb k (past j hj.le X) (X ⟨j, hj⟩), hRb k (past j hj.le X) (X ⟨j, hj⟩)])) 2
          _ = _ := by simp)
  · exact Eventually.of_forall fun X => Finset.sum_nonneg fun k _ => sq_nonneg _

end fc

end SharpLSI
