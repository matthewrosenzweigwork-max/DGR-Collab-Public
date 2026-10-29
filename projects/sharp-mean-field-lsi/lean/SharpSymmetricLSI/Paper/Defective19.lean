import SharpSymmetricLSI.Paper.Defective18

/-!
# R03 (Proposition 2.2), part 19: the conditional dissipation bound (5.19), per particle

For `ν = Q · Leb` (the regularized law) and `j < N`:
* `lintegral_dissipation_eq_S`: `E_ν D(ρ_j) = E_ν |S(past, X_j)|²`;
* `lintegral_scoreS_le`: `E_ν |S|² ≤ (1+ε) E_ν |s_j|² + (1 + 1/ε) E_ν |B_j - E[G_j | ·]|²`;
* `lintegral_force_eq_fcTerm`: the last expectation is R21's `fcTerm j`.
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem volume_ac_pi_minimizer (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (N : ℕ) :
    (volume : Measure (Config N d)) ≪ Measure.pi fun _ : Fin N => (μ : Measure (Torus d)) := by
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  rw [minimizer_eq_elDensity hyp hμ, densMeasure, pi_withDensity_ofReal hqm (fun x => (hqpos x).le)
    (integrable_of_integral_eq_one' hq1)]
  refine withDensity_absolutelyContinuous' ?_ (Eventually.of_forall fun X => ?_)
  · exact ((Finset.measurable_prod _ fun i _ =>
      hqm.comp (measurable_pi_apply i)).ennreal_ofReal).aemeasurable
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun i _ => hqpos _

section disint
variable {N j : ℕ} (hj : j < N) {Q : Config N d → ℝ} (hQm : Measurable Q) {c C : ℝ} (hc : 0 < c)
  (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
include hQm hc hQc hQC

/-- `E_ν ∫ ρ_j F(past, ·) = E_ν F(past, X_j)`. -/
theorem lintegral_condDens_mul_past {F : Config j d → Torus d → ℝ}
    (hF : Measurable (Function.uncurry F)) (hF0 : ∀ p x, 0 ≤ F p x) :
    ∫⁻ X, (∫⁻ x, ENNReal.ofReal (condDens hj Q (past j hj.le X) x * F (past j hj.le X) x) ∂haar d)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)) =
      ∫⁻ X, ENNReal.ofReal (F (past j hj.le X) (X ⟨j, hj⟩))
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)) := by
  set Dm : Config j d → ℝ≥0∞ := fun p => ∫⁻ x, ENNReal.ofReal (condDens hj Q p x * F p x) ∂haar d
  have hDm : Measurable Dm :=
    (((measurable_condDens hj hQm).mul hF).ennreal_ofReal).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ ((hQm).ennreal_ofReal)
    (show Measurable fun X : Config N d => Dm (past j hj.le X) from hDm.comp (measurable_past hj.le)),
    lintegral_withDensity_eq_lintegral_mul _ ((hQm).ennreal_ofReal)
    (show Measurable fun X : Config N d => F (past j hj.le X) (X ⟨j, hj⟩) from
      measurable_pastCur_comp hj hF).ennreal_ofReal]
  simp only [Pi.mul_apply]
  have e1 := lintegral_pastCur hj hQm hc hQc hQC (F := fun p _ => Dm p)
    (show Measurable (Function.uncurry fun (p : Config j d) (_ : Torus d) => Dm p) from hDm.comp measurable_fst)
  have e2 := lintegral_pastCur hj hQm hc hQc hQC (F := fun p x => ENNReal.ofReal (F p x))
    ((hF).ennreal_ofReal)
  simp_rw [mul_comm (ENNReal.ofReal (Q _))]
  rw [e1, e2]
  refine lintegral_congr fun p => ?_
  have hZ0 : 0 < Zc hj Q p := hc.trans_le (Zc_bounds hj hQm hQc hQC p).1
  have hmQ : ∀ x, 0 ≤ margQ hj Q p x := fun x => hc.le.trans (margQ_bounds hj hQm hQc hQC p x).1
  rw [lintegral_const_mul _ (((measurable_margQ hj hQm).of_uncurry_left).ennreal_ofReal), ← ofReal_integral_eq_lintegral_ofReal]
  · show Dm p * ENNReal.ofReal (Zc hj Q p) = _
    simp only [Dm]
    have hmx : Measurable fun x => ENNReal.ofReal (condDens hj Q p x * F p x) :=
      ((measurable_condDens hj hQm).of_uncurry_left.mul hF.of_uncurry_left).ennreal_ofReal
    rw [← lintegral_mul_const _ hmx]
    refine lintegral_congr fun x => ?_
    have hcd0 : 0 ≤ condDens hj Q p x := div_nonneg (hmQ x) hZ0.le
    rw [← ENNReal.ofReal_mul (mul_nonneg hcd0 (hF0 p x)),
      ← ENNReal.ofReal_mul (hF0 p x)]
    congr 1
    unfold condDens; field_simp
  · exact Integrable.of_bound ((measurable_margQ hj hQm).of_uncurry_left
      |>.aestronglyMeasurable) C (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hmQ x)]; exact (margQ_bounds hj hQm hQc hQC p x).2)
  · exact Eventually.of_forall hmQ

end disint

section expect
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)
include hyp hac hN hfm hf hw hgm hg2 hgi

/-- **`E_ν D(ρ_j) = E_ν |S|²`.** -/
theorem lintegral_dissipation_eq_S :
    ∫⁻ X, dissipation V W (condDens hj (Qreg V W n f) (past j hj.le X))
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      ∫⁻ X, ENNReal.ofReal (∑ k, scoreS W μ hj (Qreg V W n f) (fun k => sfun n f g ⟨j, hj⟩ k)
        (fun k => Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩) k ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  set S := fun p x k => scoreS W μ hj (Qreg V W n f) (fun k => sfun n f g ⟨j, hj⟩ k)
    (fun k => Gfun W μ ⟨j, hj⟩ k) p x k
  have hSm : ∀ k, Measurable (Function.uncurry fun p x => S p x k) := fun k =>
    measurable_scoreS hyp hac hN hfm hf hw hgm hg2 hgi n hj k
  have hS2 : Measurable (Function.uncurry fun p x => ∑ k, S p x k ^ 2) :=
    Finset.measurable_sum _ fun k _ => (hSm k).pow_const 2
  set Dm : Config j d → ℝ≥0∞ := fun p => ∫⁻ x, ENNReal.ofReal
    (condDens hj (Qreg V W n f) p x * ∑ k, S p x k ^ 2) ∂haar d
  have hDm : Measurable Dm :=
    (((measurable_condDens hj hQm).mul hS2).ennreal_ofReal).lintegral_prod_right'
  -- `D = Dm` a.e. in the past, transferred to `ν`
  have hae := ae_dissipation_eq_S hyp hac hN hfm hf hw hgm hg2 hgi n hj
  have hmap := map_past_eq hj hQm hc hQc hQC
  have hνX : ∀ᵐ X ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)),
      dissipation V W (condDens hj (Qreg V W n f) (past j hj.le X)) = Dm (past j hj.le X) := by
    have h1 : ∀ᵐ p ∂(((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal
        (Qreg V W n f X)).map (past j hj.le)),
        dissipation V W (condDens hj (Qreg V W n f) p) = Dm p := by
      rw [hmap]; exact withDensity_absolutelyContinuous _ _ |>.ae_le hae
    exact ae_of_ae_map (measurable_past hj.le).aemeasurable h1
  rw [lintegral_congr_ae hνX]
  exact lintegral_condDens_mul_past hj hQm hc hQc hQC hS2 fun p x =>
    Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **Young's splitting and conditional Jensen for the score part.** -/
theorem lintegral_scoreS_le {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ X, ENNReal.ofReal (∑ k, scoreS W μ hj (Qreg V W n f) (fun k => sfun n f g ⟨j, hj⟩ k)
        (fun k => Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩) k ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) ≤
      ENNReal.ofReal (1 + ε) * (∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g ⟨j, hj⟩ k X ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))) +
      ENNReal.ofReal (1 + 1 / ε) * ∫⁻ X, ENNReal.ofReal (∑ k,
        (condB W μ hj (Qreg V W n f) (past j hj.le X) (X ⟨j, hj⟩) k -
          condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩)) ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)
  have hπ : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
    (measurable_past hj.le).prodMk (measurable_pi_apply _)
  set A : Fin d → Config N d → ℝ := fun k X =>
    condRatio hj (Qreg V W n f) (sfun n f g ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩)
  set E : Fin d → Config N d → ℝ := fun k X =>
    condB W μ hj (Qreg V W n f) (past j hj.le X) (X ⟨j, hj⟩) k -
      condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩)
  have hAm : ∀ k, Measurable (A k) := fun k =>
    measurable_pastCur_comp hj (measurable_condRatio hj hQm (measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n _ k))
  have hEm : Measurable fun X => ∑ k, E k X ^ 2 := by
    refine Finset.measurable_sum _ fun k _ => (Measurable.pow_const ?_ 2)
    have h1 := measurable_pastCur_comp hj (measurable_scoreS hyp hac hN hfm hf hw hgm hg2 hgi n hj k)
    have h2 := hAm k
    have : E k = fun X => scoreS W μ hj (Qreg V W n f) (fun k => sfun n f g ⟨j, hj⟩ k)
        (fun k => Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩) k - A k X := by
      funext X; simp only [E, A, scoreS]; ring
    rw [this]; exact h1.sub h2
  -- pointwise Young
  have hpt : ∀ X, ENNReal.ofReal (∑ k, scoreS W μ hj (Qreg V W n f) (fun k => sfun n f g ⟨j, hj⟩ k)
      (fun k => Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩) k ^ 2) ≤
      ENNReal.ofReal (1 + ε) * (∑ k, ENNReal.ofReal (A k X ^ 2)) +
        ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (∑ k, E k X ^ 2) := fun X => by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hS : scoreS W μ hj (Qreg V W n f) (fun k => sfun n f g ⟨j, hj⟩ k)
        (fun k => Gfun W μ ⟨j, hj⟩ k) (past j hj.le X) (X ⟨j, hj⟩) k = A k X + E k X := by
      simp only [scoreS, A, E]; ring
    rw [hS]
    have h1 := sq_nonneg (ε * A k X - E k X)
    have h2 : 2 * (A k X * E k X) ≤ ε * A k X ^ 2 + E k X ^ 2 / ε := by
      rw [show ε * A k X ^ 2 + E k X ^ 2 / ε = (ε ^ 2 * A k X ^ 2 + E k X ^ 2) / ε by first | (field_simp; done) | (field_simp; ring),
        le_div_iff₀ hε]
      nlinarith
    have : 1 / ε * E k X ^ 2 = E k X ^ 2 / ε := by ring
    nlinarith
  calc _ ≤ ∫⁻ X, (ENNReal.ofReal (1 + ε) * (∑ k, ENNReal.ofReal (A k X ^ 2)) +
        ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (∑ k, E k X ^ 2)) ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal (1 + ε) * (∑ k, ∫⁻ X, ENNReal.ofReal (A k X ^ 2) ∂ν) +
        ENNReal.ofReal (1 + 1 / ε) * ∫⁻ X, ENNReal.ofReal (∑ k, E k X ^ 2) ∂ν := by
        rw [lintegral_add_left ((Finset.measurable_sum _ fun k _ =>
          ((hAm k).pow_const 2).ennreal_ofReal).const_mul _),
          lintegral_const_mul _ (Finset.measurable_sum _ fun k _ =>
            ((hAm k).pow_const 2).ennreal_ofReal),
          lintegral_finset_sum _ fun k _ => ((hAm k).pow_const 2).ennreal_ofReal,
          lintegral_const_mul _ ((hEm).ennreal_ofReal)]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => ?_)) le_rfl
        rw [lintegral_withDensity_eq_lintegral_mul _ ((hQm).ennreal_ofReal)
            (((hAm k).pow_const 2).ennreal_ofReal),
          lintegral_withDensity_eq_lintegral_mul _ ((hQm).ennreal_ofReal)
            (((measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n _ k).pow_const 2).ennreal_ofReal)]
        simp only [Pi.mul_apply]
        simp_rw [mul_comm (ENNReal.ofReal (Qreg V W n f _))]
        exact lintegral_condRatio_sq_le hj hQm hc hQc hQC (measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n _ k)

end expect

end SharpLSI
