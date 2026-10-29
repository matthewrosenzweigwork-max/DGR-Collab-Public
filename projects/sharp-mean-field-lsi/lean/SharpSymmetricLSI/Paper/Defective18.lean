import SharpSymmetricLSI.Paper.Defective17

/-!
# R03 (Proposition 2.2), part 18: the mean-field score of the conditional laws

* `lipGrad_PhiMF_ae`: `∇Φ = ∇V + β` a.e. (`β = b_μ = ∇(W * μ)`);
* `bForceL_sub_eq`: `b_ρ - β = ∫ b̃(·, y) dρ(y)` with `b̃ = bfixF`;
* `condB`: the conditional force `B_j(p, x) = ∫ b̃(x, y) ρ_p(y) dy`;
* `ae_dissipation_eq_S`: `D(ρ_p) = ∫ ρ_p |S(p, ·)|²` with
  `S = E[s | p, x] - E[G | p, x] + B_j(p, x)` (the identity (5.16)).
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section phiGrad
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
include hyp hac

theorem lipGrad_PhiMF_ae : ∀ᵐ x ∂haar d, ∀ k,
    lipGrad (PhiMF V W μ) x k = lipGrad V x k + bForceL W (densOf μ) x k := by
  have h1 := isWeakGrad_PhiMF hyp hac
  have h2 := (isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))).add
    (isWeakGrad_convDens hyp (measurable_densOf μ) (integrable_densOf μ) (W := W))
  have h2' : IsWeakGrad (PhiMF V W μ) (fun x k => lipGrad V x k + bForceL W (densOf μ) x k) := by
    convert h2 using 1
    funext x; simp [PhiMF, convMeas_eq_convDens hac]
  filter_upwards [weakGrad_ae_unique h1 h2'] with x hx k
  exact congrFun hx k

omit hac in
theorem bForceL_sub_eq {ρ : Torus d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) (x : Torus d) (k : Fin d) :
    bForceL W ρ x k - bForceL W (densOf μ) x k = ∫ y, bfixF W μ x y k * ρ y ∂haar d := by
  haveI := isProbabilityMeasure_densMeasure' hρ0 h1
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hbi : Integrable (fun y => bGrad W x y k) (densMeasure ρ) :=
    Integrable.of_bound ((measurable_bGrad hyp k).comp (measurable_const.prodMk measurable_id)
      |>.aestronglyMeasurable) Cb (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hCb x y k)
  have e1 : ∫ y, bfixF W μ x y k * ρ y ∂haar d = ∫ y, bfixF W μ x y k ∂densMeasure ρ := by
    rw [integral_densMeasure' hρ0 h1]; congr 1; funext y; ring
  rw [e1, bForce_eq hρ0 h1]
  unfold bfixF
  rw [integral_sub hbi (integrable_const _), integral_const]
  simp

end phiGrad

/-- The conditional force `B_j(p, x)_k = ∫ b̃(x, y)_k ρ_p(y) dy`. -/
noncomputable def condB (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {N j : ℕ} (hj : j < N)
    (Q : Config N d → ℝ) (p : Config j d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, bfixF W μ x y k * condDens hj Q p y ∂haar d

/-- The mean-field score `S = E[s | p, x] - E[G | p, x] + B_j(p, x)`. -/
noncomputable def scoreS (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {N j : ℕ} (hj : j < N)
    (Q : Config N d → ℝ) (s G : Fin d → Config N d → ℝ) (p : Config j d) (x : Torus d) (k : Fin d) : ℝ :=
  condRatio hj Q (s k) p x - condRatio hj Q (G k) p x + condB W μ hj Q p x k

/-- Composition with `X ↦ (past X, X_j)`. -/
theorem measurable_pastCur_comp {N j : ℕ} (hj : j < N) {F : Config j d → Torus d → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun X : Config N d => F (past j hj.le X) (X ⟨j, hj⟩) :=
  hF.comp ((measurable_past hj.le).prodMk (measurable_pi_apply _))

theorem measurable_condB (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) {N j : ℕ} (hj : j < N) {Q : Config N d → ℝ} (hQm : Measurable Q) (k : Fin d) :
    Measurable fun q : Config j d × Torus d => condB W μ hj Q q.1 q.2 k := by
  obtain ⟨hbm, -⟩ := bfixF_props hyp hac (μ := μ)
  have hb2 : Measurable (fun q : Torus d × Torus d => bfixF W μ q.1 q.2 k) := by
    have h := hbm k
    unfold Function.uncurry at h
    exact h
  have hcd : Measurable (fun q : Config j d × Torus d => condDens hj Q q.1 q.2) := by
    have h := measurable_condDens hj hQm
    unfold Function.uncurry at h
    exact h
  have hA := hb2.comp (show Measurable (fun q : (Config j d × Torus d) × Torus d => (q.1.2, q.2)) from
    (measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hB := hcd.comp (show Measurable (fun q : (Config j d × Torus d) × Torus d => (q.1.1, q.2)) from
    (measurable_fst.comp measurable_fst).prodMk measurable_snd)
  simp only [Function.comp_def] at hA hB
  have h3' := ((hA.mul hB).stronglyMeasurable.integral_prod_right' (ν := haar d)).measurable
  unfold condB
  exact h3'

theorem measurable_condB_uncurry (hyp : Hyp V W KV KW) {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hac : μ ≪ haar d) {N j : ℕ} (hj : j < N) {Q : Config N d → ℝ}
    (hQm : Measurable Q) (k : Fin d) :
    Measurable (Function.uncurry fun p x => condB W μ hj Q p x k) := by
  unfold Function.uncurry
  exact measurable_condB hyp hac hj hQm k

section score
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)
include hyp hac hN hfm hf hw hgm hg2 hgi

theorem measurable_scoreS (k : Fin d) :
    Measurable (Function.uncurry fun p x => scoreS W μ hj (Qreg V W n f)
      (fun k => sfun n f g ⟨j, hj⟩ k) (fun k => Gfun W μ ⟨j, hj⟩ k) p x k) := by
  have hQm := measurable_Qreg hyp hf hfm n
  have h1 := measurable_condRatio hj hQm (measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n ⟨j, hj⟩ k)
  have h2 := measurable_condRatio hj hQm (measurable_Gfun hyp hac hN ⟨j, hj⟩ k)
  have h3 : Measurable fun q : Config j d × Torus d => condB W μ hj (Qreg V W n f) q.1 q.2 k :=
    measurable_condB hyp hac hj hQm k
  have e : (Function.uncurry fun p x => scoreS W μ hj (Qreg V W n f)
      (fun k => sfun n f g ⟨j, hj⟩ k) (fun k => Gfun W μ ⟨j, hj⟩ k) p x k) =
      fun q => Function.uncurry (condRatio hj (Qreg V W n f) (sfun n f g ⟨j, hj⟩ k)) q -
        Function.uncurry (condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k)) q +
        condB W μ hj (Qreg V W n f) q.1 q.2 k := by
    funext q; rfl
  rw [e]
  exact (h1.sub h2).add h3

/-- **`D(ρ_p) = ∫ ρ_p |S(p, ·)|²`** for a.e. past. -/
theorem ae_dissipation_eq_S :
    ∀ᵐ p ∂(volume : Measure (Config j d)),
      dissipation V W (condDens hj (Qreg V W n f) p) = ∫⁻ x, ENNReal.ofReal
        (condDens hj (Qreg V W n f) p x * ∑ k, scoreS W μ hj (Qreg V W n f)
          (fun k => sfun n f g ⟨j, hj⟩ k) (fun k => Gfun W μ ⟨j, hj⟩ k) p x k ^ 2) ∂haar d := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hdec : ∀ᵐ q ∂((volume : Measure (Config j d)).prod (volume : Measure (Torus d))), ∀ k,
      gradMarg hj (GQreg V W μ n f g) q.1 q.2 k / margQ hj (Qreg V W n f) q.1 q.2 =
        condRatio hj (Qreg V W n f) (sfun n f g ⟨j, hj⟩ k) q.1 q.2 -
          condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) q.1 q.2 -
          lipGrad (PhiMF V W μ) q.2 k :=
    ae_all_iff.mpr fun k => ae_gradMarg_div_eq hyp hac hN hfm hf hw hgm hg2 hgi n hj k
  have hdec' := Measure.ae_ae_of_ae_prod hdec
  filter_upwards [ae_dissipation_condDens hyp hac hN hfm hf hw hgm hg2 hgi n hj, hdec'] with p hp hpd
  rw [hp]
  refine lintegral_congr_ae ?_
  filter_upwards [hpd, lipGrad_PhiMF_ae hyp hac (μ := μ)] with x hx hΦ
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  have hρ0 : ∀ y, 0 ≤ condDens hj (Qreg V W n f) p y := fun y =>
    le_trans (div_pos hc (hc.trans_le ((hb (Classical.arbitrary _)).1.trans (hb _).2))).le
      (condDens_bounds hj hQm hc (fun X => (hb X).1) (fun X => (hb X).2) p y).1
  have hB := bForceL_sub_eq hyp (μ := μ) ((measurable_condDens hj hQm).of_uncurry_left) hρ0
    (integral_condDens hj hQm hc (fun X => (hb X).1) (fun X => (hb X).2) p) x k
  unfold scoreS condB
  rw [hx k, hΦ k, ← hB]
  ring

end score

end SharpLSI
