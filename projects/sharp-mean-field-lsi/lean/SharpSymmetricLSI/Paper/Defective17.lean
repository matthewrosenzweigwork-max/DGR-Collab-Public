import SharpSymmetricLSI.Paper.Defective16

/-!
# R03 (Proposition 2.2), part 17: the conditional score identity (5.16)

With `s_{j,k} = u'(f) g_{(j,k)} / u` (the `(j,k)` score of `ν` relative to `P_N`) and
`G_{j,k} = gsG_{(j,k)}` (`= ∇_{j,k} U_N`):
`∇Q_{(j,k)} = Q (s_{j,k} - G_{j,k} - ∂_k Φ(X_j))` (`GQreg_flat_eq`), hence for a.e. `(p, x)`
`gradMarg/margQ = E[s | p, x] - E[G | p, x] - ∂Φ(x)` (`ae_gradMarg_div_eq`).
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The score `s_{j,k}`. -/
noncomputable def sfun {N : ℕ} (n : ℕ) (f : Config N d → ℝ)
    (g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ) (i : Fin N) (k : Fin d) (X : Config N d) : ℝ :=
  deriv (psiSqR n) (f X) * g (flat X) (i, k) / uReg n f X

/-- The force component `G_{j,k} = gsG_{(j,k)}`. -/
noncomputable def Gfun (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {N : ℕ} (i : Fin N)
    (k : Fin d) (X : Config N d) : ℝ :=
  gsG W μ N (flat X) (i, k)

section score
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ)

include hyp hf in
theorem uReg_pos (X : Config N d) : 0 < uReg n f X :=
  lt_of_lt_of_le (by positivity) (psiSqR_bounds n (f X)).1

include hyp hf in
theorem GQreg_flat_eq (i : Fin N) (k : Fin d) (X : Config N d) :
    GQreg V W μ n f g (flat X) (i, k) = Qreg V W n f X *
      (sfun n f g i k X - Gfun W μ i k X - lipGrad (PhiMF V W μ) (X i) k) := by
  have hu := uReg_pos hyp hf n X
  unfold GQreg Qreg sfun Gfun
  simp only [show unflat (flat X) = X from rfl, show projBlock i (flat X) = X i from rfl]
  first | (field_simp; done) | (field_simp; ring)

include hyp hac hN hfm hf hw hgm hg2 hgi

theorem measurable_sfun (i : Fin N) (k : Fin d) : Measurable (sfun n f g i k) := by
  unfold sfun uReg
  exact ((((contDiff_psiSqR n).continuous_deriv le_rfl).measurable.comp hfm).mul
    ((hgm (i, k)).comp measurable_flat)).div ((contDiff_psiSqR n).continuous.measurable.comp hfm)

omit hf hw hgm hg2 hgi hfm in
theorem measurable_Gfun (i : Fin N) (k : Fin d) : Measurable (Gfun W μ i k) :=
  (measurable_gsG hyp hac (i, k)).comp measurable_flat

theorem integrable_sfun_mul_Q (i : Fin N) (k : Fin d) :
    Integrable (fun X => sfun n f g i k X * Qreg V W n f X) volume := by
  obtain ⟨c1, C1, hc1, h1⟩ := gibbsDensR_bounds hyp (N := N)
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  have hg1 : Integrable (fun X : Config N d => g (flat X) (i, k)) volume :=
    (measurePreserving_flat' N).integrable_comp_of_integrable (hgi (i, k))
  have e : ∀ X, sfun n f g i k X * Qreg V W n f X =
      (deriv (psiSqR n) (f X) * gibbsDensR V W N X / Zreg V W n f) * g (flat X) (i, k) := fun X => by
    have hu := (uReg_pos hyp hf n X).ne'
    have hZ' := hZ0.ne'
    unfold sfun Qreg; first | (field_simp; done) | (field_simp; ring)
  simp_rw [e]
  refine hg1.bdd_mul (c := ((n : ℝ) + 1) * C1 / Zreg V W n f)
    ((((contDiff_psiSqR n).continuous_deriv le_rfl).measurable.comp hfm).mul
    (measurable_gibbsDensR hyp) |>.div_const _).aestronglyMeasurable
    (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hZ0]
  have a1 := abs_deriv_psiSqR_le n (f X)
  have a2 : |gibbsDensR V W N X| ≤ C1 := by rw [abs_of_pos (hc1.trans_le (h1 X).1)]; exact (h1 X).2
  exact div_le_div_of_nonneg_right (mul_le_mul a1 a2 (abs_nonneg _) (by positivity)) hZ0.le

/-- **The conditional score identity** (5.16), a.e. in `(p, x)`. -/
theorem ae_gradMarg_div_eq {j : ℕ} (hj : j < N) (k : Fin d) :
    ∀ᵐ q ∂((volume : Measure (Config j d)).prod (volume : Measure (Torus d))),
      gradMarg hj (GQreg V W μ n f g) q.1 q.2 k / margQ hj (Qreg V W n f) q.1 q.2 =
        condRatio hj (Qreg V W n f) (sfun n f g ⟨j, hj⟩ k) q.1 q.2 -
          condRatio hj (Qreg V W n f) (Gfun W μ ⟨j, hj⟩ k) q.1 q.2 -
          lipGrad (PhiMF V W μ) q.2 k := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_gsG hyp hac (μ := μ) (N := N)
  have hI := integrable_sfun_mul_Q hyp hac hN hfm hf hw hgm hg2 hgi n ⟨j, hj⟩ k
  have hslice : ∀ᵐ q ∂((volume : Measure (Config j d)).prod (volume : Measure (Torus d))),
      Integrable (fun z => sfun n f g ⟨j, hj⟩ k (assemble hj q.1 q.2 z) *
        Qreg V W n f (assemble hj q.1 q.2 z)) (volume : Measure (Config (N - j - 1) d)) :=
    ((measurePreserving_assemble (d := d) hj).integrable_comp_of_integrable hI).prod_right_ae
  filter_upwards [hslice] with q hq
  have hm0 : 0 < margQ hj (Qreg V W n f) q.1 q.2 :=
    hc.trans_le (margQ_bounds hj hQm (fun X => (hb X).1) (fun X => (hb X).2) q.1 q.2).1
  have hzm : Measurable fun z : Config (N - j - 1) d => assemble hj q.1 q.2 z :=
    (measurable_assemble hj).comp ((measurable_const (a := q)).prodMk measurable_id)
  have hQi : Integrable (fun z => Qreg V W n f (assemble hj q.1 q.2 z))
      (volume : Measure (Config (N - j - 1) d)) :=
    Integrable.of_bound (hQm.comp hzm).aestronglyMeasurable C (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb _).1)]; exact (hb _).2)
  have hGi : Integrable (fun z => Gfun W μ ⟨j, hj⟩ k (assemble hj q.1 q.2 z) *
      Qreg V W n f (assemble hj q.1 q.2 z)) (volume : Measure (Config (N - j - 1) d)) :=
    hQi.bdd_mul ((measurable_Gfun hyp hac hN ⟨j, hj⟩ k).comp hzm).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hCG _ _)
  have hgrad : gradMarg hj (GQreg V W μ n f g) q.1 q.2 k =
      (∫ z, sfun n f g ⟨j, hj⟩ k (assemble hj q.1 q.2 z) * Qreg V W n f (assemble hj q.1 q.2 z)
        ∂(volume : Measure (Config (N - j - 1) d))) -
      (∫ z, Gfun W μ ⟨j, hj⟩ k (assemble hj q.1 q.2 z) * Qreg V W n f (assemble hj q.1 q.2 z)
        ∂(volume : Measure (Config (N - j - 1) d))) -
      lipGrad (PhiMF V W μ) q.2 k * margQ hj (Qreg V W n f) q.1 q.2 := by
    unfold gradMarg margQ
    have hcong : ∫ z, GQreg V W μ n f g (flat (assemble hj q.1 q.2 z)) (⟨j, hj⟩, k)
        ∂(volume : Measure (Config (N - j - 1) d)) =
        ∫ z, (sfun n f g ⟨j, hj⟩ k (assemble hj q.1 q.2 z) * Qreg V W n f (assemble hj q.1 q.2 z) -
          Gfun W μ ⟨j, hj⟩ k (assemble hj q.1 q.2 z) * Qreg V W n f (assemble hj q.1 q.2 z)) -
          lipGrad (PhiMF V W μ) q.2 k * Qreg V W n f (assemble hj q.1 q.2 z)
        ∂(volume : Measure (Config (N - j - 1) d)) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      rw [GQreg_flat_eq hyp hf n, cur_assemble]
      ring
    have hd : Integrable (fun z => sfun n f g ⟨j, hj⟩ k (assemble hj q.1 q.2 z) *
        Qreg V W n f (assemble hj q.1 q.2 z) - Gfun W μ ⟨j, hj⟩ k (assemble hj q.1 q.2 z) *
        Qreg V W n f (assemble hj q.1 q.2 z)) (volume : Measure (Config (N - j - 1) d)) := hq.sub hGi
    have hl : Integrable (fun z => lipGrad (PhiMF V W μ) q.2 k * Qreg V W n f (assemble hj q.1 q.2 z))
        (volume : Measure (Config (N - j - 1) d)) := hQi.const_mul _
    rw [hcong, integral_sub hd hl, integral_sub hq hGi, integral_const_mul]
  rw [hgrad]
  unfold condRatio
  have hm0' := hm0.ne'
  first | (field_simp; done) | (field_simp; ring)

end score

end SharpLSI
