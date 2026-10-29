import SharpSymmetricLSI.Paper.GaussForm6

/-!
# R32 (B2): integration by parts for cylinder functions

`∫ u (-L c) dγ = ∑_{i<J_c} λ_i ∫ ∂_i u ∂_i c dγ` (`cyl_ibp`), from `stein_row` applied to
`u ∂_i c` and the product rule.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff

namespace SharpLSI

theorem measurable_comp_block {K : ℕ} {f : (Fin K → ℝ) → ℝ} (hf : Continuous f) :
    Measurable fun z => f (zBlock K z) := hf.measurable.comp (measurable_zBlock K)

theorem integrable_comp_block {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {K : ℕ}
    {f : (Fin K → ℝ) → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable (fun z => f (zBlock K z)) γ :=
  (integrable_const B).mono' (measurable_comp_block hf).aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _)

theorem abs_pd_le {K : ℕ} {f : (Fin K → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (k : Fin K) (x : Fin K → ℝ) : |pd f k x| ≤ B := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have : ‖(Pi.single k 1 : Fin K → ℝ)‖ = 1 := by simp [Pi.norm_single]
  rw [this, mul_one]; exact hB x

namespace Cyl

theorem dd_of_lt (c : Cyl) {i : ℕ} (h : i < c.J) (z : ℕ → ℝ) :
    c.dd i z = pd c.φ ⟨i, h⟩ (zBlock c.J z) := by simp [dd, h]

theorem exists_dd_bound (c : Cyl) : ∃ B, ∀ i z, |c.dd i z| ≤ B := by
  obtain ⟨B, -, hB2, -, -⟩ := exists_bounds_of_cc c.smooth c.compact
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB2 0)
  refine ⟨B, fun i z => ?_⟩
  unfold dd
  split_ifs
  · exact abs_pd_le hB2 _ _
  · simpa using hB0

theorem measurable_dd (c : Cyl) (i : ℕ) : Measurable (c.dd i) := by
  unfold dd
  split_ifs with h
  · exact measurable_comp_block (contDiff_pd c.smooth _).continuous
  · exact measurable_const

end Cyl

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

/-- `∂_{ii} c(z)`. -/
noncomputable def Cyl.dd2 (c : Cyl) (i : Fin c.J) (z : ℕ → ℝ) : ℝ :=
  fderiv ℝ (pd c.φ i) (zBlock c.J z) (Pi.single i 1)

/-- **One term**: `∫ (z_i + Y_i) u ∂_i c = ∫ ∂_i u ∂_i c + ∫ u ∂_{ii} c`. -/
theorem cyl_ibp_term {T : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i)) (u c : Cyl) (i : Fin c.J) :
    ∫ z, (z i + Y i z) * (u.eval z * c.dd i z) ∂γ =
      ∫ z, (u.dd i z * c.dd i z + u.eval z * c.dd2 i z) ∂γ := by
  set J := u.J + c.J
  have hu : u.J ≤ J := by omega
  have hc : c.J ≤ J := by omega
  have hiJ : (i : ℕ) < J := by have := i.isLt; omega
  set P := (projCLM hu).prod (projCLM hc)
  set c' := pd c.φ i
  set H : (Fin u.J → ℝ) × (Fin c.J → ℝ) → ℝ := fun p => u.φ p.1 * c' p.2
  have hc'1 : ContDiff ℝ ∞ c' := contDiff_pd c.smooth i
  have hH : ContDiff ℝ ∞ H := (u.smooth.comp contDiff_fst).mul (hc'1.comp contDiff_snd)
  have hHc : HasCompactSupport H := hasCompactSupport_prod_mul u.compact (hasCompactSupport_pd c.compact i)
  obtain ⟨B, hB1, hB2, hBc, hBd, hBder⟩ := exists_bounds_comp hH hHc P
  have hs := stein_row hγ hPSD hC (hY i) hBd hBc hB1 hB2 hiJ
  have hPb : ∀ z, P (zBlock J z) = (zBlock u.J z, zBlock c.J z) := fun z => rfl
  have hPv : P (Pi.single ⟨i, hiJ⟩ 1) = (projCLM hu (Pi.single ⟨i, hiJ⟩ 1), Pi.single i 1) := by
    refine Prod.ext rfl ?_
    show projCLM hc (Pi.single ⟨i, hiJ⟩ 1) = Pi.single i 1
    rw [projCLM_single, dif_pos i.isLt]
  have hud : ∀ z, fderiv ℝ u.φ (zBlock u.J z) (projCLM hu (Pi.single ⟨i, hiJ⟩ 1)) = u.dd i z :=
    fun z => by
      rw [projCLM_single]
      unfold Cyl.dd
      split_ifs with h
      · rfl
      · simp
  calc ∫ z, (z i + Y i z) * (u.eval z * c.dd i z) ∂γ
      = ∫ z, (z i + Y i z) * H (P (zBlock J z)) ∂γ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [H, hPb, Cyl.eval_eq, c.dd_of_lt i.isLt]
        rfl
    _ = ∫ z, fderiv ℝ (fun y => H (P y)) (zBlock J z) (Pi.single ⟨i, hiJ⟩ 1) ∂γ := hs
    _ = ∫ z, (u.dd i z * c.dd i z + u.eval z * c.dd2 i z) ∂γ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        show fderiv ℝ (fun y => H (P y)) (zBlock J z) (Pi.single ⟨i, hiJ⟩ 1) =
          u.dd i z * c.dd i z + u.eval z * c.dd2 i z
        rw [hBder, ContinuousLinearMap.comp_apply, hPb, hPv,
          fderiv_prod_mul_apply (u.smooth.differentiable (by simp)) (hc'1.differentiable (by simp)),
          hud, c.dd_of_lt i.isLt]
        rfl

theorem Cyl.exists_eval_bound (c : Cyl) : ∃ B, ∀ z, |c.eval z| ≤ B := by
  obtain ⟨B, hB1, -, -, -⟩ := exists_bounds_of_cc c.smooth c.compact
  exact ⟨B, fun z => hB1 _⟩

theorem Cyl.measurable_eval (c : Cyl) : Measurable c.eval :=
  measurable_comp_block c.smooth.continuous

theorem Cyl.exists_dd2_bound (c : Cyl) (i : Fin c.J) : ∃ B, ∀ z, |c.dd2 i z| ≤ B := by
  obtain ⟨B, -, hB2, -, -⟩ := exists_bounds_of_cc (contDiff_pd c.smooth i) (hasCompactSupport_pd c.compact i)
  exact ⟨B, fun z => abs_pd_le hB2 i _⟩

theorem Cyl.measurable_dd2 (c : Cyl) (i : Fin c.J) : Measurable (c.dd2 i) :=
  measurable_comp_block ((((contDiff_pd c.smooth i).continuous_fderiv (by simp))).clm_apply
    continuous_const)

theorem integrable_of_bdd_gamma {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {f : (ℕ → ℝ) → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ z, |f z| ≤ B) : Integrable f γ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)

/-- **Integration by parts for cylinders**: `∫ u (-L c) dγ = ∑_i λ_i ∫ ∂_i u ∂_i c dγ`. -/
theorem cyl_ibp {T : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i)) (lam' : ℕ → ℝ) (u c : Cyl) :
    ∫ z, u.eval z * (-(c.gen lam' Y z)) ∂γ =
      ∑ i : Fin c.J, lam' i * ∫ z, u.dd i z * c.dd i z ∂γ := by
  haveI := hγ.1
  obtain ⟨Bu, hBu⟩ := u.exists_eval_bound
  obtain ⟨Bc, hBc⟩ := c.exists_dd_bound
  obtain ⟨Bu', hBu'⟩ := u.exists_dd_bound
  have hX : ∀ i : Fin c.J, Integrable (fun z => (z i + Y i z) * (u.eval z * c.dd i z)) γ := fun i =>
    (((integrable_coord_gamma hγ i).add ((hY i).1.integrable one_le_two)).bdd_mul (c := Bu * Bc)
      (u.measurable_eval.mul (c.measurable_dd i)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        show ‖u.eval z * c.dd i z‖ ≤ Bu * Bc
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hBu z) (hBc i z) (abs_nonneg _) ((abs_nonneg _).trans (hBu z)))).congr
      (Eventually.of_forall fun z => mul_comm _ _)
  have hU : ∀ i : Fin c.J, Integrable (fun z => u.eval z * c.dd2 i z) γ := fun i => by
    obtain ⟨B2, hB2⟩ := c.exists_dd2_bound i
    exact integrable_of_bdd_gamma (u.measurable_eval.mul (c.measurable_dd2 i)) (B := Bu * B2) fun z => by
      rw [abs_mul]; exact mul_le_mul (hBu z) (hB2 z) (abs_nonneg _) ((abs_nonneg _).trans (hBu z))
  have hDD : ∀ i : Fin c.J, Integrable (fun z => u.dd i z * c.dd i z) γ := fun i =>
    integrable_of_bdd_gamma ((u.measurable_dd i).mul (c.measurable_dd i)) (B := Bu' * Bc) fun z => by
      rw [abs_mul]; exact mul_le_mul (hBu' i z) (hBc i z) (abs_nonneg _) ((abs_nonneg _).trans (hBu' i z))
  have hpt : ∀ z, u.eval z * (-(c.gen lam' Y z)) =
      ∑ i : Fin c.J, lam' i * ((z i + Y i z) * (u.eval z * c.dd i z) - u.eval z * c.dd2 i z) := by
    intro z
    unfold Cyl.gen
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : c.dd2 i z = fderiv ℝ (fun x => fderiv ℝ c.φ x (Pi.single i 1)) (fun j => z j)
        (Pi.single i 1) := rfl
    have e2 : pd c.φ i (zBlock c.J z) = fderiv ℝ c.φ (fun j => z j) (Pi.single i 1) := rfl
    rw [c.dd_of_lt i.isLt, e1, e2]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum (f := fun (i : Fin c.J) z =>
      lam' i * ((z i + Y i z) * (u.eval z * c.dd i z) - u.eval z * c.dd2 i z))
    _ fun i _ => ((hX i).sub (hU i)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_sub (hX i) (hU i), cyl_ibp_term hγ hPSD hC hY u c i,
    integral_add (hDD i) (hU i)]
  ring

end SharpLSI
