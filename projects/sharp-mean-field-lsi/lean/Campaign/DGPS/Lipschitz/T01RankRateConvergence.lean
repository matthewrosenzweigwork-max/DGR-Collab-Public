import DGPS.Lipschitz.T01CovarianceMatrix
import DGPS.Lipschitz.T01FiniteRankPositivity
import FullLabeledLSI.Paper.Prop23HAltA

/-!
# Rank convergence for the actual direct-Lipschitz covariance

The finite arrays retain the smoothing parameters of the same finite-rank witness. The
comparison uses only the actual Hessian coercivity and the proved coefficient convergence.
-/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology KernelApproximation
open scoped InnerProductSpace

private theorem rank_lamG_tendsto_of_hs
    {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {e : ℕ → Torus d → ℝ} {T C : ℕ → ℕ → ℝ} {σ : ℝ}
    (P : SharpLSI.FL.Rank3.SymPkg T C σ)
    (F : SharpLSI.FL.FiniteRankApprox W μ e) (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, SharpLSI.IsInverseOfIPlus (F.a R) (CR R))
    (b : ℕ → ℝ) (hb0 : ∀ R, 0 ≤ b R) (hb : Tendsto b atTop (𝓝 0))
    (hHS : ∀ R n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (T i j - F.a R i j) ^ 2 ≤ (b R) ^ 2) (lam : ℕ → ℝ) :
    Tendsto (fun R => SharpLSI.lamG lam (CR R)) atTop (𝓝 (SharpLSI.lamG lam C)) := by
  let ST := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2
  have hST0 : 0 ≤ ST := tsum_nonneg fun _ => sq_nonneg _
  have hΛpos : 0 < 3 / 2 + ST / 2 := by linarith
  let c : ℝ := (3 / 2 + ST / 2)⁻¹
  have hcpos : 0 < c := inv_pos.2 hΛpos
  have hσ2 : 0 < σ / 2 := half_pos P.pos
  let η : ℕ → ℝ := fun R => b R / (σ * (σ / 2))
  have hη0 : ∀ R, 0 ≤ η R := fun R => div_nonneg (hb0 R) (mul_nonneg P.pos.le hσ2.le)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    simpa only [zero_div] using hb.div_const (σ * (σ / 2))
  refine SharpLSI.FL.Rank3.tendsto_of_ratio hcpos hηlim hη0 ?_
  filter_upwards [hCR, hb.eventually (gt_mem_nhds hσ2),
    hηlim.eventually (gt_mem_nhds (half_pos hcpos))] with R hCRR hbR hηR
  have hSa : Summable fun p : ℕ × ℕ => F.a R p.1 p.2 ^ 2 := by
    refine summable_of_ne_finset_zero (s := F.s R ×ˢ F.s R) fun p hp => ?_
    have hp' : p.1 ∉ F.s R ∨ p.2 ∉ F.s R := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hp (Finset.mem_product.2 h)
    rw [F.supp R p.1 p.2 hp']; norm_num
  have Pa : SharpLSI.FL.Rank3.SymPkg (F.a R) (CR R) (σ / 2) :=
    ⟨F.symm R, hSa, hσ2, fun n y => by
      have h := SharpLSI.FL.Rank2.secOp_ge_of_close (hb0 R) P.sec (hHS R) n y
      have hy : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (by linarith : 0 ≤ σ / 2 - b R) hy], hCRR⟩
  refine SharpLSI.FL.Rank3.lamG_close hcpos (hη0 R) hηR.le ?_ ?_
  · intro v hv
    have h := P.Qlower hv
    simpa only [c, ST, inv_mul_eq_div] using h
  · intro v hv
    exact SharpLSI.FL.Rank3.Q_close P Pa (hb0 R) (hHS R) hv

theorem positiveKernelCoefficient_eq_shift {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m i j : ℕ) :
    positiveKernelCoefficient S D t m i j =
      kernelCoefficient_LIP016 S D t m (i + 1) (j + 1) := by
  have hi : i < m ↔ i + 1 ≤ m := by omega
  have hj : j < m ↔ j + 1 ≤ m := by omega
  simp only [positiveKernelCoefficient, kernelCoefficient_LIP016, hi, hj]

/-- Rank-rate convergence for the same finite-rank coefficients and their genuine inverses. -/
theorem t01_lamG_rank_tendsto {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g))
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (htlim : Tendsto t atTop (𝓝 0)) (hm : StrictMono m)
    (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j)
    (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, SharpLSI.IsInverseOfIPlus (F.a R) (CR R)) :
    Tendsto (fun R => SharpLSI.lamG (SharpLSI.lamShift S.lam) (CR R)) atTop
      (𝓝 (SharpLSI.lamG (SharpLSI.lamShift S.lam) (t01CovarianceMatrix S J))) := by
  let T := SharpLSI.Tmat J.W S.mu S.v
  let q (R : ℕ) (p : ℕ × ℕ) := (T p.1 p.2 - F.a R p.1 p.2) ^ 2
  have hsT := t01_shifted_pair_summable (fun p : ℕ × ℕ => TK S D.K p.1 p.2 ^ 2)
    (hasSum_prod_sq S D).summable
  have hqeq : ∀ R p, q R p =
      (kernelCoefficient_LIP016 S D (t R) (m R) (p.1 + 1) (p.2 + 1) -
        TK S D.K (p.1 + 1) (p.2 + 1)) ^ 2 := by
    intro R p
    dsimp only [q, T]
    rw [t01_Tmat_eq_TK S D J hD, ha, positiveKernelCoefficient_eq_shift]
    ring
  have hqbound : ∀ R p, q R p ≤ TK S D.K (p.1 + 1) (p.2 + 1) ^ 2 := by
    intro R p
    rw [hqeq]
    exact kernelCoefficient_error_le_LIP016 S D (ht R) (m R) (p.1 + 1) (p.2 + 1)
  have hqs : ∀ R, Summable (q R) := fun R =>
    Summable.of_nonneg_of_le (fun p => sq_nonneg _) (hqbound R) hsT
  have hq : Tendsto (fun R => ∑' p, q R p) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hsT (f := q) (g := fun _ => (0 : ℝ))
      (fun p => by
        simp_rw [hqeq]
        simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
          ((kernelCoefficient_tendsto_LIP016 S D t m htlim hm (p.1 + 1) (p.2 + 1)).sub_const
            (TK S D.K (p.1 + 1) (p.2 + 1))).pow 2)
      (Eventually.of_forall fun R p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hqbound R p)
    simpa only [tsum_zero] using h
  let b (R : ℕ) := Real.sqrt (∑' p, q R p)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hq.sqrt
  apply rank_lamG_tendsto_of_hs (t01CovarianceMatrix_symPkg S aux J D hD hσ hH) F CR hCR
    b (fun R => Real.sqrt_nonneg _) hb
  intro R n
  have hb2 : b R ^ 2 = ∑' p, q R p :=
    Real.sq_sqrt (tsum_nonneg (fun p => sq_nonneg _))
  rw [hb2]
  have h := (hqs R).sum_le_tsum (Finset.range n ×ˢ Finset.range n)
    (fun p _ => sq_nonneg (T p.1 p.2 - F.a R p.1 p.2))
  rw [Finset.sum_product] at h
  exact h

/-- The finite-rank comparison rates converge on the same approximation witness. -/
theorem t01_bRate_rank_tendsto {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g))
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (htlim : Tendsto t atTop (𝓝 0)) (hm : StrictMono m)
    (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j)
    (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, SharpLSI.IsInverseOfIPlus (F.a R) (CR R)) :
    Tendsto (fun R => SharpLSI.FL.bRate S.mu S.lam (CR R)) atTop
      (𝓝 (SharpLSI.FL.bRate S.mu S.lam (t01CovarianceMatrix S J))) := by
  unfold SharpLSI.FL.bRate
  exact tendsto_const_nhds.min
    (t01_lamG_rank_tendsto S aux J D hD hσ hH t m ht htlim hm F ha CR hCR)

end DGPS.Lipschitz
