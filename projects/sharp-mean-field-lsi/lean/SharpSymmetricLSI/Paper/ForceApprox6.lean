import SharpSymmetricLSI.Paper.ForceApprox5

/-!
# R31: (7.11)
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable {φ : ℕ → Torus d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i ∘ liftT)) (s : Finset ℕ)
  (a : ℕ → ℕ → ℝ)
include hφ

theorem measurable_finKerD (k : Fin d) :
    Measurable (Function.uncurry fun x y => finKerD φ s a x y k) := by
  unfold finKerD
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_const.mul ((measurable_cgrad (hφ i) k).comp measurable_fst)).mul
    ((measurable_of_contDiff (hφ j)).comp measurable_snd)

theorem measurable_finKerD_diag (k : Fin d) :
    Measurable fun x => finKerD φ s a x x k := by
  unfold finKerD
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_const.mul (measurable_cgrad (hφ i) k)).mul (measurable_of_contDiff (hφ j))

theorem exists_bound_finKerD : ∃ C, 0 ≤ C ∧ ∀ x y k, |finKerD φ s a x y k| ≤ C := by
  choose B hB using fun i => exists_bound_of_contDiff (hφ i)
  choose B' hB' using fun i => exists_bound_cgrad (hφ i)
  refine ⟨∑ i ∈ s, ∑ j ∈ s, |a i j| * |B' i| * |B j|, by positivity, fun x y k => ?_⟩
  unfold finKerD
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left ((hB' i x k).trans (le_abs_self _)) (abs_nonneg _))
    ((hB j y).trans (le_abs_self _)) (abs_nonneg _) (by positivity)

end

/-- **(7.11)**. -/
theorem force_identity (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR) (R N : ℕ) (hN : 1 ≤ N) :
    ∫ X, gradSqC (fun Y => Ucentered W μ N Y - UkernelF (KR R) N Y) X
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      ((N : ℝ) - 1) / N * ∫ x, ∫ y, sqNorm (fun k => bForce W μ x y k - grad1W (KR R) x y k)
          ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d)) +
        (N : ℝ)⁻¹ * ∫ x, sqNorm (fun k => bDiag W μ x k -
          weakGrad (fun z => KR R z z / 2) x k) ∂(μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  obtain ⟨s, a, ha, hK⟩ := hKR.1 R
  set φ : ℕ → Torus d → ℝ := fun i => eC (i + 1)
  have hφ : ∀ i, ContDiff ℝ 1 (φ i ∘ liftT) := fun i => (heC (i + 1)).1
  have hKRae := Ukernel_ae_finKer (fun j => (heC j).2.1) s a (hK) N
  have hgrad := weakGradC_diff_ae hyp hμ hφ s ha hN hKRae
  obtain ⟨-, hβm, ⟨Cβ, hCβ⟩, hβint⟩ := forceMean_props hyp hac
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  obtain ⟨CK, hCK0, hCK⟩ := exists_bound_finKerD hφ s a
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |Cb| + |Cβ| + CK := ⟨_, rfl⟩
  have hcm : ∀ k, Measurable (Function.uncurry fun x y => cOff W μm φ s a x y k) := fun k => by
    have h1 := measurable_bGrad hyp (W := W) k
    have h2 := measurable_finKerD hφ s a k
    have h3 := hβm k
    show Measurable fun p : Torus d × Torus d =>
      bGrad W p.1 p.2 k - bForceL W (densOf μm) p.1 k - finKerD φ s a p.1 p.2 k
    exact (h1.sub (h3.comp measurable_fst)).sub h2
  have hΔm : ∀ k, Measurable fun x => cDiag W μm φ s a x k := fun k => by
    have h2 := measurable_finKerD_diag hφ s a k
    have h3 := hβm k
    show Measurable fun x : Torus d => -bForceL W (densOf μm) x k - finKerD φ s a x x k
    exact h3.neg.sub h2
  have hcb : ∀ x y k, |cOff W μm φ s a x y k| ≤ M := fun x y k => by
    unfold cOff
    have := hCb x y k; have := hCβ x k; have := hCK x y k
    have h1 := abs_sub (bGrad W x y k - bForceL W (densOf μm) x k) (finKerD φ s a x y k)
    have h2 := abs_sub (bGrad W x y k) (bForceL W (densOf μm) x k)
    have := le_abs_self Cb; have := le_abs_self Cβ
    rw [hM]; linarith
  have hΔb : ∀ x k, |cDiag W μm φ s a x k| ≤ M := fun x k => by
    unfold cDiag
    have := hCβ x k; have := hCK x x k
    have h1 := abs_sub (-bForceL W (densOf μm) x k) (finKerD φ s a x x k)
    rw [abs_neg] at h1
    have := abs_nonneg Cb; have := le_abs_self Cβ
    rw [hM]; linarith
  -- centering
  have hcent : ∀ k, ∀ᵐ x ∂μm, ∫ y, cOff W μm φ s a x y k ∂μm = 0 := by
    intro k
    refine Eventually.of_forall fun x => ?_
    have hb : Integrable (fun y => bGrad W x y k) μm :=
      integrable_of_bdd ((measurable_bGrad hyp (W := W) k).of_uncurry_left (x := x))
        fun y => hCb x y k
    have hf : Integrable (fun y => finKerD φ s a x y k) μm :=
      integrable_of_bdd ((measurable_finKerD hφ s a k).of_uncurry_left (x := x))
        fun y => hCK x y k
    unfold cOff
    rw [integral_sub (f := fun y => bGrad W x y k - bForceL W (densOf μm) x k)
      (g := fun y => finKerD φ s a x y k) (hb.sub (integrable_const _)) hf,
      integral_sub (f := fun y => bGrad W x y k) (g := fun _ => bForceL W (densOf μm) x k) hb
        (integrable_const _),
      ← hβint x k, integral_const, probReal_univ, one_smul, sub_self, zero_sub, neg_eq_zero]
    unfold finKerD
    have hij : ∀ i j, Integrable (fun y => a i j * cgrad (φ i) x k * φ j y) μm := fun i j => by
      obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hφ j)
      exact (integrable_of_bdd (measurable_of_contDiff (hφ j)) hB).const_mul _
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hij i j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul]
    have h0 : ∫ y, φ j y ∂μm = 0 := by
      rw [integral_congr_ae (heC (j + 1)).2.2]
      have := he.orthonormal (j + 1) 0
      simp only [he.zero, mul_one, Nat.add_one_ne_zero, ↓reduceIte] at this
      exact this
    rw [h0, mul_zero]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- LHS
  have hL : ∫ X, gradSqC (fun Y => Ucentered W μ (n + 1) Y - UkernelF (KR R) (n + 1) Y) X
      ∂Measure.pi (fun _ : Fin (n + 1) => μm) =
      ∫ X, ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
        (∑ l ∈ Finset.univ.erase i, cOff W μm φ s a (X i) (X l) k + cDiag W μm φ s a (X i) k)) ^ 2
        ∂(Measure.pi fun _ : Fin (n + 1) => μm) := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with X hX
    unfold gradSqC
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hX i k]
  rw [hL, integral_forceSum_sq hcm hΔm hcb hΔb hcent]
  -- RHS: the off-diagonal force
  have hprod : μm.prod μm ≪ (haar d).prod (haar d) := hac.prod hac
  have hpair := weakGrad_ae_eq ((isWeakGrad_finKer_pair hφ s ha).congr_ae
    (pair_ae_finKer (fun j => (heC j).2.1) s a hK).symm)
  have hgrad1 : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k,
      grad1W (KR R) p.1 p.2 k = finKerD φ s a p.1 p.2 k := by
    filter_upwards [measurePreserving_pairFlat.quasiMeasurePreserving.ae hpair] with p hp k
    have e1 : grad1W (KR R) p.1 p.2 k = weakGrad (fun y : UnitAddTorus (Fin 2 × Fin d) =>
        KR R (projBlock 0 y) (projBlock 1 y)) (pairFlat p) (0, k) := rfl
    rw [e1, congrFun hp (0, k)]
    simp only [↓reduceIte]
    rfl
  have hoff : ∫ x, ∫ y, sqNorm (fun k => bForce W μ x y k - grad1W (KR R) x y k) ∂μm ∂μm =
      ∫ x, ∫ y, ∑ k, cOff W μm φ s a x y k ^ 2 ∂μm ∂μm := by
    have hae : (fun p : Torus d × Torus d =>
        sqNorm (fun k => bForce W μ p.1 p.2 k - grad1W (KR R) p.1 p.2 k)) =ᵐ[μm.prod μm]
        fun p => ∑ k, cOff W μm φ s a p.1 p.2 k ^ 2 := by
      filter_upwards [hprod.ae_le (bForce_ae_prod hyp hac), hprod.ae_le hgrad1] with p h1 h2
      unfold sqNorm cOff
      refine Finset.sum_congr rfl fun k _ => ?_
      beta_reduce
      rw [h1 k, h2 k]
    have hint : Integrable (fun p : Torus d × Torus d => ∑ k, cOff W μm φ s a p.1 p.2 k ^ 2)
        (μm.prod μm) :=
      integrable_finsetSum _ fun k _ => integrable_of_bdd ((hcm k).pow_const 2) (C := M ^ 2)
        fun p => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb _ _ k) 2
    rw [← integral_prod _ (hint.congr hae.symm), ← integral_prod _ hint]
    exact integral_congr_ae hae
  -- RHS: the diagonal force
  have hconv := weakGrad_ae_eq (forceMean_props hyp hac).1
  have hdiag := weakGrad_ae_eq ((isWeakGrad_finKer_diag hφ s ha).congr_ae
    (diag_ae_finKer (fun j => (heC j).2.1) s a hK).symm)
  have hon : ∫ x, sqNorm (fun k => bDiag W μ x k - weakGrad (fun z => KR R z z / 2) x k) ∂μm =
      ∫ x, ∑ k, cDiag W μm φ s a x k ^ 2 ∂μm := by
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le (particle_force_aux hyp hμ).1, hac.ae_le hconv, hac.ae_le hdiag]
      with x h1 h2 h3
    unfold sqNorm cDiag
    refine Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    rw [h1 k, congrFun h2 k, congrFun h3 k]
  rw [hoff, hon]
  push_cast
  ring

end SharpLSI
