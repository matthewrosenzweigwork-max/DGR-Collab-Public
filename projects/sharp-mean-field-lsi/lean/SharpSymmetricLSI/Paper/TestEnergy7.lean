import SharpSymmetricLSI.Paper.TestEnergy5
import SharpSymmetricLSI.Paper.TestEnergy6
import SharpSymmetricLSI.Paper.GroundT13

/-!
# R33 groundwork: the mobility converges in `L¹(P_N)` (manuscript Section 8.3)

Given the uniform `L^p(μ^{⊗N})` bound of the centered Gibbs density (Lemma 5.2, (5.6)),
`E_{P_N}|A_{N,ij} - λ_i δ_{ij}| → 0`.
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem abs_mobA_le {eC : ℕ → Torus d → ℝ} {i j : ℕ} {K : ℝ}
    (hK : ∀ x, |∑ k, cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k| ≤ K) (N : ℕ)
    (X : Config N d) : |mobA eC N X i j| ≤ K := by
  unfold mobA
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp only [Nat.cast_zero, inv_zero, zero_mul, abs_zero]
    exact (abs_nonneg _).trans (hK (Classical.arbitrary _))
  have hN : (0 : ℝ) < N := by exact_mod_cast h
  rw [abs_mul, abs_inv, abs_of_pos hN]
  calc (N : ℝ)⁻¹ * |∑ l, ∑ k, cgrad (eC (i + 1)) (X l) k * cgrad (eC (j + 1)) (X l) k|
      ≤ (N : ℝ)⁻¹ * ∑ _l : Fin N, K := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => hK (X l))
    _ = K := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

theorem measurable_mobA {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (N : ℕ)
    (i j : ℕ) : Measurable fun X : Config N d => mobA eC N X i j := by
  unfold mobA
  refine measurable_const.mul (Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun k _ => ?_)
  exact ((measurable_cgrad (hφ (i + 1)) k).comp (measurable_pi_apply l)).mul
    ((measurable_cgrad (hφ (j + 1)) k).comp (measurable_pi_apply l))

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

/-- **`E_{P_N}|A_{N,ij} - λ_i δ_{ij}| → 0`.** -/
theorem tendsto_gibbs_abs_mob (hpart : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp) (i j : ℕ) :
    Tendsto (fun N => ∫ X, |mobA eC N X i j - (if i = j then lam (i + 1) else 0)| ∂gibbs V W N)
      atTop (𝓝 0) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨Bp, p, hp1, hBp⟩ := hpart
  set q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  obtain ⟨B, hB⟩ := integral_mob_sub_sq hyp hμ he hφ heC i j
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  obtain ⟨Cj, hCj⟩ := exists_bound_cgrad (hφ (j + 1))
  have hg : ∀ x, |∑ k, cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k| ≤ d * (|Ci| * |Cj|) :=
    fun x => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k| ≤ ∑ _k : Fin d, |Ci| * |Cj| :=
            Finset.sum_le_sum fun k _ => by
              rw [abs_mul]
              exact mul_le_mul ((hCi x k).trans (le_abs_self _)) ((hCj x k).trans (le_abs_self _))
                (abs_nonneg _) (abs_nonneg _)
        _ = d * (|Ci| * |Cj|) := by simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = d * (|Ci| * |Cj|) + |lam (i + 1)| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hYb : ∀ N (X : Config N d), |mobA eC N X i j - (if i = j then lam (i + 1) else 0)| ≤ M :=
    fun N X => by
      refine (abs_sub _ _).trans ?_
      rw [hMdef]
      refine add_le_add (abs_mobA_le hg N X) ?_
      split_ifs <;> simp
  have hYm : ∀ N, Measurable fun X : Config N d =>
      mobA eC N X i j - (if i = j then lam (i + 1) else 0) := fun N =>
    (measurable_mobA hφ N i j).sub_const _
  have hbound : ∀ N : ℕ, 1 ≤ N →
      ∫ X, |mobA eC N X i j - (if i = j then lam (i + 1) else 0)| ∂gibbs V W N ≤
        Bp ^ (1 / p) * (M ^ (q - 1) * (B / N) ^ (1 / 2 : ℝ)) ^ (1 / q) := by
    intro N hN
    rw [integral_gibbs_eq' hyp hμ]
    obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm N
    have hK := centeredPartition_pos hyp μm N
    have hw0 : ∀ X, 0 ≤ rexp (-Ucentered W μm N X) / centeredPartition W μm N := fun X =>
      div_nonneg (exp_pos _).le hK.le
    have hwb : ∀ X, rexp (-Ucentered W μm N X) / centeredPartition W μm N ≤
        rexp BU / centeredPartition W μm N := fun X => by
      refine div_le_div_of_nonneg_right (exp_le_exp.2 ?_) hK.le
      have := hBU X; rw [abs_le] at this; linarith
    have hwm : Measurable fun X => rexp (-Ucentered W μm N X) / centeredPartition W μm N :=
      ((measurable_Ucentered hyp μm N).neg.exp).div_const _
    refine (integral_weight_abs_le hw0 hwm hwb (hYm N) hM0 (hYb N) hpq).trans ?_
    have hI0 : 0 ≤ ∫ X, (rexp (-Ucentered W μm N X) / centeredPartition W μm N) ^ p
        ∂Measure.pi (fun _ : Fin N => μm) := integral_nonneg fun X => rpow_nonneg (hw0 X) _
    have hY0 : 0 ≤ ∫ X, (mobA eC N X i j - (if i = j then lam (i + 1) else 0)) ^ 2
        ∂Measure.pi (fun _ : Fin N => μm) := integral_nonneg fun X => sq_nonneg _
    have hA := hBp N hN
    have hBn := hB N hN
    exact mul_le_mul (rpow_le_rpow hI0 hA (by positivity))
      (rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
        (rpow_le_rpow hY0 hBn (by norm_num)) (rpow_nonneg hM0 _)) (by positivity))
      (by positivity) (rpow_nonneg (hI0.trans hA) _)
  -- the bound tends to zero
  have h1 : Tendsto (fun N : ℕ => B / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat B
  have h2 : Tendsto (fun N : ℕ => (B / (N : ℝ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto).comp h1
    rwa [zero_rpow (by norm_num)] at this
  have h3 : Tendsto (fun N : ℕ => (M ^ (q - 1) * (B / (N : ℝ)) ^ (1 / 2 : ℝ)) ^ (1 / q))
      atTop (𝓝 0) := by
    have h2' : Tendsto (fun N : ℕ => M ^ (q - 1) * (B / (N : ℝ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := h2.const_mul (M ^ (q - 1)); rwa [mul_zero] at this
    have := ((continuousAt_rpow_const 0 (1 / q) (Or.inr (by positivity))).tendsto).comp h2'
    rw [zero_rpow (by positivity)] at this
    exact this
  have h4 := h3.const_mul (Bp ^ (1 / p))
  rw [mul_zero] at h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h4
    (Eventually.of_forall fun N => integral_nonneg fun X => abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact hbound N hN

end

end SharpLSI
