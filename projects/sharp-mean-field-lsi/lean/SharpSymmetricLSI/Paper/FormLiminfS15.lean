import SharpSymmetricLSI.Paper.FormLiminfS4
import SharpSymmetricLSI.Paper.FormLiminfS8a
import SharpSymmetricLSI.Paper.TestEnergy8
import SharpSymmetricLSI.Paper.ForceApprox4
import SharpSymmetricLSI.Statements.R19_Lemma_5_2

/-!
# (8.20) (lane s42): `E[f_k H(Z_{N_k})] → E_γ[F H(z)]`

`tendsto_mul_fluct_law`: `tendsto_integral_mul_of_law` (Paper/FormLiminfS4) with `T_k = f_k`,
`Z_k = (fluct e N_k n)_{n<J}`. The fourth moments of the fluctuations under `P_N` are uniformly
bounded (`fourth_moment_zq`, Paper/FormLiminfS8a, with the `C¹` representatives `eC` of R23 and
`fluct = zC` a.e., `zC_ae_eq_fluct`; `N = 0` is trivial since then `fluct = 0`), and under `γ`
each coordinate is Gaussian, hence in `L⁴`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **`E[f_k H(Z_{N_k})] → E_γ[F H(z)]`.** -/
theorem tendsto_mul_fluct_law (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) {C : ℕ → ℕ → ℝ}
    (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Ns : ℕ → ℕ} (hNs : Tendsto Ns atTop atTop) {f : (k : ℕ) → Config (Ns k) d → ℝ}
    (hfm : ∀ k, AEStronglyMeasurable (f k) (gibbs V W (Ns k))) {B : ℝ}
    (hf2 : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ B)
    (hUI : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, ∫⁻ X in {X | M < f k X ^ 2},
      ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k) ≤ ENNReal.ofReal ε)
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ) {J : ℕ}
    (hlaw : ∀ g : ℝ × (Fin J → ℝ) →ᵇ ℝ, Tendsto (fun k => ∫ X, g (f k X,
      fun n => fluct e (Ns k) n X) ∂gibbs V W (Ns k)) atTop (𝓝 (∫ z, g (F z, fun n => z n) ∂γ)))
    {H : (Fin J → ℝ) → ℝ} (hH : Continuous H) {A : ℝ} (hHb : ∀ z, |H z| ≤ A * (1 + ∑ j, |z j|)) :
    Tendsto (fun k => ∫ X, f k X * H (fun n => fluct e (Ns k) n X) ∂gibbs V W (Ns k)) atTop
      (𝓝 (∫ z, F z * H (fun n => z n) ∂γ)) := by
  have := hγ.1
  have : ∀ k, IsProbabilityMeasure (gibbs V W (Ns k)) := fun k =>
    gibbs_isProbabilityMeasure hyp (Ns k)
  set μm := (μ : Measure (Torus d))
  -- `C¹` representatives and the moment bound
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  have hpart : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => μm) ≤ Bp := ⟨Cp, p, hp, fun N hN => (hCp N hN).2.2⟩
  choose K4 hK4 using fun q : ℕ => fourth_moment_zq hyp hμ he (fun j => (heC j).1)
    (fun j => (heC j).2.1) hpart q
  have hac : μm ≪ haar d := minimizer_ac hyp hμ
  have hPac : ∀ N, gibbs V W N ≪ Measure.pi (fun _ : Fin N => μm) := fun N => by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  -- `fluct = zC` a.e. under `P_N`
  have hZae : ∀ N, ∀ᵐ X ∂gibbs V W N, zC eC N J X = fun n : Fin J => fluct e N n X := fun N =>
    hPac N (zC_ae_eq_fluct hac (fun j => (heC j).2.1) N J)
  have hzCm : ∀ N, Measurable (zC eC N J) := fun N => by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_const.mul (Finset.measurable_sum _ fun l _ =>
      (measurable_of_contDiff (heC (i + 1)).1).comp (measurable_pi_apply l))
  have hZm : ∀ k, AEStronglyMeasurable (fun X => fun n : Fin J => fluct e (Ns k) n X)
      (gibbs V W (Ns k)) := fun k =>
    (hzCm (Ns k)).aestronglyMeasurable.congr (hZae (Ns k))
  -- the constant
  set K := max B (∑ j : Fin J, |K4 j|)
  have hZ4 : ∀ k (j : Fin J), Integrable (fun X => fluct e (Ns k) j X ^ 4) (gibbs V W (Ns k)) ∧
      ∫ X, fluct e (Ns k) j X ^ 4 ∂gibbs V W (Ns k) ≤ K := fun k j => by
    have hKj : K4 j ≤ K := (le_abs_self _).trans ((Finset.single_le_sum (f := fun j : Fin J =>
      |K4 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans (le_max_right _ _))
    have hK0 : 0 ≤ K := (abs_nonneg _).trans ((Finset.single_le_sum (f := fun j : Fin J =>
      |K4 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans (le_max_right _ _))
    rcases Nat.eq_zero_or_pos (Ns k) with h0 | hpos
    · -- no particles: `fluct = 0`
      have hz : ∀ X : Config (Ns k) d, fluct e (Ns k) j X = 0 := fun X => by
        unfold fluct
        rw [show (∑ l : Fin (Ns k), e (j + 1) (X l)) = 0 by
          rw [Finset.sum_eq_zero]; intro l _; exact absurd l.2 (by omega), mul_zero]
      simp only [hz]
      refine ⟨by simp, by simpa using hK0⟩
    · obtain ⟨hi, hb⟩ := hK4 j (Ns k) hpos
      have hae : (fun X => ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (j + 1) (X l)) ^ 4) =ᵐ[gibbs V W (Ns k)]
          fun X => fluct e (Ns k) j X ^ 4 := by
        filter_upwards [hZae (Ns k)] with X hX
        have := congrFun hX j
        simp only [zC] at this
        rw [this]
      exact ⟨hi.congr hae, (integral_congr_ae hae).symm.le.trans (hb.trans hKj)⟩
  have hT2 : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ K := fun k => (hf2 k).trans (le_max_left _ _)
  -- Gaussian coordinates are in `L⁴`
  have hz4 : ∀ j : Fin J, MemLp (fun z : ℕ → ℝ => z j) 4 γ := fun j => by
    have hmap : γ.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 (C j j).toNNReal := by
      have := hγ.2 {(j : ℕ)} (fun _ => 1)
      simpa using this
    have hg : MemLp id (4 : ℝ≥0) (γ.map (fun z : ℕ → ℝ => z j)) := by
      rw [hmap]; exact memLp_id_gaussianReal 4
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_pi_apply (j : ℕ)).aemeasurable).1 hg
  exact tendsto_integral_mul_of_law (fun k => gibbs V W (Ns k)) (fun k => f k)
    (fun k X n => fluct e (Ns k) n X) hfm hZm hF hlaw hUI hT2 hZ4 hz4 hH hHb

end SharpLSI
