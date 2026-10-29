import SharpSymmetricLSI.Paper.LemmaA2_11

/-!
# R25 (A.9), part 12: the limit equation

If `ρₙ → ρ` pointwise (bounded), `Φₙ → h` and `uₙ → u` uniformly (`uₙ` `C¹` with uniformly bounded
gradients, `u` Lipschitz) and `∫ ρₙ(Φₙ - uₙ)Θ = -τ ∫ uₙ div(ρₙ∇Θ)` for smooth periodic `Θ`, then
`∫ ρ(h - u)Θ = τ ∫ ρ ∇u·∇Θ` (`limit_resolvent_eq`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem integral_u_divRho {ρ u : Torus d → ℝ} (hρs : ContDiff ℝ ∞ (ρ ∘ liftT))
    (hu : ContDiff ℝ 1 (u ∘ liftT)) {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    ∫ y, u y * divRho ρ Θ (secT y) = -∑ k, ∫ y, dpart u k y * (ρ y * Dk Θ k (secT y)) := by
  set Ψ : Fin d → (Fin d → ℝ) → ℝ := fun k z => ρ (liftT z) * Dk Θ k z
  have hΨ : ∀ k, ContDiff ℝ ∞ (Ψ k) := fun k => hρs.mul (contDiff_Dk hΘ k)
  have hΨp : ∀ k, IsPer (Ψ k) := fun k m z => by simp only [Ψ, liftT_add_intVec, hp.Dk k m z]
  have huc : Continuous u := continuous_of_liftT' hu.continuous
  have hdc : ∀ k, Continuous (dpart u k) := fun k =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (by simpa using hu) k).continuous
  have hw := isWeakGrad_of_contDiff hu
  have hibp : ∀ k, ∫ y, u y * Dk (Ψ k) k (secT y) = -∫ y, dpart u k y * (ρ y * Dk Θ k (secT y)) := by
    intro k
    have := integral_mul_Dk_eq hw (integrable_of_continuous_torus' huc)
      (fun j => integrable_of_continuous_torus' (hdc j)) (hΨ k) (hΨp k) k
    rw [this]
    congr 2; funext y; simp [Ψ, liftT_secT, dpart]
  have hi : ∀ k ∈ Finset.univ, Integrable fun y => u y * Dk (Ψ k) k (secT y) := fun k _ =>
    integrable_of_continuous_torus' (huc.mul (continuous_comp_secT
      (contDiff_Dk (hΨ k) k).continuous ((hΨp k).Dk k)))
  have e : (fun y => u y * divRho ρ Θ (secT y)) = fun y => ∑ k, u y * Dk (Ψ k) k (secT y) := by
    funext y; simp only [divRho, Finset.mul_sum, Ψ]
  rw [e, integral_finset_sum _ hi, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => hibp k

/-- **The limit equation.** -/
theorem limit_resolvent_eq {ρ : Torus d → ℝ} (hρc : Continuous ρ) {ρn : ℕ → Torus d → ℝ}
    (hρns : ∀ n, ContDiff ℝ ∞ (ρn n ∘ liftT)) {Cρ : ℝ} (hρnb : ∀ n y, |ρn n y| ≤ Cρ)
    (hρnt : ∀ y, Tendsto (fun n => ρn n y) atTop (𝓝 (ρ y)))
    {Φn : ℕ → (Fin d → ℝ) → ℝ} (hΦs : ∀ n, ContDiff ℝ ∞ (Φn n)) (hΦp : ∀ n, IsPer (Φn n))
    {h : Torus d → ℝ} {BΦ : ℝ} (hΦb : ∀ n y, |Φn n (secT y)| ≤ BΦ)
    (hΦt : ∀ y, Tendsto (fun n => Φn n (secT y)) atTop (𝓝 (h y)))
    {u : ℕ → Torus d → ℝ} (hu : ∀ n, ContDiff ℝ 1 (u n ∘ liftT)) {D : ℝ}
    (hD : ∀ n k y, |dpart (u n) k y| ≤ D) (hD0 : 0 ≤ D) {Bu : ℝ} (hub : ∀ n y, |u n y| ≤ Bu)
    {u₀ : Torus d → ℝ} (hconv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ y, |u n y - u₀ y| ≤ ε)
    (hu₀ : Continuous u₀) {L : ℝ≥0} (hL : LipschitzWith L (u₀ ∘ liftT)) {τ : ℝ}
    (heq : ∀ n, ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, ρn n y * (Φn n (secT y) - u n y) * Θ (secT y) =
        -τ * ∫ y, u n y * divRho (ρn n) Θ (secT y))
    {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    ∫ y, ρ y * (h y - u₀ y) * Θ (secT y) =
      τ * ∫ y, ρ y * ∑ k, lipGrad u₀ y k * Dk Θ k (secT y) := by
  have hρnc : ∀ n, Continuous (ρn n) := fun n => continuous_of_liftT' (hρns n).continuous
  have hΘc : Continuous fun y => Θ (secT y) := continuous_comp_secT hΘ.continuous hp
  obtain ⟨BΘ, hBΘ⟩ := periodic_bounded hΘ.continuous hp
  have hDΘ : ∀ k, ∃ B, ∀ x, ‖Dk Θ k x‖ ≤ B := fun k =>
    periodic_bounded (contDiff_Dk hΘ k).continuous (hp.Dk k)
  choose BD hBD using hDΘ
  have hDΘc : ∀ k, Continuous fun y => Dk Θ k (secT y) := fun k =>
    continuous_comp_secT (contDiff_Dk hΘ k).continuous (hp.Dk k)
  have hut : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (u₀ y)) := fun y => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; linarith [hN n hn y]⟩
  have hΦc : ∀ n, Continuous fun y => Φn n (secT y) := fun n =>
    continuous_comp_secT (hΦs n).continuous (hΦp n)
  have huc : ∀ n, Continuous (u n) := fun n => continuous_of_liftT' (hu n).continuous
  have hdc : ∀ n k, Continuous (dpart (u n) k) := fun n k =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (by simpa using hu n) k).continuous
  obtain ⟨Bρ, hBρ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  -- left side
  have hL1 : Tendsto (fun n => ∫ y, ρn n y * (Φn n (secT y) - u n y) * Θ (secT y)) atTop
      (𝓝 (∫ y, ρ y * (h y - u₀ y) * Θ (secT y))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Cρ * (BΦ + Bu) * BΘ)
      (fun n => (((hρnc n).mul ((hΦc n).sub (huc n))).mul hΘc).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ((hρnt y).mul ((hΦt y).sub (hut y))).mul_const _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul (hρnb n y) ((abs_sub _ _).trans (add_le_add (hΦb n y) (hub n y)))
      (abs_nonneg _) ((abs_nonneg _).trans (hρnb n y))) (by rw [← Real.norm_eq_abs]; exact hBΘ _)
      (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans (hρnb n y))
        ((abs_nonneg _).trans ((abs_sub _ _).trans (add_le_add (hΦb n y) (hub n y)))))
  -- right side
  have hR : ∀ n, ∫ y, ρn n y * (Φn n (secT y) - u n y) * Θ (secT y) =
      τ * ∑ k, ∫ y, dpart (u n) k y * (ρn n y * Dk Θ k (secT y)) := by
    intro n
    rw [heq n Θ hΘ hp, integral_u_divRho (hρns n) (hu n) hΘ hp]
    ring
  have hk : ∀ k, Tendsto (fun n => ∫ y, dpart (u n) k y * (ρn n y * Dk Θ k (secT y))) atTop
      (𝓝 (∫ y, lipGrad u₀ y k * (ρ y * Dk Θ k (secT y)))) := by
    intro k
    have hA := tendsto_integral_dpart_mul hu hD hconv hu₀ hL
      (ψ := fun y => ρ y * Dk Θ k (secT y)) (hρc.mul (hDΘc k)) k
    have hB : Tendsto (fun n => ∫ y, dpart (u n) k y * ((ρn n y - ρ y) * Dk Θ k (secT y)))
        atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Torus d)))
        (F := fun n y =>
          dpart (u n) k y * ((ρn n y - ρ y) * Dk Θ k (secT y))) (f := fun _ => (0 : ℝ))
        (fun _ => D * ((Cρ + Bρ) * BD k))
        (fun n => ((hdc n k).mul (((hρnc n).sub hρc).mul (hDΘc k))).aestronglyMeasurable)
        (integrable_const _) (fun n => Eventually.of_forall fun y => ?_)
        (Eventually.of_forall fun y => ?_)
      · simpa using this
      · rw [Real.norm_eq_abs, abs_mul, abs_mul]
        refine mul_le_mul (hD n k y) (mul_le_mul ((abs_sub _ _).trans (add_le_add (hρnb n y)
          (by simpa [Real.norm_eq_abs] using hBρ y (mem_univ _))))
          (by rw [← Real.norm_eq_abs]; exact hBD k _) (abs_nonneg _)
          ((abs_nonneg _).trans ((abs_sub _ _).trans (add_le_add (hρnb n y)
            (by simpa [Real.norm_eq_abs] using hBρ y (mem_univ _)))))) (by positivity) hD0
      · have h0 : Tendsto (fun n => ρn n y - ρ y) atTop (𝓝 0) := by
          simpa using (hρnt y).sub_const (ρ y)
        refine squeeze_zero_norm (a := fun n => D * (|ρn n y - ρ y| * BD k)) (fun n => ?_) ?_
        · rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul (hD n k y) (mul_le_mul_of_nonneg_left
            (by rw [← Real.norm_eq_abs]; exact hBD k _) (abs_nonneg _))
            (by positivity) hD0
        · have := ((h0.abs).mul_const (BD k)).const_mul D
          simpa using this
    have hsum := hB.add hA
    rw [zero_add] at hsum
    refine hsum.congr fun n => ?_
    rw [← integral_add]
    · congr 1; funext y; ring
    · exact integrable_of_continuous_torus' ((hdc n k).mul (((hρnc n).sub hρc).mul (hDΘc k)))
    · exact integrable_of_continuous_torus' ((hdc n k).mul (hρc.mul (hDΘc k)))
  have hRt := (tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun k _ => hk k).const_mul τ
  have hlim := tendsto_nhds_unique hL1 (hRt.congr fun n => (hR n).symm)
  rw [hlim]
  congr 1
  have hint : ∀ k ∈ Finset.univ, Integrable fun y => lipGrad u₀ y k * (ρ y * Dk Θ k (secT y)) :=
    fun k _ => (integrable_of_continuous_torus' (hρc.mul (hDΘc k))).bdd_mul (c := L)
      (measurable_lipGrad hu₀ k).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_lipGrad_le hL y k)
  rw [← integral_finset_sum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

end SharpLSI
