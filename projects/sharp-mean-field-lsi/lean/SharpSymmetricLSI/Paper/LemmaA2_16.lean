import SharpSymmetricLSI.Paper.LemmaA2_15

/-!
# R25 (A.9), part 16: the Euler formula and the Lipschitz bound for the semigroup

Iterating the Lipschitz resolvent `n` times with step `t/n` gives `gₙ` with
`Lip gₙ ≤ (1 - Kt/n)^{-n} L` and `⟨h, e_j⟩ = (1 + tλ_j/n)^n ⟨gₙ, e_j⟩`; the `gₙ` are uniformly
bounded (their `μ`-mean is that of `h`), so a subsequence converges uniformly to `g` with
`Lip g ≤ e^{Kt}L` and `⟨g, e_j⟩ = e^{-tλ_j}⟨h, e_j⟩` (`euler_lipschitz`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

section euler

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {K : ℝ}
  (hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
include hρ hρc hQ hb

theorem resolvent_iter (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (hKτ : K * τ < 1)
    {h : Torus d → ℝ} (hhc : Continuous h) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, h (liftT x) - h (liftT y) ≤ L * dE x y) {Bh0 : ℝ} (hhB : ∀ y, |h y| ≤ Bh0)
    (m : ℕ) :
    ∃ u : Torus d → ℝ, Continuous u ∧
      (∀ x y, u (liftT x) - u (liftT y) ≤ L / (1 - K * τ) ^ m * dE x y) ∧ (∀ y, |u y| ≤ Bh0) ∧
      ∀ j, ∫ y, h y * e j y ∂densMeasure ρ =
        (1 + τ * lam j) ^ m * ∫ y, u y * e j y ∂densMeasure ρ := by
  have hKτ' : 0 < 1 - K * τ := by linarith
  induction m with
  | zero => exact ⟨h, hhc, by simpa using hL, hhB, fun j => by simp⟩
  | succ m ih =>
    obtain ⟨u, huc, hul, huB, huj⟩ := ih
    obtain ⟨u', hu'c, hu'l, hu'B, hu'j⟩ := resolvent_core hd hρ hρc hQ hb hτ hKτ huc
      (div_nonneg hL0 (pow_nonneg hKτ'.le m)) hul huB
    refine ⟨u', hu'c, fun x y => ?_, hu'B, fun j => ?_⟩
    · have := hu'l x y
      rwa [div_div, ← pow_succ] at this
    · rw [huj j, hu'j j, pow_succ]; ring

/-- **Euler formula: the Lipschitz bound for the semigroup.** -/
theorem euler_lipschitz (hd : 1 ≤ d) (hK0 : 0 ≤ K) {t : ℝ} (ht : 0 < t)
    {h : Torus d → ℝ} (hhc : Continuous h) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, h (liftT x) - h (liftT y) ≤ L * dE x y) {Bh0 : ℝ} (hhB : ∀ y, |h y| ≤ Bh0) :
    ∃ g : Torus d → ℝ, Continuous g ∧ (∀ y, |g y| ≤ Bh0) ∧
      (∀ x y, g (liftT x) - g (liftT y) ≤ Real.exp (K * t) * L * dE x y) ∧
      ∀ j, ∫ y, g y * e j y ∂densMeasure ρ =
        Real.exp (-t * lam j) * ∫ y, h y * e j y ∂densMeasure ρ := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  -- choose the steps
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ n ≥ N0, K * (t / ((n : ℝ) + 1)) < 1 / 2 := by
    obtain ⟨N0, hN⟩ := exists_nat_gt (2 * K * t)
    refine ⟨N0, fun n hn => ?_⟩
    have hn' : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  set τ : ℕ → ℝ := fun n => t / (((n + N0 : ℕ) : ℝ) + 1)
  have hτ : ∀ n, 0 < τ n := fun n => by positivity
  have hKτ : ∀ n, K * τ n < 1 := fun n => (hN0 (n + N0) (by omega)).trans (by norm_num)
  have hit : ∀ n, ∃ u : Torus d → ℝ, Continuous u ∧
      (∀ x y, u (liftT x) - u (liftT y) ≤ L / (1 - K * τ n) ^ (n + N0 + 1) * dE x y) ∧
      (∀ y, |u y| ≤ Bh0) ∧
      ∀ j, ∫ y, h y * e j y ∂P = (1 + τ n * lam j) ^ (n + N0 + 1) * ∫ y, u y * e j y ∂P :=
    fun n => resolvent_iter hρ hρc hQ hb hd (hτ n) (hKτ n) hhc hL0 hL hhB (n + N0 + 1)
  choose g hgc hgl hgB hgj using hit
  -- the constants
  set Ln : ℕ → ℝ := fun n => L / (1 - K * τ n) ^ (n + N0 + 1)
  have hLim : Tendsto Ln atTop (𝓝 (Real.exp (K * t) * L)) := by
    have h1 := (Real.tendsto_one_add_div_pow_exp (-(K * t))).comp
      ((tendsto_add_atTop_iff_nat (N0 + 1)).mpr tendsto_id)
    have h2 : Tendsto (fun n => (1 - K * τ n) ^ (n + N0 + 1)) atTop (𝓝 (Real.exp (-(K * t)))) := by
      refine h1.congr fun n => ?_
      simp only [Function.comp, id, τ]
      push_cast; ring_nf
    have h3 := h2.inv₀ (Real.exp_pos _).ne'
    have h4 := h3.const_mul L
    rw [Real.exp_neg, inv_inv, mul_comm] at h4
    refine h4.congr fun n => ?_
    simp only [Ln, div_eq_mul_inv]
  have hLn0 : ∀ n, 0 ≤ Ln n := fun n =>
    div_nonneg hL0 (pow_nonneg (by linarith [hKτ n]) _)
  obtain ⟨Lmax, hLmax⟩ : ∃ Lmax, ∀ n, Ln n ≤ Lmax := by
    obtain ⟨B, hB⟩ := hLim.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hLmax0 : 0 ≤ Lmax := (hLn0 0).trans (hLmax 0)
  -- the means are preserved
  have hlam0 : lam 0 = 0 := refLam_zero hρ hb
  have hmean : ∀ n, ∫ y, g n y ∂P = ∫ y, h y ∂P := by
    intro n
    have := hgj n 0
    rw [hb.zero, hlam0] at this
    simpa using this.symm
  have hosc : ∀ n y z, |g n y - g n z| ≤ Lmax * d := by
    intro n y z
    obtain ⟨a, b, ha, hb', -, hab⟩ := dE_close_lifts hd y z
    rw [← ha, ← hb', abs_le]
    have h1 := hgl n a b
    have h2 := hgl n b a
    have hs : dE b a = dE a b := by
      simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs] at h2
    have h4 : Ln n * dE a b ≤ Lmax * d := by nlinarith [hLmax n, dE_nonneg a b, hLn0 n]
    simp only [Ln] at h4
    constructor <;> linarith
  obtain ⟨Bh, hBh⟩ := isCompact_univ.exists_bound_of_continuousOn hhc.continuousOn
  have hhi : Integrable h P := (integrable_const Bh).mono' hhc.aestronglyMeasurable
    (Eventually.of_forall fun y => hBh y (mem_univ _))
  have hgb : ∀ n y, |g n y| ≤ |∫ y, h y ∂P| + Lmax * d := by
    intro n y
    have hgi : Integrable (g n) P := by
      obtain ⟨B', hB'⟩ := isCompact_univ.exists_bound_of_continuousOn (hgc n).continuousOn
      exact (integrable_const B').mono' (hgc n).aestronglyMeasurable
        (Eventually.of_forall fun y => hB' y (mem_univ _))
    have e0 : g n y - ∫ z, h z ∂P = ∫ z, (g n y - g n z) ∂P := by
      rw [integral_sub (integrable_const _) hgi, hmean n]; simp
    have b1 : |∫ z, (g n y - g n z) ∂P| ≤ Lmax * d := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ z, |g n y - g n z| ∂P ≤ ∫ _z, Lmax * d ∂P :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
              (Eventually.of_forall fun z => hosc n y z)
        _ = Lmax * d := by simp
    rw [← e0] at b1
    have := abs_sub_abs_le_abs_sub (g n y) (∫ z, h z ∂P)
    linarith
  -- Arzelà–Ascoli
  have hLd : 0 ≤ Lmax * d := mul_nonneg hLmax0 (Nat.cast_nonneg _)
  obtain ⟨φ, hφ, v, hvc, hvconv⟩ := exists_subseq_unif_holder (X := Torus d) (κ := Unit)
    (fun n x _ => g n x) one_pos hLd
    (C := |∫ y, h y ∂P| + Lmax * d) (fun n x _ => hgb n x)
    (fun n x y _ => by
      obtain ⟨a, b, rfl, rfl, hab, -⟩ := dE_close_lifts hd x y
      rw [Real.rpow_one, abs_le]
      have h1 := hgl n a b
      have h2 := hgl n b a
      have hs : dE b a = dE a b := by
        simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
      rw [hs] at h2
      have h3 : Ln n * dE a b ≤ Lmax * d * dist (liftT a) (liftT b) := by
        nlinarith [hLmax n, dE_nonneg a b, hLn0 n, dist_nonneg (x := liftT a) (y := liftT b)]
      simp only [Ln] at h3
      constructor <;> nlinarith [dist_nonneg (x := liftT a) (y := liftT b)])
  set g₀ : Torus d → ℝ := fun y => v y ()
  have hconv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ y, |g (φ n) y - g₀ y| ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hvconv ε hε)
    exact ⟨N, fun n hn y => hN n hn y ()⟩
  have hpt : ∀ y, Tendsto (fun n => g (φ n) y) atTop (𝓝 (g₀ y)) := fun y => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; linarith [hN n hn y]⟩
  refine ⟨g₀, (continuous_apply ()).comp hvc, fun y => ?_, fun x y => ?_, fun j => ?_⟩
  · exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hpt y)) fun n => hgB (φ n) y
  · exact le_of_tendsto_of_tendsto' ((hpt _).sub (hpt _))
      ((hLim.comp hφ.tendsto_atTop).mul_const _) fun n => hgl (φ n) x y
  · -- coefficients
    have hej : Integrable (e j) P := ((hb.memH1 j).2.1).integrable one_le_two
    have hc1 : Tendsto (fun n => ∫ y, g (φ n) y * e j y ∂P) atTop (𝓝 (∫ y, g₀ y * e j y ∂P)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := hconv (ε / (2 * (∫ y, |e j y| ∂P + 1))) (by positivity)
      refine ⟨N, fun n hn => ?_⟩
      have hgi : ∀ m, Integrable (fun y => g m y * e j y) P := fun m => by
        obtain ⟨B', hB'⟩ := isCompact_univ.exists_bound_of_continuousOn (hgc m).continuousOn
        exact hej.bdd_mul (c := B') (hgc m).aestronglyMeasurable
          (Eventually.of_forall fun y => hB' y (mem_univ _))
      have hg₀c : Continuous g₀ := (continuous_apply ()).comp hvc
      have hg₀i : Integrable (fun y => g₀ y * e j y) P := by
        obtain ⟨B', hB'⟩ := isCompact_univ.exists_bound_of_continuousOn hg₀c.continuousOn
        exact hej.bdd_mul (c := B') hg₀c.aestronglyMeasurable
          (Eventually.of_forall fun y => hB' y (mem_univ _))
      rw [Real.dist_eq, ← integral_sub (hgi _) hg₀i]
      set δ := ε / (2 * (∫ y, |e j y| ∂P + 1))
      calc |∫ y, (g (φ n) y * e j y - g₀ y * e j y) ∂P| ≤ ∫ y, |g (φ n) y * e j y - g₀ y * e j y| ∂P :=
            abs_integral_le_integral_abs
        _ ≤ ∫ y, δ * |e j y| ∂P := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (hej.abs.const_mul _) (Eventually.of_forall fun y => ?_)
            show |g (φ n) y * e j y - g₀ y * e j y| ≤ δ * |e j y|
            rw [← sub_mul, abs_mul]
            exact mul_le_mul_of_nonneg_right (hN n hn y) (abs_nonneg _)
        _ = δ * ∫ y, |e j y| ∂P := integral_const_mul _ _
        _ < ε := by
            have hI : 0 ≤ ∫ y, |e j y| ∂P := integral_nonneg fun _ => abs_nonneg _
            simp only [δ]
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
    have hc2 : Tendsto (fun n => ∫ y, g (φ n) y * e j y ∂P) atTop
        (𝓝 (Real.exp (-t * lam j) * ∫ y, h y * e j y ∂P)) := by
      have h1 := (Real.tendsto_one_add_div_pow_exp (t * lam j)).comp
        ((tendsto_add_atTop_iff_nat (N0 + 1)).mpr tendsto_id)
      have h2 : Tendsto (fun n => (1 + τ n * lam j) ^ (n + N0 + 1)) atTop
          (𝓝 (Real.exp (t * lam j))) := by
        refine h1.congr fun n => ?_
        simp only [Function.comp, id, τ]
        push_cast; ring_nf
      have h3 := (h2.inv₀ (Real.exp_pos _).ne').mul_const (∫ y, h y * e j y ∂P)
      rw [← Real.exp_neg] at h3
      rw [neg_mul]
      refine (h3.comp hφ.tendsto_atTop).congr fun n => ?_
      simp only [Function.comp]
      have := hgj (φ n) j
      have hpos : (1 + τ (φ n) * lam j) ^ (φ n + N0 + 1) ≠ 0 := by
        have : 0 ≤ lam j := refLam_nonneg hρ hb j
        exact pow_ne_zero _ (by nlinarith [hτ (φ n)])
      rw [this]; field_simp
    exact tendsto_nhds_unique hc1 hc2

end euler

end SharpLSI
