import SharpSymmetricLSI.Paper.LemmaA2_24

/-!
# R25 Lemma A.2, part 25: `K_t → K` uniformly

The `K_t` (`0 < t ≤ 1`) are uniformly bounded and uniformly Lipschitz; any uniform limit point of
`K_{t_n}` (`t_n → 0`) equals `K` because `K_{t_n} → K` in `L²(μ ⊗ μ)` and continuous functions
vanishing `μ ⊗ μ`-a.e. vanish (`uniform_Kt`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

section zero

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
include hρ

theorem eq_zero_of_integral_eq_zero {f : Torus d → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (h : ∫ y, f y ∂densMeasure ρ = 0) : ∀ y, f y = 0 := by
  haveI := hρ.isProb
  have hi : Integrable f (densMeasure ρ) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 := (integral_eq_zero_iff_of_nonneg hf0 hi).mp h
  have h2 : f =ᵐ[volume] 0 := hρ.ac'.ae_le h1
  exact congrFun (eq_of_ae_eq_continuous hf continuous_const h2)

theorem eq_zero_of_integral2_eq_zero {F : Torus d → Torus d → ℝ}
    (hF : Continuous (Function.uncurry F)) (hF0 : ∀ x y, 0 ≤ F x y)
    (h : ∫ y, (∫ x, F x y ∂densMeasure ρ) ∂densMeasure ρ = 0) : ∀ x y, F x y = 0 := by
  haveI := hρ.isProb
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  have hinner : Continuous fun y => ∫ x, F x y ∂densMeasure ρ := by
    refine continuous_of_dominated (bound := fun _ => B) (fun y => ?_) (fun y => ?_)
      (integrable_const _) (Eventually.of_forall fun x => ?_)
    · exact (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => hB (x, y) (mem_univ _)
    · exact hF.comp (continuous_const.prodMk continuous_id)
  have h1 := eq_zero_of_integral_eq_zero hρ hinner (fun y => integral_nonneg fun x => hF0 x y) h
  intro x y
  exact eq_zero_of_integral_eq_zero hρ (hF.comp (continuous_id.prodMk continuous_const))
    (fun x => hF0 x y) (h1 y) x

end zero

section unif

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {K : ℝ}
  (hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
  {eC : ℕ → Torus d → ℝ} (heC1 : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
  (heCae : ∀ j, eC j =ᵐ[densMeasure ρ] e j)
  {M M' : ℕ → ℝ} (hM : ∀ j x, |eC j x| ≤ M j) (hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j)
  (hS : ∀ t, 0 < t → Summable (fun j => Real.exp (-t * lam j) * M j) ∧
    Summable (fun j => Real.exp (-t * lam j) * M' j))
  (hd : 1 ≤ d) (hK0 : 0 ≤ K) {Kf : Torus d → Torus d → ℝ}
  (hKc : Continuous (Function.uncurry Kf)) {BK : ℝ} (hBK : ∀ x y, |Kf x y| ≤ BK) {LK : ℝ}
  (hLK0 : 0 ≤ LK) (hL1 : ∀ y a b, Kf (liftT a) y - Kf (liftT b) y ≤ LK * dE a b)
  (hL2 : ∀ x a b, Kf x (liftT a) - Kf x (liftT b) ≤ LK * dE a b)
include hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2

/-- **`K_t → K` uniformly.** -/
theorem uniform_Kt {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hs1 : ∀ n, s n ≤ 1)
    (hs0 : Tendsto s atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x y, |Kt (densMeasure ρ) e eC lam (s n) Kf x y - Kf x y| ≤ ε := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  by_contra hcon
  push_neg at hcon
  obtain ⟨ε, hε, hN⟩ := hcon
  choose n hn x y hxy using hN
  have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  set L' : ℝ := 2 * (Real.exp K * LK) * d
  have hL'0 : 0 ≤ L' := by positivity
  have hE : ∀ m, Real.exp (K * s m) * LK ≤ Real.exp K * LK := fun m =>
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hs1 m])) hLK0
  set F : ℕ → Torus d × Torus d → Unit → ℝ := fun k p _ => Kt P e eC lam (s (n k)) Kf p.1 p.2
  have hFb : ∀ k p u, |F k p u| ≤ BK := fun k p _ =>
    (Kt_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 (hs _) hKc hBK hLK0 hL1 hL2).1 _ _
  have hFH : ∀ k p q u, |F k p u - F k q u| ≤ L' * dist p q ^ (1 : ℝ) := by
    intro k p q _
    obtain ⟨-, h1, h2, -, -⟩ := Kt_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 (hs (n k)) hKc
      hBK hLK0 hL1 hL2
    rw [Real.rpow_one]
    have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have e1 : ∀ x x' y', |Kt P e eC lam (s (n k)) Kf x y' - Kt P e eC lam (s (n k)) Kf x' y'| ≤
        Real.exp K * LK * d * dist x x' := by
      intro x x' y'
      obtain ⟨a, b, rfl, rfl, hab, -⟩ := dE_close_lifts hd x x'
      rw [abs_le]
      have g1 := h1 y' a b; have g2 := h1 y' b a; rw [dE_symm'] at g2
      have := mul_le_mul (hE (n k)) hab (dE_nonneg a b) (by positivity)
      constructor <;> nlinarith [dE_nonneg a b]
    have e2 : ∀ x' y y', |Kt P e eC lam (s (n k)) Kf x' y - Kt P e eC lam (s (n k)) Kf x' y'| ≤
        Real.exp K * LK * d * dist y y' := by
      intro x' y y'
      obtain ⟨a, b, rfl, rfl, hab, -⟩ := dE_close_lifts hd y y'
      rw [abs_le]
      have g1 := h2 x' a b; have g2 := h2 x' b a; rw [dE_symm'] at g2
      have := mul_le_mul (hE (n k)) hab (dE_nonneg a b) (by positivity)
      constructor <;> nlinarith [dE_nonneg a b]
    simp only [F]
    calc |Kt P e eC lam (s (n k)) Kf p.1 p.2 - Kt P e eC lam (s (n k)) Kf q.1 q.2|
        ≤ |Kt P e eC lam (s (n k)) Kf p.1 p.2 - Kt P e eC lam (s (n k)) Kf q.1 p.2| +
          |Kt P e eC lam (s (n k)) Kf q.1 p.2 - Kt P e eC lam (s (n k)) Kf q.1 q.2| := by
          have := abs_add_le (Kt P e eC lam (s (n k)) Kf p.1 p.2 - Kt P e eC lam (s (n k)) Kf q.1 p.2)
            (Kt P e eC lam (s (n k)) Kf q.1 p.2 - Kt P e eC lam (s (n k)) Kf q.1 q.2)
          rwa [sub_add_sub_cancel] at this
      _ ≤ Real.exp K * LK * d * dist p.1 q.1 + Real.exp K * LK * d * dist p.2 q.2 :=
          add_le_add (e1 _ _ _) (e2 _ _ _)
      _ ≤ L' * dist p q := by
          have := (show dist p.1 q.1 ≤ dist p q by rw [Prod.dist_eq]; exact le_max_left _ _); have := (show dist p.2 q.2 ≤ dist p q by rw [Prod.dist_eq]; exact le_max_right _ _)
          have h0 : 0 ≤ Real.exp K * LK * d := by positivity
          simp only [L']; nlinarith
  obtain ⟨φ, hφ, G, hGc, hGconv⟩ := exists_subseq_unif_holder F one_pos hL'0 hFb hFH
  -- the limit is `K`
  set G' : Torus d → Torus d → ℝ := fun a b => G (a, b) ()
  have hG'c : Continuous (Function.uncurry G') := (continuous_apply ()).comp hGc
  have hsφ : Tendsto (fun k => s (n (φ k))) atTop (𝓝 0) :=
    hs0.comp (hnt.comp hφ.tendsto_atTop)
  have hL2t := tendsto_L2_Kt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2
    (fun k => hs _) hsφ
  have hlimG : Tendsto (fun k => ∫ y, (∫ x, (Kt P e eC lam (s (n (φ k))) Kf x y - Kf x y) ^ 2 ∂P) ∂P)
      atTop (𝓝 (∫ y, (∫ x, (G' x y - Kf x y) ^ 2 ∂P) ∂P)) := by
    have hpt : ∀ a b, Tendsto (fun k => Kt P e eC lam (s (n (φ k))) Kf a b) atTop (𝓝 (G' a b)) := by
      intro a b
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (hGconv (δ / 2) (by positivity))
      exact ⟨k₁, fun k hk => by
        rw [Real.dist_eq]; have := hk₁ k hk (a, b) (); simp only [F] at this; linarith⟩
    have hGb : ∀ a b, |G' a b| ≤ BK := fun a b =>
      le_of_tendsto' ((continuous_abs.tendsto _).comp (hpt a b)) fun k => hFb (φ k) (a, b) ()
    have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK (Classical.arbitrary _) (Classical.arbitrary _))
    have hsq : ∀ {u v : ℝ}, |u| ≤ BK → |v| ≤ BK → (u - v) ^ 2 ≤ (2 * BK) ^ 2 := fun {u v} hu hv => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _)
        ((abs_sub _ _).trans (by linarith)) 2
    have hKtc : ∀ k, Continuous (Function.uncurry (Kt P e eC lam (s (n (φ k))) Kf)) := fun k =>
      continuous_Kt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs _)
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * BK) ^ 2) (fun k => ?_)
      (integrable_const _) (fun k => Eventually.of_forall fun y' => ?_)
      (Eventually.of_forall fun y' => ?_)
    · refine (continuous_of_dominated (bound := fun _ => (2 * BK) ^ 2) (fun y => ?_) (fun y => ?_)
        (integrable_const _) (Eventually.of_forall fun x => ?_)).aestronglyMeasurable
      · exact ((((hKtc k).sub hKc).pow 2).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      · exact Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hsq (hFb (φ k) (x, y) ()) (hBK x y)
      · exact (((hKtc k).sub hKc).pow 2).comp (continuous_const.prodMk continuous_id)
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      calc ∫ x, (Kt P e eC lam (s (n (φ k))) Kf x y' - Kf x y') ^ 2 ∂P ≤ ∫ _x, (2 * BK) ^ 2 ∂P :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) (integrable_const _)
              (Eventually.of_forall fun x => hsq (hFb (φ k) (x, y') ()) (hBK x y'))
        _ = (2 * BK) ^ 2 := by simp
    · refine tendsto_integral_of_dominated_convergence (fun _ => (2 * BK) ^ 2) (fun k => ?_)
        (integrable_const _) (fun k => Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ((hpt x y').sub tendsto_const_nhds).pow 2)
      · exact ((((hKtc k).sub hKc).pow 2).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsq (hFb (φ k) (x, y') ()) (hBK x y')
  have hzero := tendsto_nhds_unique hlimG hL2t
  have hGK : ∀ a b, G' a b = Kf a b := by
    have := eq_zero_of_integral2_eq_zero hρ (F := fun a b => (G' a b - Kf a b) ^ 2)
      (by exact (continuous_pow 2).comp (hG'c.sub hKc)) (fun a b => sq_nonneg _) hzero
    intro a b; have := this a b; nlinarith [sq_nonneg (G' a b - Kf a b)]
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hGconv (ε / 2) (by positivity))
  have h1 := hk₀ k₀ le_rfl (x (φ k₀), y (φ k₀)) ()
  simp only [F] at h1
  rw [show G (x (φ k₀), y (φ k₀)) () = Kf (x (φ k₀)) (y (φ k₀)) from hGK _ _] at h1
  have h2 := hxy (φ k₀)
  linarith

end unif

end SharpLSI
