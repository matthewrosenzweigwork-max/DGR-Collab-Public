import SharpSymmetricLSI.Paper.LemmaA2_13

/-!
# R25 (A.9), part 14: the resolvent of the reference operator is Lipschitz

For the minimizer `μ = ρ m` (`D²(-log ρ) ≥ -K` distributionally), `Kτ < 1` and `h` with
`h(x) - h(y) ≤ L|x - y|` on lifts, there is a continuous `u` with
`u(x) - u(y) ≤ L/(1 - Kτ)|x - y|` on lifts and `⟨h, e_j⟩_μ = (1 + τλ_j)⟨u, e_j⟩_μ`
(`resolvent_core`): the smooth resolvents for `ρₙ = e^{-Qₙ}/Zₙ` (`Q = -log ρ` mollified) and
`Φₙ = φₙ ⋆ h` are uniformly Lipschitz and bounded, a subsequence converges uniformly
(Arzelà–Ascoli), and the limit equation identifies the coefficients.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem abs_fderiv_le_of_lip {F : (Fin d → ℝ) → ℝ} (hF : Differentiable ℝ F) {M : ℝ}
    (hM : ∀ x y, F x - F y ≤ M * dE x y) (x : Fin d → ℝ) (k : Fin d) :
    |fderiv ℝ F x (Pi.single k 1)| ≤ M := by
  set v : Fin d → ℝ := Pi.single k 1
  have hdE : ∀ s t : ℝ, dE (x + s • v) (x + t • v) = |s - t| := by
    intro s t
    simp only [dE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, v]
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [Pi.single_apply, hik]) (by simp)]
    simp only [Pi.single_eq_same, mul_one, add_sub_add_left_eq_sub]
    convert Real.sqrt_sq_eq_abs (s - t) using 2
  have hM0 : 0 ≤ M := by
    have e1 : dE (x + (1 : ℝ) • v) x = 1 := by simpa using hdE 1 0
    have e2 : dE x (x + (1 : ℝ) • v) = 1 := by simpa using hdE 0 1
    have h1 := hM (x + (1 : ℝ) • v) x
    have h2 := hM x (x + (1 : ℝ) • v)
    rw [e1] at h1; rw [e2] at h2
    linarith
  have hlip : LipschitzWith (Real.toNNReal M) fun t : ℝ => F (x + t • v) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM0, abs_le]
    have h1 := hM (x + s • v) (x + t • v)
    have h2 := hM (x + t • v) (x + s • v)
    rw [hdE] at h1 h2
    rw [abs_sub_comm] at h2
    constructor <;> linarith
  have hd := hasDerivAt_line hF x v 0
  have := norm_deriv_le_of_lipschitz (x₀ := (0 : ℝ)) hlip
  rw [hd.deriv] at this
  simpa [Real.norm_eq_abs, Real.coe_toNNReal _ hM0] using this

theorem dE_le_card_mul_dist (hd : 1 ≤ d) (x y : Fin d → ℝ) : dE x y ≤ d * dist x y := by
  have hdist : ∀ i, |x i - y i| ≤ dist x y := fun i => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
  rw [dE, Real.sqrt_le_left (by positivity)]
  · calc ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin d, dist x y ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdist i) 2
      _ = d * dist x y ^ 2 := by simp
      _ ≤ (d * dist x y) ^ 2 := by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          nlinarith [sq_nonneg (dist x y), dist_nonneg (x := x) (y := y)]

/-- Close lifts of two torus points. -/
theorem exists_close_lifts' (x y : Torus d) :
    ∃ a b : Fin d → ℝ, liftT a = x ∧ liftT b = y ∧ ∀ i, |a i - b i| = ‖x i - y i‖ := by
  refine ⟨secT x, fun i => secT y i + round (secT x i - secT y i), liftT_secT x, ?_, fun i => ?_⟩
  · funext i
    have := congrFun (liftT_secT y) i
    simp only [liftT] at this ⊢
    rw [AddCircle.coe_add, this]
    simp
  · have hx := congrFun (liftT_secT x) i
    have hy := congrFun (liftT_secT y) i
    simp only [liftT] at hx hy
    rw [← hx, ← hy, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
    congr 1; ring

theorem flat_bound_of_lift {f : Torus d → ℝ} {M : ℝ}
    (hf : ∀ x y, f (liftT x) - f (liftT y) ≤ M * dE x y) : FlatLipschitzWith M f := by
  intro x y
  obtain ⟨a, b, ha, hb, hab⟩ := exists_close_lifts' x y
  have hd : dE a b = flatDist x y := by
    simp only [dE, flatDist]; congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [← hab i, sq_abs]
  rw [← hd, abs_le, ← ha, ← hb]
  have h1 := hf a b
  have h2 := hf b a
  have hs : dE b a = dE a b := by
    simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs] at h2
  constructor <;> linarith

theorem lift_bound_of_flat {f : Torus d → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : FlatLipschitzWith M f)
    (x y : Fin d → ℝ) : f (liftT x) - f (liftT y) ≤ M * dE x y := by
  refine (le_abs_self _).trans ((hf _ _).trans (mul_le_mul_of_nonneg_left ?_ hM))
  simp only [flatDist, dE]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [← sq_abs (x i - y i)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have : liftT x i - liftT y i = ((x i - y i : ℝ) : UnitAddCircle) := by simp [liftT]
  rw [this, UnitAddCircle.norm_eq]
  have := abs_sub_round (x i - y i)
  have h2 : |x i - y i - round (x i - y i)| ≤ |x i - y i| := by
    rcases lt_or_ge (|x i - y i|) (1 / 2) with h | h
    · rw [abs_lt] at h
      have : round (x i - y i) = 0 := by
        rw [round_eq_zero_iff]; constructor <;> linarith
      simp [this]
    · linarith
  exact h2

end SharpLSI
