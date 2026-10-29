import SharpSymmetricLSI.Paper.LemmaA2_14

/-!
# R25 (A.9), part 15: the Lipschitz resolvent of the reference operator (`resolvent_core`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem secondDirDeriv_add_const {F : (Fin d → ℝ) → ℝ} (a : ℝ) (v x : Fin d → ℝ) :
    secondDirDeriv (fun z => F z + a) v x = secondDirDeriv F v x := by
  unfold secondDirDeriv
  have : (fun y => fderiv ℝ (fun z => F z + a) y v) = fun y => fderiv ℝ F y v := by
    funext y; rw [fderiv_add_const]
  rw [this]

theorem dE_close_lifts (hd : 1 ≤ d) (x y : Torus d) :
    ∃ a b : Fin d → ℝ, liftT a = x ∧ liftT b = y ∧ dE a b ≤ d * dist x y ∧ dE a b ≤ d := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_close_lifts' x y
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · have hle : ∀ i, |a i - b i| ≤ dist x y := fun i => by
      rw [hab i, dist_eq_norm]
      exact norm_le_pi_norm (x - y) i
    have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [dE, Real.sqrt_le_left (by positivity)]
    calc ∑ i, (a i - b i) ^ 2 ≤ ∑ _i : Fin d, dist x y ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hle i) 2
      _ = d * dist x y ^ 2 := by simp
      _ ≤ (d * dist x y) ^ 2 := by nlinarith [sq_nonneg (dist x y), dist_nonneg (x := x) (y := y)]
  · have hle : ∀ i, |a i - b i| ≤ 1 := fun i => by
      rw [hab i]
      exact (AddCircle.norm_le_half_period (p := (1 : ℝ)) one_ne_zero).trans (by norm_num)
    have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [dE, Real.sqrt_le_left (by positivity)]
    calc ∑ i, (a i - b i) ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; nlinarith [hle i, abs_nonneg (a i - b i)]
      _ = d := by simp
      _ ≤ (d : ℝ) ^ 2 := by nlinarith

/-- **The Lipschitz resolvent.** -/
theorem resolvent_core (hd : 1 ≤ d) {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
    (hρc : Continuous ρ) {K : ℝ}
    (hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
    {τ : ℝ} (hτ : 0 < τ) (hKτ : K * τ < 1) {h : Torus d → ℝ} (hhc : Continuous h) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x y, h (liftT x) - h (liftT y) ≤ L * dE x y) {Bh0 : ℝ}
    (hhB : ∀ y, |h y| ≤ Bh0) :
    ∃ u : Torus d → ℝ, Continuous u ∧
      (∀ x y, u (liftT x) - u (liftT y) ≤ L / (1 - K * τ) * dE x y) ∧ (∀ y, |u y| ≤ Bh0) ∧
      ∀ j, ∫ y, h y * e j y ∂densMeasure ρ =
        (1 + τ * lam j) * ∫ y, u y * e j y ∂densMeasure ρ := by
  have hpos : ∀ y, 0 < ρ y := fun y => hρ.pos.trans_le (hρ.lower y)
  set Q : Torus d → ℝ := fun y => -Real.log (ρ y)
  have hQc : Continuous Q := (hρc.log fun y => (hpos y).ne').neg
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hQc.continuousOn
  have hB' : ∀ y, |Q y| ≤ B := fun y => by simpa [Real.norm_eq_abs] using hB y (mem_univ _)
  have hQloc : LocallyIntegrable (Q ∘ liftT) volume := (hQc.comp continuous_liftT).locallyIntegrable
  have hZ : ∫ y, Real.exp (-Q y) = 1 := by
    have e : (fun y => Real.exp (-Q y)) = ρ := funext fun y => by
      simp only [Q, neg_neg, Real.exp_log (hpos y)]
    rw [e]; exact hρ.one
  set ρn : ℕ → Torus d → ℝ := rhoN Q
  have hρnG : ∀ n, GoodDens (ρn n) (Real.exp (-(2 * B))) (Real.exp (2 * B)) := fun n =>
    goodDens_rhoN hQc hB' n
  have hρns : ∀ n, ContDiff ℝ ∞ (ρn n ∘ liftT) := fun n => contDiff_rhoN hQc hB' n
  have hQn : ∀ n x v, -K * ∑ i, v i ^ 2 ≤
      secondDirDeriv (fun z => -Real.log (ρn n (liftT z))) v x := by
    intro n x v
    rw [negLog_rhoN hQc hB' n, secondDirDeriv_add_const]
    have e : QN Q n ∘ liftT = mollL n (Q ∘ liftT) := moll_comp_liftT n Q
    rw [e]
    exact semiconvex_mollL hQloc hQ n x v
  -- smoothed data
  set Φn : ℕ → (Fin d → ℝ) → ℝ := fun n => mollL n (h ∘ liftT)
  obtain ⟨Bh, hBh⟩ := isCompact_univ.exists_bound_of_continuousOn hhc.continuousOn
  have hBh' : ∀ x, |(h ∘ liftT) x| ≤ Bh := fun x => by
    simpa [Real.norm_eq_abs] using hBh _ (mem_univ _)
  have hΦs : ∀ n, ContDiff ℝ ∞ (Φn n) := fun n =>
    contDiff_mollL n (hhc.comp continuous_liftT).locallyIntegrable
  have hΦp : ∀ n, IsPer (Φn n) := fun n m x => mollL_comp_liftT_add n h x m
  have hΦl : ∀ n x y, Φn n x - Φn n y ≤ L * dE x y := fun n =>
    mollL_sub_le (hhc.comp continuous_liftT) hL hBh' n
  have hΦb : ∀ n y, |Φn n (secT y)| ≤ Bh := fun n y => abs_mollL_le hBh' n _
  have hΦt : ∀ y, Tendsto (fun n => Φn n (secT y)) atTop (𝓝 (h y)) := fun y => by
    have := tendsto_mollL_apply hhc (secT y)
    rwa [liftT_secT] at this
  -- smooth resolvents
  have hres : ∀ n, ∃ u : Torus d → ℝ, ContDiff ℝ 1 (u ∘ liftT) ∧
      (∀ x y, u (liftT x) - u (liftT y) ≤ L / (1 - K * τ) * dE x y) ∧ (∀ y, |u y| ≤ Bh0) ∧
      ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
        ∫ y, ρn n y * (Φn n (secT y) - u y) * Θ (secT y) =
          -τ * ∫ y, u y * divRho (ρn n) Θ (secT y) := fun n =>
    resolvent_smooth_lip (hρnG n) (hρns n) hd hτ hKτ (hQn n) (hΦs n) (hΦp n) hL0 (hΦl n)
      (fun x => abs_mollL_le (F := h ∘ liftT) (fun z => hhB _) n x)
  choose un hun1 hunl hunB huneq using hres
  set M := L / (1 - K * τ)
  have hKτ' : 0 < 1 - K * τ := by linarith
  have hM0 : 0 ≤ M := div_nonneg hL0 hKτ'.le
  have hunc : ∀ n, Continuous (un n) := fun n => continuous_of_liftT' (hun1 n).continuous
  -- uniform bounds
  have hD : ∀ n k y, |dpart (un n) k y| ≤ M := fun n k y =>
    abs_fderiv_le_of_lip ((hun1 n).differentiable one_ne_zero) (hunl n) (secT y) k
  have hosc : ∀ n y z, |un n y - un n z| ≤ M * d := by
    intro n y z
    obtain ⟨a, b, ha, hb', -, hab⟩ := dE_close_lifts hd y z
    rw [← ha, ← hb', abs_le]
    have h1 := hunl n a b
    have h2 := hunl n b a
    have hs : dE b a = dE a b := by
      simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs] at h2
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hab hM0]
  have hmean : ∀ n, ∫ y, ρn n y * un n y = ∫ y, ρn n y * Φn n (secT y) := by
    intro n
    have h1 := huneq n (fun _ => 1) contDiff_const (fun _ _ => rfl)
    have hdiv : ∀ x, divRho (ρn n) (fun _ => (1 : ℝ)) x = 0 := fun x => by
      simp [divRho, Dk]
    simp only [hdiv, mul_zero, integral_zero, mul_one] at h1
    have hi1 : Integrable fun y => ρn n y * Φn n (secT y) :=
      integrable_of_continuous_torus' ((continuous_of_liftT' (hρns n).continuous).mul
        (continuous_comp_secT (hΦs n).continuous (hΦp n)))
    have hi2 : Integrable fun y => ρn n y * un n y :=
      integrable_of_continuous_torus' ((continuous_of_liftT' (hρns n).continuous).mul (hunc n))
    have : ∫ y, ρn n y * (Φn n (secT y) - un n y) =
        (∫ y, ρn n y * Φn n (secT y)) - ∫ y, ρn n y * un n y := by
      rw [← integral_sub hi1 hi2]; congr 1; funext y; ring
    linarith
  have hub : ∀ n y, |un n y| ≤ Bh + M * d := by
    intro n y
    have hG := hρnG n
    have hone : ∫ z, ρn n z = 1 := hG.one
    have hρc' : Continuous (ρn n) := continuous_of_liftT' (hρns n).continuous
    have hρi : Integrable (ρn n) := integrable_of_continuous_torus' hρc'
    have hi2 : Integrable fun z => ρn n z * un n z :=
      integrable_of_continuous_torus' (hρc'.mul (hunc n))
    have e0 : ∫ z, ρn n z * (un n y - un n z) = un n y - ∫ z, ρn n z * Φn n (secT z) := by
      rw [← hmean n]
      have : (fun z => ρn n z * (un n y - un n z)) = fun z => ρn n z * un n y - ρn n z * un n z := by
        funext z; ring
      rw [this, integral_sub (hρi.mul_const _) hi2, integral_mul_const, hone, one_mul]
    have b1 : |∫ z, ρn n z * (un n y - un n z)| ≤ M * d := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ z, |ρn n z * (un n y - un n z)| ≤ ∫ z, ρn n z * (M * d) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (hρi.mul_const _) (Eventually.of_forall fun z => ?_)
            show |ρn n z * (un n y - un n z)| ≤ ρn n z * (M * d)
            rw [abs_mul, abs_of_nonneg (hG.nonneg z)]
            exact mul_le_mul_of_nonneg_left (hosc n y z) (hG.nonneg z)
        _ = M * d := by rw [integral_mul_const, hone, one_mul]
    have b2 : |∫ z, ρn n z * Φn n (secT z)| ≤ Bh := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ z, |ρn n z * Φn n (secT z)| ≤ ∫ z, ρn n z * Bh := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (hρi.mul_const _) (Eventually.of_forall fun z => ?_)
            show |ρn n z * Φn n (secT z)| ≤ ρn n z * Bh
            rw [abs_mul, abs_of_nonneg (hG.nonneg z)]
            exact mul_le_mul_of_nonneg_left (hΦb n z) (hG.nonneg z)
        _ = Bh := by rw [integral_mul_const, hone, one_mul]
    rw [e0] at b1
    have := abs_sub_abs_le_abs_sub (un n y) (∫ z, ρn n z * Φn n (secT z))
    linarith [abs_nonneg (∫ z, ρn n z * Φn n (secT z))]
  -- Arzelà–Ascoli
  have hMd : 0 ≤ M * d := mul_nonneg hM0 (Nat.cast_nonneg _)
  obtain ⟨φ, hφ, v, hvc, hvconv⟩ := exists_subseq_unif_holder (X := Torus d) (κ := Unit)
    (fun n x _ => un n x) one_pos hMd (C := Bh + M * d) (fun n x _ => hub n x)
    (fun n x y _ => by
      obtain ⟨a, b, rfl, rfl, hab, -⟩ := dE_close_lifts hd x y
      rw [Real.rpow_one, abs_le]
      have h1 := hunl n a b
      have h2 := hunl n b a
      have hs : dE b a = dE a b := by
        simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
      rw [hs] at h2
      have := mul_le_mul_of_nonneg_left hab hM0
      constructor <;> nlinarith)
  set u₀ : Torus d → ℝ := fun y => v y ()
  have hu₀c : Continuous u₀ := (continuous_apply ()).comp hvc
  have hconv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ y, |un (φ n) y - u₀ y| ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hvconv ε hε)
    exact ⟨N, fun n hn y => hN n hn y ()⟩
  have hpt : ∀ y, Tendsto (fun n => un (φ n) y) atTop (𝓝 (u₀ y)) := fun y => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; linarith [hN n hn y]⟩
  have hu₀l : ∀ x y, u₀ (liftT x) - u₀ (liftT y) ≤ M * dE x y := fun x y =>
    le_of_tendsto' ((hpt _).sub (hpt _)) fun n => hunl (φ n) x y
  have hLip : LipschitzWith (Real.toNNReal (M * d)) (u₀ ∘ liftT) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ hMd, abs_le]
    have h1 := hu₀l x y
    have h2 := hu₀l y x
    have hs : dE y x = dE x y := by
      simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs] at h2
    have h3 := mul_le_mul_of_nonneg_left (dE_le_card_mul_dist hd x y) hM0
    simp only [Function.comp]
    constructor <;> nlinarith
  -- the limit equation and the coefficients
  have hρnt : ∀ y, Tendsto (fun n => ρn (φ n) y) atTop (𝓝 (ρ y)) := fun y => by
    have := (tendsto_rhoN hQc hB' hZ y).comp hφ.tendsto_atTop
    simp only [Q, neg_neg, Real.exp_log (hpos y)] at this
    exact this
  have hlim : ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, ρ y * (h y - u₀ y) * Θ (secT y) =
        τ * ∫ y, ρ y * ∑ k, lipGrad u₀ y k * Dk Θ k (secT y) := fun Θ hΘ hp => limit_resolvent_eq hρc (ρn := fun n => ρn (φ n))
    (fun n => hρns (φ n)) (Cρ := Real.exp (2 * B))
    (fun n y => by
      rw [abs_of_nonneg ((hρnG (φ n)).nonneg y)]; exact (hρnG (φ n)).upper y)
    hρnt (Φn := fun n => Φn (φ n)) (fun n => hΦs (φ n)) (fun n => hΦp (φ n))
    (fun n y => hΦb (φ n) y) (fun y => (hΦt y).comp hφ.tendsto_atTop)
    (u := fun n => un (φ n)) (fun n => hun1 (φ n)) (fun n k y => hD (φ n) k y) hM0
    (fun n y => hub (φ n) y) hconv hu₀c hLip (τ := τ) (fun n => huneq (φ n)) hΘ hp
  refine ⟨u₀, hu₀c, hu₀l, fun y => ?_, fun j => coeff_of_limit_eq hρ hρc hb hhc hu₀c hLip hlim j⟩
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hpt y)) fun n => hunB (φ n) y

end SharpLSI
