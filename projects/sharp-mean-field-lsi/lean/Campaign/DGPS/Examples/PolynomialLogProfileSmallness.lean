import DGPS.Examples.PolynomialScoreUniformCapture
import DGPS.Examples.PolynomialLogCalculus
import DGPS.Examples.PolynomialLogDerivativeBounds
import DGPS.Frontier.STR029.T69

/-! Full retained circular C2,1/2 smallness for actual logarithmic minimizer
profiles. Quantitative controls are derived from actual root/score capture and
physical model coefficients before applying the periodic Hölder estimate. -/

noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal ContDiff
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.PolynomialSpecies

private theorem c2_small_of_derivatives (F0 F1 F2 F3 : ℕ → ℝ → ℝ)
    (hp : ∀ n, Periodic (F0 n) (2 * Real.pi))
    (h0 : ∀ n t, HasDerivAt (F0 n) (F1 n t) t)
    (h1 : ∀ n t, HasDerivAt (F1 n) (F2 n t) t)
    (h2 : ∀ n t, HasDerivAt (F2 n) (F3 n t) t)
    (hc3 : ∀ n, Continuous (F3 n))
    (hs0 : USmall F0) (hs1 : USmall F1) (hs2 : USmall F2) (hs3 : USmall F3) :
    (∀ n, IsC2Alpha_STR02901 (1 / 2) (F0 n)) ∧
      Tendsto (fun n => c2Norm_STR02901 (1 / 2) (F0 n)) atTop (𝓝 0) := by
  have e0 (n : ℕ) : deriv (F0 n) = F1 n := funext fun t => (h0 n t).deriv
  have e1 (n : ℕ) : deriv (F1 n) = F2 n := funext fun t => (h1 n t).deriv
  have e2 (n : ℕ) : deriv (F2 n) = F3 n := funext fun t => (h2 n t).deriv
  have hp1 (n : ℕ) : Periodic (F1 n) (2 * Real.pi) := e0 n ▸ periodic_deriv_STR02901 (hp n)
  have hp2 (n : ℕ) : Periodic (F2 n) (2 * Real.pi) := e1 n ▸ periodic_deriv_STR02901 (hp1 n)
  have hp3 (n : ℕ) : Periodic (F3 n) (2 * Real.pi) := e2 n ▸ periodic_deriv_STR02901 (hp2 n)
  have hbd3 (n : ℕ) : Bdd (deriv (F2 n)) := by
    rw [e2]
    exact bdd_of_periodic_continuous_STR02953 (hp3 n) (hc3 n)
  have hholder (n : ℕ) := c0_of_deriv_STR02953 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (hp2 n) (fun t => (h2 n t).differentiableAt) (hbd3 n)
  have hclass (n : ℕ) : IsC2Alpha_STR02901 (1 / 2) (F0 n) := by
    refine ⟨hp n, fun t => (h0 n t).differentiableAt, ?_, ?_, ?_⟩
    · rw [e0]
      exact fun t => (h1 n t).differentiableAt
    · rw [e0, e1]
      exact continuous_iff_continuousAt.2 fun t => (h2 n t).continuousAt
    · rw [e0, e1]
      exact (hholder n).1.2
  refine ⟨hclass, Metric.tendsto_nhds.2 fun e he => ?_⟩
  let C := 3 + Real.pi ^ (1 / 2 : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  let d := e / (2 * C)
  have hd : 0 < d := div_pos he (by positivity)
  filter_upwards [hs0 d hd, hs1 d hd, hs2 d hd, hs3 d hd] with n hn0 hn1 hn2 hn3
  have hi := (hholder n).2
  rw [c0Norm_STR02953, e2] at hi
  have hb0 := supNorm_le hn0
  have hb1 := supNorm_le hn1
  have hb2 := supNorm_le hn2
  have hb3 := supNorm_le hn3
  have hpn : 0 ≤ Real.pi ^ (1 / 2 : ℝ) := by positivity
  have hnorm : c2Norm_STR02901 (1 / 2) (F0 n) ≤ C * d := by
    rw [c2Norm_STR02901, e0, e1]
    have hm := mul_le_mul_of_nonneg_left hb3 hpn
    dsimp only [C]
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hi
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (c2Norm_nonneg_STR02969 _)]
  refine hnorm.trans_lt ?_
  have heq : C * d = e / 2 := by dsimp only [d]; field_simp <;> ring
  rw [heq]
  exact half_lt_self he

/-- Every actual original-domain minimizer sequence at fields tending to zero
has actual smooth relative logarithmic profiles tending to zero in the FULL
retained circular C2,1/2 norm. The profile reconstructs the original density
almost everywhere; no positive representative or C2-nearness premise occurs. -/
theorem polynomial_scalarMinimizer_log_profile_C2_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, ∃ f : ℕ → Torus 1 → ℝ, StrictMono φ ∧
      (∀ n, IsSmoothPeriodic (f n)) ∧
      (∀ n, (ρ (φ n)).density =ᵐ[haar 1] fun x =>
        (polynomialRankOne (h (φ n))).q x * Real.exp (f n x)) ∧
      (∀ n, IsC2Alpha_STR02901 (1 / 2) (fun t => f n (pt (t / (2 * Real.pi))))) ∧
      Tendsto (fun n => c2Norm_STR02901 (1 / 2) (fun t => f n (pt (t / (2 * Real.pi))))) atTop (𝓝 0) := by
  classical
  obtain ⟨φ, v0, A0, θ0, hφ, hθ0, hclass, hθb0, hA0⟩ :=
    polynomial_scalarMinimizer_root_score_capture h hh b ρ hG hmin
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hθ0.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let ψ := fun n => φ (n + N)
  let hs := fun n => h (ψ n)
  let bs := fun n => b (ψ n)
  let τ := fun n => ρ (ψ n)
  let v := fun n => v0 (n + N)
  let A := fun n => A0 (n + N)
  let θ := fun n => θ0 (n + N)
  let M := fun n => polynomialRankOne (hs n)
  let r := fun n => (scalarRate (canonical_elementary_polynomial_model (hs n)) (bs n)).toReal
  have hψ : StrictMono ψ := fun i j hij => hφ (Nat.add_lt_add_right hij N)
  have hhs : Tendsto hs atTop (𝓝 0) := hh.comp hψ.tendsto_atTop
  have hθ : Tendsto θ atTop (𝓝 0) := hθ0.comp (tendsto_add_atTop_nat N)
  have hv (n : ℕ) : Continuous (v n) := (hclass (n + N)).1
  have hAc (n : ℕ) : Continuous (A n) := (hclass (n + N)).2.1
  have hae (n : ℕ) : (τ n).sqrt =ᵐ[haar 1] v n := (hclass (n + N)).2.2.1
  have hvd (n : ℕ) := (hclass (n + N)).2.2.2.1
  have hAd (n : ℕ) := (hclass (n + N)).2.2.2.2
  have hvhalf (n : ℕ) (x : Torus 1) : (1 / 2 : ℝ) ≤ v n x := by
    have hi := (abs_le.mp (hθb0 (n + N) x)).1
    have hn := hN (n + N) (by omega)
    change θ n ≤ 1 / 2 at hn
    change -θ n ≤ v n x - 1 at hi
    linarith
  have hvpos (n : ℕ) (x : Torus 1) : 0 < v n x := lt_of_lt_of_le (by norm_num) (hvhalf n x)
  have hsm (n : ℕ) := polynomial_classicalScore_smooth (hs n) (r n) (τ n)
    (hv n) (hAc n) (hvpos n) (hvd n) (hAd n)
  let f := fun n x => Real.log (v n x ^ 2) - Real.log ((M n).q x)
  have hfs (n : ℕ) : IsSmoothPeriodic (f n) := (hsm n).2.2.sub (M n).log_smooth
  have hdensity (n : ℕ) : (τ n).density =ᵐ[haar 1] fun x => (M n).q x * Real.exp (f n x) := by
    filter_upwards [hae n] with x hx
    change (τ n).sqrt x ^ 2 = (M n).q x * Real.exp (Real.log (v n x ^ 2) - Real.log ((M n).q x))
    rw [hx, Real.exp_sub, Real.exp_log (pow_pos (hvpos n x) 2), Real.exp_log ((M n).q_pos x)]
    field_simp [((M n).q_pos x).ne'] <;> ring
  let F0 := fun n t => f n (pt t)
  let F1 := fun n t => A n (pt t) / v n (pt t)
  let F2 := fun n t => -(M n).dlogq (pt t) * F1 n t - F1 n t ^ 2 / 2 - r n * F0 n t +
    polynomialEulerCorrection (hs n) (r n) (τ n) (pt t) / 2 - polynomialEulerMultiplier (hs n) (r n) (τ n) / 2
  let F3 := fun n t => -coordPartial 0 (M n).dlogq (pt t) * F1 n t - (M n).dlogq (pt t) * F2 n t -
    F1 n t * F2 n t - r n * F1 n t + coordPartial 0 (polynomialEulerCorrection (hs n) (r n) (τ n)) (pt t) / 2
  have hd0 (n : ℕ) (t : ℝ) : HasDerivAt (F0 n) (F1 n t) t :=
    polynomial_log_profile_hasDerivAt (hs n) (hvpos n) (hvd n) t
  have hd1 (n : ℕ) (t : ℝ) : HasDerivAt (F1 n) (F2 n t) t :=
    polynomial_log_profile_second_hasDerivAt (hs n) (r n) (τ n) (hvpos n) (hvd n) (hAd n) t
  have hd2 (n : ℕ) (t : ℝ) : HasDerivAt (F2 n) (F3 n t) t :=
    polynomial_log_profile_third_hasDerivAt (hs n) (r n) (τ n) (hvpos n) (hvd n) (hAd n) t
  have e0 (n : ℕ) : deriv (F0 n) = F1 n := funext fun t => (hd0 n t).deriv
  have e1 (n : ℕ) : deriv (F1 n) = F2 n := funext fun t => (hd1 n t).deriv
  have e2 (n : ℕ) : deriv (F2 n) = F3 n := funext fun t => (hd2 n t).deriv
  have hc3 (n : ℕ) : Continuous (F3 n) := by
    have h0 : ContDiff ℝ ∞ (F0 n) := (hfs n).comp (contDiff_pi.mpr fun _ => contDiff_id)
    have h1 := (contDiff_infty_iff_deriv.1 h0).2
    have h2 := (contDiff_infty_iff_deriv.1 h1).2
    have h3 := (contDiff_infty_iff_deriv.1 h2).2
    rw [← e2, ← e1, ← e0]
    exact h3.continuous
  have hV0 : USmall (fun n t => v n (pt t) - 1) :=
    USmall.of_abs_le hθ (fun n t => hθb0 (n + N) (pt t))
  have hAsmall : USmall (fun n t => A n (pt t)) := by
    intro e he
    exact (tendsto_add_atTop_nat N).eventually (hA0 e he)
  have hinv : ∀ᶠ n in atTop, ∀ t : ℝ, |(v n (pt t))⁻¹| ≤ 2 := Eventually.of_forall fun n t => by
    rw [abs_inv, abs_of_pos (hvpos n (pt t)), ← one_div]
    exact (div_le_iff₀ (hvpos n (pt t))).2 (by nlinarith [hvhalf n (pt t)])
  have hs1 : USmall F1 := USmall.congr (fun n t => div_eq_mul_inv _ _) (hAsmall.mul_bdd 2 hinv)
  obtain ⟨δR, hδR, hupper⟩ := polynomial_scalarRate_eventual_upper 1 (by norm_num)
  have hr : ∀ᶠ n in atTop, |r n| ≤ a0 + 1 := by
    have ht : Tendsto (fun n => |hs n|) atTop (𝓝 0) := by simpa using hhs.abs
    filter_upwards [ht.eventually (gt_mem_nhds hδR)] with n hn
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (by unfold a0; positivity) (hupper (hs n) hn (bs n))
  have hrootθ : ∀ n, ∀ᵐ x ∂haar 1, |(τ n).sqrt x - 1| ≤ θ n := fun n =>
    (hae n).mono fun x hx => by rw [hx]; exact hθb0 (n + N) x
  obtain ⟨hXi, hXid, hLambda⟩ := polynomial_varying_euler_corrections_small hs hhs τ θ hθ hrootθ r (a0 + 1) hr
  obtain ⟨εq, hεq, hq⟩ := polynomial_uniform_data_at_origin
  have hlog : USmall (fun n t => Real.log ((M n).q (pt t))) := by
    apply USmall.of_abs_le (hεq.comp hhs)
    intro n t
    have he := hq (hs n) (pt t)
    dsimp only [Function.comp_apply]
    dsimp only [M] at *
    nlinarith [abs_nonneg ((M n).φ (pt t) - (polynomialRankOne 0).φ (pt t)),
      abs_nonneg ((M n).Aq (pt t) - (polynomialRankOne 0).Aq (pt t)), abs_nonneg ((M n).dlogq (pt t)),
      abs_nonneg ((M n).dφ (pt t) - (polynomialRankOne 0).dφ (pt t))]
  have hσ : USmall (fun n t => (M n).dlogq (pt t)) := by
    apply USmall.of_abs_le (hεq.comp hhs)
    intro n t
    have he := hq (hs n) (pt t)
    dsimp only [Function.comp_apply]
    dsimp only [M] at *
    nlinarith [abs_nonneg ((M n).φ (pt t) - (polynomialRankOne 0).φ (pt t)),
      abs_nonneg ((M n).Aq (pt t) - (polynomialRankOne 0).Aq (pt t)), abs_nonneg (Real.log ((M n).q (pt t))),
      abs_nonneg ((M n).dφ (pt t) - (polynomialRankOne 0).dφ (pt t))]
  obtain ⟨εd, hεd, hder⟩ := polynomial_log_score_second_derivatives_at_origin
  have hσ1 : USmall (fun n t => coordPartial 0 (M n).dlogq (pt t)) := by
    apply USmall.of_abs_le (hεd.comp hhs)
    intro n t
    have he := hder (hs n) (pt t)
    dsimp only [Function.comp_apply]
    dsimp only [M] at *
    nlinarith [abs_nonneg ((M n).dlogq (pt t)),
      abs_nonneg (coordPartial 0 (fun x => coordPartial 0 (M n).dlogq x) (pt t))]
  have hlogsq : USmall (fun n t => Real.log (v n (pt t) ^ 2)) := by
    refine hV0.of_le 4 (Eventually.of_forall fun n t => ?_)
    exact abs_log_sq_le ((hθb0 (n + N) (pt t)).trans (hN (n + N) (by omega)))
  have hs0 : USmall F0 := hlogsq.sub hlog
  have hrb : ∀ᶠ n in atTop, ∀ _ : ℝ, |r n| ≤ a0 + 1 := hr.mono fun n hn _ => hn
  have hs2 : USmall F2 := by
    have he := ((((hσ.neg.mul_bdd 1 hs1.bdd).sub
      ((hs1.mul_bdd 1 hs1.bdd).const_mul (1 / 2))).sub (hs0.mul_bdd (a0 + 1) hrb)).add
        (hXi.const_mul (1 / 2))).sub (hLambda.const_mul (1 / 2))
    exact USmall.congr (fun n t => by dsimp only [F2]; ring) he
  have hs3 : USmall F3 := by
    have he := ((((hσ1.neg.mul_bdd 1 hs1.bdd).sub (hσ.mul_bdd 1 hs2.bdd)).sub
      (hs1.mul_bdd 1 hs2.bdd)).sub (hs1.mul_bdd (a0 + 1) hrb)).add (hXid.const_mul (1 / 2))
    exact USmall.congr (fun n t => by dsimp only [F3]; ring) he
  let γ : ℝ := (2 * Real.pi)⁻¹
  let G0 := fun n t => F0 n (γ * t)
  let G1 := fun n t => γ * F1 n (γ * t)
  let G2 := fun n t => γ ^ 2 * F2 n (γ * t)
  let G3 := fun n t => γ ^ 3 * F3 n (γ * t)
  have hg0 (n : ℕ) (t : ℝ) : HasDerivAt (G0 n) (G1 n t) t := by
    convert (hd0 n (γ * t)).comp t ((hasDerivAt_id t).const_mul γ) using 1 <;> dsimp only [G0, G1, G2, G3, Function.comp_apply] <;> first | rfl | ring
  have hg1 (n : ℕ) (t : ℝ) : HasDerivAt (G1 n) (G2 n t) t := by
    convert ((hd1 n (γ * t)).comp t ((hasDerivAt_id t).const_mul γ)).const_mul γ using 1 <;> dsimp only [G0, G1, G2, G3, Function.comp_apply] <;> first | rfl | ring
  have hg2 (n : ℕ) (t : ℝ) : HasDerivAt (G2 n) (G3 n t) t := by
    convert ((hd2 n (γ * t)).comp t ((hasDerivAt_id t).const_mul γ)).const_mul (γ ^ 2) using 1 <;> dsimp only [G0, G1, G2, G3, Function.comp_apply] <;> first | rfl | ring
  have hgc3 (n : ℕ) : Continuous (G3 n) :=
    ((hc3 n).comp (continuous_const.mul continuous_id)).const_mul (γ ^ 3)
  have hgp (n : ℕ) : Periodic (G0 n) (2 * Real.pi) := by
    intro t
    have he : γ * (t + 2 * Real.pi) = γ * t + 1 := by
      dsimp only [γ]
      field_simp [Real.pi_ne_zero] <;> ring
    change f n (pt (γ * (t + 2 * Real.pi))) = f n (pt (γ * t))
    rw [he]
    apply congrArg (f n)
    ext i
    change (((γ * t + 1 : ℝ) : AddCircle (1 : ℝ))) = ((γ * t : ℝ) : AddCircle (1 : ℝ))
    exact AddCircle.coe_add_period (1 : ℝ) (γ * t)
  have small_pullback {F : ℕ → ℝ → ℝ} (hf : USmall F) : USmall (fun n t => F n (γ * t)) := by
    intro e he
    exact (hf e he).mono fun n hn t => hn (γ * t)
  have hgs0 : USmall G0 := small_pullback hs0
  have hgs1 : USmall G1 := (small_pullback hs1).const_mul γ
  have hgs2 : USmall G2 := (small_pullback hs2).const_mul (γ ^ 2)
  have hgs3 : USmall G3 := (small_pullback hs3).const_mul (γ ^ 3)
  obtain ⟨hC2, hnorm⟩ := c2_small_of_derivatives G0 G1 G2 G3 hgp hg0 hg1 hg2 hgc3 hgs0 hgs1 hgs2 hgs3
  have heq (n : ℕ) : (fun t => f n (pt (t / (2 * Real.pi)))) = G0 n := by
    funext t
    change f n (pt (t / (2 * Real.pi))) = f n (pt (γ * t))
    congr 2
    dsimp only [γ]
    ring
  refine ⟨ψ, f, hψ, hfs, hdensity, ?_, ?_⟩
  · intro n
    rw [heq]
    exact hC2 n
  · simpa only [heq] using hnorm

end DGPS.Examples.PolynomialSpecies
