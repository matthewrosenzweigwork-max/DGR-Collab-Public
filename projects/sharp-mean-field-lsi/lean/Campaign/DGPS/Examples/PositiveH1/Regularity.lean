import Mathlib
import DGPS.Examples.PositiveH1.Fourier
import DGPS.Examples.PositiveH1.Model
import DGPS.Lipschitz.Representatives

/-!
# Frequency block lower bound at the origin (H1005)

For `0 < h ≤ 1/8` we keep only the frequencies `⌈1/(4h)⌉ ≤ n ≤ ⌊1/(2h)⌋` of the nonnegative series
`A - R(h) = Σ a_n (1 - cos (2π n h))`, each with deficit at least one, to get
`A - R(h) ≥ 2^(-5/4) h^(3/4)`.

Reading choices: `R(h)` is `R (torusLift fun _ => h)`; `W(h,0)` is
`positiveH1.W (torusLift fun _ => h) 0`; "`W` is not Lipschitz" is the negation of the `W` clause of
`DGPS.LipschitzData` (Euclidean quotient distance, Euclidean product distance).

# `W` is not in `W^{1,∞}` (H1006)

`W^{1,∞}(𝕋^d)` is `W1Infinity u := ∃ g, IsWeakGradientLp ⊤ u g` (the campaign's `Lᵖ` weak
gradient with `p = ⊤`: `u ∈ L^∞`, `g ∈ L^∞`, and the weak integration by parts identity), the same
notion used by LIP001 (`DGPS.Lipschitz`). The route uses LIP001 (a continuous function with an `L^∞`
weak gradient is Lipschitz, proved there through periodic mollification) and contradicts H1005.
-/

open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
open Filter Topology

namespace DGPS.Examples.PositiveH1.Regularity

/-- Each retained term. -/
theorem block_term_lower {h : ℝ} (hh : 0 < h) {n : ℕ}
    (h1 : 1 ≤ 4 * h * n) (h2 : 2 * h * n ≤ 1) (hn2 : 2 ≤ n) :
    (2 * h) ^ (7 / 4 : ℝ) ≤ a n * (1 - Real.cos (2 * Real.pi * n * h)) := by
  have hcos : Real.cos (2 * Real.pi * n * h) ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have han : a n = (n : ℝ) ^ (-(7 / 4 : ℝ)) := by simp [a, hn2]
  have hle : (n : ℝ) ≤ (2 * h)⁻¹ := by
    rw [le_inv_comm₀ hn0 (by positivity), inv_eq_one_div, le_div_iff₀ hn0]; linarith
  have hpow : (2 * h) ^ (7 / 4 : ℝ) ≤ (n : ℝ) ^ (-(7 / 4 : ℝ)) := by
    rw [Real.rpow_neg hn0.le, ← Real.inv_rpow (by positivity)]
    have := Real.rpow_le_rpow hn0.le hle (by norm_num : (0 : ℝ) ≤ 7 / 4)
    rw [Real.inv_rpow (by positivity)] at this ⊢
    rw [le_inv_comm₀ (by positivity) (by positivity)]
    simpa using this
  rw [han]
  have : (n : ℝ) ^ (-(7 / 4 : ℝ)) * 1 ≤ (n : ℝ) ^ (-(7 / 4 : ℝ)) * (1 - Real.cos (2 * Real.pi * n * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

theorem block_lower_bound {h : ℝ} (hh : 0 < h) (hh8 : h ≤ 1 / 8) :
    (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (3 / 4 : ℝ) ≤ A - R (torusLift fun _ => h) := by
  set x : ℝ := 1 / (4 * h) with hx
  have hx2 : 2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]; linarith
  have hx0 : 0 ≤ x := by linarith
  have h2x : 1 / (2 * h) = 2 * x := by rw [hx]; field_simp; ring
  -- series form
  have hsumm : Summable fun n : ℕ => a n * cosMode n (torusLift fun _ => h) := summable_term _
  have hR : R (torusLift fun _ => h) = ∑' n : ℕ, a n * Real.cos (2 * Real.pi * n * h) :=
    R_lift h
  have hsumm' : Summable fun n : ℕ => a n * Real.cos (2 * Real.pi * n * h) := by
    refine Summable.of_norm_bounded a_summable fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (a_nonneg n)]
    exact mul_le_of_le_one_right (a_nonneg n) (Real.abs_cos_le_one _)
  have hdiff : A - R (torusLift fun _ => h) =
      ∑' n : ℕ, a n * (1 - Real.cos (2 * Real.pi * n * h)) := by
    rw [hR, A, ← Summable.tsum_sub a_summable hsumm']
    exact tsum_congr fun n => by ring
  have hsumm2 : Summable fun n : ℕ => a n * (1 - Real.cos (2 * Real.pi * n * h)) := by
    simpa [mul_sub] using a_summable.sub hsumm'
  have hnonneg : ∀ n : ℕ, 0 ≤ a n * (1 - Real.cos (2 * Real.pi * n * h)) := fun n =>
    mul_nonneg (a_nonneg n) (by linarith [Real.cos_le_one (2 * Real.pi * n * h)])
  set S : Finset ℕ := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ with hS
  have hbound : ∑ n ∈ S, a n * (1 - Real.cos (2 * Real.pi * n * h)) ≤
      A - R (torusLift fun _ => h) := by
    rw [hdiff]
    exact hsumm2.sum_le_tsum S (fun n _ => hnonneg n)
  have hterm : ∀ n ∈ S, (2 * h) ^ (7 / 4 : ℝ) ≤ a n * (1 - Real.cos (2 * Real.pi * n * h)) := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    have hnx : x ≤ n := (Nat.ceil_le).1 hn.1
    have hnx2 : (n : ℝ) ≤ 2 * x := (Nat.le_floor_iff (by linarith)).1 hn.2
    have h1 : 1 ≤ 4 * h * n := by
      have : 1 ≤ 4 * h * x := by rw [hx]; field_simp; exact le_refl _
      nlinarith
    have h2 : 2 * h * n ≤ 1 := by
      have : 2 * h * (2 * x) = 1 := by rw [hx]; field_simp; ring
      nlinarith
    have hn2 : 2 ≤ n := by
      have : (2 : ℝ) ≤ n := le_trans hx2 hnx
      exact_mod_cast this
    exact block_term_lower hh h1 h2 hn2
  have hsum : (S.card : ℝ) * (2 * h) ^ (7 / 4 : ℝ) ≤
      ∑ n ∈ S, a n * (1 - Real.cos (2 * Real.pi * n * h)) := by
    have := Finset.card_nsmul_le_sum S _ _ hterm
    simpa using this
  have hcard : x / 2 ≤ (S.card : ℝ) := by
    rw [hS, Nat.card_Icc]
    have hf : 2 * x - 1 < (⌊2 * x⌋₊ : ℝ) := Nat.sub_one_lt_floor (2 * x)
    have hc : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have hle : ⌈x⌉₊ ≤ ⌊2 * x⌋₊ + 1 := by
      have : (⌈x⌉₊ : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) + 1 := by linarith
      exact_mod_cast this
    rw [Nat.cast_sub hle]
    push_cast
    linarith
  have hpos : (0 : ℝ) ≤ (2 * h) ^ (7 / 4 : ℝ) := by positivity
  have key : (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (3 / 4 : ℝ) = x / 2 * (2 * h) ^ (7 / 4 : ℝ) := by
    have e1 : (2 * h) ^ (7 / 4 : ℝ) = 2 ^ (7 / 4 : ℝ) * h ^ (7 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hh.le
    have e2 : h ^ (7 / 4 : ℝ) = h * h ^ (3 / 4 : ℝ) := by
      rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, Real.rpow_add hh, Real.rpow_one]
    have e3 : (2 : ℝ) ^ (7 / 4 : ℝ) = 2 ^ (3 : ℝ) * 2 ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have e4 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
    rw [e1, e2, e3, e4, hx]
    field_simp
    ring
  calc (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (3 / 4 : ℝ)
      = x / 2 * (2 * h) ^ (7 / 4 : ℝ) := key
    _ ≤ (S.card : ℝ) * (2 * h) ^ (7 / 4 : ℝ) := mul_le_mul_of_nonneg_right hcard hpos
    _ ≤ _ := hsum.trans hbound

theorem W_lift_zero {h : ℝ} :
    positiveH1.W (torusLift fun _ => h) 0 - positiveH1.W 0 0 =
      -(kappa * (A - R (torusLift fun _ => h))) := by
  have : positiveH1.W 0 0 = 0 := positiveH1.W_diag 0
  rw [this]
  show kappa * (R ((torusLift fun _ => h) - 0) - A) - 0 = _
  simp only [sub_zero]; ring

/-- H1005: Frequency block lower bound at the origin.

For every real `0 < h ≤ 1/8`, `A - R(h) ≥ 2^(-5/4) h^(3/4)`; hence
`|W(h,0) - W(0,0)| / h ≥ κ 2^(-5/4) h^(-1/4)`, and `W` is not Lipschitz (the `W` clause of
`LipschitzData` fails for every constant). -/
theorem frequency_block_lower_bound_at_the_origin :
    (∀ h : ℝ, 0 < h → h ≤ 1 / 8 →
      (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (3 / 4 : ℝ) ≤ A - R (torusLift fun _ => h)) ∧
    (∀ h : ℝ, 0 < h → h ≤ 1 / 8 →
      kappa * (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (-(1 / 4 : ℝ)) ≤
        |positiveH1.W (torusLift fun _ => h) 0 - positiveH1.W 0 0| / h) ∧
    ¬ ∃ L : ℝ, ∀ x y x' y' : Torus 1,
      |positiveH1.W x y - positiveH1.W x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := by
  have part2 : ∀ h : ℝ, 0 < h → h ≤ 1 / 8 →
      kappa * (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (-(1 / 4 : ℝ)) ≤
        |positiveH1.W (torusLift fun _ => h) 0 - positiveH1.W 0 0| / h := by
    intro h hh hh8
    have hb := block_lower_bound hh hh8
    have hAR : 0 ≤ A - R (torusLift fun _ => h) :=
      le_trans (by positivity) hb
    rw [W_lift_zero, abs_neg, abs_of_nonneg (mul_nonneg kappa_pos.le hAR),
      le_div_iff₀ hh]
    have e : h ^ (-(1 / 4 : ℝ)) * h = h ^ (3 / 4 : ℝ) := by
      rw [show h ^ (-(1 / 4 : ℝ)) * h = h ^ (-(1 / 4 : ℝ)) * h ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hh]; norm_num
    calc kappa * (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (-(1 / 4 : ℝ)) * h
        = kappa * ((2 : ℝ) ^ (-(5 / 4 : ℝ)) * (h ^ (-(1 / 4 : ℝ)) * h)) := by ring
      _ = kappa * ((2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (3 / 4 : ℝ)) := by rw [e]
      _ ≤ kappa * (A - R (torusLift fun _ => h)) :=
          mul_le_mul_of_nonneg_left hb kappa_pos.le
  refine ⟨fun h hh hh8 => block_lower_bound hh hh8, part2, ?_⟩
  rintro ⟨L, hL⟩
  set c : ℝ := kappa * (2 : ℝ) ^ (-(5 / 4 : ℝ)) with hc
  have hcpos : 0 < c := by rw [hc]; have := kappa_pos; positivity
  -- choose h small with L * h^(1/4) < c
  have hcont : ContinuousAt (fun h : ℝ => |L| * h ^ (1 / 4 : ℝ)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num)))
  have hval : (fun h : ℝ => |L| * h ^ (1 / 4 : ℝ)) 0 < c := by
    simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using hcpos
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), |L| * h ^ (1 / 4 : ℝ) < c ∧ 0 < h ∧ h ≤ 1 / 8 := by
    have h1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), |L| * h ^ (1 / 4 : ℝ) < c :=
      (hcont.eventually (gt_mem_nhds hval)).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
    have h3 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ≤ 1 / 8 :=
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8)).filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, h2, h3] with h a b c using ⟨a, b, c⟩
  obtain ⟨h, hlt, hh, hh8⟩ := hev.exists
  have hd : torusDist (torusLift fun _ : Fin 1 => h) (0 : Torus 1) = h := by
    have e0 : (0 : Torus 1) = torusLift fun _ => (0 : ℝ) := by
      funext i; simp [torusLift, SharpLSI.liftT]
    rw [e0, torusDist_liftT_eq (by intro j; simp [abs_of_pos hh]; linarith)]
    simp [Real.sqrt_sq hh.le]
  have hineq := hL (torusLift fun _ => h) 0 0 0
  rw [hd, (torusDist_metric (d := 1)).1 (0 : Torus 1)] at hineq
  have hsq : Real.sqrt (h ^ 2 + 0 ^ 2) = h := by simp [Real.sqrt_sq hh.le]
  rw [hsq] at hineq
  have hp := part2 h hh hh8
  have hq : |positiveH1.W (torusLift fun _ => h) 0 - positiveH1.W 0 0| / h ≤ L := by
    rw [div_le_iff₀ hh]; linarith
  have hr : c * h ^ (-(1 / 4 : ℝ)) ≤ L := by
    have : c * h ^ (-(1 / 4 : ℝ)) = kappa * (2 : ℝ) ^ (-(5 / 4 : ℝ)) * h ^ (-(1 / 4 : ℝ)) := by
      rw [hc]
    linarith
  have hinv : h ^ (-(1 / 4 : ℝ)) * h ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hh]; norm_num
  have hpos : 0 < h ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hh _
  have : c ≤ L * h ^ (1 / 4 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hr hpos.le
    calc c = c * (h ^ (-(1 / 4 : ℝ)) * h ^ (1 / 4 : ℝ)) := by rw [hinv, mul_one]
      _ = c * h ^ (-(1 / 4 : ℝ)) * h ^ (1 / 4 : ℝ) := by ring
      _ ≤ _ := this
  have : L * h ^ (1 / 4 : ℝ) ≤ |L| * h ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self L) hpos.le
  linarith

/-- `W^{1,∞}(𝕋^d)`: `u` has an essentially bounded weak gradient (and is itself essentially
bounded), i.e. `IsWeakGradientLp ⊤`. -/
def W1Infinity {d : ℕ} (u : Torus d → ℝ) : Prop := ∃ g : Torus d → Tangent d, IsWeakGradientLp ⊤ u g

theorem torusDist_two (p q : Torus 2) :
    torusDist p q = Real.sqrt (torusDist (fun _ : Fin 1 => p 0) (fun _ : Fin 1 => q 0) ^ 2 +
      torusDist (fun _ : Fin 1 => p 1) (fun _ : Fin 1 => q 1) ^ 2) := by
  unfold torusDist SharpLSI.flatDist
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_two]

theorem continuous_pairFun_W : Continuous (pairFun positiveH1.W) := by
  rw [pairFun_positiveH1]
  exact continuous_const.mul ((continuous_R.comp continuous_diffPt).sub continuous_const)

/-- H1006: The continuous `W` of H1004 is in `H¹(𝕋²)` but not in `W^{1,∞}(𝕋²)`. -/
theorem positive_example_excludes_w1_infinity :
    Continuous (fun p : Torus 1 × Torus 1 => positiveH1.W p.1 p.2) ∧
    MemH1 (pairFun positiveH1.W) ∧ ¬ W1Infinity (pairFun positiveH1.W) := by
  have hdata := positive_h1_interaction_data
  refine ⟨hdata.2.2.2.1, hdata.2.2.2.2.2.2.1, ?_⟩
  rintro ⟨g, hg⟩
  obtain ⟨v, hvc, hvu, hv⟩ :=
    (Lipschitz.lipschitz_representative_and_weak_gradient 2).2.1 _ g hg
  have hveq : v = pairFun positiveH1.W :=
    Lipschitz.continuous_ae_eq hvc continuous_pairFun_W hvu
  subst hveq
  obtain ⟨_, _, hno⟩ := frequency_block_lower_bound_at_the_origin
  refine hno ⟨(MeasureTheory.eLpNorm g ⊤ (haar 2)).toReal, fun x y x' y' => ?_⟩
  have h := hv ![x 0, y 0] ![x' 0, y' 0]
  rw [torusDist_two] at h
  have ex : ∀ z : Torus 1, (fun _ : Fin 1 => z 0) = z := fun z => funext fun i => by
    rw [Subsingleton.elim i 0]
  simpa [pairFun, ex] using h

end DGPS.Examples.PositiveH1.Regularity
