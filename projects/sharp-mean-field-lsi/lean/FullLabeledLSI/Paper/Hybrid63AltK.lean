import FullLabeledLSI.Paper.Hybrid63AltJ

/-!
# Proposition 6.3: the `(7.21)` terms `errT1`, `errT5` are small

For `N` large (depending on `δ` and the data, not on `c`), uniformly over the coefficient arrays
with `SpectralCoeff lam L c` and `∑ c² ≤ B²`: `n > 0`, `errT1 ≤ τ` and `errT5 ≤ τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

theorem choose_t (Cs Mq Kq bmax τ : ℝ) (hCs : 0 ≤ Cs) (hMq : 0 ≤ Mq) (hKq : 0 ≤ Kq)
    (hτ : 0 < τ) :
    ∃ t : ℝ, 0 < t ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ, 0 ≤ x → x ≤ bmax / N →
      Cs * ((t / 4) * Mq + Kq * x / (2 * t)) ≤ τ := by
  set t : ℝ := τ / (2 * (Cs * Mq / 4 + 1)) with ht
  have hp : 0 < Cs * Mq / 4 + 1 := by positivity
  have htpos : 0 < t := by positivity
  have h1 : Cs * ((t / 4) * Mq) ≤ τ / 2 := by
    have : Cs * ((t / 4) * Mq) = t * (Cs * Mq / 4) := by ring
    rw [this, ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  set q : ℝ := Cs * Kq + 1 with hq
  have hqpos : 0 < q := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max (bmax * q / (τ * t / 2)) 1)
  refine ⟨t, htpos, N0 + 1, fun N hN x hx0 hxb => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : (N0 : ℝ) < N := by exact_mod_cast (by omega : N0 < N)
    have h1' : (1 : ℝ) ≤ max (bmax * q / (τ * t / 2)) 1 := le_max_right _ _
    linarith
  have hNbig : bmax * q / (τ * t / 2) < N := by
    have : (N0 : ℝ) < N := by exact_mod_cast (by omega : N0 < N)
    have h1' : bmax * q / (τ * t / 2) ≤ max (bmax * q / (τ * t / 2)) 1 := le_max_left _ _
    linarith
  have hx : x ≤ τ * t / 2 / q := by
    have h2 : bmax / N ≤ τ * t / 2 / q := by
      rw [div_le_div_iff₀ hNpos hqpos]
      rw [div_lt_iff₀ (by positivity)] at hNbig
      nlinarith
    exact hxb.trans h2
  have h2 : Cs * (Kq * x / (2 * t)) ≤ τ / 2 := by
    have : Cs * (Kq * x / (2 * t)) = (Cs * Kq) * x / (2 * t) := by ring
    rw [this, div_le_iff₀ (by positivity)]
    have hxq : x * q ≤ τ * t / 2 := by
      rw [le_div_iff₀ hqpos] at hx; exact hx
    have : (Cs * Kq) * x ≤ x * q := by rw [hq]; nlinarith
    nlinarith
  calc Cs * ((t / 4) * Mq + Kq * x / (2 * t)) =
      Cs * ((t / 4) * Mq) + Cs * (Kq * x / (2 * t)) := by ring
    _ ≤ τ / 2 + τ / 2 := add_le_add h1 h2
    _ = τ := by ring

section perN
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
  {e e' : ℕ → Torus d → ℝ}

theorem measurable_fluct (hG : GoodBasis μ e') (N n : ℕ) :
    Measurable (fun X : Config N d => fluct e' N n X) := by
  unfold fluct
  exact measurable_const.mul (Finset.measurable_sum _ fun l _ =>
    (hG.meas _).comp (measurable_pi_apply l))

theorem measurable_Zlow (hG : GoodBasis μ e') {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (m : Fin J) : Measurable (fun X : Config N d => Zlow e' c δ X m) := by
  unfold Zlow
  exact measurable_const.mul (Finset.measurable_sum _ fun l _ =>
    (hG.meas _).comp (measurable_pi_apply l))

theorem measurable_zext_Zlow (hG : GoodBasis μ e') {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (δ : ℝ) (i : ℕ) :
    Measurable (fun X : Config N d => zext (fun m : Fin J => Zlow e' c δ X m) i) := by
  unfold zext
  by_cases h : i < J
  · simp only [h, dite_true]; exact measurable_Zlow hG c δ _
  · simp only [h, dite_false]; exact measurable_const

theorem errT_eq_integral (hG : GoodBasis μ e') (A : FiniteRankApprox W μ e) (R : ℕ)
    {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (Qm : ℕ → ℕ → ℝ) (c0 : ℝ) (w : (ℕ → ℝ) → ℝ) (hw : ∀ y, w y = quadFA (A.s R) Qm y + c0) :
    ∫ X, polyEval e' c X ^ 2 * w (fun n => fluct e' N n X) ∂Measure.pi (fun _ : Fin N => μ) -
      ∫ X, polyEval e' c X ^ 2 * w (zext (fun m : Fin J => Zlow e' c δ X m))
        ∂Measure.pi (fun _ : Fin N => μ) =
    ∫ X, polyEval e' c X ^ 2 * (quadFA (A.s R) Qm (fun n => fluct e' N n X) -
      quadFA (A.s R) Qm (zext (fun m : Fin J => Zlow e' c δ X m)))
        ∂Measure.pi (fun _ : Fin N => μ) := by
  obtain ⟨Kf, hKf⟩ := polyEval_bounded hG c
  choose Ki hKi using fluct_bdd hG N
  choose Kl hKl using Zlow_bdd hG c δ
  set Kl' : ℕ → ℝ := fun i => if h : i < J then |Kl ⟨i, h⟩| else 0 with hKl'
  set Kz : ℝ := ∑ i ∈ A.s R, (|Ki i| + Kl' i) with hKz
  have hz1 : ∀ i ∈ A.s R, ∀ X : Config N d, |fluct e' N i X| ≤ Kz := by
    intro i hi X
    have h1 : |fluct e' N i X| ≤ |Ki i| + Kl' i := by
      have : 0 ≤ Kl' i := by
        simp only [hKl']; split_ifs <;> positivity
      linarith [hKi i X, le_abs_self (Ki i)]
    exact h1.trans (Finset.single_le_sum (f := fun i => |Ki i| + Kl' i)
      (fun i _ => by
        have : 0 ≤ Kl' i := by simp only [hKl']; split_ifs <;> positivity
        positivity) hi)
  have hz2 : ∀ i ∈ A.s R, ∀ X : Config N d, |zext (fun m : Fin J => Zlow e' c δ X m) i| ≤ Kz := by
    intro i hi X
    have h1 : |zext (fun m : Fin J => Zlow e' c δ X m) i| ≤ |Ki i| + Kl' i := by
      unfold zext
      by_cases h : i < J
      · simp only [h, dite_true, hKl']
        have := (hKl ⟨i, h⟩ X).trans (le_abs_self _)
        linarith [abs_nonneg (Ki i)]
      · simp only [h, dite_false, hKl', abs_zero]
        positivity
    exact h1.trans (Finset.single_le_sum (f := fun i => |Ki i| + Kl' i)
      (fun i _ => by
        have : 0 ≤ Kl' i := by simp only [hKl']; split_ifs <;> positivity
        positivity) hi)
  have := integral_sub_quad (P := Measure.pi (fun _ : Fin N => μ))
    (f := fun X : Config N d => polyEval e' c X) (Kf := Kf) (measurable_polyEval hG c) hKf
    (s := A.s R) Qm (z := fun i X => fluct e' N i X)
    (z' := fun i X => zext (fun m : Fin J => Zlow e' c δ X m) i) (Kz := Kz)
    (fun i _ => measurable_fluct hG N i) hz1
    (fun i _ => measurable_zext_Zlow hG c δ i) hz2 w c0 hw
  exact this

end perN

end SharpLSI.FL

end
