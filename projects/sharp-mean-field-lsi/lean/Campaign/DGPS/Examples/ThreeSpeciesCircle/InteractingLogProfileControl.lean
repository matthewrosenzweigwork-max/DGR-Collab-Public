import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarLogEuler
import Mathlib.Analysis.Calculus.MeanValue

/-! The actual first score equation identifies the physical logarithmic
profile derivative. A common positive lower bound then transfers genuine root
and score uniform convergence to profile and first-derivative convergence. -/

noncomputable section
open MeasureTheory Filter Topology Set
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The physical derivative has no missing reference term: the reference score
in the first equation cancels exactly against the derivative of ellT. -/
theorem positiveScore_logFirstDerivative (h : ℝ) {v S : Torus 1 → ℝ}
    (hp : ∀ x, 0 < v x)
    (hd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t)+v (pt t)*sigT h (pt t))/2) t) :
    ∀ t, deriv (fun s : ℝ => Real.log (v (pt s)^2)-ellT h (pt s)) t = S (pt t)/v (pt t) := by
  intro t
  have hlog := ((hd t).pow 2).log (pow_ne_zero 2 (hp (pt t)).ne')
  have hell := hasDerivAt_smooth_one (isSmoothPeriodic_ellT h) t
  have hL : HasDerivAt (fun s : ℝ => Real.log (v (pt s)^2)-ellT h (pt s))
      (S (pt t)/v (pt t)) t := by
    convert hlog.sub hell using 1
    change S (pt t)/v (pt t) =
      (2*v (pt t)^(2-1)*((S (pt t)+v (pt t)*sigT h (pt t))/2))/v (pt t)^2-sigT h (pt t)
    field_simp [(hp (pt t)).ne']
    <;> ring
  exact hL.deriv

private theorem log_square_lipschitz {m : ℝ} (hm : 0 < m) {z w : ℝ}
    (hz : m ≤ z) (hw : m ≤ w) :
    |Real.log (z^2)-Real.log (w^2)| ≤ (2/m)*|z-w| := by
  have hd (t : ℝ) (ht : t ∈ Ici m) : HasDerivAt (fun z : ℝ => Real.log (z^2)) (2/t) t := by
    have ht0 := hm.trans_le ht
    convert ((hasDerivAt_id t).pow 2).log (pow_ne_zero 2 ht0.ne') using 1
    · funext y; rfl
    · change 2/t = (2*t^(2-1)*1)/t^2
      field_simp [ht0.ne'] <;> ring
  have hb (t : ℝ) (ht : t ∈ Ici m) : ‖2/t‖ ≤ 2/m := by
    have ht0 := hm.trans_le ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) ht0.le)]
    exact (div_le_div_iff₀ ht0 hm).2 (by have hmt : m ≤ t := ht; linarith)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z : ℝ => Real.log (z^2)) (f' := fun z => 2/z) (C := 2/m)
    (fun t ht => (hd t ht).hasDerivWithinAt) hb (convex_Ici m) hw hz
  simpa only [Real.norm_eq_abs] using he

/-- Genuine root and score uniform convergence on the same positive interval
imply uniform convergence of the physical log profile and its first derivative.
The baseline score bound is fixed before the sequence; no desired logarithmic
convergence or higher-derivative convergence is assumed. -/
theorem positiveRoot_logProfile_first_small (h m : ℝ) (hm : 0 < m)
    (v S : ℕ → Torus 1 → ℝ) (u S0 : Torus 1 → ℝ)
    (hvp : ∀ n x, m ≤ v n x) (hup : ∀ x, m ≤ u x)
    (hvd : ∀ (n : ℕ) (t : ℝ), HasDerivAt (fun s => v n (pt s))
      ((S n (pt t)+v n (pt t)*sigT h (pt t))/2) t)
    (hud : ∀ t : ℝ, HasDerivAt (fun s => u (pt s))
      ((S0 (pt t)+u (pt t)*sigT h (pt t))/2) t)
    (hS0 : Bdd (fun t => S0 (pt t)))
    (hV : USmall (fun n t => v n (pt t)-u (pt t)))
    (hS : USmall (fun n t => S n (pt t)-S0 (pt t))) :
    USmall (fun n t => (Real.log (v n (pt t)^2)-ellT h (pt t))-
      (Real.log (u (pt t)^2)-ellT h (pt t))) ∧
    USmall (fun n t => deriv (fun s : ℝ => Real.log (v n (pt s)^2)-ellT h (pt s)) t-
      deriv (fun s : ℝ => Real.log (u (pt s)^2)-ellT h (pt s)) t) := by
  have hlog : USmall (fun n t => Real.log (v n (pt t)^2)-Real.log (u (pt t)^2)) := by
    intro e he
    filter_upwards [hV (e*m/2) (by positivity)] with n hn t
    calc
      _ ≤ (2/m)*|v n (pt t)-u (pt t)| := log_square_lipschitz hm (hvp n _) (hup _)
      _ ≤ (2/m)*(e*m/2) := mul_le_mul_of_nonneg_left (hn t) (by positivity)
      _ = e := by field_simp [hm.ne']
  refine ⟨?_, ?_⟩
  · have he : (fun n t => (Real.log (v n (pt t)^2)-ellT h (pt t))-
        (Real.log (u (pt t)^2)-ellT h (pt t))) =
        fun n t => Real.log (v n (pt t)^2)-Real.log (u (pt t)^2) := by funext n t; ring
    rw [he]
    exact hlog
  obtain ⟨B, hB⟩ := hS0
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hvinv : ∀ n t, |(1 : ℝ)/v n (pt t)| ≤ 1/m := by
    intro n t
    rw [abs_div, abs_one, abs_of_pos (hm.trans_le (hvp n _))]
    exact (div_le_div_iff₀ (hm.trans_le (hvp n _)) hm).2 (by linarith [hvp n (pt t)])
  have hbase : ∀ t, |S0 (pt t)/u (pt t)| ≤ B/m := by
    intro t
    rw [abs_div, abs_of_pos (hm.trans_le (hup _))]
    calc
      _ ≤ B/u (pt t) := div_le_div_of_nonneg_right (hB t) (hm.trans_le (hup _)).le
      _ ≤ B/m := (div_le_div_iff₀ (hm.trans_le (hup _)) hm).2
        (mul_le_mul_of_nonneg_left (hup (pt t)) hB0)
  have hfirst := hS.mul_bdd (1/m) (Eventually.of_forall fun n => hvinv n)
  have hsecond := (hV.mul_bdd (B/m) (Eventually.of_forall fun _ => hbase)).mul_bdd
    (1/m) (Eventually.of_forall fun n => hvinv n)
  have he : (fun n t => deriv (fun s : ℝ => Real.log (v n (pt s)^2)-ellT h (pt s)) t-
      deriv (fun s : ℝ => Real.log (u (pt s)^2)-ellT h (pt s)) t) =
      fun n t => (S n (pt t)-S0 (pt t))*(1/v n (pt t))-
        ((v n (pt t)-u (pt t))*(S0 (pt t)/u (pt t)))*(1/v n (pt t)) := by
    funext n t
    rw [positiveScore_logFirstDerivative h (fun x => hm.trans_le (hvp n x)) (hvd n),
      positiveScore_logFirstDerivative h (fun x => hm.trans_le (hup x)) hud]
    field_simp [(hm.trans_le (hvp n (pt t))).ne', (hm.trans_le (hup (pt t))).ne']
    <;> ring
  rw [he]
  exact hfirst.sub hsecond

end DGPS.Examples.ThreeSpeciesCircle
