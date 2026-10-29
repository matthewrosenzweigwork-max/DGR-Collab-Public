import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import SharpSymmetricLSI.Infra.HeatTorus2
import DGPS.Foundations.Torus
import DGPS.SingularCounterexample.Scales

open MeasureTheory
open Filter Topology

namespace DGPS.SingularCounterexample

/-- A fixed smooth step from zero on `(-∞, 1/2]` to one on `[1, ∞)`. -/
noncomputable def chi : ℝ → ℝ := fun x => Real.smoothTransition (2 * x - 1)

theorem chi_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) chi := by
  unfold chi
  have harg : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => 2 * x - 1) := by fun_prop
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp harg

theorem chi_nonneg (x : ℝ) : 0 ≤ chi x := by
  exact Real.smoothTransition.nonneg _

theorem chi_le_one (x : ℝ) : chi x ≤ 1 := by
  exact Real.smoothTransition.le_one _

theorem chi_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 2) : chi x = 0 := by
  unfold chi
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

theorem chi_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : chi x = 1 := by
  unfold chi
  apply Real.smoothTransition.one_of_one_le
  nlinarith

theorem chi_deriv_zero_outside {x : ℝ} (hx : x ∉ Set.Icc (1 / 2) 1) :
    deriv chi x = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · have hnear : chi =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact chi_eq_zero_of_le (le_of_lt hy)
    rw [hnear.deriv_eq]
    simp
  · have hnear : chi =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact chi_eq_one_of_one_le (le_of_lt hy)
    rw [hnear.deriv_eq]
    simp

theorem chi_deriv_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv chi x| ≤ C := by
  have hderiv : Continuous (deriv chi) :=
    chi_contDiff.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hderiv.continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC (1 / 2) (by norm_num)
    exact le_trans (abs_nonneg _) (by simpa [Real.norm_eq_abs] using h)
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (1 / 2) 1
  · exact (by simpa [Real.norm_eq_abs] using hC x hx)
  · rw [chi_deriv_zero_outside hx, abs_zero]
    exact hC0

/-- The valley cutoff on the lifted arc from zero to the first satellite peak. -/
noncomputable def valleyCutoffLift (n : ℕ) (t : ℝ) : ℝ :=
  chi (t / width n) * chi ((separation n - t) / width n)

theorem valleyCutoffLift_contDiff (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (valleyCutoffLift n) := by
  have harg₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ => t / width n) := by
    fun_prop
  have harg₂ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun t : ℝ => (separation n - t) / width n) := by
    fun_prop
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun t : ℝ => chi (t / width n) * chi ((separation n - t) / width n))
  exact (chi_contDiff.comp harg₁).mul (chi_contDiff.comp harg₂)

theorem valleyCutoffLift_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ valleyCutoffLift n t :=
  mul_nonneg (chi_nonneg _) (chi_nonneg _)

theorem valleyCutoffLift_deriv_formula (n : ℕ) (t : ℝ) :
    deriv (valleyCutoffLift n) t =
      deriv chi (t / width n) / width n * chi ((separation n - t) / width n) -
        chi (t / width n) * deriv chi ((separation n - t) / width n) / width n := by
  have harg₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s : ℝ => s / width n) := by fun_prop
  have harg₂ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun s : ℝ => (separation n - s) / width n) := by fun_prop
  have hleft : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s : ℝ => chi (s / width n)) :=
    chi_contDiff.comp harg₁
  have hright : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun s : ℝ => chi ((separation n - s) / width n)) :=
    chi_contDiff.comp harg₂
  have hleftDiff : DifferentiableAt ℝ (fun s : ℝ => chi (s / width n)) t :=
    hleft.contDiffAt.differentiableAt (by norm_num)
  have hrightDiff : DifferentiableAt ℝ
      (fun s : ℝ => chi ((separation n - s) / width n)) t :=
    hright.contDiffAt.differentiableAt (by norm_num)
  have hchiLeft : DifferentiableAt ℝ chi (t / width n) :=
    chi_contDiff.contDiffAt.differentiableAt (by norm_num)
  have hchiRight : DifferentiableAt ℝ chi ((separation n - t) / width n) :=
    chi_contDiff.contDiffAt.differentiableAt (by norm_num)
  have hargLeft : DifferentiableAt ℝ (fun s : ℝ => s / width n) t :=
    harg₁.contDiffAt.differentiableAt (by norm_num)
  have hargRight : DifferentiableAt ℝ
      (fun s : ℝ => (separation n - s) / width n) t :=
    harg₂.contDiffAt.differentiableAt (by norm_num)
  change deriv (fun s : ℝ => chi (s / width n) *
      chi ((separation n - s) / width n)) t = _
  change deriv ((fun s : ℝ => chi (s / width n)) *
      (fun s : ℝ => chi ((separation n - s) / width n))) t = _
  rw [deriv_mul hleftDiff hrightDiff]
  rw [show (fun s : ℝ => chi (s / width n)) =
      chi ∘ (fun s : ℝ => s / width n) by rfl]
  rw [deriv_comp t hchiLeft hargLeft, deriv_div_const]
  have hId : deriv (fun s : ℝ => s) t = 1 := by
    change deriv id t = 1
    exact deriv_id t
  rw [hId]
  rw [show (fun s : ℝ => chi ((separation n - s) / width n)) =
      chi ∘ (fun s : ℝ => (separation n - s) / width n) by rfl]
  rw [deriv_comp t hchiRight hargRight, deriv_div_const]
  have hlin : deriv (fun s : ℝ => separation n - s) t = -1 := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => separation n) t :=
      differentiableAt_const _
    change deriv ((fun _ : ℝ => separation n) - id) t = -1
    rw [deriv_sub hc differentiableAt_id, deriv_const, deriv_id]
    norm_num
  rw [hlin]
  ring

theorem valleyCutoffLift_deriv_bound (n : ℕ) (t : ℝ)
    (C : ℝ) (hC : ∀ x, |deriv chi x| ≤ C) :
    |deriv (valleyCutoffLift n) t| ≤ 2 * C / width n := by
  have heps := width_pos n
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (deriv chi 0)) (hC 0)
  have hleft : |deriv chi (t / width n) / width n *
      chi ((separation n - t) / width n)| ≤ C / width n := by
    rw [abs_mul, abs_div, abs_of_pos heps]
    have hchi : |chi ((separation n - t) / width n)| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [chi_nonneg ((separation n - t) / width n)], chi_le_one _⟩
    calc
      |deriv chi (t / width n)| / width n *
          |chi ((separation n - t) / width n)| ≤ C / width n * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right (hC (t / width n)) heps.le) hchi
              (abs_nonneg _) (div_nonneg hC0 heps.le)
      _ = C / width n := by ring
  have hright : |chi (t / width n) *
      deriv chi ((separation n - t) / width n) / width n| ≤ C / width n := by
    rw [abs_div, abs_mul, abs_of_pos heps]
    have hchi : |chi (t / width n)| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [chi_nonneg (t / width n)], chi_le_one _⟩
    calc
      |chi (t / width n)| * |deriv chi ((separation n - t) / width n)| /
          width n ≤ 1 * C / width n := by
            apply div_le_div_of_nonneg_right _ heps.le
            exact mul_le_mul hchi (hC _) (abs_nonneg _) (by norm_num)
      _ = C / width n := by ring
  calc
    |deriv (valleyCutoffLift n) t| =
        |deriv chi (t / width n) / width n *
          chi ((separation n - t) / width n) -
            chi (t / width n) * deriv chi ((separation n - t) / width n) / width n| := by
          rw [valleyCutoffLift_deriv_formula]
    _ ≤ |deriv chi (t / width n) / width n *
          chi ((separation n - t) / width n)| +
        |chi (t / width n) * deriv chi ((separation n - t) / width n) / width n| :=
          abs_sub _ _
    _ ≤ C / width n + C / width n := add_le_add hleft hright
    _ = 2 * C / width n := by ring

theorem valleyCutoffLift_deriv_support (n : ℕ) (t : ℝ)
    (hderiv : deriv (valleyCutoffLift n) t ≠ 0) :
    t ∈ Set.Icc (width n / 2) (width n) ∨
      t ∈ Set.Icc (separation n - width n) (separation n - width n / 2) := by
  by_cases hleft : t ∈ Set.Icc (width n / 2) (width n)
  · exact Or.inl hleft
  by_cases hright : t ∈ Set.Icc (separation n - width n)
      (separation n - width n / 2)
  · exact Or.inr hright
  have hchiLeft : deriv chi (t / width n) = 0 := by
    apply chi_deriv_zero_outside
    intro hx
    apply hleft
    rw [Set.mem_Icc]
    rcases hx with ⟨hxlo, hxhi⟩
    rw [le_div_iff₀ (width_pos n)] at hxlo
    rw [div_le_iff₀ (width_pos n)] at hxhi
    constructor <;> nlinarith
  have hchiRight : deriv chi ((separation n - t) / width n) = 0 := by
    apply chi_deriv_zero_outside
    intro hx
    apply hright
    rw [Set.mem_Icc]
    rcases hx with ⟨hxlo, hxhi⟩
    rw [le_div_iff₀ (width_pos n)] at hxlo
    rw [div_le_iff₀ (width_pos n)] at hxhi
    constructor <;> nlinarith
  have hformula := valleyCutoffLift_deriv_formula n t
  rw [hchiLeft, hchiRight] at hformula
  simp at hformula
  exact (hderiv hformula).elim

theorem valleyCutoffLift_le_one (n : ℕ) (t : ℝ) :
    valleyCutoffLift n t ≤ 1 := by
  unfold valleyCutoffLift
  calc
    chi (t / width n) * chi ((separation n - t) / width n)
        ≤ 1 * chi ((separation n - t) / width n) :=
          mul_le_mul_of_nonneg_right (chi_le_one _) (chi_nonneg _)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (chi_le_one _) (by norm_num)
    _ = 1 := by norm_num

theorem valleyCutoffLift_eq_zero_of_le {n : ℕ} {t : ℝ}
    (ht : t ≤ width n / 2) : valleyCutoffLift n t = 0 := by
  unfold valleyCutoffLift
  rw [chi_eq_zero_of_le]
  · simp
  · rw [div_le_iff₀ (width_pos n)]
    linarith

theorem valleyCutoffLift_eq_zero_of_ge {n : ℕ} {t : ℝ}
    (ht : separation n - width n / 2 ≤ t) : valleyCutoffLift n t = 0 := by
  unfold valleyCutoffLift
  have hz : chi ((separation n - t) / width n) = 0 :=
    chi_eq_zero_of_le (by
      rw [div_le_iff₀ (width_pos n)]
      linarith)
  simp [hz]

theorem valleyCutoffLift_eq_one_of_mem_Icc {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (separation n / 3) (2 * separation n / 3)) :
    valleyCutoffLift n t = 1 := by
  have heps := width_le_separation_div_hundred n
  have htleft : width n ≤ t := by nlinarith [separation_pos n, ht.1]
  have htright : width n ≤ separation n - t := by nlinarith [separation_pos n, ht.2]
  have hleft : chi (t / width n) = 1 :=
    chi_eq_one_of_one_le (by
      rw [one_le_div (width_pos n)]
      exact htleft)
  have hright : chi ((separation n - t) / width n) = 1 :=
    chi_eq_one_of_one_le (by
      rw [one_le_div (width_pos n)]
      exact htright)
  simp [valleyCutoffLift, hleft, hright]

/-- The even, one-periodic lift of the two cutoff arcs. -/
noncomputable def cutoffLine (n : ℕ) (t : ℝ) : ℝ :=
  valleyCutoffLift n (Int.fract t) + valleyCutoffLift n (1 - Int.fract t)

theorem cutoffLine_periodic (n : ℕ) : Function.Periodic (cutoffLine n) 1 := by
  intro t
  simp [cutoffLine, Int.fract_add_one]

theorem cutoffLine_contDiff (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cutoffLine n) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases hfrac : Int.fract t = 0
  · obtain ⟨k, htk⟩ := (Int.fract_eq_zero_iff).1 hfrac
    let δ : ℝ := width n / 4
    have hδpos : 0 < δ := by
      simpa [δ] using div_pos (width_pos n) (by norm_num : (0 : ℝ) < 4)
    have hwidthsmall : width n < 1 := by
      have hw := width_le_ten_neg_twenty_four n
      have h10 : (10 : ℝ) ^ (-(24 : ℝ)) < 1 := by
        norm_num [Real.rpow_neg, Real.rpow_natCast]
      exact lt_of_le_of_lt hw h10
    have hδlt : δ < 1 := by dsimp [δ]; linarith
    have hsep : separation n < 1 / 2 := by
      have hs := separation_le_ten_neg_four n
      have h10 : (10 : ℝ) ^ (-(4 : ℝ)) < 1 / 2 := by
        norm_num [Real.rpow_neg, Real.rpow_natCast]
      exact lt_of_le_of_lt hs h10
    have hIoo : Set.Ioo (t - δ) (t + δ) ∈ 𝓝 t := by
      apply Ioo_mem_nhds
      · linarith [hδpos]
      · linarith [hδpos]
    have hnear : cutoffLine n =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [hIoo] with y hy
      by_cases hty : (k : ℝ) ≤ y
      · have hfloor : Int.floor y = k := by
          rw [Int.floor_eq_iff]
          constructor
          · exact hty
          · have hy' := hy.2
            rw [← htk] at hy'
            linarith [hy', hδlt]
        have hfract_y : Int.fract y = y - (k : ℝ) := by
          calc
            Int.fract y = y - (Int.floor y : ℝ) := by rw [← Int.self_sub_floor]
            _ = y - (k : ℝ) := by rw [hfloor]
        have hleft : valleyCutoffLift n (Int.fract y) = 0 := by
          rw [hfract_y]
          apply valleyCutoffLift_eq_zero_of_le
          have hy' := hy.2
          rw [← htk] at hy'
          dsimp [δ] at hy' ⊢
          linarith [hy']
        have hright : valleyCutoffLift n (1 - Int.fract y) = 0 := by
          rw [hfract_y]
          apply valleyCutoffLift_eq_zero_of_ge
          have hy' := hy.2
          rw [← htk] at hy'
          dsimp [δ] at hy' ⊢
          nlinarith [hy', hsep, width_pos n]
        simp [cutoffLine, hleft, hright]
      · have hylt : y < (k : ℝ) := lt_of_not_ge hty
        have hfloor : Int.floor y = k - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · have hy' := hy.1
            rw [← htk] at hy'
            have hcast : ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by norm_num
            rw [hcast]
            linarith [hy', hδlt]
          · have hy' : y < (k : ℝ) := hylt
            simpa only [Int.cast_sub, Int.cast_one, sub_add_cancel] using hy'
        have hfract_y : Int.fract y = 1 + (y - t) := by
          calc
            Int.fract y = y - (Int.floor y : ℝ) := by rw [← Int.self_sub_floor]
            _ = 1 + (y - t) := by
              rw [hfloor]
              push_cast
              rw [← htk]
              ring
        have hleft : valleyCutoffLift n (Int.fract y) = 0 := by
          rw [hfract_y]
          apply valleyCutoffLift_eq_zero_of_ge
          have hy' := hy.1
          rw [← htk] at hy'
          dsimp [δ] at hy' ⊢
          nlinarith [hy', hsep, width_pos n]
        have hright : valleyCutoffLift n (1 - Int.fract y) = 0 := by
          rw [hfract_y]
          apply valleyCutoffLift_eq_zero_of_le
          have hy' := hy.1
          rw [← htk] at hy'
          dsimp [δ] at hy' ⊢
          linarith [hy']
        simp [cutoffLine, hleft, hright]
    have hconst : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : ℝ => (0 : ℝ)) := contDiff_const
    exact hconst.contDiffAt.congr_of_eventuallyEq hnear
  · let k : ℤ := Int.floor t
    have hfrac_pos : 0 < Int.fract t := by
      by_contra hn
      have hz : Int.fract t = 0 :=
        le_antisymm (le_of_not_gt hn) (Int.fract_nonneg t)
      exact hfrac hz
    have hfloor_lt : (k : ℝ) < t := by
      have hfract_as : Int.fract t = t - (k : ℝ) := by
        dsimp [k]
      rw [hfract_as] at hfrac_pos
      linarith
    have hnear : cutoffLine n =ᶠ[𝓝 t]
        (fun y : ℝ => valleyCutoffLift n (y - (k : ℝ)) +
          valleyCutoffLift n (1 - (y - (k : ℝ)))) := by
      filter_upwards [Ioo_mem_nhds hfloor_lt (Int.lt_floor_add_one t)] with y hy
      have hfloor : Int.floor y = k := by
        rw [Int.floor_eq_iff]
        exact ⟨hy.1.le, hy.2⟩
      have hfract_y : Int.fract y = y - (k : ℝ) := by
        calc
          Int.fract y = y - (Int.floor y : ℝ) := by rw [← Int.self_sub_floor]
          _ = y - (k : ℝ) := by rw [hfloor]
      simp [cutoffLine, hfract_y]
    have harg₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => y - (k : ℝ)) := by
      fun_prop
    have harg₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 1 - (y - (k : ℝ))) := by
      fun_prop
    have hbase := valleyCutoffLift_contDiff n
    have hg : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun y : ℝ => valleyCutoffLift n (y - (k : ℝ)) +
          valleyCutoffLift n (1 - (y - (k : ℝ)))) :=
      (hbase.comp harg₁).add (hbase.comp harg₂)
    exact hg.contDiffAt.congr_of_eventuallyEq hnear

private theorem cutoffLine_deriv_formula_on_Ioo {n : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    deriv (cutoffLine n) t =
      deriv (valleyCutoffLift n) t - deriv (valleyCutoffLift n) (1 - t) := by
  have hnear : cutoffLine n =ᶠ[𝓝 t]
      (fun y : ℝ => valleyCutoffLift n y + valleyCutoffLift n (1 - y)) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with y hy
    have hfloor : Int.floor y = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · simpa using hy.1.le
      · simpa using hy.2
    have hfract : Int.fract y = y := by
      calc
        Int.fract y = y - (Int.floor y : ℝ) := by rw [← Int.self_sub_floor]
        _ = y := by simp [hfloor]
    simp [cutoffLine, hfract]
  rw [hnear.deriv_eq]
  have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (valleyCutoffLift n) :=
    valleyCutoffLift_contDiff n
  have harg : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 1 - y) := by fun_prop
  have hleftDiff : DifferentiableAt ℝ (valleyCutoffLift n) t :=
    hbase.contDiffAt.differentiableAt (by norm_num)
  have hrightDiff : DifferentiableAt ℝ (valleyCutoffLift n) (1 - t) :=
    hbase.contDiffAt.differentiableAt (by norm_num)
  have hargDiff : DifferentiableAt ℝ (fun y : ℝ => 1 - y) t :=
    harg.contDiffAt.differentiableAt (by norm_num)
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => valleyCutoffLift n (1 - y)) := hbase.comp harg
  have hcompDiff : DifferentiableAt ℝ
      (fun y : ℝ => valleyCutoffLift n (1 - y)) t :=
    hcomp.contDiffAt.differentiableAt (by norm_num)
  change deriv ((fun y : ℝ => valleyCutoffLift n y) +
      (fun y : ℝ => valleyCutoffLift n (1 - y))) t = _
  rw [deriv_add hleftDiff hcompDiff]
  rw [show (fun y : ℝ => valleyCutoffLift n (1 - y)) =
      (valleyCutoffLift n) ∘ (fun y : ℝ => 1 - y) by rfl]
  rw [deriv_comp t hrightDiff hargDiff]
  have hinner : deriv (fun y : ℝ => 1 - y) t = -1 := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) t := differentiableAt_const _
    change deriv ((fun _ : ℝ => (1 : ℝ)) - id) t = -1
    rw [deriv_sub hc differentiableAt_id, deriv_const, deriv_id]
    norm_num
  rw [hinner]
  ring

theorem cutoffLine_deriv_support_on_Ioc {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) (hderiv : deriv (cutoffLine n) t ≠ 0) :
    t ∈ Set.Icc (0 : ℝ) (width n) ∨
      t ∈ Set.Icc (separation n - width n) (separation n + width n) ∨
      t ∈ Set.Icc (1 - separation n - width n) (1 - separation n + width n) ∨
      t ∈ Set.Icc (1 - width n) 1 := by
  rcases eq_or_lt_of_le ht.2 with htEq | htlt
  · subst t
    right
    right
    right
    exact ⟨by linarith [width_pos n], le_rfl⟩
  have hformula := cutoffLine_deriv_formula_on_Ioo (n := n) ht.1 htlt
  by_cases hleft : deriv (valleyCutoffLift n) t = 0
  · have hright : deriv (valleyCutoffLift n) (1 - t) ≠ 0 := by
      intro hz
      apply hderiv
      rw [hformula, hleft, hz]
      ring
    rcases valleyCutoffLift_deriv_support n (1 - t) hright with hnear0 | hnearSat
    · right
      right
      right
      constructor <;> nlinarith [hnear0.1, hnear0.2, width_pos n]
    · right
      right
      left
      constructor <;> nlinarith [hnearSat.1, hnearSat.2, width_pos n]
  · rcases valleyCutoffLift_deriv_support n t hleft with hnear0 | hnearSat
    · left
      constructor <;> nlinarith [hnear0.1, hnear0.2, width_pos n]
    · right
      left
      constructor <;> nlinarith [hnearSat.1, hnearSat.2, width_pos n]

private theorem cutoffLine_zero_nhds_zero (n : ℕ) :
    cutoffLine n =ᶠ[𝓝 0] fun _ : ℝ => (0 : ℝ) := by
  let δ : ℝ := width n / 4
  have hδpos : 0 < δ := by
    simpa [δ] using div_pos (width_pos n) (by norm_num : (0 : ℝ) < 4)
  have hwidthlt : width n < 1 := by
    have hw := width_le_ten_neg_twenty_four n
    have hsmall : (10 : ℝ) ^ (-(24 : ℝ)) < 1 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    exact lt_of_le_of_lt hw hsmall
  have hδsmall : δ ≤ width n / 2 := by dsimp [δ]; nlinarith [width_pos n]
  have hδltone : δ < 1 := by dsimp [δ]; linarith
  have hsep : separation n < 1 / 2 := by
    have hs := separation_le_ten_neg_four n
    have hsmall : (10 : ℝ) ^ (-(4 : ℝ)) < 1 / 2 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    exact lt_of_le_of_lt hs hsmall
  have hgap : separation n - width n / 2 ≤ 1 - δ := by
    dsimp [δ]
    nlinarith [hsep, width_pos n, hwidthlt]
  have hIoo : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := by
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [hIoo] with y hy
  by_cases hnonneg : 0 ≤ y
  · have hfloor : Int.floor y = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · simpa using hnonneg
      · norm_num
        linarith [hy.2, hδltone]
    have hfract : Int.fract y = y := by
      calc
        Int.fract y = y - (Int.floor y : ℝ) := by rw [← Int.self_sub_floor]
        _ = y := by simp [hfloor]
    have hleft : valleyCutoffLift n y = 0 :=
      valleyCutoffLift_eq_zero_of_le (le_trans hy.2.le hδsmall)
    have hright : valleyCutoffLift n (1 - y) = 0 :=
      valleyCutoffLift_eq_zero_of_ge (by linarith [hy.2, hgap])
    simp [cutoffLine, hfract, hleft, hright]
  · have hylt : y < 0 := lt_of_not_ge hnonneg
    have hfloor : Int.floor y = -1 := by
      rw [Int.floor_eq_iff]
      constructor
      · norm_num
        linarith [hy.1, hδltone]
      · norm_num
        exact hylt
    have hfract : Int.fract y = 1 + y := by
      calc
        Int.fract y = y - (Int.floor y : ℝ) := by rw [← Int.self_sub_floor]
        _ = 1 + y := by simp [hfloor]; ring
    have hleft : valleyCutoffLift n (Int.fract y) = 0 := by
      rw [hfract]
      apply valleyCutoffLift_eq_zero_of_ge
      linarith [hy.1, hgap]
    have hright : valleyCutoffLift n (1 - Int.fract y) = 0 := by
      rw [hfract]
      apply valleyCutoffLift_eq_zero_of_le
      linarith [hy.1, hδsmall]
    simp [cutoffLine, hleft, hright]

private theorem cutoffLine_deriv_zero_at_zero (n : ℕ) :
    deriv (cutoffLine n) 0 = 0 := by
  rw [(cutoffLine_zero_nhds_zero n).deriv_eq]
  simp

private theorem cutoffLine_deriv_periodic (n : ℕ) (t : ℝ) :
    deriv (cutoffLine n) (t + 1) = deriv (cutoffLine n) t := by
  have hfun : (fun s : ℝ => cutoffLine n (s + 1)) = cutoffLine n := by
    funext s
    exact cutoffLine_periodic n s
  have hEq := congrArg (fun f : ℝ → ℝ => deriv f t) hfun
  have hlineDiff : DifferentiableAt ℝ (cutoffLine n) (t + 1) :=
    (cutoffLine_contDiff n).contDiffAt.differentiableAt (by norm_num)
  have hargDiff : DifferentiableAt ℝ (fun s : ℝ => s + 1) t := by fun_prop
  have hcomp : deriv (fun s : ℝ => cutoffLine n (s + 1)) t =
      deriv (cutoffLine n) (t + 1) := by
    change deriv ((cutoffLine n) ∘ (fun s : ℝ => s + 1)) t = _
    rw [deriv_comp t hlineDiff hargDiff, deriv_add_const 1]
    have hId : deriv (fun s : ℝ => s) t = 1 := by
      change deriv id t = 1
      exact deriv_id t
    rw [hId]
    ring
  exact hcomp.symm.trans hEq

theorem cutoffLine_deriv_bound_on_Ioc (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) (C : ℝ)
    (hC : ∀ x, |deriv chi x| ≤ C) :
    |deriv (cutoffLine n) t| ≤ 4 * C / width n := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (deriv chi 0)) (hC 0)
  rcases eq_or_lt_of_le ht.2 with htEq | htlt
  · subst t
    have hper : deriv (cutoffLine n) 1 = deriv (cutoffLine n) 0 := by
      simpa using cutoffLine_deriv_periodic n 0
    rw [hper, cutoffLine_deriv_zero_at_zero n]
    simpa using div_nonneg (show 0 ≤ 4 * C by positivity) (width_pos n).le
  · have hformula := cutoffLine_deriv_formula_on_Ioo (n := n) ht.1 htlt
    calc
      |deriv (cutoffLine n) t| =
          |deriv (valleyCutoffLift n) t - deriv (valleyCutoffLift n) (1 - t)| := by
            rw [hformula]
      _ ≤ |deriv (valleyCutoffLift n) t| +
          |deriv (valleyCutoffLift n) (1 - t)| := abs_sub _ _
      _ ≤ 2 * C / width n + 2 * C / width n :=
            add_le_add (valleyCutoffLift_deriv_bound n t C hC)
              (valleyCutoffLift_deriv_bound n (1 - t) C hC)
      _ = 4 * C / width n := by ring

/-- The squared derivative has size `O(εₙ⁻²)` on a set of length `O(εₙ)`. -/
theorem cutoffLine_deriv_sq_integral_bound_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ t in Set.Ioc (0 : ℝ) 1, |deriv (cutoffLine n) t| ^ 2 ∂volume) ≤
        96 * C ^ 2 / width n := by
  obtain ⟨C, hC0, hC⟩ := chi_deriv_bounded
  refine ⟨C, hC0, fun n => ?_⟩
  let Azero : Set ℝ := Set.Icc (0 : ℝ) (width n)
  let Aplus : Set ℝ := Set.Icc (separation n - width n) (separation n + width n)
  let Aminus : Set ℝ := Set.Icc (1 - separation n - width n) (1 - separation n + width n)
  let Aend : Set ℝ := Set.Icc (1 - width n) 1
  let U : Set ℝ := Azero ∪ (Aplus ∪ (Aminus ∪ Aend))
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let F : ℝ → ℝ := fun t => |deriv (cutoffLine n) t| ^ 2
  let K : ℝ := (4 * C / width n) ^ 2
  have hAzero : volume Azero = ENNReal.ofReal (width n) := by
    dsimp [Azero]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hAplus : volume Aplus = ENNReal.ofReal (2 * width n) := by
    dsimp [Aplus]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hAminus : volume Aminus = ENNReal.ofReal (2 * width n) := by
    dsimp [Aminus]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hAend : volume Aend = ENNReal.ofReal (width n) := by
    dsimp [Aend]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hUvol : volume U ≤ ENNReal.ofReal (width n) +
      (ENNReal.ofReal (2 * width n) +
        (ENNReal.ofReal (2 * width n) + ENNReal.ofReal (width n))) := by
    have hlast : volume (Aminus ∪ Aend) ≤ volume Aminus + volume Aend :=
      measure_union_le _ _
    calc
      volume U ≤ volume Azero + (volume Aplus + (volume Aminus + volume Aend)) := by
        dsimp [U]
        calc
          volume (Azero ∪ (Aplus ∪ (Aminus ∪ Aend))) ≤
              volume Azero + volume (Aplus ∪ (Aminus ∪ Aend)) := measure_union_le _ _
          _ ≤ volume Azero + (volume Aplus + volume (Aminus ∪ Aend)) :=
                add_le_add le_rfl (measure_union_le _ _)
          _ ≤ volume Azero + (volume Aplus + (volume Aminus + volume Aend)) :=
                add_le_add le_rfl (add_le_add le_rfl hlast)
      _ = ENNReal.ofReal (width n) +
          (ENNReal.ofReal (2 * width n) +
            (ENNReal.ofReal (2 * width n) + ENNReal.ofReal (width n))) := by
        rw [hAzero, hAplus, hAminus, hAend]
  let Uvol := ENNReal.ofReal (width n) +
      (ENNReal.ofReal (2 * width n) +
        (ENNReal.ofReal (2 * width n) + ENNReal.ofReal (width n)))
  have hUmeas : MeasurableSet U := by
    dsimp [U, Azero, Aplus, Aminus, Aend]
    exact measurableSet_Icc.union
      (measurableSet_Icc.union (measurableSet_Icc.union measurableSet_Icc))
  have hmuUle : μ U ≤ volume U := by
    rw [Measure.restrict_apply hUmeas]
    exact measure_mono Set.inter_subset_left
  have hw : 0 < width n := width_pos n
  have h2w : 0 ≤ 2 * width n := by positivity
  have hUvolCast : Uvol = ENNReal.ofReal (6 * width n) := by
    dsimp [Uvol]
    rw [← ENNReal.ofReal_add h2w hw.le]
    rw [← ENNReal.ofReal_add h2w (by positivity)]
    rw [← ENNReal.ofReal_add hw.le (by positivity)]
    congr 1
    ring
  have hUvolTop : Uvol < ⊤ := by
    rw [hUvolCast]
    exact ENNReal.ofReal_lt_top
  have hmuUlt : μ U < ⊤ := lt_of_le_of_lt (le_trans hmuUle hUvol) hUvolTop
  have hmuUbound : μ.real U ≤ 6 * width n := by
    have hto := ENNReal.toReal_mono (ne_of_lt hUvolTop) (le_trans hmuUle hUvol)
    have hto' : (μ U).toReal ≤ 6 * width n := by
      have hsum : Uvol.toReal = 6 * width n := by
        rw [hUvolCast, ENNReal.toReal_ofReal (by positivity)]
      simpa [Measure.real, hsum] using hto
    exact hto'
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hconstOn : IntegrableOn (fun _ : ℝ => K) U μ :=
    integrableOn_const (μ := μ) (s := U) (C := K) (ne_of_lt hmuUlt)
  have hG : Integrable (U.indicator (fun _ : ℝ => K)) μ := by
    rw [integrable_indicator_iff hUmeas]
    exact hconstOn
  have hFcont : Continuous F := by
    have hderivCont : Continuous (deriv (cutoffLine n)) :=
      (cutoffLine_contDiff n).continuous_deriv (by norm_num)
    change Continuous (fun t : ℝ => |deriv (cutoffLine n) t| ^ 2)
    exact (hderivCont.abs).pow 2
  have hFIcc : IntegrableOn F (Set.Icc (0 : ℝ) 1) volume := hFcont.integrableOn_Icc
  have hFIoc : Integrable F μ := by
    apply (hFIcc.mono_set ?_).integrable
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hle : F ≤ᵐ[μ] U.indicator (fun _ : ℝ => K) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases htU : t ∈ U
    · have hD := cutoffLine_deriv_bound_on_Ioc n ht C hC
      have hsq : |deriv (cutoffLine n) t| ^ 2 ≤ (4 * C / width n) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hD 2
      simpa [F, K, Set.indicator_of_mem, htU] using hsq
    · have hzero : deriv (cutoffLine n) t = 0 := by
        by_contra hnonzero
        rcases cutoffLine_deriv_support_on_Ioc ht hnonzero with hzeroArc | hplusArc | hminusArc | hendArc
        · apply htU
          change t ∈ Azero ∪ (Aplus ∪ (Aminus ∪ Aend))
          exact Or.inl hzeroArc
        · apply htU
          change t ∈ Azero ∪ (Aplus ∪ (Aminus ∪ Aend))
          exact Or.inr (Or.inl hplusArc)
        · apply htU
          change t ∈ Azero ∪ (Aplus ∪ (Aminus ∪ Aend))
          exact Or.inr (Or.inr (Or.inl hminusArc))
        · apply htU
          change t ∈ Azero ∪ (Aplus ∪ (Aminus ∪ Aend))
          exact Or.inr (Or.inr (Or.inr hendArc))
      simp [Set.indicator, F, htU, hzero]
  have hbound :
      (∫ t in Set.Ioc (0 : ℝ) 1, F t ∂volume) ≤ 96 * C ^ 2 / width n := by
    calc
      (∫ t in Set.Ioc (0 : ℝ) 1, F t ∂volume) = ∫ t, F t ∂μ := rfl
      _ ≤ ∫ t, U.indicator (fun _ : ℝ => K) t ∂μ := integral_mono_ae hFIoc hG hle
      _ = μ.real U * K := by
        rw [integral_indicator_const K hUmeas, smul_eq_mul]
      _ ≤ (6 * width n) * K := mul_le_mul_of_nonneg_right hmuUbound hK0
      _ = 96 * C ^ 2 / width n := by
        dsimp [K]
        field_simp [ne_of_gt (width_pos n)]
        ring
  simpa [F] using hbound

/-- The fixed-index form of the uniform derivative estimate. -/
theorem cutoffLine_deriv_sq_integral_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ t in Set.Ioc (0 : ℝ) 1, |deriv (cutoffLine n) t| ^ 2 ∂volume) ≤
        96 * C ^ 2 / width n := by
  obtain ⟨C, hC0, hC⟩ := cutoffLine_deriv_sq_integral_bound_uniform
  exact ⟨C, hC0, hC n⟩

theorem cutoffLine_even (n : ℕ) (t : ℝ) : cutoffLine n (-t) = cutoffLine n t := by
  unfold cutoffLine
  by_cases ht : Int.fract t = 0
  · rw [(Int.fract_neg_eq_zero).2 ht, ht]
  · rw [Int.fract_neg ht]
    simp [sub_sub_cancel, add_comm]

/-- The periodized cutoff on the unit circle, represented by its real lift. -/
noncomputable def pairCutoff (n : ℕ) : Torus 1 → ℝ :=
  fun x => cutoffLine n (SharpLSI.secT x 0)

theorem pairCutoff_lift (n : ℕ) (t : ℝ) :
    pairCutoff n (torusLift (fun _ : Fin 1 => t)) = cutoffLine n t := by
  rw [pairCutoff]
  have hrep : ∃ k : ℤ, t = SharpLSI.secT (torusLift (fun _ : Fin 1 => t)) 0 + k := by
    have h : ((SharpLSI.secT (torusLift (fun _ : Fin 1 => t)) 0 : ℝ) :
        AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
      simpa [DGPS.torusLift, SharpLSI.liftT] using
        congrFun (SharpLSI.liftT_secT (torusLift (fun _ : Fin 1 => t))) 0
    have h0 : ((t - SharpLSI.secT (torusLift (fun _ : Fin 1 => t)) 0 : ℝ) :
        AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, ← h, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
    exact ⟨k, by simp at hk; linarith⟩
  obtain ⟨k, hk⟩ := hrep
  have hper := (cutoffLine_periodic n).int_mul k
    (SharpLSI.secT (torusLift (fun _ : Fin 1 => t)) 0)
  rw [mul_one] at hper
  rw [← hper, ← hk]

theorem pairCutoff_isSmoothPeriodic (n : ℕ) : DGPS.IsSmoothPeriodic (pairCutoff n) := by
  have hcomp : pairCutoff n ∘ torusLift =
      fun y : Fin 1 → ℝ => cutoffLine n (y 0) := by
    funext y
    have hy : y = fun _ : Fin 1 => y 0 := by
      funext i
      fin_cases i
      rfl
    rw [hy]
    simpa using pairCutoff_lift n (y 0)
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (pairCutoff n ∘ torusLift)
  rw [hcomp]
  have hcoord : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : Fin 1 → ℝ => y 0) := by
    fun_prop
  exact (cutoffLine_contDiff n).comp hcoord

theorem pairCutoff_measurable (n : ℕ) : Measurable (pairCutoff n) := by
  have hline : Continuous (cutoffLine n) := (cutoffLine_contDiff n).continuous
  exact hline.measurable.comp
    ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)

theorem pairCutoff_even (n : ℕ) (x : Torus 1) :
    pairCutoff n (-x) = pairCutoff n x := by
  let s := SharpLSI.secT x 0
  let sn := SharpLSI.secT (-x) 0
  have hs : ((s : ℝ) : AddCircle (1 : ℝ)) = x 0 := by
    simpa [s, DGPS.torusLift, SharpLSI.liftT] using
      congrFun (SharpLSI.liftT_secT x) 0
  have hsn : ((sn : ℝ) : AddCircle (1 : ℝ)) = (-x) 0 := by
    simpa [sn, DGPS.torusLift, SharpLSI.liftT] using
      congrFun (SharpLSI.liftT_secT (-x)) 0
  have h0 : ((-s - sn : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_neg, hs, hsn]
    simp
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
  have hrel : -s = sn + k := by
    have hk' : (k : ℝ) = -s - sn := by simpa using hk
    linarith
  have hper := (cutoffLine_periodic n).int_mul k sn
  have hper' : cutoffLine n (sn + k) = cutoffLine n sn := by simpa using hper
  calc
    pairCutoff n (-x) = cutoffLine n sn := rfl
    _ = cutoffLine n (sn + k) := hper'.symm
    _ = cutoffLine n (-s) := congrArg (cutoffLine n) hrel.symm
    _ = cutoffLine n s := cutoffLine_even n s
    _ = pairCutoff n x := rfl

theorem cutoffLine_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cutoffLine n t :=
  add_nonneg (valleyCutoffLift_nonneg _ _) (valleyCutoffLift_nonneg _ _)

theorem valleyCutoffLift_ne_zero_upper {n : ℕ} {t : ℝ}
    (ht : valleyCutoffLift n t ≠ 0) : t < separation n - width n / 2 := by
  by_contra h
  exact ht (valleyCutoffLift_eq_zero_of_ge (le_of_not_gt h))

theorem cutoffLine_le_one (n : ℕ) (t : ℝ) : cutoffLine n t ≤ 1 := by
  unfold cutoffLine
  by_cases hleft : valleyCutoffLift n (Int.fract t) = 0
  · simpa [hleft] using valleyCutoffLift_le_one n (1 - Int.fract t)
  · have hright : valleyCutoffLift n (1 - Int.fract t) = 0 := by
      by_contra hr
      have hl := valleyCutoffLift_ne_zero_upper hleft
      have hr' := valleyCutoffLift_ne_zero_upper hr
      have hs := separation_le_ten_neg_four n
      have hs' : separation n < 1 / 2 := by
        have hsmall : (10 : ℝ) ^ (-(4 : ℝ)) < 1 / 2 := by
          norm_num [Real.rpow_neg, Real.rpow_natCast]
        exact lt_of_le_of_lt hs hsmall
      nlinarith [width_pos n]
    simpa [hright] using valleyCutoffLift_le_one n (Int.fract t)

theorem pairCutoff_nonneg (n : ℕ) (x : Torus 1) : 0 ≤ pairCutoff n x :=
  cutoffLine_nonneg n _

theorem pairCutoff_le_one (n : ℕ) (x : Torus 1) : pairCutoff n x ≤ 1 :=
  cutoffLine_le_one n _

theorem cutoffLine_eq_zero_of_mem_Icc {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (separation n) (1 - separation n)) : cutoffLine n t = 0 := by
  have hsep := separation_pos n
  have hsmall : separation n < 1 / 2 := by
    have h := separation_le_ten_neg_four n
    have h10 : (10 : ℝ) ^ (-(4 : ℝ)) < 1 / 2 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    exact lt_of_le_of_lt h h10
  have ht0 : 0 ≤ t := le_trans hsep.le ht.1
  have ht1 : t < 1 := by linarith [ht.2, hsep]
  have hfract : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, ht1⟩
  have hleft : valleyCutoffLift n t = 0 := by
    apply valleyCutoffLift_eq_zero_of_ge
    linarith [ht.1, width_pos n]
  have hright : valleyCutoffLift n (1 - t) = 0 := by
    apply valleyCutoffLift_eq_zero_of_ge
    linarith [ht.2, width_pos n]
  simp [cutoffLine, hfract, hleft, hright]

theorem pairCutoff_support_arcs (n : ℕ) (x : Torus 1) (hx : pairCutoff n x ≠ 0) :
    SharpLSI.secT x 0 < separation n ∨
      1 - separation n < SharpLSI.secT x 0 := by
  by_cases hleft : SharpLSI.secT x 0 < separation n
  · exact Or.inl hleft
  · have hleft' : separation n ≤ SharpLSI.secT x 0 := le_of_not_gt hleft
    by_cases hright : SharpLSI.secT x 0 ≤ 1 - separation n
    · have hzero : cutoffLine n (SharpLSI.secT x 0) = 0 :=
        cutoffLine_eq_zero_of_mem_Icc ⟨hleft', hright⟩
      exact (hx (by simpa [pairCutoff] using hzero)).elim
    · exact Or.inr (lt_of_not_ge hright)

theorem cutoffLine_eq_one_of_mem_Icc {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (separation n / 3) (2 * separation n / 3)) :
    cutoffLine n t = 1 := by
  have hsep := separation_pos n
  have hsmall : separation n < 1 / 2 := by
    have h := separation_le_ten_neg_four n
    have h10 : (10 : ℝ) ^ (-(4 : ℝ)) < 1 / 2 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    exact lt_of_le_of_lt h h10
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have ht1 : t < 1 := by linarith [ht.2, hsmall]
  have hfract : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, ht1⟩
  have hleft := valleyCutoffLift_eq_one_of_mem_Icc ht
  have hright : valleyCutoffLift n (1 - t) = 0 := by
    apply valleyCutoffLift_eq_zero_of_ge
    have heps := width_le_separation_div_hundred n
    linarith [ht.2, width_pos n, hsmall]
  simp [cutoffLine, hfract, hleft, hright]

theorem cutoffLine_eq_one_of_mem_negative_Icc {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (-(2 * separation n / 3)) (-(separation n / 3))) :
    cutoffLine n t = 1 := by
  have hpos : -t ∈ Set.Icc (separation n / 3) (2 * separation n / 3) := by
    constructor <;> linarith [ht.1, ht.2]
  calc
    cutoffLine n t = cutoffLine n (-t) := (cutoffLine_even n t).symm
    _ = 1 := cutoffLine_eq_one_of_mem_Icc hpos

theorem pairCutoff_zero_on_lifted_middle {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (separation n) (1 - separation n)) :
    pairCutoff n (torusLift (fun _ : Fin 1 => t)) = 0 := by
  rw [pairCutoff_lift]
  exact cutoffLine_eq_zero_of_mem_Icc ht

theorem pairCutoff_one_on_positive_plateau {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (separation n / 3) (2 * separation n / 3)) :
    pairCutoff n (torusLift (fun _ : Fin 1 => t)) = 1 := by
  rw [pairCutoff_lift]
  exact cutoffLine_eq_one_of_mem_Icc ht

theorem pairCutoff_one_on_negative_plateau {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (-(2 * separation n / 3)) (-(separation n / 3))) :
    pairCutoff n (torusLift (fun _ : Fin 1 => t)) = 1 := by
  rw [pairCutoff_lift]
  exact cutoffLine_eq_one_of_mem_negative_Icc ht

/-- The nonzero set is contained in two arcs, so its Haar measure is at most `2aₙ`. -/
theorem pairCutoff_support_measure_le (n : ℕ) :
    (DGPS.haar 1) {x : Torus 1 | pairCutoff n x ≠ 0} ≤
      ENNReal.ofReal (2 * separation n) := by
  let S : Set (Torus 1) := {x | pairCutoff n x ≠ 0}
  let A : Set (Fin 1 → ℝ) := Set.univ.pi fun _ => Set.Ioc (0 : ℝ) (separation n)
  let B : Set (Fin 1 → ℝ) := Set.univ.pi fun _ => Set.Ioc (1 - separation n) 1
  have hS : MeasurableSet S := by
    have hzero : MeasurableSet ((pairCutoff n) ⁻¹' ({0} : Set ℝ)) :=
      (measurableSet_singleton (0 : ℝ)).preimage (pairCutoff_measurable n)
    change MeasurableSet (((pairCutoff n) ⁻¹' ({0} : Set ℝ))ᶜ)
    exact hzero.compl
  have hboxA :
      (volume.restrict (SharpLSI.unitBox (Fin 1))) A = ENNReal.ofReal (separation n) := by
    rw [SharpLSI.volume_restrict_unitBox]
    have hi : Set.Ioc (0 : ℝ) (separation n) ∩ Set.Ioc 0 1 =
        Set.Ioc 0 (separation n) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨hx, _⟩
        exact hx
      · intro hx
        have hsep1 : separation n ≤ 1 := by
          have hs := separation_le_ten_neg_four n
          have hs' : (10 : ℝ) ^ (-(4 : ℝ)) ≤ 1 := by
            norm_num [Real.rpow_neg, Real.rpow_natCast]
          exact le_trans hs hs'
        exact ⟨hx, ⟨hx.1, le_trans hx.2 hsep1⟩⟩
    simp [A, Real.volume_Ioc, hi]
  have hboxB :
      (volume.restrict (SharpLSI.unitBox (Fin 1))) B = ENNReal.ofReal (separation n) := by
    rw [SharpLSI.volume_restrict_unitBox]
    have hi : Set.Ioc (1 - separation n : ℝ) 1 ∩ Set.Ioc 0 1 =
        Set.Ioc (1 - separation n) 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨hx, _⟩
        exact hx
      · intro hx
        have hsep1 : separation n ≤ 1 := by
          have hs := separation_le_ten_neg_four n
          have hs' : (10 : ℝ) ^ (-(4 : ℝ)) ≤ 1 := by
            norm_num [Real.rpow_neg, Real.rpow_natCast]
          exact le_trans hs hs'
        have hnonneg : 0 ≤ 1 - separation n := by linarith
        exact ⟨hx, ⟨lt_of_le_of_lt hnonneg hx.1, hx.2⟩⟩
    simp [B, Real.volume_Ioc, hi]
  have hpre : torusLift ⁻¹' S ∩ SharpLSI.unitBox (Fin 1) ⊆ A ∪ B := by
    rintro y ⟨hyS, hybox⟩
    have hnonzero : pairCutoff n (torusLift y) ≠ 0 := by
      simpa [S, Set.mem_preimage] using hyS
    rcases pairCutoff_support_arcs n (torusLift y) hnonzero with hleft | hright
    · have hsec : SharpLSI.secT (torusLift y) 0 = y 0 := by
        have h := SharpLSI.secT_liftT hybox
        exact congrFun h 0
      have hy0 : y 0 ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [SharpLSI.unitBox] using hybox
      have hleft' : y 0 < separation n := by simpa [hsec] using hleft
      have hAcoord : y 0 ∈ Set.Ioc (0 : ℝ) (separation n) :=
        ⟨hy0.1, hleft'.le⟩
      apply Or.inl
      change ∀ i ∈ Set.univ, y i ∈ Set.Ioc (0 : ℝ) (separation n)
      intro i _
      fin_cases i
      exact hAcoord
    · have hsec : SharpLSI.secT (torusLift y) 0 = y 0 := by
        have h := SharpLSI.secT_liftT hybox
        exact congrFun h 0
      have hy0 : y 0 ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [SharpLSI.unitBox] using hybox
      have hBcoord : y 0 ∈ Set.Ioc (1 - separation n) 1 :=
        ⟨by simpa [hsec] using hright, hy0.2⟩
      apply Or.inr
      change ∀ i ∈ Set.univ, y i ∈ Set.Ioc (1 - separation n) 1
      intro i _
      fin_cases i
      exact hBcoord
  have hpremeas : MeasurableSet (torusLift ⁻¹' S) :=
    hS.preimage SharpLSI.measurable_liftT
  have hboxmeas : MeasurableSet (SharpLSI.unitBox (Fin 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hsum : ENNReal.ofReal (separation n) + ENNReal.ofReal (separation n) =
      ENNReal.ofReal (2 * separation n) := by
    rw [← ENNReal.ofReal_add (le_of_lt (separation_pos n)) (le_of_lt (separation_pos n))]
    congr 1
    ring
  calc
    (DGPS.haar 1) S =
        (Measure.map torusLift (volume.restrict (SharpLSI.unitBox (Fin 1)))) S := by
          rw [DGPS.haar_eq_map_unitBox]
    _ = (volume.restrict (SharpLSI.unitBox (Fin 1))) (torusLift ⁻¹' S) :=
          Measure.map_apply SharpLSI.measurable_liftT hS
    _ = (volume.restrict (SharpLSI.unitBox (Fin 1)))
          (torusLift ⁻¹' S ∩ SharpLSI.unitBox (Fin 1)) := by
          rw [Measure.restrict_apply hpremeas]
          rw [Measure.restrict_apply (hpremeas.inter hboxmeas)]
          simp only [Set.inter_assoc, Set.inter_self]
    _ ≤ (volume.restrict (SharpLSI.unitBox (Fin 1))) (A ∪ B) :=
          measure_mono hpre
    _ ≤ (volume.restrict (SharpLSI.unitBox (Fin 1))) A +
          (volume.restrict (SharpLSI.unitBox (Fin 1))) B := measure_union_le A B
    _ = ENNReal.ofReal (2 * separation n) := by rw [hboxA, hboxB, hsum]

end DGPS.SingularCounterexample
