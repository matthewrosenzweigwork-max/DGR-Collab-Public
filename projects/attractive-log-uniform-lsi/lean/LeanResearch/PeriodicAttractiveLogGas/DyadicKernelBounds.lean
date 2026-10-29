import LeanResearch.PeriodicAttractiveLogGas.WeightedCubeBounds
import LeanResearch.PeriodicAttractiveLogGas.ClusterScaling

/-! Dyadic-annulus estimate for the weakly singular kernel in Appendix A.
The pole is removed using its actual zero measure. The ball growth
hypothesis is supplied below by the proved cube A1 inequality. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.DyadicKernelBounds

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

def shell (x : E) (r : ℝ) : Set E := {y | r / 2 < ‖x - y‖ ∧ ‖x - y‖ ≤ r}

lemma shell_measurable (x : E) (r : ℝ) : MeasurableSet (shell x r) :=
  (measurableSet_lt measurable_const ((continuous_const.sub continuous_id).norm).measurable).inter
    (measurableSet_le ((continuous_const.sub continuous_id).norm).measurable measurable_const)

lemma shell_subset_closedBall (x : E) (r : ℝ) : shell x r ⊆ closedBall x r := by
  intro y hy
  simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hy.2

lemma closedBall_subset_shells (x : E) {D : ℝ} (hD : 0 < D) :
    closedBall x D ⊆ {x} ∪ ⋃ m : ℕ, shell x (D * (1 / 2 : ℝ) ^ m) := by
  intro y hy
  by_cases he : y = x
  · exact Or.inl he
  · have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => he h.symm))
    have hu : ‖x - y‖ ≤ D := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
    obtain ⟨m, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hn hD)
      ((div_le_one hD).mpr hu) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine Or.inr (mem_iUnion.mpr ⟨m, ?_⟩)
    have hl := (lt_div_iff₀ hD).mp hlo
    have hh := (div_le_iff₀ hD).mp hhi
    rw [pow_succ] at hl
    constructor <;> nlinarith only [hl, hh]

lemma shell_power_identity {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (K : ℝ) :
    (r / 2) ^ (1 - (d : ℝ)) * (K * r ^ d) = (2 : ℝ) ^ (d - 1) * K * r := by
  have he : 1 - (d : ℝ) = -(((d - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  have hp : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [he, Real.rpow_neg (by positivity : 0 ≤ r / 2), Real.rpow_natCast, div_pow, hp]
  field_simp [hr.ne']

lemma shell_integral_le {μ : Measure E} {d : ℕ} (hd : 1 ≤ d) (x : E)
    {K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hb : μ (closedBall x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    (∫⁻ y in shell x r, ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * K * r) := by
  have hk (y : E) (hy : y ∈ shell x r) :
      ‖x - y‖ₑ ^ (1 - (d : ℝ)) ≤ ENNReal.ofReal ((r / 2) ^ (1 - (d : ℝ))) := by
    have hn : 0 < ‖x - y‖ := (half_pos hr).trans hy.1
    have he : ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ))) =
        ‖x - y‖ₑ ^ (1 - (d : ℝ)) := by
      rw [← ENNReal.ofReal_rpow_of_pos hn, ofReal_norm]
    rw [← he]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_nonpos (half_pos hr) hy.1.le
      (sub_nonpos.mpr (by exact_mod_cast hd))
  calc
    _ ≤ ∫⁻ _y in shell x r, ENNReal.ofReal ((r / 2) ^ (1 - (d : ℝ))) ∂μ :=
      setLIntegral_mono' (shell_measurable x r) hk
    _ ≤ ∫⁻ _y in closedBall x r, ENNReal.ofReal ((r / 2) ^ (1 - (d : ℝ))) ∂μ :=
      lintegral_mono_set (shell_subset_closedBall x r)
    _ = ENNReal.ofReal ((r / 2) ^ (1 - (d : ℝ))) * μ (closedBall x r) := by
      rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal ((r / 2) ^ (1 - (d : ℝ))) * ENNReal.ofReal (K * r ^ d) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), shell_power_identity hd hr K]

/-- The source dyadic summation, for any measure with the specified ball growth. -/
theorem kernel_integral_le_of_ball_growth {μ : Measure E} {d : ℕ} (hd : 1 ≤ d) (x : E)
    {K D : ℝ} (hK : 0 ≤ K) (hD : 0 < D) (hx : μ {x} = 0)
    (hb : ∀ r : ℝ, 0 < r → μ (closedBall x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    (∫⁻ y in closedBall x D, ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * K * D) := by
  have hz : (∫⁻ y in ({x} : Set E), ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hx, lintegral_zero_measure]
  have hs (m : ℕ) := shell_integral_le hd x hK
    (mul_pos hD (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m))
    (hb _ (mul_pos hD (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m)))
  have hsum : (∑' m : ℕ, ENNReal.ofReal
      ((2 : ℝ) ^ (d - 1) * K * (D * (1 / 2 : ℝ) ^ m))) =
        ENNReal.ofReal ((2 : ℝ) ^ d * K * D) := by
    have hc : 0 ≤ (2 : ℝ) ^ (d - 1) * K := by positivity
    calc
      _ = ∑' m : ℕ, ENNReal.ofReal ((D * (1 / 2 : ℝ) ^ m) ^ (1 : ℝ)) *
          ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * K) := by
        apply tsum_congr
        intro m
        rw [Real.rpow_one, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ = ENNReal.ofReal (D ^ (1 : ℝ) / (1 - (1 / 2 : ℝ) ^ (1 : ℝ))) *
          ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * K) := ennreal_dyadic_scaling_sum hD zero_lt_one _
      _ = _ := by
        rw [Real.rpow_one, Real.rpow_one, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show (2 : ℝ) ^ d = 2 ^ (d - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hd]]
        ring
  calc
    _ ≤ ∫⁻ y in {x} ∪ ⋃ m : ℕ, shell x (D * (1 / 2 : ℝ) ^ m),
        ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ := lintegral_mono_set (closedBall_subset_shells x hD)
    _ ≤ (∫⁻ y in ({x} : Set E), ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ) +
        ∫⁻ y in ⋃ m : ℕ, shell x (D * (1 / 2 : ℝ) ^ m),
          ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ := lintegral_union_le _ _ _
    _ = ∫⁻ y in ⋃ m : ℕ, shell x (D * (1 / 2 : ℝ) ^ m),
          ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ := by rw [hz, zero_add]
    _ ≤ ∑' m : ℕ, ∫⁻ y in shell x (D * (1 / 2 : ℝ) ^ m),
          ‖x - y‖ₑ ^ (1 - (d : ℝ)) ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * K * (D * (1 / 2 : ℝ) ^ m)) :=
      ENNReal.tsum_le_tsum hs
    _ = _ := hsum

end PeriodicAttractiveLogGas.DyadicKernelBounds
