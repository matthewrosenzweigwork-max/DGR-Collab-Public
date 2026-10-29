import DGPS.Frontier.LIP032.T20

/-!
# LIP032.21: Exact 2C density bound

Task id and title: LIP032.21, "Exact 2C density bound" (node LIP032, contractibility of the
minimizer set; leaf formalization, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_21_exact_2c_density_bound` : for continuous real `U`, `V` on
  `𝕋^d` with `|U|, |V| ≤ B_0`, `‖p_U - p_V‖_∞ ≤ 2 C ‖U - V‖_∞` with `C = e^{2 B_0}`, where
  `‖f‖_∞ = ⨆ x, |f x|` and `p_U = normExp_LIP03217 U`.
* `DGPS.Frontier.LIP032.lip032_21_exact_2c_density_bound_of_le` : the pointwise form: if
  `|U x - V x| ≤ δ` for all `x` then `|p_U x - p_V x| ≤ 2 C δ` for all `x`.
* `DGPS.Frontier.LIP032.lip032_21_exact_2c_density_bound_interaction` : for
  `U_ν(x) = A.V x + ∫ A.W(x,y) dν(y)` and `U_η` likewise (probabilities `ν`, `η`, bounds
  `|A.V| ≤ M_V`, `|A.W| ≤ M_W`, `B_0 = M_V + M_W`), `‖p_{U_ν} - p_{U_η}‖_∞ ≤ 2 C ‖K_ν - K_η‖_∞`
  with `K_ν(x) = ∫ A.W(x,y) dν(y)`.

## R5 notes
* Hypotheses of the main statement: `U V : Torus d → ℝ` continuous, a real `B_0` and
  `∀ x, |U x| ≤ B_0`, `∀ x, |V x| ≤ B_0`. Nonnegativity of `B_0` follows from the bound at any
  point of the torus and is not assumed separately. `C` is written out as `Real.exp (2 * B_0)`.
* The sup norms are spelled as real suprema `⨆ x, |f x|`. They are the true suprema because the
  functions involved are continuous on the compact torus, hence bounded (no junk value of
  `iSup` is used); on the right-hand side the supremum is bounded below by each pointwise
  difference through this boundedness.
* The specification's proof goes through `log p_U = -U - log Z(U)` and LIP032.20; the same
  route is used. The exponential estimate `|e^a - e^b| ≤ max(e^a, e^b) |a - b|` (LIB06) is
  proved from `1 + t ≤ e^t` as a helper.
* "For `U_ν, U_η` the potential difference can be replaced by `K_ν - K_η`" is the separate
  public corollary `..._interaction`; there `U_ν` is spelled out as the function
  `x ↦ A.V x + ∫ y, A.W x y ∂ν` (as in LIP032.17) and `A.V` cancels exactly in `U_ν - U_η`.
  Its hypotheses are `A : InteractionData d`, reals `M_V`, `M_W` with the two bounds, and
  probability measures `ν`, `η` on the torus.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- One-sided exponential estimate `e^a - e^b ≤ e^a (a - b)`. -/
theorem exp_sub_le_LIP03221 (a b : ℝ) : Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have h : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp _
  have hb : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  have := mul_le_mul_of_nonneg_left h (Real.exp_pos a).le
  rw [hb]
  nlinarith

/-- LIB06: `|e^a - e^b| ≤ max(e^a, e^b) |a - b|`. -/
theorem abs_exp_sub_exp_le_LIP03221 (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  have h1 := exp_sub_le_LIP03221 a b
  have h2 := exp_sub_le_LIP03221 b a
  have ma : Real.exp a ≤ max (Real.exp a) (Real.exp b) := le_max_left _ _
  have mb : Real.exp b ≤ max (Real.exp a) (Real.exp b) := le_max_right _ _
  have hab : a - b ≤ |a - b| := le_abs_self _
  have hba : b - a ≤ |a - b| := by rw [abs_sub_comm]; exact le_abs_self _
  have pa := Real.exp_pos a
  have pb := Real.exp_pos b
  have u1 := mul_le_mul_of_nonneg_left hab pa.le
  have u2 := mul_le_mul_of_nonneg_right ma (abs_nonneg (a - b))
  have v1 := mul_le_mul_of_nonneg_left hba pb.le
  have v2 := mul_le_mul_of_nonneg_right mb (abs_nonneg (a - b))
  rw [abs_le]
  constructor <;> linarith

/-- The logarithm of the normalized exponential: `log p_U = -U - log Z(U)`. -/
theorem log_normExp_LIP03221 {U : Torus d → ℝ} (hZ : 0 < normalizer_LIP03217 U) (x : Torus d) :
    Real.log (normExp_LIP03217 U x) = -U x - Real.log (normalizer_LIP03217 U) := by
  unfold normExp_LIP03217
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

/-- Pointwise form of the `2C` density bound. -/
theorem lip032_21_exact_2c_density_bound_of_le
    {U V : Torus d → ℝ} (hU : Continuous U) (hV : Continuous V) {B₀ : ℝ}
    (hUB : ∀ x, |U x| ≤ B₀) (hVB : ∀ x, |V x| ≤ B₀) {δ : ℝ}
    (hδ : ∀ x, |U x - V x| ≤ δ) (x : Torus d) :
    |normExp_LIP03217 U x - normExp_LIP03217 V x| ≤ 2 * Real.exp (2 * B₀) * δ := by
  obtain ⟨-, -, hZU, hpU, -⟩ := lip032_17_positive_normalized_exponential U hU B₀ hUB
  obtain ⟨-, -, hZV, hpV, -⟩ := lip032_17_positive_normalized_exponential V hV B₀ hVB
  have hlog := lip032_20_log_partition_lipschitz_bound_of_le hU hV hδ
  have pU : 0 < normExp_LIP03217 U x := lt_of_lt_of_le (Real.exp_pos _) (hpU x).1
  have pV : 0 < normExp_LIP03217 V x := lt_of_lt_of_le (Real.exp_pos _) (hpV x).1
  have hdiff : |Real.log (normExp_LIP03217 U x) - Real.log (normExp_LIP03217 V x)| ≤ 2 * δ := by
    rw [log_normExp_LIP03221 hZU, log_normExp_LIP03221 hZV]
    have e : -U x - Real.log (normalizer_LIP03217 U) -
        (-V x - Real.log (normalizer_LIP03217 V)) =
        -(U x - V x) - (Real.log (normalizer_LIP03217 U) - Real.log (normalizer_LIP03217 V)) := by
      ring
    rw [e]
    calc _ ≤ |-(U x - V x)| +
          |Real.log (normalizer_LIP03217 U) - Real.log (normalizer_LIP03217 V)| :=
          abs_sub _ _
      _ ≤ δ + δ := by rw [abs_neg]; exact add_le_add (hδ x) hlog
      _ = 2 * δ := by ring
  have key := abs_exp_sub_exp_le_LIP03221 (Real.log (normExp_LIP03217 U x))
    (Real.log (normExp_LIP03217 V x))
  rw [Real.exp_log pU, Real.exp_log pV] at key
  have hmax : max (normExp_LIP03217 U x) (normExp_LIP03217 V x) ≤ Real.exp (2 * B₀) :=
    max_le (hpU x).2 (hpV x).2
  have hC : 0 ≤ Real.exp (2 * B₀) := (Real.exp_pos _).le
  calc _ ≤ max (normExp_LIP03217 U x) (normExp_LIP03217 V x) *
        |Real.log (normExp_LIP03217 U x) - Real.log (normExp_LIP03217 V x)| := key
    _ ≤ Real.exp (2 * B₀) * (2 * δ) :=
        mul_le_mul hmax hdiff (abs_nonneg _) hC
    _ = 2 * Real.exp (2 * B₀) * δ := by ring

/-- **LIP032.21.** For continuous real potentials `U`, `V` on the torus with `|U|, |V| ≤ B₀`,
`‖p_U - p_V‖_∞ ≤ 2 C ‖U - V‖_∞` with `C = e^{2 B₀}`. -/
theorem lip032_21_exact_2c_density_bound
    (U V : Torus d → ℝ) (hU : Continuous U) (hV : Continuous V) (B₀ : ℝ)
    (hUB : ∀ x, |U x| ≤ B₀) (hVB : ∀ x, |V x| ≤ B₀) :
    ⨆ x, |normExp_LIP03217 U x - normExp_LIP03217 V x| ≤
      2 * Real.exp (2 * B₀) * ⨆ x, |U x - V x| := by
  have hb : BddAbove (Set.range fun x => |U x - V x|) :=
    (isCompact_range (hU.sub hV).abs).bddAbove
  have hC : 0 ≤ 2 * Real.exp (2 * B₀) := by positivity
  refine Real.iSup_le (fun x => ?_) (mul_nonneg hC (Real.iSup_nonneg fun _ => abs_nonneg _))
  exact lip032_21_exact_2c_density_bound_of_le hU hV hUB hVB (fun y => le_ciSup hb y) x

/-- The interaction form: the potential difference is `K_ν - K_η`. -/
theorem lip032_21_exact_2c_density_bound_interaction
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W) (ν η : Measure (Torus d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    ⨆ x, |normExp_LIP03217 (fun x => A.V x + ∫ y, A.W x y ∂ν) x -
        normExp_LIP03217 (fun x => A.V x + ∫ y, A.W x y ∂η) x| ≤
      2 * Real.exp (2 * (M_V + M_W)) * ⨆ x, |(∫ y, A.W x y ∂ν) - ∫ y, A.W x y ∂η| := by
  have hKν := (lip032_16_continuous_kernel_integrals_common_bounds A M_W hW).1 ν
  have hKη := (lip032_16_continuous_kernel_integrals_common_bounds A M_W hW).1 η
  have hUν : Continuous (fun x => A.V x + ∫ y, A.W x y ∂ν) := A.V_continuous.add hKν.1
  have hUη : Continuous (fun x => A.V x + ∫ y, A.W x y ∂η) := A.V_continuous.add hKη.1
  have hdiff : (fun x => |(A.V x + ∫ y, A.W x y ∂ν) - (A.V x + ∫ y, A.W x y ∂η)|) =
      fun x => |(∫ y, A.W x y ∂ν) - ∫ y, A.W x y ∂η| := by
    funext x; congr 1; ring
  have := lip032_21_exact_2c_density_bound _ _ hUν hUη (M_V + M_W)
    (fun x => (abs_add_le _ _).trans (add_le_add (hV x) (hKν.2 x)))
    (fun x => (abs_add_le _ _).trans (add_le_add (hV x) (hKη.2 x)))
  simp only [hdiff] at this
  exact this

end DGPS.Frontier.LIP032
