import SharpSymmetricLSI.Paper.TestEnergy7
import SharpSymmetricLSI.Paper.FormLiminf8

/-!
# (8.20) (lane s42): the weighted mobility error

`tendsto_mob_err`: for `f_k` bounded in `L²(P_{N_k})` and `H_k` bounded in `L⁴(P_{N_k})`,
`E|f_k H_k (A_{N_k,ij} - λ_{i+1} δ_{ij})| → 0`. With `D = A - λδ`, `|D| ≤ M` (the `C¹` functions
`eC` have bounded gradients), and the pointwise bound
`|f H D| ≤ (η/2) f² + (η'/(4η)) H⁴ + (M³/(4ηη')) |D|` (twice `ab ≤ (ta² + b²/t)/2` and
`D⁴ ≤ M³|D|`), the claim follows from `E|D| → 0` (`tendsto_gibbs_abs_mob`, TestEnergy7).
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The pointwise bound `|f H D| ≤ (η/2) f² + (η'/(4η)) H⁴ + (M³/(4ηη')) |D|` for `|D| ≤ M`. -/
theorem abs_mul_three_le {f h D M η η' : ℝ} (hη : 0 < η) (hη' : 0 < η') (hD : |D| ≤ M) :
    |f * h * D| ≤ η / 2 * f ^ 2 + η' / (4 * η) * h ^ 4 + M ^ 3 / (4 * η * η') * |D| := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hD
  have h1 : |f * h * D| ≤ η / 2 * f ^ 2 + 1 / (2 * η) * (h * D) ^ 2 := by
    rw [mul_assoc, abs_mul, ← sq_abs f, ← sq_abs (h * D)]
    have := sq_nonneg (η * |f| - |h * D|)
    rw [div_mul_eq_mul_div, one_div_mul_eq_div, div_add_div _ _ (by norm_num) (by positivity),
      le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : (h * D) ^ 2 ≤ η' / 2 * h ^ 4 + 1 / (2 * η') * D ^ 4 := by
    have := sq_nonneg (η' * h ^ 2 - D ^ 2)
    rw [div_mul_eq_mul_div, one_div_mul_eq_div, div_add_div _ _ (by norm_num) (by positivity),
      le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : D ^ 4 ≤ M ^ 3 * |D| := by
    have hD3 : |D| ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hD 3
    calc D ^ 4 = |D| ^ 3 * |D| := by
          rw [← pow_succ, show (3 + 1 : ℕ) = 4 from rfl, ← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ M ^ 3 * |D| := mul_le_mul_of_nonneg_right hD3 (abs_nonneg _)
  have h4 : 1 / (2 * η) * (h * D) ^ 2 ≤
      η' / (4 * η) * h ^ 4 + M ^ 3 / (4 * η * η') * |D| := by
    have := mul_le_mul_of_nonneg_left (h2.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left h3 (by positivity)))) (by positivity : (0 : ℝ) ≤ 1 / (2 * η))
    calc 1 / (2 * η) * (h * D) ^ 2 ≤ 1 / (2 * η) * (η' / 2 * h ^ 4 + 1 / (2 * η') * (M ^ 3 * |D|)) :=
          this
      _ = _ := by field_simp; ring
  linarith

/-- **The weighted error, abstractly**: `E_k|f_k H_k D_k| → 0` if `f_k` is bounded in `L²`, `H_k` in
`L⁴`, `|D_k| ≤ M` and `E_k|D_k| → 0`. -/
theorem tendsto_weighted_err {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)] (P : ∀ k, Measure (α k))
    [∀ k, IsProbabilityMeasure (P k)] {f H D : ∀ k, α k → ℝ}
    (hfm : ∀ k, AEStronglyMeasurable (f k) (P k)) {B : ℝ}
    (hf2 : ∀ k, MemLp (f k) 2 (P k) ∧ ∫ x, f k x ^ 2 ∂P k ≤ B) {K : ℝ}
    (hH : ∀ k, MemLp (H k) 4 (P k) ∧ ∫ x, H k x ^ 4 ∂P k ≤ K)
    (hDm : ∀ k, Measurable (D k)) {M : ℝ} (hDM : ∀ k x, |D k x| ≤ M)
    (hD : Tendsto (fun k => ∫ x, |D k x| ∂P k) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |f k x * H k x * D k x| ∂P k) atTop (𝓝 0) := by
  have hf2i : ∀ k, Integrable (fun x => f k x ^ 2) (P k) := fun k => (hf2 k).1.integrable_sq
  have hH4i : ∀ k, Integrable (fun x => H k x ^ 4) (P k) := fun k => by
    have := (hH k).1.integrable_norm_rpow'
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hDi : ∀ k, Integrable (fun x => |D k x|) (P k) := fun k =>
    Integrable.of_bound (hDm k).abs.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]; exact hDM k x)
  have hB0 : 0 ≤ B := (integral_nonneg fun _ => sq_nonneg _).trans (hf2 0).2
  have hK0 : 0 ≤ K := (integral_nonneg fun x => by positivity).trans (hH 0).2
  have hbound : ∀ η η' : ℝ, 0 < η → 0 < η' → ∀ k,
      ∫ x, |f k x * H k x * D k x| ∂P k ≤
        η / 2 * B + η' / (4 * η) * K + M ^ 3 / (4 * η * η') * ∫ x, |D k x| ∂P k :=
    fun η η' hη hη' k => by
      have i1 := (hf2i k).const_mul (η / 2)
      have i2 := (hH4i k).const_mul (η' / (4 * η))
      have i3 := (hDi k).const_mul (M ^ 3 / (4 * η * η'))
      have hdom : Integrable (fun x => η / 2 * f k x ^ 2 + η' / (4 * η) * H k x ^ 4 +
          M ^ 3 / (4 * η * η') * |D k x|) (P k) := (i1.add i2).add i3
      have hmeas : AEStronglyMeasurable (fun x => |f k x * H k x * D k x|) (P k) :=
        (((hfm k).mul (hH k).1.aestronglyMeasurable).mul (hDm k).aestronglyMeasurable).norm
      have hint : Integrable (fun x => |f k x * H k x * D k x|) (P k) :=
        hdom.mono' hmeas (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_abs]; exact abs_mul_three_le hη hη' (hDM k x))
      have e1 : ∫ x, (η / 2 * f k x ^ 2 + η' / (4 * η) * H k x ^ 4 +
          M ^ 3 / (4 * η * η') * |D k x|) ∂P k = η / 2 * ∫ x, f k x ^ 2 ∂P k +
            η' / (4 * η) * ∫ x, H k x ^ 4 ∂P k + M ^ 3 / (4 * η * η') * ∫ x, |D k x| ∂P k := by
        rw [integral_add (f := fun x => η / 2 * f k x ^ 2 + η' / (4 * η) * H k x ^ 4)
          (g := fun x => M ^ 3 / (4 * η * η') * |D k x|) (i1.add i2) i3,
          integral_add (f := fun x => η / 2 * f k x ^ 2) (g := fun x => η' / (4 * η) * H k x ^ 4)
          i1 i2, integral_const_mul, integral_const_mul, integral_const_mul]
      calc ∫ x, |f k x * H k x * D k x| ∂P k
          ≤ ∫ x, (η / 2 * f k x ^ 2 + η' / (4 * η) * H k x ^ 4 +
              M ^ 3 / (4 * η * η') * |D k x|) ∂P k :=
            integral_mono hint hdom fun x => abs_mul_three_le hη hη' (hDM k x)
        _ = _ := e1
        _ ≤ η / 2 * B + η' / (4 * η) * K + M ^ 3 / (4 * η * η') * ∫ x, |D k x| ∂P k := by
            gcongr
            · exact (hf2 k).2
            · exact (hH k).2
  have hM0 : ∀ k (x : α k), 0 ≤ M := fun k x => (abs_nonneg _).trans (hDM k x)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (4 * (B + 1))
  have hη : 0 < η := by positivity
  set η' := ε * η / (K + 1)
  have hη' : 0 < η' := by positivity
  have h1 : η / 2 * B < ε / 4 := by
    have hB1 : B < B + 1 := by linarith
    have : η * B < ε / 4 := by
      simp only [η]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have h2 : η' / (4 * η) * K < ε / 2 := by
    have e : η' / (4 * η) = ε / (4 * (K + 1)) := by simp only [η']; field_simp
    rw [e, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set c := M ^ 3 / (4 * η * η')
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hD (ε / 4 / (|c| + 1)) (by positivity)
  refine ⟨N0, fun k hk => ?_⟩
  have hk' := hN0 k hk
  have hDk0 : 0 ≤ ∫ x, |D k x| ∂P k := integral_nonneg fun _ => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hDk0] at hk'
  have h3 : c * ∫ x, |D k x| ∂P k < ε / 4 := by
    calc c * ∫ x, |D k x| ∂P k ≤ (|c| + 1) * ∫ x, |D k x| ∂P k :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hDk0
      _ < (|c| + 1) * (ε / 4 / (|c| + 1)) := mul_lt_mul_of_pos_left hk' (by positivity)
      _ = ε / 4 := by field_simp
  have hnn : 0 ≤ ∫ x, |f k x * H k x * D k x| ∂P k := integral_nonneg fun _ => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have := hbound η η' hη hη' k
  linarith

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **The weighted mobility error** `E|f_k H_k (A_{N_k,ij} - λ_{i+1} δ_{ij})| → 0`. -/
theorem tendsto_mob_err (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    (hpart : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    {Ns : ℕ → ℕ} (hNs : Tendsto Ns atTop atTop) {f : (k : ℕ) → Config (Ns k) d → ℝ}
    (hfm : ∀ k, AEStronglyMeasurable (f k) (gibbs V W (Ns k))) {B : ℝ}
    (hf2 : ∀ k, MemLp (f k) 2 (gibbs V W (Ns k)) ∧ ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ B)
    {H : (k : ℕ) → Config (Ns k) d → ℝ} {K : ℝ}
    (hH : ∀ k, MemLp (H k) 4 (gibbs V W (Ns k)) ∧ ∫ X, H k X ^ 4 ∂gibbs V W (Ns k) ≤ K) (i j : ℕ) :
    Tendsto (fun k => ∫ X, |f k X * H k X * (mobA eC (Ns k) X i j - if i = j then lam (i + 1) else 0)|
      ∂gibbs V W (Ns k)) atTop (𝓝 0) := by
  have : ∀ k, IsProbabilityMeasure (gibbs V W (Ns k)) := fun k =>
    gibbs_isProbabilityMeasure hyp (Ns k)
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  obtain ⟨Cj, hCj⟩ := exists_bound_cgrad (hφ (j + 1))
  have hK : ∀ x, |∑ l, cgrad (eC (i + 1)) x l * cgrad (eC (j + 1)) x l| ≤ d * (Ci * Cj) :=
    fun x => (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ l, |cgrad (eC (i + 1)) x l * cgrad (eC (j + 1)) x l| ≤ ∑ _l : Fin d, Ci * Cj :=
            Finset.sum_le_sum fun l _ => by
              rw [abs_mul]
              exact mul_le_mul (hCi x l) (hCj x l) (abs_nonneg _) ((abs_nonneg _).trans (hCi x l))
        _ = d * (Ci * Cj) := by simp)
  exact tendsto_weighted_err (fun k => gibbs V W (Ns k)) hfm hf2 hH
    (D := fun k X => mobA eC (Ns k) X i j - if i = j then lam (i + 1) else 0)
    (fun k => (measurable_mobA hφ (Ns k) i j).sub measurable_const)
    (M := d * (Ci * Cj) + |if i = j then lam (i + 1) else 0|)
    (fun k X => (abs_sub _ _).trans (add_le_add (abs_mobA_le hK _ X) le_rfl))
    ((tendsto_gibbs_abs_mob hyp hμ he hφ heC hpart i j).comp hNs)

end SharpLSI
