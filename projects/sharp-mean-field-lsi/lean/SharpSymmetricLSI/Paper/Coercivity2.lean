import SharpSymmetricLSI.Defs.D05_FreeEnergy
import SharpSymmetricLSI.Paper.FreeEnergyMin
import SharpSymmetricLSI.Paper.GibbsVariational
import SharpSymmetricLSI.Paper.CondEmpirical

/-!
# Lemma 4.2 (lane s42; R16): bilinear and quadratic estimates

For probabilities `ρ, μ` on `𝕋^d` and a continuous kernel `F`:
* `bForm F μ ρ = F(ρ-μ, ρ-μ)` (expanded through `interE`); it is linear in `F`, equals
  `∑ (ρ-μ)(fᵢ)(ρ-μ)(gᵢ)` for `F = ∑ fᵢ ⊗ gᵢ`, and `|bForm D μ ρ| ≤ 2 ε H(ρ|μ)` for `|D| ≤ ε`
  (Pinsker, twice);
* `quadF F μ w = ∬ w(x) F(x,y) w(y) dμ dμ`; linear in `F`, explicit for finite rank, and
  `|quadF D μ w| ≤ ε ∫ w² dμ` for `|D| ≤ ε`;
* the cubic bound `log ∫ eᵍ dμ ≤ ½ ∫ g² dμ + M³` for `μ(g) = 0`, `|g| ≤ M ≤ 1`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

section kernels
variable {F G : Torus d → Torus d → ℝ}

theorem cont_left (hF : Continuous (Function.uncurry F)) (y : Torus d) :
    Continuous fun x => F x y :=
  hF.comp (continuous_id.prodMk continuous_const)

theorem cont_right (hF : Continuous (Function.uncurry F)) (x : Torus d) :
    Continuous fun y => F x y :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem cont_integral_left (hF : Continuous (Function.uncurry F)) (ρ : Measure (Torus d))
    [IsProbabilityMeasure ρ] : Continuous fun y => ∫ x, F x y ∂ρ :=
  continuous_convAux hF ⟨ρ, inferInstance⟩

theorem cont_integral_right (hF : Continuous (Function.uncurry F)) (ρ : Measure (Torus d))
    [IsProbabilityMeasure ρ] : Continuous fun x => ∫ y, F x y ∂ρ :=
  continuous_convAux (W := fun a b => F b a) (hF.comp continuous_swap) ⟨ρ, inferInstance⟩

theorem interE_sub (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (ρ η : Measure (Torus d)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    interE (fun x y => F x y - G x y) ρ η = interE F ρ η - interE G ρ η := by
  have hin : ∀ y, ∫ x, (F x y - G x y) ∂ρ = ∫ x, F x y ∂ρ - ∫ x, G x y ∂ρ := fun y =>
    integral_sub (integrable_of_continuous (cont_left hF y))
      (integrable_of_continuous (cont_left hG y))
  simp only [interE, hin]
  exact integral_sub (integrable_of_continuous (cont_integral_left hF ρ))
    (integrable_of_continuous (cont_integral_left hG ρ))

theorem interE_finiteRank {n : ℕ} (f g : Fin n → C(Torus d, ℝ)) (ρ η : Measure (Torus d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    interE (fun x y => ∑ i, f i x * g i y) ρ η = ∑ i, (∫ x, f i x ∂ρ) * ∫ y, g i y ∂η := by
  have hin : ∀ y, ∫ x, ∑ i, f i x * g i y ∂ρ = ∑ i, (∫ x, f i x ∂ρ) * g i y := fun y => by
    rw [integral_finsetSum _ fun i _ => (integrable_of_continuous (f i).continuous).mul_const _]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  simp only [interE, hin]
  rw [integral_finsetSum _ fun i _ => (integrable_of_continuous (g i).continuous).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- `F(ρ-μ, ρ-μ)`. -/
def bForm (F : Torus d → Torus d → ℝ) (μ ρ : Measure (Torus d)) : ℝ :=
  interE F ρ ρ - interE F μ ρ - interE F ρ μ + interE F μ μ

theorem bForm_sub (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (μ ρ : Measure (Torus d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] :
    bForm F μ ρ = bForm G μ ρ + bForm (fun x y => F x y - G x y) μ ρ := by
  simp only [bForm, interE_sub hF hG]
  ring

theorem bForm_finiteRank {n : ℕ} (f g : Fin n → C(Torus d, ℝ)) (μ ρ : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] :
    bForm (fun x y => ∑ i, f i x * g i y) μ ρ =
      ∑ i, (∫ x, f i x ∂ρ - ∫ x, f i x ∂μ) * (∫ y, g i y ∂ρ - ∫ y, g i y ∂μ) := by
  simp only [bForm, interE_finiteRank]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|F(ρ-μ,ρ-μ)| ≤ 2 ε H(ρ|μ)` for `|F| ≤ ε`. -/
theorem abs_bForm_le (hF : Continuous (Function.uncurry F)) {ε : ℝ} (hε : ∀ x y, |F x y| ≤ ε)
    (μ ρ : Measure (Torus d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (hK : klDiv ρ μ ≠ ⊤) :
    |bForm F μ ρ| ≤ ε * (2 * (klDiv ρ μ).toReal) := by
  set s := Real.sqrt (2 * (klDiv ρ μ).toReal) with hs
  set φ : Torus d → ℝ := fun y => ∫ x, F x y ∂ρ - ∫ x, F x y ∂μ with hφ
  have hφc : Continuous φ := (cont_integral_left hF ρ).sub (cont_integral_left hF μ)
  have hφb : ∀ y, |φ y| ≤ ε * s := fun y =>
    abs_integral_sub_le_pinsker (cont_left hF y).measurable (fun x => hε x y) hK
  have e : bForm F μ ρ = ∫ y, φ y ∂ρ - ∫ y, φ y ∂μ := by
    have i1 := integrable_of_continuous (μ := ρ) (cont_integral_left hF ρ)
    have i2 := integrable_of_continuous (μ := ρ) (cont_integral_left hF μ)
    have i3 := integrable_of_continuous (μ := μ) (cont_integral_left hF ρ)
    have i4 := integrable_of_continuous (μ := μ) (cont_integral_left hF μ)
    simp only [bForm, interE, hφ, integral_sub i1 i2, integral_sub i3 i4]
    ring
  rw [e]
  have h2 := abs_integral_sub_le_pinsker hφc.measurable hφb hK
  have hss : s * s = 2 * (klDiv ρ μ).toReal := Real.mul_self_sqrt (by positivity)
  calc _ ≤ ε * s * s := h2
    _ = ε * (2 * (klDiv ρ μ).toReal) := by rw [mul_assoc, hss]

/-- `∬ w(x) F(x,y) w(y) dμ(y) dμ(x)`. -/
def quadF (F : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (w : Torus d → ℝ) : ℝ :=
  ∫ x, w x * ∫ y, F x y * w y ∂μ ∂μ

theorem cont_kernel_mul (hF : Continuous (Function.uncurry F)) {w : Torus d → ℝ}
    (hw : Continuous w) : Continuous (Function.uncurry fun x y => F x y * w y) :=
  hF.mul (hw.comp continuous_snd)

theorem quadF_sub (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {w : Torus d → ℝ} (hw : Continuous w) :
    quadF F μ w = quadF G μ w + quadF (fun x y => F x y - G x y) μ w := by
  have hin : ∀ x, ∫ y, (F x y - G x y) * w y ∂μ =
      ∫ y, F x y * w y ∂μ - ∫ y, G x y * w y ∂μ := fun x => by
    rw [← integral_sub (integrable_of_continuous (cont_right (cont_kernel_mul hF hw) x))
      (integrable_of_continuous (cont_right (cont_kernel_mul hG hw) x))]
    congr 1; funext y; ring
  have c1 : Continuous fun x => w x * ∫ y, F x y * w y ∂μ :=
    hw.mul (cont_integral_right (cont_kernel_mul hF hw) μ)
  have c2 : Continuous fun x => w x * ∫ y, G x y * w y ∂μ :=
    hw.mul (cont_integral_right (cont_kernel_mul hG hw) μ)
  have i1 : Integrable (fun x => w x * ∫ y, F x y * w y ∂μ) μ := integrable_of_continuous c1
  have i2 : Integrable (fun x => w x * ∫ y, G x y * w y ∂μ) μ := integrable_of_continuous c2
  simp only [quadF, hin, mul_sub]
  rw [integral_sub i1 i2]
  ring

theorem quadF_finiteRank {n : ℕ} (f g : Fin n → C(Torus d, ℝ)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {w : Torus d → ℝ} (hw : Continuous w) :
    quadF (fun x y => ∑ i, f i x * g i y) μ w =
      ∑ i, (∫ x, w x * f i x ∂μ) * ∫ y, g i y * w y ∂μ := by
  have hin : ∀ x, ∫ y, (∑ i, f i x * g i y) * w y ∂μ = ∑ i, f i x * ∫ y, g i y * w y ∂μ :=
    fun x => by
      simp only [Finset.sum_mul]
      have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          Integrable (fun y => f i x * g i y * w y) μ := fun i _ =>
        integrable_of_continuous ((continuous_const.mul (g i).continuous).mul hw)
      rw [integral_finsetSum _ hi]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      congr 1; funext y; ring
  simp only [quadF, hin, Finset.mul_sum]
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun x => w x * (f i x * ∫ y, g i y * w y ∂μ)) μ := fun i _ =>
    integrable_of_continuous (hw.mul ((f i).continuous.mul continuous_const))
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_mul_const]
  congr 1; funext x; ring

theorem sq_integral_abs_le_coerc (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {w : Torus d → ℝ}
    (hw : Continuous w) : (∫ x, |w x| ∂μ) ^ 2 ≤ ∫ x, w x ^ 2 ∂μ := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hw
  have hm : MemLp (fun x => |w x|) 2 μ :=
    MemLp.of_bound hw.abs.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hC x)
  have hv := ProbabilityTheory.variance_nonneg (fun x => |w x|) μ
  rw [ProbabilityTheory.variance_eq_sub hm] at hv
  have e : ∫ x, ((fun x => |w x|) ^ 2) x ∂μ = ∫ x, w x ^ 2 ∂μ := by
    congr 1; funext x; simp [sq_abs]
  rw [e] at hv
  linarith

/-- `|∬ w F w| ≤ ε ∫ w²` for `|F| ≤ ε`. -/
theorem abs_quadF_le (_hF : Continuous (Function.uncurry F)) {ε : ℝ} (hε : ∀ x y, |F x y| ≤ ε)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {w : Torus d → ℝ} (hw : Continuous w) :
    |quadF F μ w| ≤ ε * ∫ x, w x ^ 2 ∂μ := by
  set a := ∫ x, |w x| ∂μ with ha
  have hwi : Integrable (fun x => |w x|) μ := integrable_of_continuous hw.abs
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε (Classical.arbitrary _) (Classical.arbitrary _))
  have hin : ∀ x, |∫ y, F x y * w y ∂μ| ≤ ε * a := fun x => by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [ha, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hwi.const_mul ε) (Eventually.of_forall fun y => ?_)
    show |F x y * w y| ≤ ε * |w y|
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hε x y) (abs_nonneg _)
  have h1 : |quadF F μ w| ≤ ε * a * a := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |w x * ∫ y, F x y * w y ∂μ| ∂μ ≤ ∫ x, |w x| * (ε * a) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hwi.mul_const _) (Eventually.of_forall fun x => by
              show |w x * ∫ y, F x y * w y ∂μ| ≤ |w x| * (ε * a)
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hin x) (abs_nonneg _))
      _ = ε * a * a := by rw [integral_mul_const, ← ha]; ring
  have h2 := sq_integral_abs_le_coerc μ hw
  calc |quadF F μ w| ≤ ε * a * a := h1
    _ = ε * a ^ 2 := by ring
    _ ≤ ε * ∫ x, w x ^ 2 ∂μ := mul_le_mul_of_nonneg_left h2 hε0

end kernels

section cubic

theorem exp_le_cubic {t : ℝ} (ht : |t| ≤ 1) : exp t ≤ 1 + t + t ^ 2 / 2 + |t| ^ 3 := by
  have h := Real.exp_bound ht (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, t ^ m / (m.factorial : ℝ) = 1 + t + t ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h
  have hc : |t| ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ |t| ^ 3 := by
    have : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 1 := by
      simp [Nat.factorial]; norm_num
    exact mul_le_of_le_one_right (by positivity) this
  have := (le_abs_self _).trans (h.trans hc)
  linarith

/-- `log ∫ eᵍ dμ ≤ ½ ∫ g² dμ + M³` for `μ(g) = 0`, `|g| ≤ M ≤ 1`. -/
theorem log_integral_exp_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : M ≤ 1) (hgM : ∀ x, |g x| ≤ M) (hg0 : ∫ x, g x ∂μ = 0) :
    log (∫ x, exp (g x) ∂μ) ≤ (∫ x, g x ^ 2 ∂μ) / 2 + M ^ 3 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM (Classical.arbitrary _))
  have hi : Integrable (fun x => exp (g x)) μ := integrable_of_continuous (continuous_exp.comp hg)
  have hpos : 0 < ∫ x, exp (g x) ∂μ := integral_exp_pos hi
  have hgi : Integrable g μ := integrable_of_continuous hg
  have hg2 : Integrable (fun x => g x ^ 2) μ := integrable_of_continuous (hg.pow 2)
  have hle : ∫ x, exp (g x) ∂μ ≤ ∫ x, (1 + g x + g x ^ 2 / 2 + M ^ 3) ∂μ := by
    refine integral_mono hi (((integrable_const 1).add hgi).add (hg2.div_const 2) |>.add
      (integrable_const _)) fun x => ?_
    have h1 := exp_le_cubic ((hgM x).trans hM)
    have h2 : |g x| ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hgM x) 3
    linarith
  have e : ∫ x, (1 + g x + g x ^ 2 / 2 + M ^ 3) ∂μ = 1 + (∫ x, g x ^ 2 ∂μ) / 2 + M ^ 3 := by
    have i1 : Integrable (fun x => (1 : ℝ) + g x) μ := (integrable_const 1).add hgi
    have i2 : Integrable (fun x => 1 + g x + g x ^ 2 / 2) μ := i1.add (hg2.div_const 2)
    have i3 : Integrable (fun x => g x ^ 2 / 2) μ := hg2.div_const 2
    rw [integral_add i2 (integrable_const _), integral_add i1 i3,
      integral_add (integrable_const 1) hgi, integral_div, hg0]
    simp
  rw [e] at hle
  have := Real.log_le_sub_one_of_pos hpos
  linarith

end cubic

end SharpLSI
