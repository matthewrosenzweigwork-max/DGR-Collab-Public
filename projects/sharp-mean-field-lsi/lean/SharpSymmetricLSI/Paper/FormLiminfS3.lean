import SharpSymmetricLSI.Paper.LamSym6
import SharpSymmetricLSI.Paper.GaussLaw6

/-!
# (8.20) (lane s42): products with a law-convergent, uniformly square-integrable factor

`tendsto_integral_mul_of_law`: if `(T_k, Z_k) → (F, z)` in law (`z` the coordinates of `γ`),
`T_k²` is uniformly integrable with bounded second moments, `Z_k` has bounded fourth moments and
`H` is continuous with `|H(z)| ≤ A(1 + ∑|z_j|)`, then `E[T_k H(Z_k)] → E_γ[F H(z)]`.

Truncation at level `M`: test the law convergence against `clip_M(t) H(clip_M z)`. The pointwise
error (`trunc_pointwise`) is `≤ (t - clip t)²/(2η) + η A²(1+L)⁴/2 + η t²/2 + 2A²(1+L)⁴/(η M²)`
with `L = ∑|z_j|`, so the integrated error (`trunc_error`) is small uniformly in `k` by the
uniform integrability of `T_k²` and the fourth moments of `Z_k`; on the limit side by dominated
convergence. Then `tendsto_of_trunc` (Paper/GaussLaw6).
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

/-- `L(z) = ∑_j |z_j|`. -/
def sumAbs {J : ℕ} (z : Fin J → ℝ) : ℝ := ∑ j, |z j|

/-- Coordinatewise truncation. -/
def clipV {J : ℕ} (M : ℝ) (z : Fin J → ℝ) : Fin J → ℝ := fun j => clipF M (z j)

theorem sumAbs_nonneg {J : ℕ} (z : Fin J → ℝ) : 0 ≤ sumAbs z :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_sumAbs {J : ℕ} : Continuous (sumAbs (J := J)) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).abs

theorem continuous_clipV {J : ℕ} (M : ℝ) : Continuous (clipV (J := J) M) :=
  continuous_pi fun j => (continuous_clipF M).comp (continuous_apply j)

theorem clipV_eq_of_le {J : ℕ} {M : ℝ} {z : Fin J → ℝ} (h : sumAbs z ≤ M) : clipV M z = z :=
  funext fun j => clipF_eq ((Finset.single_le_sum (f := fun i => |z i|)
    (fun i _ => abs_nonneg (z i)) (Finset.mem_univ j)).trans h)

theorem sumAbs_clipV_le {J : ℕ} {M : ℝ} (hM : 0 ≤ M) (z : Fin J → ℝ) :
    sumAbs (clipV M z) ≤ sumAbs z :=
  Finset.sum_le_sum fun _ _ => abs_clipF_le_abs hM

theorem sumAbs_clipV_le' {J : ℕ} {M : ℝ} (hM : 0 ≤ M) (z : Fin J → ℝ) :
    sumAbs (clipV M z) ≤ J * M := by
  calc sumAbs (clipV M z) ≤ ∑ _j : Fin J, M := Finset.sum_le_sum fun j _ => abs_clipF_le hM _
    _ = J * M := by simp

theorem abs_clipF_le_abs' (M x : ℝ) : |clipF M x| ≤ |M| := by
  rcases le_or_gt 0 M with hM | hM
  · rw [abs_of_nonneg hM]; exact abs_clipF_le hM x
  · unfold clipF
    rw [max_eq_left (by linarith [min_le_right x M]), abs_neg]

theorem sub_clipF_sq_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : (t - clipF M t) ^ 2 ≤ t ^ 2 := by
  have hc := abs_clipF_le_abs hM (x := t)
  have hsign : 0 ≤ t * clipF M t := by
    unfold clipF
    rcases le_or_gt 0 t with ht | ht
    · exact mul_nonneg ht (le_max_of_le_right (le_min ht hM))
    · rw [min_eq_left (by linarith)]
      exact mul_nonneg_of_nonpos_of_nonpos ht.le (max_le (by linarith) ht.le)
  have h2 : clipF M t ^ 2 ≤ t * clipF M t := by
    have e1 : |clipF M t| * |t| = t * clipF M t := by
      rw [← abs_mul, mul_comm, abs_of_nonneg hsign]
    nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (clipF M t)), sq_abs (clipF M t),
      abs_mul_abs_self (clipF M t)]
  nlinarith

theorem one_add_pow_four_le {J : ℕ} (z : Fin J → ℝ) :
    (1 + sumAbs z) ^ 4 ≤ 8 * (1 + (J : ℝ) ^ 3 * ∑ j, z j ^ 4) := by
  set L := sumAbs z
  have hL := sumAbs_nonneg z
  have h1 : (1 + L) ^ 4 ≤ 8 * (1 + L ^ 4) := by
    nlinarith [sq_nonneg (L - 1), sq_nonneg (L ^ 2 - 1), sq_nonneg (L ^ 2 - L), mul_nonneg hL
      (sq_nonneg (L - 1))]
  have h2 : L ^ 2 ≤ J * ∑ j, z j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin J => |z j|)
    simpa [L, sumAbs, sq_abs] using this
  have h3 : (∑ j, z j ^ 2) ^ 2 ≤ J * ∑ j, z j ^ 4 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin J => z j ^ 2)
    simpa [← pow_mul] using this
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h4 : L ^ 4 ≤ (J : ℝ) ^ 3 * ∑ j, z j ^ 4 := by
    have hs : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc L ^ 4 = (L ^ 2) ^ 2 := by ring
      _ ≤ (J * ∑ j, z j ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
      _ = J ^ 2 * (∑ j, z j ^ 2) ^ 2 := by ring
      _ ≤ J ^ 2 * (J * ∑ j, z j ^ 4) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = _ := by ring
  linarith

section trunc
variable {J : ℕ} {H : (Fin J → ℝ) → ℝ} {A : ℝ} (hHb : ∀ z, |H z| ≤ A * (1 + ∑ j, |z j|))
include hHb

theorem nonneg_of_growth : 0 ≤ A := by
  have := hHb 0
  simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero, mul_one] at this
  exact (abs_nonneg _).trans this

/-- **The pointwise truncation error.** -/
theorem trunc_pointwise {M η : ℝ} (hM : 0 < M) (hη : 0 < η) (t : ℝ) (z : Fin J → ℝ) :
    |t * H z - clipF M t * H (clipV M z)| ≤
      (t - clipF M t) ^ 2 / (2 * η) + η * A ^ 2 * (1 + sumAbs z) ^ 4 / 2 + η * t ^ 2 / 2 +
        2 * A ^ 2 * (1 + sumAbs z) ^ 4 / (η * M ^ 2) := by
  have hA := nonneg_of_growth hHb
  set L := sumAbs z with hLdef
  have hL0 : 0 ≤ L := sumAbs_nonneg z
  have hHz : |H z| ≤ A * (1 + L) := hHb z
  have hHc : |H (clipV M z)| ≤ A * (1 + L) :=
    (hHb _).trans (mul_le_mul_of_nonneg_left (add_le_add_right (sumAbs_clipV_le hM.le z) 1) hA)
  set c := clipF M t
  have hc : |c| ≤ |t| := abs_clipF_le_abs hM.le
  have e : t * H z - c * H (clipV M z) = (t - c) * H z + c * (H z - H (clipV M z)) := by ring
  have h1L : (1 + L) ^ 2 ≤ (1 + L) ^ 4 := by
    have : 1 ≤ (1 + L) ^ 2 := by nlinarith
    nlinarith
  have t1 : |(t - c) * H z| ≤ (t - c) ^ 2 / (2 * η) + η * A ^ 2 * (1 + L) ^ 4 / 2 := by
    rw [abs_mul]
    have hH2 : |H z| ^ 2 ≤ A ^ 2 * (1 + L) ^ 4 := by
      calc |H z| ^ 2 ≤ (A * (1 + L)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hHz 2
        _ = A ^ 2 * (1 + L) ^ 2 := by ring
        _ ≤ A ^ 2 * (1 + L) ^ 4 := mul_le_mul_of_nonneg_left h1L (sq_nonneg A)
    have key : |t - c| * |H z| ≤ (t - c) ^ 2 / (2 * η) + η * |H z| ^ 2 / 2 := by
      have h := sq_nonneg (|t - c| - η * |H z|)
      rw [← sq_abs (t - c), div_add_div _ _ (by positivity) (by norm_num),
        le_div_iff₀ (by positivity)]
      nlinarith
    have : η * |H z| ^ 2 / 2 ≤ η * A ^ 2 * (1 + L) ^ 4 / 2 := by
      have := mul_le_mul_of_nonneg_left hH2 hη.le
      linarith
    linarith
  have t2 : |c * (H z - H (clipV M z))| ≤
      η * t ^ 2 / 2 + 2 * A ^ 2 * (1 + L) ^ 4 / (η * M ^ 2) := by
    by_cases hLM : L ≤ M
    · rw [clipV_eq_of_le hLM, sub_self, mul_zero, abs_zero]; positivity
    · push_neg at hLM
      have hd : |H z - H (clipV M z)| ≤ 2 * A * (1 + L) := by
        linarith [abs_sub (H z) (H (clipV M z))]
      have hM2 : M ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ hM.le (by linarith) 2
      have h4 : (1 + L) ^ 2 * M ^ 2 ≤ (1 + L) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hM2 (sq_nonneg (1 + L))
        nlinarith
      rw [abs_mul]
      have s1 : |c| * |H z - H (clipV M z)| ≤ |t| * (2 * A * (1 + L)) :=
        mul_le_mul hc hd (abs_nonneg _) (abs_nonneg _)
      have s2 : |t| * (2 * A * (1 + L)) ≤ η * t ^ 2 / 2 + 2 * A ^ 2 * (1 + L) ^ 2 / η := by
        rw [← sq_abs t, div_add_div _ _ (by norm_num) hη.ne', le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (η * |t| - 2 * A * (1 + L))]
      have s3 : 2 * A ^ 2 * (1 + L) ^ 2 / η ≤ 2 * A ^ 2 * (1 + L) ^ 4 / (η * M ^ 2) := by
        rw [div_le_div_iff₀ hη (by positivity)]
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * A ^ 2 * η)
        nlinarith
      linarith
  rw [e]
  calc _ ≤ |(t - c) * H z| + |c * (H z - H (clipV M z))| := abs_add_le _ _
    _ ≤ _ := by linarith [t1, t2]

/-- **The integrated truncation error** on one probability space. -/
theorem trunc_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → ℝ} {Z : Ω → Fin J → ℝ} (hTm : AEStronglyMeasurable T P)
    (hZm : AEStronglyMeasurable Z P) (hT2 : Integrable (fun x => T x ^ 2) P)
    (hΦ : Integrable (fun x => (1 + sumAbs (Z x)) ^ 4) P) (hH : Continuous H)
    {M η : ℝ} (hM : 0 < M) (hη : 0 < η) :
    Integrable (fun x => T x * H (Z x)) P ∧
    |∫ x, T x * H (Z x) ∂P - ∫ x, clipF M (T x) * H (clipV M (Z x)) ∂P| ≤
      (∫ x, (T x - clipF M (T x)) ^ 2 ∂P) / (2 * η) +
        η * A ^ 2 * (∫ x, (1 + sumAbs (Z x)) ^ 4 ∂P) / 2 + η * (∫ x, T x ^ 2 ∂P) / 2 +
        2 * A ^ 2 * (∫ x, (1 + sumAbs (Z x)) ^ 4 ∂P) / (η * M ^ 2) := by
  have hA := nonneg_of_growth hHb
  have hcT : AEStronglyMeasurable (fun x => clipF M (T x)) P :=
    (continuous_clipF M).comp_aestronglyMeasurable hTm
  have hHZ : AEStronglyMeasurable (fun x => H (Z x)) P := hH.comp_aestronglyMeasurable hZm
  have hHcZ : AEStronglyMeasurable (fun x => H (clipV M (Z x))) P :=
    (hH.comp (continuous_clipV M)).comp_aestronglyMeasurable hZm
  -- domination by `T²/2 + A²(1+L)⁴/2`
  have hdom : Integrable (fun x => T x ^ 2 / 2 + A ^ 2 / 2 * (1 + sumAbs (Z x)) ^ 4) P :=
    (hT2.div_const 2).add (hΦ.const_mul _)
  have hgen : ∀ (s t : ℝ) (w z : Fin J → ℝ), |s| ≤ |t| → sumAbs w ≤ sumAbs z →
      |s * H w| ≤ t ^ 2 / 2 + A ^ 2 / 2 * (1 + sumAbs z) ^ 4 := fun s t w z hs hw => by
    have hz0 := sumAbs_nonneg z
    have hHw : |H w| ≤ A * (1 + sumAbs z) :=
      (hHb w).trans (mul_le_mul_of_nonneg_left (add_le_add_right hw 1) hA)
    have h1L : (1 + sumAbs z) ^ 2 ≤ (1 + sumAbs z) ^ 4 := by
      have : 1 ≤ (1 + sumAbs z) ^ 2 := by nlinarith
      nlinarith
    rw [abs_mul]
    have := mul_le_mul hs hHw (abs_nonneg _) (abs_nonneg _)
    nlinarith [sq_nonneg (|t| - A * (1 + sumAbs z)), sq_abs t,
      mul_le_mul_of_nonneg_left h1L (sq_nonneg A)]
  have hi1 : Integrable (fun x => T x * H (Z x)) P :=
    hdom.mono' (hTm.mul hHZ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hgen _ _ _ _ le_rfl le_rfl)
  have hi2 : Integrable (fun x => clipF M (T x) * H (clipV M (Z x))) P :=
    hdom.mono' (hcT.mul hHcZ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact hgen _ _ _ _ (abs_clipF_le_abs hM.le) (sumAbs_clipV_le hM.le _))
  have hi3 : Integrable (fun x => (T x - clipF M (T x)) ^ 2) P :=
    hT2.mono' ((hTm.sub hcT).pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sub_clipF_sq_le hM.le _)
  refine ⟨hi1, ?_⟩
  rw [← integral_sub hi1 hi2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hbig : Integrable (fun x => (T x - clipF M (T x)) ^ 2 / (2 * η) +
      η * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / 2 + η * T x ^ 2 / 2 +
      2 * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / (η * M ^ 2)) P :=
    (((hi3.div_const _).add ((hΦ.const_mul (η * A ^ 2)).div_const 2)).add
      ((hT2.const_mul η).div_const 2)).add ((hΦ.const_mul (2 * A ^ 2)).div_const _)
  calc ∫ x, |T x * H (Z x) - clipF M (T x) * H (clipV M (Z x))| ∂P
      ≤ ∫ x, ((T x - clipF M (T x)) ^ 2 / (2 * η) +
          η * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / 2 + η * T x ^ 2 / 2 +
          2 * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / (η * M ^ 2)) ∂P :=
        integral_mono (hi1.sub hi2).abs hbig fun x => trunc_pointwise hHb hM hη _ _
    _ = _ := by
        have i1 := hi3.div_const (2 * η)
        have i2 := (hΦ.const_mul (η * A ^ 2)).div_const 2
        have i3 := (hT2.const_mul η).div_const 2
        have i4 := (hΦ.const_mul (2 * A ^ 2)).div_const (η * M ^ 2)
        rw [integral_add (f := fun x => (T x - clipF M (T x)) ^ 2 / (2 * η) +
            η * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / 2 + η * T x ^ 2 / 2)
            (g := fun x => 2 * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / (η * M ^ 2)) ((i1.add i2).add i3) i4,
          integral_add (f := fun x => (T x - clipF M (T x)) ^ 2 / (2 * η) +
            η * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / 2) (g := fun x => η * T x ^ 2 / 2) (i1.add i2) i3,
          integral_add (f := fun x => (T x - clipF M (T x)) ^ 2 / (2 * η))
            (g := fun x => η * A ^ 2 * (1 + sumAbs (Z x)) ^ 4 / 2) i1 i2,
          integral_div, integral_div, integral_div, integral_div, integral_const_mul,
          integral_const_mul, integral_const_mul]

end trunc

end SharpLSI
