import FullLabeledLSI.Paper.Sec8Fourier7

/-!
# Section 8.5 (Corollary 8.4), part 8: lower bound for the dissipation

`D(ρ) ≥ 4 ∑_k ∫ (∂_k √ρ)² - 2 ∬ ΔG(x-y) ρ(x)ρ(y)` for `W = G(x-y) - G(0)`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem sq_expand_ge {u : Torus d → ℝ} {w b : Fin d → Torus d → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hu : MemLp u 2 (haar d)) (hw : ∀ k, MemLp (w k) 2 (haar d))
    (hbm : ∀ k, Measurable (b k)) (hbb : ∀ k x, |b k x| ≤ C) :
    Integrable (fun x => ∑ k, (2 * w k x + u x * b k x) ^ 2) (haar d) ∧
    4 * ∑ k, ∫ x, w k x ^ 2 ∂haar d + 4 * ∑ k, ∫ x, u x * w k x * b k x ∂haar d ≤
      ∫ x, ∑ k, (2 * w k x + u x * b k x) ^ 2 ∂haar d := by
  have iU2 : Integrable (fun x => u x ^ 2) (haar d) := hu.integrable_sq
  have iA : ∀ k, Integrable (fun x => w k x ^ 2) (haar d) := fun k => (hw k).integrable_sq
  have iB : ∀ k, Integrable (fun x => u x * w k x * b k x) (haar d) := fun k =>
    Integrable.mono' ((iU2.add (iA k)).const_mul C)
      (((hu.aestronglyMeasurable.mul (hw k).aestronglyMeasurable).mul
        (hbm k).aestronglyMeasurable)) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |u x| * |w k x| ≤ u x ^ 2 + w k x ^ 2 := by
          nlinarith [sq_abs (u x), sq_abs (w k x), sq_nonneg (|u x| - |w k x|)]
        calc |u x| * |w k x| * |b k x| ≤ (u x ^ 2 + w k x ^ 2) * C :=
              mul_le_mul h1 (hbb k x) (abs_nonneg _) (by positivity)
          _ = C * (u x ^ 2 + w k x ^ 2) := by ring)
  have iC : ∀ k, Integrable (fun x => (u x * b k x) ^ 2) (haar d) := fun k =>
    Integrable.mono' (iU2.const_mul (C ^ 2))
      ((hu.aestronglyMeasurable.mul (hbm k).aestronglyMeasurable).pow 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
        have : b k x ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbb k x) 2
        calc u x ^ 2 * b k x ^ 2 ≤ u x ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
          _ = C ^ 2 * u x ^ 2 := by ring)
  have hpt : ∀ k x, (2 * w k x + u x * b k x) ^ 2 =
      4 * w k x ^ 2 + 4 * (u x * w k x * b k x) + (u x * b k x) ^ 2 := fun k x => by ring
  have iT : ∀ k, Integrable (fun x => (2 * w k x + u x * b k x) ^ 2) (haar d) := fun k => by
    simp_rw [hpt]
    exact (((iA k).const_mul 4).add ((iB k).const_mul 4)).add (iC k)
  refine ⟨integrable_finsetSum _ fun k _ => iT k, ?_⟩
  rw [integral_finsetSum _ fun k _ => iT k]
  have hk : ∀ k, ∫ x, (2 * w k x + u x * b k x) ^ 2 ∂haar d =
      4 * ∫ x, w k x ^ 2 ∂haar d + 4 * ∫ x, u x * w k x * b k x ∂haar d +
        ∫ x, (u x * b k x) ^ 2 ∂haar d := fun k => by
    simp_rw [hpt]
    have h1 : Integrable (fun x => 4 * w k x ^ 2 + 4 * (u x * w k x * b k x)) (haar d) :=
      ((iA k).const_mul 4).add ((iB k).const_mul 4)
    rw [integral_add h1 (iC k), integral_add ((iA k).const_mul 4) ((iB k).const_mul 4),
      integral_const_mul, integral_const_mul]
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have : 0 ≤ ∑ k, ∫ x, (u x * b k x) ^ 2 ∂haar d :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  linarith

theorem abs_bForceL_le {G : Torus d → ℝ} (hG : IsSmoothT G) {ρ : Torus d → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k x, |bForceL (WG G) ρ x k| ≤ C := by
  have hρi := integrable_of_integral_eq_one' hρ1
  have hb : ∀ k : Fin d, ∃ C, 0 ≤ C ∧ ∀ x, |bForceL (WG G) ρ x k| ≤ C := fun k => by
    obtain ⟨C, hC⟩ := exists_abs_le_of_smooth (isSmoothT_dpart hG k)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine ⟨C, hC0, fun x => ?_⟩
    rw [bForceL_WG hG]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |dpart G k (x - y) * ρ y| ∂haar d ≤ ∫ y, C * ρ y ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hρi.const_mul C) (Eventually.of_forall fun y => by
              show |dpart G k (x - y) * ρ y| ≤ C * ρ y
              rw [abs_mul, abs_of_nonneg (hρ0 y)]
              exact mul_le_mul_of_nonneg_right (hC _) (hρ0 y))
      _ = C := by rw [integral_const_mul, hρ1, mul_one]
  choose C hC0 hC using hb
  refine ⟨∑ k, C k, Finset.sum_nonneg fun k _ => hC0 k, fun k x => ?_⟩
  exact (hC k x).trans (Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ k))

/-- **`D(ρ) ≥ 4∫|∇√ρ|² - 2∬ ΔG(x-y) ρ(x)ρ(y)`.** -/
theorem dissipation_WG_ge {G : Torus d → ℝ} (hG : IsSmoothT G) (hGe : ∀ x, G (-x) = G x)
    {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    ENNReal.ofReal (4 * ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x k ^ 2 ∂haar d -
        2 * Qint (densMeasure ρ) (lap G)) ≤ dissipation (fun _ => (0 : ℝ)) (WG G) ρ := by
  obtain ⟨KW, hyp⟩ := hyp_WG hG hGe
  have hρi := integrable_of_integral_eq_one' hρ1
  set u : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hudef
  have hw := isWeakGrad_weakGrad hH1.1
  have hu2 : MemLp u 2 (haar d) := hH1.2.1
  have hg2 : ∀ k, MemLp (fun x => weakGrad u x k) 2 (haar d) := fun k =>
    hH1.2.2.of_le (hw.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)
  have hsq := isWeakGrad_sq hw hu2 hg2
  have hsq' : IsWeakGrad ρ (fun y k => 2 * u y * weakGrad u y k) := by
    have : (fun y => u y ^ 2) = ρ := funext fun x => Real.sq_sqrt (hρ0 x)
    rwa [this] at hsq
  have hb2 : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b => by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hgi : ∀ k, Integrable (fun y => 2 * u y * weakGrad u y k) (haar d) := fun k =>
    Integrable.mono' (hu2.integrable_sq.add (hg2 k).integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul (hg2 k).aestronglyMeasurable)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb2 _ _)
  have hcross := cross_term_eq hG hρ0 hρ1 hsq' hgi
  have hΦ : IsWeakGrad (fun x => (0 : ℝ) + convDens (WG G) ρ x) (bForceL (WG G) ρ) := by
    simpa using isWeakGrad_convDens' hyp hρi
  have hae : weakGrad (fun x => (0 : ℝ) + convDens (WG G) ρ x) =ᵐ[haar d] bForceL (WG G) ρ :=
    appA_weakGrad_ae_eq hΦ
  obtain ⟨C, hC0, hC⟩ := abs_bForceL_le hG hρ0 hρ1
  obtain ⟨hint, hge⟩ := sq_expand_ge (u := u) (w := fun k x => weakGrad u x k)
    (b := fun k x => bForceL (WG G) ρ x k) hC0 hu2 hg2
    (fun k => measurable_bForceL' hyp hρi k) hC
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hΦ⟩⟩]
  have hL : ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad u x k +
        u x * weakGrad (fun y => (fun _ => (0 : ℝ)) y + convDens (WG G) ρ y) x k) ^ 2) ∂haar d =
      ENNReal.ofReal (∫ x, ∑ k, (2 * weakGrad u x k + u x * bForceL (WG G) ρ x k) ^ 2 ∂haar d) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
      Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    have hx' : weakGrad (fun y => (fun _ => (0 : ℝ)) y + convDens (WG G) ρ y) x =
        bForceL (WG G) ρ x := hx
    simp only [hx']
  rw [hL]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∀ k, ∫ x, 2 * u x * weakGrad u x k * bForceL (WG G) ρ x k ∂haar d =
      2 * ∫ x, u x * weakGrad u x k * bForceL (WG G) ρ x k ∂haar d := fun k => by
    rw [← integral_const_mul]; congr 1; funext x; ring
  simp_rw [e] at hcross
  rw [← Finset.mul_sum] at hcross
  linarith

end Sec8
end SharpLSI.FL
