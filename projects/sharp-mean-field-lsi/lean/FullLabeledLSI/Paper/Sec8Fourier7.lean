import FullLabeledLSI.Paper.Sec8Fourier6

/-!
# Section 8.5 (Corollary 8.4), part 7: the cross term

For `ρ ≥ 0` with `∫ρ = 1` and weak gradient `g`:
`∑_k ∫ g_k b_k = -∬ ΔG(x-y) ρ(x)ρ(y)`, where `b_k = ∫ ∂_k G(· - y) ρ(y) dy = ∂_k (W*ρ)`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem bForceL_WG {G : Torus d → ℝ} (hG : IsSmoothT G) (ρ : Torus d → ℝ) (x : Torus d)
    (k : Fin d) : bForceL (WG G) ρ x k = ∫ y, dpart G k (x - y) * ρ y ∂haar d := by
  unfold bForceL
  simp_rw [bGrad_WG hG]

theorem Qint_dens {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (K : Torus d → ℝ) :
    Qint (densMeasure ρ) K = ∫ y, ρ y * ∫ x, ρ x * K (x - y) ∂haar d ∂haar d := by
  unfold Qint
  have h1 : ∀ y, ∫ x, K (x - y) ∂densMeasure ρ = ∫ x, ρ x * K (x - y) ∂haar d := fun y =>
    integral_densMeasure' hρ0 hρ1 (fun x => K (x - y))
  simp_rw [h1]
  exact integral_densMeasure' hρ0 hρ1 (fun y => ∫ x, ρ x * K (x - y) ∂haar d)

theorem cross_term_eq {G : Torus d → ℝ} (hG : IsSmoothT G) {ρ : Torus d → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) {g : Torus d → Fin d → ℝ}
    (h : IsWeakGrad ρ g) (hg : ∀ k, Integrable (fun x => g x k) (haar d)) :
    ∑ k, ∫ x, g x k * bForceL (WG G) ρ x k ∂haar d = -Qint (densMeasure ρ) (lap G) := by
  have hρi : Integrable ρ (haar d) := integrable_of_integral_eq_one' hρ1
  have hdc : ∀ k, Continuous (dpart G k) := fun k => continuous_of_isSmoothT (isSmoothT_dpart hG k)
  have hd2c : ∀ k, Continuous (dpart (dpart G k) k) := fun k =>
    continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_dpart hG k) k)
  have hlapc : Continuous (lap G) := continuous_of_isSmoothT (isSmoothT_lap hG)
  -- step 1: Fubini
  have step1 : ∀ k, Integrable (fun y => ρ y * ∫ x, g x k * dpart G k (x - y) ∂haar d) (haar d) ∧
      ∫ x, g x k * bForceL (WG G) ρ x k ∂haar d =
        ∫ y, ρ y * ∫ x, g x k * dpart G k (x - y) ∂haar d ∂haar d := by
    intro k
    obtain ⟨C, hC⟩ := exists_abs_le_of_smooth (isSmoothT_dpart hG k)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    set F : Torus d × Torus d → ℝ := fun p => g p.1 k * (dpart G k (p.1 - p.2) * ρ p.2) with hF
    have hFi : Integrable F ((haar d).prod (haar d)) := by
      refine Integrable.mono' (((hg k).norm.mul_prod hρi.norm).const_mul C) ?_
        (Eventually.of_forall fun p => ?_)
      · exact ((hg k).aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst).mul
          (((hdc k).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul
            (hρi.aestronglyMeasurable.comp_quasiMeasurePreserving
              Measure.quasiMeasurePreserving_snd))
      · simp only [hF, norm_mul, Real.norm_eq_abs]
        have := hC (p.1 - p.2)
        calc |g p.1 k| * (|dpart G k (p.1 - p.2)| * |ρ p.2|) ≤ |g p.1 k| * (C * |ρ p.2|) := by gcongr
          _ = C * (‖g p.1 k‖ * ‖ρ p.2‖) := by simp only [Real.norm_eq_abs]; ring
    have e1 : ∀ x, g x k * bForceL (WG G) ρ x k = ∫ y, F (x, y) ∂haar d := fun x => by
      rw [bForceL_WG hG, ← integral_const_mul]
    have e2 : ∀ y, ρ y * ∫ x, g x k * dpart G k (x - y) ∂haar d = ∫ x, F (x, y) ∂haar d :=
      fun y => by
        rw [← integral_const_mul]
        congr 1; funext x; simp only [hF]; ring
    refine ⟨?_, ?_⟩
    · have := hFi.integral_prod_right
      exact this.congr (Eventually.of_forall fun y => (e2 y).symm)
    · simp_rw [e1, e2]
      exact integral_integral_swap hFi
  -- step 2: sum over k
  have step2 : ∀ y : Torus d,
      ∑ k, ∫ x, g x k * dpart G k (x - y) ∂haar d = -∫ x, ρ x * lap G (x - y) ∂haar d := by
    intro y
    have hi : ∀ k, Integrable (fun x => ρ x * dpart (dpart G k) k (x - y)) (haar d) := fun k => by
      obtain ⟨C, hC⟩ := exists_abs_le_of_smooth (isSmoothT_dpart (isSmoothT_dpart hG k) k)
      refine Integrable.mono' (hρi.norm.const_mul C) (hρi.aestronglyMeasurable.mul
        ((hd2c k).comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Real.norm_eq_abs]
      calc |ρ x| * |dpart (dpart G k) k (x - y)| ≤ |ρ x| * C := by gcongr; exact hC _
        _ = C * ‖ρ x‖ := by simp only [Real.norm_eq_abs]; ring
    have : ∫ x, ρ x * lap G (x - y) ∂haar d =
        ∑ k, ∫ x, ρ x * dpart (dpart G k) k (x - y) ∂haar d := by
      rw [← integral_finsetSum _ fun k _ => hi k]
      congr 1; funext x
      simp only [lap, Finset.mul_sum]
    rw [this, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [ibp_shift hG h hρi hg y k, neg_neg]
  -- assemble
  rw [Finset.sum_congr rfl fun k _ => (step1 k).2]
  rw [← integral_finsetSum _ fun k _ => (step1 k).1]
  rw [Qint_dens hρ0 hρ1, ← integral_neg]
  congr 1; funext y
  rw [← Finset.mul_sum, step2 y]
  ring

end Sec8
end SharpLSI.FL
