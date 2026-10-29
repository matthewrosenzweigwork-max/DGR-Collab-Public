import FullLabeledLSI.Examples.E01g0_Classify

/-!
# Lane D, helper E01g0: the matrix `T` of an attractive kernel in a Haar reference eigenbasis

For `W = attrW C` with `C` good, `K(x,y) = -C(x-y)` (centered kernel), and in a reference
eigenbasis of Haar measure `T_{ij} = -Ĉ(N_j) δ_{ij}` where `N_j` is the frequency of `e_j`
(Task A, steps 4-5 of PLAN.md).
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem continuous_of_good {C : Torus 1 → ℝ} (hC : GoodKernel C) : Continuous C :=
  Sec8.continuous_of_isSmoothT hC.smooth

/-- The centered kernel of `W = C(0) - C(x-y)` at Haar measure is `-C(x-y)`. -/
theorem centeredKernel_attr {C : Torus 1 → ℝ} (hC : GoodKernel C) (x y : Torus 1) :
    centeredKernel (attrW C) (haar 1) x y = -C (x - y) := by
  have hc := continuous_of_good hC
  have hint : ∀ a : Torus 1, Integrable (fun z => C (a - z)) (haar 1) := fun a =>
    (hc.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hconv : ∀ a : Torus 1, convMeas (attrW C) (haar 1) a = C 0 := by
    intro a
    unfold convMeas attrW
    rw [integral_sub (integrable_const _) (hint a), integral_const,
      integral_sub_left_eq_self (fun z => C z) (haar 1) a, hC.meanZero]
    simp
  have hE : interE (attrW C) (haar 1) (haar 1) = C 0 := by
    unfold interE attrW
    have : ∀ b : Torus 1, ∫ a, (C 0 - C (a - b)) ∂haar 1 = C 0 := by
      intro b
      have hint2 : Integrable (fun a => C (a - b)) (haar 1) :=
        (hc.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [integral_sub (integrable_const _) hint2, integral_const,
        integral_sub_right_eq_self (fun z => C z) b, hC.meanZero]
      simp
    simp_rw [this]
    simp
  unfold centeredKernel
  rw [hconv, hconv, hE]
  unfold attrW
  ring

/-- Frequencies of the Fourier support. -/
def SuppFreq (u : Torus 1 → ℝ) (N : ℕ) : Prop := ∀ k : Fin 1 → ℤ, cf u k ≠ 0 → k = K1 N ∨ k = -K1 N

/-- `T_{ij} = -Ĉ(N_j) δ_{ij}` when `e_{j+1}` has frequency `N_j ≥ 1`. -/
theorem Tmat_entry {C : Torus 1 → ℝ} (hC : GoodKernel C) {e : ℕ → Torus 1 → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (haar 1) e lam) (i j : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hs : SuppFreq (e (j + 1)) N) :
    Tmat (attrW C) (haar 1) e i j = if i = j then -chat C (N : ℤ) else 0 := by
  have hc := continuous_of_good hC
  have hk : K1 (N : ℤ) ≠ 0 := K1_ne_zero (by exact_mod_cast (by omega : N ≠ 0))
  have hL2 : MemLp (e (j + 1)) 2 volume := (he.memH1 (j + 1)).2.1
  set α : ℂ := cf (e (j + 1)) (K1 N) with hα
  have hae := ae_eq_two_re (e (j + 1)) hL2 (K1 N) hk hs
  have hcev : ∀ x, C (-x) = C x := hC.even
  -- inner integral
  have hinner : ∀ x : Torus 1, ∫ y, C (x - y) * e (j + 1) y =
      chat C N * (2 * (α * mFourier (K1 N) x).re) := by
    intro x
    have h1 : ∫ y, C (x - y) * e (j + 1) y = ∫ y, C (x - y) * (2 * (α * mFourier (K1 N) y).re) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [hy]
    rw [h1, conv_two_re C hcev hc α (K1 N) x, chat_eq]
  have hT : ∀ x : Torus 1, ∫ y, centeredKernel (attrW C) (haar 1) x y * e (i + 1) x * e (j + 1) y ∂haar 1 =
      -(e (i + 1) x) * (chat C N * (2 * (α * mFourier (K1 N) x).re)) := by
    intro x
    rw [← hinner x, ← integral_const_mul]
    -- rewrite integrand
    have : ∀ y, centeredKernel (attrW C) (haar 1) x y * e (i + 1) x * e (j + 1) y =
        -(e (i + 1) x) * (C (x - y) * e (j + 1) y) := by
      intro y; rw [centeredKernel_attr hC]; ring
    simp_rw [this]
  have hTm : Tmat (attrW C) (haar 1) e i j = -chat C N * ∫ x, e (i + 1) x * e (j + 1) x := by
    unfold Tmat
    simp_rw [hT]
    have h2 : ∀ x, -(e (i + 1) x) * (chat C N * (2 * (α * mFourier (K1 N) x).re)) =
        -chat C N * (e (i + 1) x * (2 * (α * mFourier (K1 N) x).re)) := by intro x; ring
    simp_rw [h2]
    rw [integral_const_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hTm]
  have := he.orthonormal (i + 1) (j + 1)
  rw [this]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (by omega)]; simp

end SharpLSI.FL.Ex.LaneD
