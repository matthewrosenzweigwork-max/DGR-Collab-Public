import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D13_Equilibrium
import SharpSymmetricLSI.Infra.Classical

/-!
# D12 and D20: the cosine model (3.1), (3.3), (3.23), (3.24)

`d = 1`, `V = 0`, `g(x) = cos(2πx)`, `W_κ(x,y) = κ(g(x-y) - 1)`, `a = 4π²`, `κ > 0` fixed.
`Q(ρ) = |∫ e^{2πix} ρ(x) dm(x)|²` (3.3). The cosine Gibbs measure, its constants
`r^sym_{N,κ}`, `r^all_{N,κ}` (3.2), `λ^all_{N,κ}` (3.24), `r_{*,κ}` are the general
definitions applied to `V = 0`, `W = W_κ` (`cosGibbs`, …). `U_N = (κ/(2N)) |∑ⱼ e^{2πixⱼ}|²`,
`K_N = ∫ e^{-U_N} dm^{⊗N}` (3.23).

Points of `𝕋 = 𝕋^1` are `x : Fin 1 → ℝ/ℤ`; `e^{2πix}` is `fourier 1 (x 0)`.
-/

open MeasureTheory
open scoped Real

namespace SharpLSI

/-- `a = 4π²`, the first positive eigenvalue of `-∂²` on the unit circle. -/
noncomputable def aCos : ℝ := 4 * π ^ 2

/-- `e^{2πix}` on `𝕋`. -/
noncomputable def expT (x : Torus 1) : ℂ := fourier 1 (x 0)

/-- `g(x) = cos(2πx)`. -/
noncomputable def gCos (x : Torus 1) : ℝ := (expT x).re

/-- `V = 0`. -/
def cosV : Torus 1 → ℝ := fun _ => 0

/-- `W_κ(x,y) = κ(cos(2π(x-y)) - 1)` (manuscript (3.1)). -/
noncomputable def cosW (κ : ℝ) (x y : Torus 1) : ℝ := κ * (gCos (x - y) - 1)

/-- `Q(ρ) = |∫ e^{2πix} ρ(x) dm(x)|²` for a density `ρ` (manuscript (3.3)). -/
noncomputable def firstMode (ρ : Torus 1 → ℝ) : ℝ :=
  Complex.normSq (∫ x, expT x * (ρ x : ℂ) ∂haar 1)

/-- `(g*ρ)(x) = ∫ g(x-y) ρ(y) dm(y)`. -/
noncomputable def gConv (ρ : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  ∫ y, gCos (x - y) * ρ y ∂haar 1

/-- `U_N(X) = (κ/(2N)) |∑ⱼ e^{2πixⱼ}|²` (manuscript (3.23)). -/
noncomputable def cosU (κ : ℝ) (N : ℕ) (X : Config N 1) : ℝ :=
  κ / (2 * (N : ℝ)) * Complex.normSq (∑ j, expT (X j))

/-- `K_N = ∫ e^{-U_N} dm^{⊗N}` (manuscript (3.23)). -/
noncomputable def cosK (κ : ℝ) (N : ℕ) : ℝ := ∫ X : Config N 1, Real.exp (-cosU κ N X)

/-- The generator `L_N g = Δg - ∇U_N·∇g` (manuscript, before (3.33)). -/
noncomputable def cosGen (κ : ℝ) (N : ℕ) (g : Config N 1 → ℝ) (X : Config N 1) : ℝ :=
  laplacianC g X - gradDotC (cosU κ N) g X

/-- Sanity lemma for D20: for the cosine model, `U_N`, `K_N` of (3.23) coincide with the
centered objects of (4.15) for `μ = m`. -/
theorem cosU_eq_Ucentered (κ : ℝ) (N : ℕ) :
    cosU κ N = Ucentered (cosW κ) (haar 1) N ∧
      cosK κ N = centeredPartition (cosW κ) (haar 1) N := by
  set h0 : UnitAddCircle := ((2⁻¹ : ℝ) : UnitAddCircle)
  have hf : ∀ x : UnitAddCircle, fourier 1 (x + h0) = -fourier 1 x := fun x => by
    have := fourier_add_half_inv_index (T := 1) (n := 1) one_ne_zero one_pos x
    simpa [h0] using this
  have hh : h0 + h0 = 0 := by
    simp only [h0, ← AddCircle.coe_add]
    norm_num
  set h : Torus 1 := fun _ => h0
  have hneg : -h = h := by
    funext k; simp only [h, Pi.neg_apply]; exact neg_eq_of_add_eq_zero_left hh
  have hg : ∀ z : Torus 1, gCos (z + h) = -gCos z := fun z => by
    simp only [gCos, expT, Pi.add_apply, h, hf, Complex.neg_re]
  have hgc : Continuous gCos := by
    unfold gCos expT
    exact Complex.continuous_re.comp ((fourier 1).continuous.comp (continuous_apply 0))
  have hgb : ∀ z, |gCos z| ≤ 1 := fun z => by
    unfold gCos expT
    refine (Complex.abs_re_le_norm _).trans ?_
    simp
  have hint : ∀ f : Torus 1 → ℝ, Continuous f → (∀ z, |f z| ≤ 1) → Integrable f (haar 1) :=
    fun f hf1 hf2 => Integrable.of_bound hf1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hf2 z)
  -- `∫ g(x - y) dy = 0` and `∫ g(x - y) dx = 0`
  have hy : ∀ x : Torus 1, ∫ y, gCos (x - y) ∂haar 1 = 0 := fun x => by
    have h1 := integral_add_right_eq_self (μ := haar 1) (fun y => gCos (x - y)) h
    have h2 : ∀ y, gCos (x - (y + h)) = -gCos (x - y) := fun y => by
      rw [show x - (y + h) = x - y + -h by abel, hneg, hg]
    simp only [h2, integral_neg] at h1
    linarith
  have hx : ∀ y : Torus 1, ∫ x, gCos (x - y) ∂haar 1 = 0 := fun y => by
    have h1 := integral_add_right_eq_self (μ := haar 1) (fun x => gCos (x - y)) h
    have h2 : ∀ x, gCos (x + h - y) = -gCos (x - y) := fun x => by
      rw [show x + h - y = x - y + h by abel, hg]
    simp only [h2, integral_neg] at h1
    linarith
  have hconv : ∀ x, convMeas (cosW κ) (haar 1) x = -κ := fun x => by
    unfold convMeas cosW
    rw [integral_const_mul, integral_sub (f := fun y => gCos (x - y)) (g := fun _ => (1 : ℝ))
      (hint _ (hgc.comp (continuous_const.sub continuous_id)) fun y => hgb _) (integrable_const 1),
      hy]
    simp
  have hinter : interE (cosW κ) (haar 1) (haar 1) = -κ := by
    unfold interE cosW
    have : ∀ y, ∫ x, κ * (gCos (x - y) - 1) ∂haar 1 = -κ := fun y => by
      rw [integral_const_mul, integral_sub (f := fun x => gCos (x - y)) (g := fun _ => (1 : ℝ))
        (hint _ (hgc.comp (continuous_id.sub continuous_const)) fun x => hgb _) (integrable_const 1),
        hx]
      simp
    simp [this]
  have hK : ∀ x y, centeredKernel (cosW κ) (haar 1) x y = κ * gCos (x - y) := fun x y => by
    unfold centeredKernel
    rw [hconv, hconv, hinter]
    unfold cosW; ring
  have hU : cosU κ N = Ucentered (cosW κ) (haar 1) N := by
    funext X
    unfold cosU Ucentered
    simp_rw [hK]
    have hns : Complex.normSq (∑ j, expT (X j)) = ∑ i, ∑ j, gCos (X i - X j) := by
      have e1 : (Complex.normSq (∑ j, expT (X j)) : ℂ) =
          ∑ i, ∑ j, expT (X i) * (starRingEnd ℂ) (expT (X j)) := by
        rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      have e2 : ∀ i j, expT (X i) * (starRingEnd ℂ) (expT (X j)) = expT (X i - X j) := by
        intro i j
        unfold expT
        rw [Pi.sub_apply, ← fourier_neg, fourier_apply, fourier_apply, fourier_apply,
          show (1 : ℤ) • (X i 0 - X j 0) = 1 • X i 0 + (-1 : ℤ) • X j 0 by
            simp [sub_eq_add_neg], AddCircle.toCircle_add, Circle.coe_mul]
        rfl
      have := congrArg Complex.re e1
      simp only [Complex.ofReal_re, Complex.re_sum] at this
      rw [this]
      simp only [e2, gCos]
    rw [hns, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨hU, ?_⟩
  unfold cosK centeredPartition
  rw [hU]
  rfl

end SharpLSI
