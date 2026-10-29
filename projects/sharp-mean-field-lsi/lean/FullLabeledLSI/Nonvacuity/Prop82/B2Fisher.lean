import FullLabeledLSI.Nonvacuity.Prop82.B1Convergence

/-!
# Lane B, module 2: lower semicontinuity of the Fisher information

If the weak gradients of `√ρ_n` converge weakly in `L²` to `g` and the Fisher
informations converge to `L`, then `4 ∫ g² ≤ L`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

theorem integrable_mul_of_memLp_two {f g : Torus 1 → Real} (hf : MemLp f 2 (haar 1))
    (hg : MemLp g 2 (haar 1)) : Integrable (fun x => f x * g x) (haar 1) := by
  refine Integrable.mono' (hf.integrable_sq.add hg.integrable_sq)
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le, Pi.add_apply]
  constructor <;> nlinarith [sq_nonneg (f x + g x), sq_nonneg (f x - g x)]

/-- Weak lower semicontinuity of the `L²` norm along a sequence whose squared
norms converge. -/
theorem sq_integral_le_of_weak_tendsto {w : ℕ → Torus 1 → Real} {g : Torus 1 → Real}
    (hw : ∀ n, MemLp (w n) 2 (haar 1)) (hg : MemLp g 2 (haar 1))
    (hweak : ∀ h : Torus 1 → Real, MemLp h 2 (haar 1) →
      Tendsto (fun n => ∫ x, w n x * h x ∂haar 1) atTop (𝓝 (∫ x, g x * h x ∂haar 1)))
    {L : Real} (hL : Tendsto (fun n => ∫ x, w n x ^ 2 ∂haar 1) atTop (𝓝 L)) :
    ∫ x, g x ^ 2 ∂haar 1 ≤ L := by
  have hlim : Tendsto (fun n => 2 * ∫ x, w n x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1)
      atTop (𝓝 (2 * ∫ x, g x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1)) :=
    ((hweak g hg).const_mul 2).sub_const _
  have hgg : ∫ x, g x * g x ∂haar 1 = ∫ x, g x ^ 2 ∂haar 1 := by
    congr 1; funext x; ring
  rw [hgg] at hlim
  have hle : ∀ n, 2 * ∫ x, w n x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1 ≤
      ∫ x, w n x ^ 2 ∂haar 1 := by
    intro n
    have i1 := (hw n).integrable_sq
    have i2 := hg.integrable_sq
    have i3 := integrable_mul_of_memLp_two (hw n) hg
    have h0 : 0 ≤ ∫ x, (w n x - g x) ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (w n x - g x) ^ 2 ∂haar 1 =
        ∫ x, w n x ^ 2 ∂haar 1 - 2 * ∫ x, w n x * g x ∂haar 1 + ∫ x, g x ^ 2 ∂haar 1 := by
      have : ∀ x, (w n x - g x) ^ 2 = (w n x ^ 2 - 2 * (w n x * g x)) + g x ^ 2 :=
        fun x => by ring
      simp_rw [this]
      rw [integral_add (f := fun x => w n x ^ 2 - 2 * (w n x * g x))
        (g := fun x => g x ^ 2) (i1.sub (i3.const_mul 2)) i2,
        integral_sub (f := fun x => w n x ^ 2) (g := fun x => 2 * (w n x * g x)) i1
          (i3.const_mul 2), integral_const_mul]
    linarith
  have := le_of_tendsto_of_tendsto' hlim hL hle
  linarith

/-- Lower semicontinuity of the physical Fisher information. -/
theorem fisher_lsc {rho : ℕ → Torus 1 → Real}
    (ha : ∀ n, Admissible cosV (cosW 1) (rho n)) {g : Torus 1 → Fin 1 → Real}
    (hg : MemLp (fun x => g x 0) 2 (haar 1))
    (hweak : ∀ h : Torus 1 → Real, MemLp h 2 (haar 1) →
      Tendsto (fun n => ∫ x, weakGrad (fun y => Real.sqrt (rho n y)) x 0 * h x ∂haar 1)
        atTop (𝓝 (∫ x, g x 0 * h x ∂haar 1)))
    {L : Real} (hL : Tendsto (fun n => fisher (rho n)) atTop (𝓝 L)) :
    4 * ∫ x, g x 0 ^ 2 ∂haar 1 ≤ L := by
  have hw : ∀ n, MemLp (fun x => weakGrad (fun y => Real.sqrt (rho n y)) x 0) 2 (haar 1) :=
    fun n => memLp_weakGrad_zero (ha n).2.2.1
  have hL' : Tendsto (fun n => ∫ x, weakGrad (fun y => Real.sqrt (rho n y)) x 0 ^ 2 ∂haar 1)
      atTop (𝓝 (L / 4)) := by
    refine (hL.div_const 4).congr fun n => ?_
    rw [fisher_eq_sqrt_energy (ha n)]
    ring
  have := sq_integral_le_of_weak_tendsto hw hg hweak hL'
  linarith

end SharpLSI.FL.Prop82
