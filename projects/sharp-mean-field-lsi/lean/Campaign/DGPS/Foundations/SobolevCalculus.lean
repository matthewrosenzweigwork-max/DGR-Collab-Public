import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.WeakContractions

/-!
# Weak gradient on a zero set; the gradient of a density (DEF003)

INTERFACES/common_lemmas.md DEF003. For `u ∈ H¹(m)` with weak gradient `g`:

* `DGPS.gradient_zero_on_zero_set`: `g = 0` a.e. on `{u = 0}` (FOU003 level-set statement at
  level `0`).
* `DGPS.density_gradient`: `u²` has the `L¹` weak gradient `2 u ∇u`; for an absolute-admissible
  density `ρ = u²` this is `DGPS.AbsoluteDensity.density_gradient` (with `∇u = weakGradient u`),
  and where the product `2 u ∇u` lies in `L²` (and `ρ ∈ L²`) it is the `H¹` gradient of `ρ`.

Route: smooth periodic approximation in `H¹` (FOU002) plus the classical product rule, closed
in `L¹` by Hölder (`weak_product_rule_L1`), instead of the truncation/Lipschitz approximation
sketched in the lemma DAG.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-! ### Zero set -/

/-- `∇u = 0` a.e. on the zero set `{u = 0}` of `u ∈ H¹(m)`. -/
theorem gradient_zero_on_zero_set {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) : ∀ᵐ x ∂haar d, u x = 0 → g x = 0 :=
  h.ae_grad_eq_zero 0

/-- The same statement for the canonical gradient `weakGradient u hu`. -/
theorem weakGradient_zero_on_zero_set {u : Torus d → ℝ} (hu : MemH1 u) :
    ∀ᵐ x ∂haar d, u x = 0 → weakGradient u hu x = 0 :=
  gradient_zero_on_zero_set (isWeakGradient_weakGradient hu)

/-! ### Hölder convergence of products -/

theorem eLpNorm_mul_le_two {a b : Torus d → ℝ} (ha : MemLp a 2 (haar d)) (hb : MemLp b 2 (haar d)) :
    eLpNorm (fun x => a x * b x) 1 (haar d)
      ≤ eLpNorm a 2 (haar d) * eLpNorm b 2 (haar d) := by
  have := eLpNorm_smul_le_mul_eLpNorm (μ := haar d) (p := 2) (q := 2) (r := 1)
    ha.aestronglyMeasurable hb.aestronglyMeasurable
  exact this

theorem tendsto_eLpNorm_one_mul_sub {P Q : ℕ → Torus d → ℝ} {p q : Torus d → ℝ}
    (hQ : ∀ n, MemLp (Q n) 2 (haar d)) (hP : ∀ n, MemLp (P n) 2 (haar d))
    (hp : MemLp p 2 (haar d)) (hq : MemLp q 2 (haar d))
    (hPc : Tendsto (fun n => eLpNorm (fun x => P n x - p x) 2 (haar d)) atTop (𝓝 0))
    (hQc : Tendsto (fun n => eLpNorm (fun x => Q n x - q x) 2 (haar d)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun y => P n y * Q n y - p y * q y) 1 (haar d)) atTop (𝓝 0) := by
  have key : ∀ n, eLpNorm (fun y => P n y * Q n y - p y * q y) 1 (haar d) ≤
      eLpNorm (fun x => P n x - p x) 2 (haar d) *
        (eLpNorm q 2 (haar d) + eLpNorm (fun x => Q n x - q x) 2 (haar d))
      + eLpNorm p 2 (haar d) * eLpNorm (fun x => Q n x - q x) 2 (haar d) := by
    intro n
    have hPp : MemLp (fun x => P n x - p x) 2 (haar d) := (hP n).sub hp
    have hQq : MemLp (fun x => Q n x - q x) 2 (haar d) := (hQ n).sub hq
    have e : (fun y => P n y * Q n y - p y * q y)
        = (fun y => (P n y - p y) * Q n y) + (fun y => p y * (Q n y - q y)) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [e]
    refine le_trans (eLpNorm_add_le le_rfl) ?_
    refine add_le_add ((eLpNorm_mul_le_two hPp (hQ n)).trans ?_) (eLpNorm_mul_le_two hp hQq)
    gcongr
    have e2 : Q n = (fun x => q x) + (fun x => Q n x - q x) := by funext x; simp
    calc eLpNorm (Q n) 2 (haar d)
        = eLpNorm ((fun x => q x) + (fun x => Q n x - q x)) 2 (haar d) := by rw [← e2]
      _ ≤ _ := eLpNorm_add_le one_le_two
  have hb : Tendsto (fun n => eLpNorm q 2 (haar d) + eLpNorm (fun x => Q n x - q x) 2 (haar d))
      atTop (𝓝 (eLpNorm q 2 (haar d) + 0)) := tendsto_const_nhds.add hQc
  have h1 := ENNReal.Tendsto.mul hPc (Or.inr (by simpa using hq.eLpNorm_ne_top)) hb
    (Or.inr ENNReal.zero_ne_top)
  have h2 := ENNReal.Tendsto.const_mul hQc (Or.inr hp.eLpNorm_ne_top)
  have := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun n => zero_le) key

/-! ### The weak product rule in `L¹` -/

/-- Weak product rule for two `H¹` functions: `uv` has the `L¹` weak gradient `v ∇u + u ∇v`. -/
theorem weak_product_rule_L1 {u v : Torus d → ℝ} {g h : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (hv : IsWeakGradient v h) :
    IsWeakGradientLp 1 (fun x => u x * v x) (fun x => v x • g x + u x • h x) where
  memLp := by
    have := hu.memLp.mul (r := 1) hv.memLp
    exact this
  memLp_grad := by
    have h1 : MemLp (fun x => v x • g x) 1 (haar d) :=
      MemLp.smul (r := 1) hv.memLp hu.memLp_grad
    have h2 : MemLp (fun x => u x • h x) 1 (haar d) :=
      MemLp.smul (r := 1) hu.memLp hv.memLp_grad
    exact h1.add h2
  ibp φ hφ j := by
    obtain ⟨a, ha, haw, ha1, ha2⟩ := exists_smooth_tendsto_H1 hu
    obtain ⟨b, hb, hbw, hb1, hb2⟩ := exists_smooth_tendsto_H1 hv
    have haL : ∀ n, MemLp (a n) 2 (haar d) := fun n => (haw n).memLp
    have hbL : ∀ n, MemLp (b n) 2 (haar d) := fun n => (hbw n).memLp
    have hgaL : ∀ n, MemLp (fun x => coordPartial j (a n) x) 2 (haar d) := fun n =>
      memLp_coord (haw n).memLp_grad j
    have hgbL : ∀ n, MemLp (fun x => coordPartial j (b n) x) 2 (haar d) := fun n =>
      memLp_coord (hbw n).memLp_grad j
    have hgj : MemLp (fun x => g x j) 2 (haar d) := memLp_coord hu.memLp_grad j
    have hhj : MemLp (fun x => h x j) 2 (haar d) := memLp_coord hv.memLp_grad j
    -- convergence of the product in `L¹`
    have c1 := tendsto_eLpNorm_one_mul_sub hbL haL hu.memLp hv.memLp ha1 hb1
    have i1 : ∀ n, Integrable (fun x => a n x * b n x) (haar d) := fun n =>
      (MemLp.mul (r := 1) (haL n) (hbL n)).integrable le_rfl
    have c1' : Tendsto (fun n => ∫⁻ y, ‖a n y * b n y - u y * v y‖ₑ ∂haar d) atTop (𝓝 0) := by
      refine c1.congr fun n => eLpNorm_one_eq_lintegral_enorm ?_
      exact ((haL n).aestronglyMeasurable.mul (hbL n).aestronglyMeasurable).sub
        (hu.memLp.aestronglyMeasurable.mul hv.memLp.aestronglyMeasurable)
    have t1 := tendsto_integral_mul_of_L1 i1
      ((MemLp.mul (r := 1) hu.memLp hv.memLp).integrable le_rfl)
      (hφ.memLp_top_coordPartial j) c1'
    -- convergence of the gradient product in `L¹`
    have d1 := tendsto_eLpNorm_one_mul_sub (P := fun n x => b n x)
      (Q := fun n x => coordPartial j (a n) x) (p := v) (q := fun x => g x j) hgaL hbL hv.memLp hgj
      hb1 (by simpa [smoothGrad_apply] using ha2 j)
    have d2 := tendsto_eLpNorm_one_mul_sub (P := fun n x => a n x)
      (Q := fun n x => coordPartial j (b n) x) (p := u) (q := fun x => h x j) hgbL haL hu.memLp hhj
      ha1 (by simpa [smoothGrad_apply] using hb2 j)
    have hm1 : ∀ n, MemLp (fun x => b n x * coordPartial j (a n) x) 1 (haar d) := fun n =>
      MemLp.mul (r := 1) (hbL n) (hgaL n)
    have hm2 : ∀ n, MemLp (fun x => a n x * coordPartial j (b n) x) 1 (haar d) := fun n =>
      MemLp.mul (r := 1) (haL n) (hgbL n)
    have hm1' : MemLp (fun x => v x * g x j) 1 (haar d) := MemLp.mul (r := 1) hv.memLp hgj
    have hm2' : MemLp (fun x => u x * h x j) 1 (haar d) := MemLp.mul (r := 1) hu.memLp hhj
    have c2 : Tendsto (fun n => ∫⁻ y, ‖(b n y * coordPartial j (a n) y
        + a n y * coordPartial j (b n) y) - (v y * g y j + u y * h y j)‖ₑ ∂haar d)
        atTop (𝓝 0) := by
      have hsum := d1.add d2
      rw [add_zero] at hsum
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun n => zero_le) (fun n => ?_)
      have hmeas : AEStronglyMeasurable (fun y => (b n y * coordPartial j (a n) y
          + a n y * coordPartial j (b n) y) - (v y * g y j + u y * h y j)) (haar d) :=
        ((hm1 n).aestronglyMeasurable.add (hm2 n).aestronglyMeasurable).sub
          (hm1'.aestronglyMeasurable.add hm2'.aestronglyMeasurable)
      rw [← eLpNorm_one_eq_lintegral_enorm hmeas]
      have e : (fun y => (b n y * coordPartial j (a n) y + a n y * coordPartial j (b n) y)
          - (v y * g y j + u y * h y j)) =
          (fun y => b n y * coordPartial j (a n) y - v y * g y j)
          + (fun y => a n y * coordPartial j (b n) y - u y * h y j) := by
        funext y; simp only [Pi.add_apply]; ring
      rw [e]
      exact eLpNorm_add_le le_rfl
    have t2 := tendsto_integral_mul_of_L1
      (F := fun n x => b n x * coordPartial j (a n) x + a n x * coordPartial j (b n) x)
      (fun n => (hm1 n).integrable le_rfl |>.add ((hm2 n).integrable le_rfl))
      (hm1'.integrable le_rfl |>.add (hm2'.integrable le_rfl)) hφ.memLp_top c2
    -- classical integration by parts for the smooth approximants
    have hsm : ∀ n, ∫ x, a n x * b n x * coordPartial j φ x ∂haar d
        = -∫ x, (b n x * coordPartial j (a n) x + a n x * coordPartial j (b n) x) * φ x
          ∂haar d := by
      intro n
      have := ((ha n).mul (hb n)).isWeakGradient.ibp φ hφ j
      simp only [smoothGrad_apply] at this
      rw [this]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [coordPartial_mul (ha n) (hb n) j]
      ring
    have t3 := (t2.neg).congr (fun n => (hsm n).symm)
    have := tendsto_nhds_unique t3 t1
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact this.symm

/-! ### The gradient of a square and of a density -/

/-- For `u ∈ H¹(m)`, `u²` has the `L¹` weak gradient `2 u ∇u` (no sign condition on `u`). -/
theorem weak_square_gradient {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) :
    IsWeakGradientLp 1 (fun x => u x ^ 2) (fun x => (2 * u x) • g x) := by
  have e1 : (fun x => u x ^ 2) = fun x => u x * u x := by funext x; ring
  have e2 : (fun x => (2 * u x) • g x) = fun x => u x • g x + u x • g x := by
    funext x; rw [two_mul, add_smul]
  rw [e1, e2]
  exact weak_product_rule_L1 hu hu

/-- DEF003: the density `ρ = u²` of an absolute-admissible density has the `L¹` weak gradient
`2 u ∇u`, `∇u = weakGradient u`; and where `ρ` and the product `2 u ∇u` lie in `L²` it is the
`H¹` weak gradient of `ρ`. -/
theorem density_gradient (ρ : AbsoluteDensity d) :
    IsWeakGradientLp 1 ρ.density
        (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) ∧
      (MemLp ρ.density 2 (haar d) →
        MemLp (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) 2 (haar d) →
        IsWeakGradient ρ.density
          (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x)) := by
  have h := weak_square_gradient (isWeakGradient_weakGradient ρ.sqrt_mem)
  exact ⟨h, fun h1 h2 => ⟨h1, h2, h.ibp⟩⟩

end DGPS
