import SharpSymmetricLSI.Paper.LyapSchmidt16

/-!
# Section 4.2 (lane s42; R14): `L^∞` toolkit for the gradient of `y(a)`

* `toLinf : C(𝕋^d) →L L^∞(m)`;
* `mulLinf : L^∞ →L L^∞ →L L^∞`, the (Hölder) product;
* `forceL k : C(𝕋^d) →L L^∞`, `u ↦ ∂ₖ (W * (p u))` (the weak derivative `bForceL W (p u) · k`).
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `L^∞(m)` on the torus. -/
abbrev Linf (d : ℕ) := Lp ℝ ⊤ (haar d)

/-- The embedding `C(𝕋^d) → L^∞`. -/
def toLinf : CT d →L[ℝ] Linf d := ContinuousMap.toLp (E := ℝ) ⊤ (haar d) ℝ

theorem toLinf_ae (u : CT d) : (toLinf u : Torus d → ℝ) =ᵐ[haar d] u :=
  ContinuousMap.coeFn_toLp (E := ℝ) (μ := haar d) (p := ⊤) (𝕜 := ℝ) u

/-- The product on `L^∞`. -/
def mulLinf : Linf d →L[ℝ] Linf d →L[ℝ] Linf d :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun f g : Linf d => (f • g : Linf d))
      (fun f₁ f₂ g => Lp.smul_add f₁ f₂ g)
      (fun c f g => Lp.smul_assoc c f g)
      (fun f g₁ g₂ => Lp.add_smul f g₁ g₂)
      (fun c f g => (Lp.smul_comm c f g).symm))
    1 fun f g => by
      simp only [LinearMap.mk₂_apply, one_mul]
      exact Lp.norm_smul_le f g

theorem mulLinf_ae (f g : Linf d) :
    (mulLinf f g : Torus d → ℝ) =ᵐ[haar d] fun x => f x * g x := by
  have := Lp.coeFn_lpSMul (r := ⊤) f g
  filter_upwards [this] with x hx
  rw [show (mulLinf f g : Linf d) = (f • g : Linf d) from rfl, hx]
  rfl

section force
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

omit hμ in
theorem integral_abs_elDens_mul_le (u : CT d) :
    ∫ y, |elDens V W (μ : Measure (Torus d)) y * u y| ∂haar d ≤ ‖u‖ := by
  obtain ⟨-, hp0, hp1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hpi := integrable_of_integral_eq_one' hp1
  calc ∫ y, |elDens V W (μ : Measure (Torus d)) y * u y| ∂haar d ≤
      ∫ y, elDens V W (μ : Measure (Torus d)) y * ‖u‖ ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hpi.mul_const _) (Eventually.of_forall fun y => by
            show |elDens V W (μ : Measure (Torus d)) y * u y| ≤ _
            rw [abs_mul, abs_of_pos (hp0 y)]
            exact mul_le_mul_of_nonneg_left (abs_CT_le u y) (hp0 y).le)
    _ = ‖u‖ := by rw [integral_mul_const, hp1, one_mul]

theorem bForce_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : CT d) x k,
    |bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * u y) x k| ≤ C * ‖u‖ := by
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  refine ⟨max Cb₀ 0, le_max_right _ _, fun u x k => ?_⟩
  unfold bForceL
  refine (abs_integral_le_integral_abs).trans ?_
  have hi : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * u y) (haar d) :=
    integrable_elDens_mul hyp hμ (integrable_of_continuous u.continuous)
  calc ∫ y, |bGrad W x y k * (elDens V W (μ : Measure (Torus d)) y * u y)| ∂haar d ≤
      ∫ y, max Cb₀ 0 * |elDens V W (μ : Measure (Torus d)) y * u y| ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hi.abs.const_mul _) (Eventually.of_forall fun y => by
            show |bGrad W x y k * _| ≤ _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right ((hCb₀ x y k).trans (le_max_left _ _))
              (abs_nonneg _))
    _ = max Cb₀ 0 * ∫ y, |elDens V W (μ : Measure (Torus d)) y * u y| ∂haar d :=
        integral_const_mul _ _
    _ ≤ max Cb₀ 0 * ‖u‖ :=
        mul_le_mul_of_nonneg_left (integral_abs_elDens_mul_le hyp (μ := μ) u) (le_max_right _ _)

theorem memLp_force (u : CT d) (k : Fin d) :
    MemLp (fun x => bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * u y) x k) ⊤
      (haar d) := by
  obtain ⟨C, hC0, hC⟩ := bForce_bound hyp hμ
  have hi : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * u y) (haar d) :=
    integrable_elDens_mul hyp hμ (integrable_of_continuous u.continuous)
  exact memLp_top_of_bound (measurable_bForceL' hyp hi k).aestronglyMeasurable (C * ‖u‖)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC u x k)

/-- `u ↦ ∂ₖ (W * (p u))` into `L^∞`. -/
def forceL (k : Fin d) : CT d →L[ℝ] Linf d :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_force hyp hμ u k).toLp _
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        have hu : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * u y) (haar d) :=
          integrable_elDens_mul hyp hμ (integrable_of_continuous u.continuous)
        have hv : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * v y) (haar d) :=
          integrable_elDens_mul hyp hμ (integrable_of_continuous v.continuous)
        have := bForceL_add hyp hu hv 1 1 x k
        simp only [one_mul] at this
        simp only [Pi.add_apply, ContinuousMap.add_apply, mul_add]
        exact this
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        have hu : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * u y) (haar d) :=
          integrable_elDens_mul hyp hμ (integrable_of_continuous u.continuous)
        have := bForceL_add hyp hu hu c 0 x k
        simp only [zero_mul, add_zero] at this
        simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
        rw [← this]
        congr 1; funext y; ring }
    (bForce_bound hyp hμ).choose fun u => by
      obtain ⟨hC0, hC⟩ := (bForce_bound hyp hμ).choose_spec
      show ‖((memLp_force hyp hμ u k).toLp _ : Linf d)‖ ≤ _
      refine (Lp.norm_le_of_ae_bound (C := (bForce_bound hyp hμ).choose * ‖u‖) (by positivity)
        ?_).trans (by simp)
      filter_upwards [MemLp.coeFn_toLp (memLp_force hyp hμ u k)] with x hx
      rw [hx, Real.norm_eq_abs]
      exact hC u x k

theorem forceL_ae (k : Fin d) (u : CT d) :
    (forceL hyp hμ k u : Torus d → ℝ) =ᵐ[haar d]
      fun x => bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * u y) x k := by
  show ((memLp_force hyp hμ u k).toLp _ : Torus d → ℝ) =ᵐ[haar d] _
  exact MemLp.coeFn_toLp _

end force

end SharpLSI
