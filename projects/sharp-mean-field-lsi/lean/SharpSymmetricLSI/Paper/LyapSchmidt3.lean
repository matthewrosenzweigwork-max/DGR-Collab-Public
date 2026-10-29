import SharpSymmetricLSI.Paper.LyapSchmidt1
import SharpSymmetricLSI.Paper.LyapSchmidt2
import SharpSymmetricLSI.Paper.Coercivity3
import SharpSymmetricLSI.Paper.LocalStructure5

/-!
# Section 4.2 (lane s42; R14): the Lyapunov–Schmidt setting in `C(𝕋^d)`

Fix a minimizer `μ` and an `L²(μ)`-orthonormal basis `φ₁, …, φₙ` of `E = ker(I+T)`.
* `TC : C(𝕋^d) →L C(𝕋^d)` is `T` (manuscript (2.1)) on continuous functions;
* `phiC i = -T φᵢ` is the continuous (Lipschitz) representative of `φᵢ`;
* `lamC u = (μ(u), ⟨u, φᵢ⟩)` and `YC = ker lamC = E^⊥ ∩ {μ(u) = 0}` (closed, complete);
* `QC : C(𝕋^d) →L YC`, `QC u = u - μ(u) - ∑ ⟨u, φᵢ⟩ φᵢ` (the projection `P_{E^⊥} P_{μ,0}`);
* `kC a = ∑ aᵢ phiC i`.
-/

noncomputable section
open MeasureTheory Filter Real Topology

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `C(𝕋^d)`. -/
abbrev CT (d : ℕ) := C(Torus d, ℝ)

section setting
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

theorem integrable_CT (u : CT d) : Integrable (⇑u) μ := integrable_of_continuous u.continuous

theorem memL20_CT {u : CT d} (hu : ∫ x, u x ∂μ = 0) : MemL20 μ (⇑u) := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous u.continuous
  exact ⟨MemLp.of_bound u.continuous.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x), hu⟩

theorem continuous_Top_CT (u : CT d) : Continuous (Top W μ (⇑u)) := by
  have h1 : Continuous fun x => ∫ y, W x y * u y ∂μ :=
    cont_integral_right (cont_kernel_mul hyp.continuous_W u.continuous) μ
  exact h1.sub continuous_const

theorem abs_Top_CT_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : CT d) x, |Top W μ (⇑u) x| ≤ B * ‖u‖ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  refine ⟨2 * BW, by positivity, fun u x => ?_⟩
  have hu : ∀ y, |u y| ≤ ‖u‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm u y
  have hin : ∀ x, |∫ y, W x y * u y ∂μ| ≤ BW * ‖u‖ := fun x =>
    abs_integral_le_of_bdd fun y => by
      rw [abs_mul]; exact mul_le_mul (hBW (x, y)) (hu y) (abs_nonneg _) hBW0
  unfold Top
  refine (abs_sub _ _).trans ?_
  have h2 : |∫ x', (∫ y, W x' y * u y ∂μ) ∂μ| ≤ BW * ‖u‖ := abs_integral_le_of_bdd hin
  linarith [hin x]

/-- `T` on `C(𝕋^d)`. -/
def TC : CT d →L[ℝ] CT d :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨Top W μ (⇑u), continuous_Top_CT hyp μ u⟩
      map_add' := fun u v => by
        ext x
        have := Top_lin hyp μ (integrable_CT hyp μ u) (integrable_CT hyp μ v) 1 1 x
        simp only [one_mul] at this
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.coe_add]
        exact this
      map_smul' := fun c u => by
        ext x
        have := Top_lin hyp μ (integrable_CT hyp μ u) (integrable_CT hyp μ u) c 0 x
        simp only [zero_mul, add_zero] at this
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, ContinuousMap.coe_smul,
          smul_eq_mul, RingHom.id_apply]
        exact this }
    (abs_Top_CT_le hyp μ).choose fun u => by
      obtain ⟨hB0, hB⟩ := (abs_Top_CT_le hyp μ).choose_spec
      refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
      rw [Real.norm_eq_abs]
      exact hB u x

theorem TC_apply (u : CT d) (x : Torus d) : TC hyp μ u x = Top W μ (⇑u) x := rfl

end setting

section basis
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ hφ

omit hμ in
theorem memL20_phi (i : Fin n) : MemL20 (μ : Measure (Torus d)) (φ i) := (hφ.1 i).1

omit hμ in
/-- The continuous representative `-T φᵢ` of `φᵢ`. -/
theorem continuous_neg_Top_phi (i : Fin n) :
    Continuous fun x => -Top W (μ : Measure (Torus d)) (φ i) x := by
  obtain ⟨C, hC⟩ := Top_W1inf hyp (μ : Measure (Torus d))
  exact (hC _ (memL20_phi hyp hφ i)).2.continuous.neg

omit hμ in
/-- The continuous representatives of the basis. -/
def phiC (i : Fin n) : CT d := ⟨fun x => -Top W (μ : Measure (Torus d)) (φ i) x,
  continuous_neg_Top_phi hyp hφ i⟩

omit hμ in
theorem phiC_ae (i : Fin n) : (⇑(phiC hyp hφ i)) =ᵐ[(μ : Measure (Torus d))] φ i := by
  filter_upwards [(hφ.1 i).2] with x hx
  simp only [Pi.zero_apply] at hx
  show -Top W (μ : Measure (Torus d)) (φ i) x = φ i x
  linarith

omit hμ in
theorem integral_mul_phiC (u : Torus d → ℝ) (i : Fin n) :
    ∫ x, u x * phiC hyp hφ i x ∂(μ : Measure (Torus d)) =
      ∫ x, u x * φ i x ∂(μ : Measure (Torus d)) := by
  refine integral_congr_ae ?_
  filter_upwards [phiC_ae hyp hφ i] with x hx
  rw [hx]

omit hμ in
theorem integral_phiC (i : Fin n) : ∫ x, phiC hyp hφ i x ∂(μ : Measure (Torus d)) = 0 := by
  rw [integral_congr_ae (phiC_ae hyp hφ i)]; exact (memL20_phi hyp hφ i).2

omit hμ in
theorem phiC_orthonormal (i j : Fin n) :
    ∫ x, phiC hyp hφ i x * phiC hyp hφ j x ∂(μ : Measure (Torus d)) = if i = j then 1 else 0 := by
  rw [integral_mul_phiC hyp hφ, ← hφ.2.1 i j]
  refine integral_congr_ae ?_
  filter_upwards [phiC_ae hyp hφ i] with x hx
  rw [hx]

omit hμ in
/-- `T phiC = -phiC` everywhere. -/
theorem TC_phiC (i : Fin n) : TC hyp (μ : Measure (Torus d)) (phiC hyp hφ i) = -phiC hyp hφ i := by
  ext x
  rw [TC_apply, Top_congr_ae hyp (μ : Measure (Torus d)) (phiC_ae hyp hφ i) x,
    ContinuousMap.neg_apply]
  show _ = -(-Top W (μ : Measure (Torus d)) (φ i) x)
  ring

end basis

end SharpLSI
