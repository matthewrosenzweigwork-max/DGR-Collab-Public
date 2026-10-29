import FullLabeledLSI.Infra.GaussianTiltA

/-!
# The tilted Gaussian block (plan, section 2)

For `A : FiniteRankApprox`, `R`, `J` with `∀ i ∈ A.s R, i < J`, `B ⊆ Fin N` with `|B| < N`:
* `uT A R J B y = u_R(ext (Gc y)) = ½ yᵀ Gcᵀ Tm Gc y` on `Fin (N*J) → ℝ`;
* `tilt_normalization`: `∫ exp(-uT) dγ_{NJ} = κ_R`;
* `Pt`: the tilted probability `κ_R⁻¹ exp(-uT) dγ_{NJ}`, `tilted_law`:
  `Pt = (γ_{NJ}).map (CFC.sqrt (Smat B (CJ C J)) *ᵥ ·)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI
open scoped MatrixOrder

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

section tilt
variable (A : FiniteRankApprox W μ e) (R J : ℕ) {N : ℕ} (B : Finset (Fin N))

/-- `u(y) = u_R(ext (Gc y))`. -/
def uT (y : Fin (N * J) → ℝ) : ℝ := uJ A R J (Gc J B y)

/-- The tilt density `κ_R⁻¹ exp(-u(y))`. -/
def tiltDens (y : Fin (N * J) → ℝ) : ℝ := Real.exp (-uT A R J B y) / kappaR A R

/-- The tilted probability measure `P̃_y` of the Gaussian block. -/
def Pt : Measure (Fin (N * J) → ℝ) :=
  (gpi (N * J)).withDensity fun y => ENNReal.ofReal (tiltDens A R J B y)

variable {A R J B}

theorem continuous_Gc : Continuous (Gc J B : (Fin (N * J) → ℝ) → Fin J → ℝ) :=
  continuous_const.matrix_mulVec continuous_id

theorem continuous_uT : Continuous (uT A R J B) :=
  (continuous_uJ A R J).comp continuous_Gc

theorem uT_eq (hJ : ∀ i ∈ A.s R, i < J) (y : Fin (N * J) → ℝ) :
    uT A R J B y = (y ⬝ᵥ ((Gcm J B)ᵀ * Tm A R J * Gcm J B) *ᵥ y) / 2 := by
  unfold uT
  rw [uJ_eq A hJ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_Gcm_transpose]
  have : (Tm A R J *ᵥ (Gcm J B *ᵥ y)) ⬝ᵥ Gc J B y = Gc J B y ⬝ᵥ (Tm A R J *ᵥ Gc J B y) :=
    dotProduct_comm _ _
  rw [this]; ring


section normalization
variable (hJ : ∀ i ∈ A.s R, i < J) {σ : ℝ} (hσ : 0 < σ) (hpos : PosTm A R J σ)
  (hB : B.card < N)
include hJ hσ hpos hB

theorem integrable_exp_uJ : Integrable (fun g => Real.exp (-uJ A R J g)) (gpi J) := by
  by_contra h
  have := kappa_pos A hJ hσ hpos
  rw [kappa_eq A hJ, integral_undef h] at this
  exact lt_irrefl _ this

theorem integrable_exp_uT : Integrable (fun y => Real.exp (-uT A R J B y)) (gpi (N * J)) := by
  have h := integrable_exp_uJ hJ hσ hpos hB
  rw [← Gc_law (J := J) hB] at h
  exact (integrable_map_measure (continuous_uJ A R J).neg.rexp.aestronglyMeasurable
    continuous_Gc.measurable.aemeasurable).1 h

/-- `∫ exp(-u) dγ_{NJ} = κ_R`. -/
theorem tilt_normalization : ∫ y, Real.exp (-uT A R J B y) ∂gpi (N * J) = kappaR A R := by
  rw [kappa_eq A hJ, ← Gc_law (J := J) hB, integral_map (f := fun g => Real.exp (-uJ A R J g))
    continuous_Gc.measurable.aemeasurable (continuous_uJ A R J).neg.rexp.aestronglyMeasurable]
  rfl

theorem integral_tiltDens : ∫ y, tiltDens A R J B y ∂gpi (N * J) = 1 := by
  unfold tiltDens
  rw [integral_div, tilt_normalization hJ hσ hpos hB]
  exact div_self (kappa_pos A hJ hσ hpos).ne'

theorem integrable_tiltDens : Integrable (tiltDens A R J B) (gpi (N * J)) :=
  (integrable_exp_uT hJ hσ hpos hB).div_const _

theorem tiltDens_nonneg (y : Fin (N * J) → ℝ) : 0 ≤ tiltDens A R J B y :=
  div_nonneg (Real.exp_pos _).le (kappa_pos A hJ hσ hpos).le

theorem isProbabilityMeasure_Pt : IsProbabilityMeasure (Pt A R J B) := by
  constructor
  unfold Pt
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_tiltDens hJ hσ hpos hB)
      (Filter.Eventually.of_forall (tiltDens_nonneg hJ hσ hpos hB)),
    integral_tiltDens hJ hσ hpos hB, ENNReal.ofReal_one]


variable {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (A.a R) C)
include hC

/-- The moment generating function of a linear functional under `P̃_y`. -/
theorem mgf_Pt (v : Fin (N * J) → ℝ) (s : ℝ) :
    mgf (fun y => v ⬝ᵥ y) (Pt A R J B) s =
      Real.exp (s ^ 2 * (v ⬝ᵥ (Smat B (CJ C J) *ᵥ v)) / 2) := by
  have hCt := CJ_transpose A hJ hC
  set X : Matrix (Fin (N * J)) (Fin (N * J)) ℝ := (Gcm J B)ᵀ * Tm A R J * Gcm J B with hXdef
  set S := Smat B (CJ C J) with hSdef
  have hXt : Xᵀ = X := by
    rw [hXdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Tm_transpose, Matrix.mul_assoc]
  have hSX : S * (1 + X) = 1 := Smat_mul_Atot hB (hCJ A hJ hC)
  have hSt : Sᵀ = S := Smat_transpose B hCt
  have hc : 0 < min (σ / 2) 1 := lt_min (by linarith) one_pos
  have hlow : ∀ y : Fin (N * J) → ℝ, min (σ / 2) 1 * (y ⬝ᵥ y) ≤ y ⬝ᵥ y + y ⬝ᵥ (X *ᵥ y) := by
    intro y
    have h := Atot_lower hB (Tm := Tm A R J) (c := min (σ / 2) 1) (min_le_right _ _)
      (fun a => by
        have h1 := hpos a
        have h2 : 0 ≤ a ⬝ᵥ a := dotProduct_self_star_nonneg a
        nlinarith [min_le_left (σ / 2) 1]) y
    have e : y ⬝ᵥ (Atot B (Tm A R J) *ᵥ y) = y ⬝ᵥ y + y ⬝ᵥ (X *ᵥ y) := by
      unfold Atot
      rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    rwa [e] at h
  have hdens : ∀ y, tiltDens A R J B y * Real.exp (s * (v ⬝ᵥ y)) =
      (kappaR A R)⁻¹ * Real.exp ((s • v) ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2) := by
    intro y
    unfold tiltDens
    rw [uT_eq hJ y, smul_dotProduct, smul_eq_mul, div_eq_inv_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hint : Integrable (tiltDens A R J B) (gpi (N * J)) := integrable_tiltDens hJ hσ hpos hB
  unfold mgf
  rw [Pt, integral_withDensity_eq_integral_toReal_smul₀
    (f := fun y => ENNReal.ofReal (tiltDens A R J B y))
    (ENNReal.measurable_ofReal.comp_aemeasurable hint.1.aemeasurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ y, ((ENNReal.ofReal (tiltDens A R J B y)).toReal) • Real.exp (s * (v ⬝ᵥ y)) =
      (kappaR A R)⁻¹ * Real.exp ((s • v) ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2) := by
    intro y
    rw [ENNReal.toReal_ofReal (tiltDens_nonneg hJ hσ hpos hB y), smul_eq_mul, hdens]
  simp_rw [hpt]
  obtain ⟨-, -, hmain⟩ := gauss_quad_tilt hXt (lt_min (by linarith) one_pos) hlow hSX hSt (s • v)
  rw [integral_const_mul, hmain]
  have hnorm : ∫ y, Real.exp (-(y ⬝ᵥ (X *ᵥ y)) / 2) ∂gpi (N * J) = kappaR A R := by
    rw [← tilt_normalization hJ hσ hpos hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [uT_eq hJ y, neg_div]
  rw [hnorm]
  have hq : (s • v) ⬝ᵥ (S *ᵥ (s • v)) = s ^ 2 * (v ⬝ᵥ (S *ᵥ v)) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [hq]
  have hk := (kappa_pos A hJ hσ hpos).ne'
  field_simp

/-- Tilted law, matrix form: `P̃_y = N(0, S)` for any factor `G` with `G Gᵀ = S`. -/
theorem tilted_law_of (G : Matrix (Fin (N * J)) (Fin (N * J)) ℝ)
    (hG : G * Gᵀ = Smat B (CJ C J)) :
    Pt A R J B = (gpi (N * J)).map (fun g => G *ᵥ g) := by
  have hm : Measurable fun y : Fin (N * J) → ℝ => G *ᵥ y :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  haveI : IsProbabilityMeasure (Pt A R J B) := isProbabilityMeasure_Pt hJ hσ hpos hB
  haveI : IsProbabilityMeasure ((gpi (N * J)).map fun y => G *ᵥ y) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hPSD : (Smat B (CJ C J)).PosSemidef :=
    Smat_posSemidef hB (CJ_transpose A hJ hC) (CJ_quad_nonneg A hJ hC hσ hpos)
  refine ext_of_cfPi fun t => ?_
  rw [cfPi_of_mgf (Pt A R J B) hPSD (fun v s => mgf_Pt hJ hσ hpos hB hC v s) t,
    cfPi_map_mulVec, cfPi_gpi]
  have h : (Gᵀ *ᵥ t) ⬝ᵥ (Gᵀ *ᵥ t) = t ⬝ᵥ (Smat B (CJ C J) *ᵥ t) := by
    have h1 := Matrix.vecMul_transpose Gᵀ t
    rw [Matrix.transpose_transpose] at h1
    rw [← hG, ← Matrix.mulVec_mulVec, eq_comm, Matrix.dotProduct_mulVec, h1]
  rw [h]

/-- **Tilted law.** `P̃_y = N(0, S)` as the image of the standard Gaussian under `√S`. -/
theorem tilted_law :
    Pt A R J B = (gpi (N * J)).map (fun g => CFC.sqrt (Smat B (CJ C J)) *ᵥ g) :=
  tilted_law_of hJ hσ hpos hB hC _ (sqrt_mul_transpose
    (Smat_posSemidef hB (CJ_transpose A hJ hC) (CJ_quad_nonneg A hJ hC hσ hpos)))

end normalization

end tilt

end SharpLSI.FL
