import FullLabeledLSI.Infra.GaussianMobility
import SharpSymmetricLSI.Paper.GaussForm3
import SharpSymmetricLSI.Paper.GaussForm17
import Mathlib.Probability.ProductMeasure

/-!
# Gaussian tools for the tilted block (plan, section 2): reshape, quadratic tilt, cfPi

* `reshape`: the measurable equivalence `(Fin N → Fin J → ℝ) ≃ᵐ (Fin (N*J) → ℝ)` carrying the
  iterated product Gaussian to `gpi (N*J)`.
* `gauss_quad_tilt`: the Gaussian integral of `exp(⟨u,y⟩ - ½ yᵀXy)` against `gpi n`.
* `cfPi`, `ext_of_cfPi`, `cfPi_of_mgf`: characteristic functions on `Fin n → ℝ`.
* `map_mulVec_gpi`, `Gc_law`: coisometries preserve the standard Gaussian.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset Complex
open scoped ENNReal RealInnerProductSpace

namespace SharpLSI.FL

open SharpLSI

/-! ### Extension of a finite matrix to `ℕ × ℕ` (to use the SYM Gaussian integral) -/

/-- Extension by zero of an `n × n` matrix to `ℕ × ℕ`. -/
def extMat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℕ → ℝ := fun i j =>
  if h : i < n ∧ j < n then X ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem extMat_coe {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    extMat X i j = X i j := by
  simp [extMat, i.2, j.2]

theorem extMat_symm {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : Xᵀ = X) (i j : ℕ) :
    extMat X i j = extMat X j i := by
  unfold extMat
  by_cases h : i < n ∧ j < n
  · have h' : j < n ∧ i < n := ⟨h.2, h.1⟩
    rw [dif_pos h, dif_pos h']
    have := congrFun (congrFun hX ⟨j, h.2⟩) ⟨i, h.1⟩
    simpa using this
  · have h' : ¬ (j < n ∧ i < n) := fun h2 => h ⟨h2.2, h2.1⟩
    rw [dif_neg h, dif_neg h']

theorem secOp_extMat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    secOp (extMat X) n y = WithLp.toLp 2 (X *ᵥ WithLp.ofLp y) := by
  ext i
  simp only [secOp_apply, mulVec, dotProduct, extMat_coe]

theorem quadFin_extMat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    quadFin (extMat X) n y = WithLp.ofLp y ⬝ᵥ (X *ᵥ WithLp.ofLp y) - Matrix.trace X := by
  rw [quadFin_eq_inner, secOp_extMat]
  simp only [Matrix.trace, Matrix.diag, extMat_coe]
  congr 1
  simp [PiLp.inner_apply, dotProduct, mul_comm]


theorem inner_eq_dot {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [inner_euclid]; rfl

theorem integral_gpi_eq_E {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    ∫ y, f y ∂gpi n = ∫ y, f (WithLp.ofLp y) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [← map_pi_eq_stdGaussian, integral_map (WithLp.measurable_toLp 2 _).aemeasurable]
  exact (hf.comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable

theorem integrable_gpi_iff_E {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    Integrable f (gpi n) ↔
      Integrable (fun y => f (WithLp.ofLp y)) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [← map_pi_eq_stdGaussian, integrable_map_measure]
  · simp [Function.comp_def]
  · exact (hf.comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable
  · exact (WithLp.measurable_toLp 2 _).aemeasurable


theorem sum_secEig_inv {n : ℕ} {X S : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, extMat X i j = extMat X j i)
    (hE : ∀ k, 0 < 1 + (1 : ℝ) * secEig hA n k)
    (hS : S * (1 + X) = 1) (hSt : Sᵀ = S) (u : Fin n → ℝ) :
    ∑ k, (1 + (1 : ℝ) * secEig hA n k)⁻¹ * inner ℝ (secVec hA n k) (WithLp.toLp 2 u) ^ 2 =
      u ⬝ᵥ (S *ᵥ u) := by
  have e1 : ∀ k, (1 + (1 : ℝ) * secEig hA n k) • (S *ᵥ WithLp.ofLp (secVec hA n k)) =
      WithLp.ofLp (secVec hA n k) := by
    intro k
    have h1 : X *ᵥ WithLp.ofLp (secVec hA n k) = secEig hA n k • WithLp.ofLp (secVec hA n k) := by
      have := secOp_secVec hA k
      rw [secOp_extMat] at this
      exact congrArg WithLp.ofLp this
    have h2 : (1 + X) *ᵥ WithLp.ofLp (secVec hA n k) =
        (1 + secEig hA n k) • WithLp.ofLp (secVec hA n k) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, h1, add_smul, one_smul]
    have h3 : S *ᵥ ((1 + X) *ᵥ WithLp.ofLp (secVec hA n k)) = WithLp.ofLp (secVec hA n k) := by
      rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]
    rw [h2, Matrix.mulVec_smul] at h3
    simpa using h3
  have e2 : ∀ k, WithLp.ofLp (secVec hA n k) ⬝ᵥ (S *ᵥ u) =
      (1 + (1 : ℝ) * secEig hA n k)⁻¹ * (u ⬝ᵥ WithLp.ofLp (secVec hA n k)) := by
    intro k
    have hpos : (1 + (1 : ℝ) * secEig hA n k) ≠ 0 := (hE k).ne'
    have := dotProduct_transpose_mulVec S (WithLp.ofLp (secVec hA n k)) u
    rw [hSt] at this
    rw [this]
    have h4 : S *ᵥ WithLp.ofLp (secVec hA n k) = (1 + (1 : ℝ) * secEig hA n k)⁻¹ •
        WithLp.ofLp (secVec hA n k) := by
      have := congrArg (fun w => (1 + (1 : ℝ) * secEig hA n k)⁻¹ • w) (e1 k)
      simp only [smul_smul, one_mul] at this
      rw [inv_mul_cancel₀ (by simpa using hpos), one_smul] at this
      simpa using this
    rw [h4, dotProduct_smul, smul_eq_mul]
  have h := (secVec hA n).sum_inner_mul_inner (WithLp.toLp 2 u) (WithLp.toLp 2 (S *ᵥ u))
  rw [inner_eq_dot] at h
  simp only [WithLp.ofLp_toLp, inner_eq_dot] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [inner_eq_dot, WithLp.ofLp_toLp, e2 k]
  rw [dotProduct_comm (WithLp.ofLp (secVec hA n k)) u]
  ring


/-- **Gaussian integral of an exponential of a quadratic form.** For a symmetric `X` with
`1 + X ≥ c > 0` and `S (1 + X) = 1`: `∫ exp(⟨u,y⟩ - ½ yᵀXy) dγ = (∫ exp(-½ yᵀXy) dγ) exp(½ uᵀSu)`,
the integrals being finite and positive. -/
theorem gauss_quad_tilt {n : ℕ} {X S : Matrix (Fin n) (Fin n) ℝ} (hX : Xᵀ = X) {c : ℝ}
    (hc : 0 < c) (hlow : ∀ y : Fin n → ℝ, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ y + y ⬝ᵥ (X *ᵥ y))
    (hS : S * (1 + X) = 1) (hSt : Sᵀ = S) (u : Fin n → ℝ) :
    0 < ∫ y, Real.exp (-(y ⬝ᵥ (X *ᵥ y)) / 2) ∂gpi n ∧
    Integrable (fun y => Real.exp (u ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2)) (gpi n) ∧
    ∫ y, Real.exp (u ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2) ∂gpi n =
      (∫ y, Real.exp (-(y ⬝ᵥ (X *ᵥ y)) / 2) ∂gpi n) * Real.exp (u ⬝ᵥ (S *ᵥ u) / 2) := by
  have hA := extMat_symm hX
  have hE : ∀ k, 0 < 1 + (1 : ℝ) * secEig hA n k := fun k => by
    have h := secEig_ge hA (c := c) (fun y => by
      rw [secOp_extMat, inner_eq_dot, inner_eq_dot]
      simpa using hlow (WithLp.ofLp y)) k
    linarith
  have hSum := sum_secEig_inv hA hE hS hSt
  have hcont : ∀ u : Fin n → ℝ,
      Continuous fun y : Fin n → ℝ => Real.exp (u ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2) := by
    intro u; simp only [dotProduct, mulVec]; fun_prop
  have hpt : ∀ (u : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)),
      Real.exp (u ⬝ᵥ WithLp.ofLp y - (WithLp.ofLp y ⬝ᵥ (X *ᵥ WithLp.ofLp y)) / 2) =
        Real.exp (-(Matrix.trace X) / 2) *
          Real.exp (inner ℝ (WithLp.toLp 2 u) y - 1 * quadFin (extMat X) n y / 2) := by
    intro u y
    rw [← Real.exp_add, quadFin_extMat, inner_eq_dot]
    simp only [WithLp.ofLp_toLp]
    congr 1; ring
  have hI : ∀ u : Fin n → ℝ,
      Integrable (fun y => Real.exp (u ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2)) (gpi n) ∧
      ∫ y, Real.exp (u ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2) ∂gpi n =
        Real.exp (-(Matrix.trace X) / 2) *
          ∫ y, Real.exp (inner ℝ (WithLp.toLp 2 u) y - 1 * quadFin (extMat X) n y / 2)
            ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    intro u
    refine ⟨?_, ?_⟩
    · rw [integrable_gpi_iff_E _ (hcont u)]
      simp_rw [hpt u]
      exact (integrable_exp_quadFin hA 1 (WithLp.toLp 2 u) hE).const_mul _
    · rw [integral_gpi_eq_E _ (hcont u)]
      simp_rw [hpt u]
      rw [integral_const_mul]
  -- the product formula
  have hZ : ∀ u : Fin n → ℝ,
      ∫ y, Real.exp (inner ℝ (WithLp.toLp 2 u) y - 1 * quadFin (extMat X) n y / 2)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
      (∫ y, Real.exp (inner ℝ (WithLp.toLp 2 (0 : Fin n → ℝ)) y - 1 * quadFin (extMat X) n y / 2)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) * Real.exp (u ⬝ᵥ (S *ᵥ u) / 2) := by
    intro u
    have hform : ∀ u' : EuclideanSpace ℝ (Fin n),
        ∫ y, Real.exp (inner ℝ u' y - 1 * quadFin (extMat X) n y / 2)
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
        (∏ k, (Real.exp (1 * secEig hA n k / 2) * (√(1 + 1 * secEig hA n k))⁻¹)) *
          Real.exp (∑ k, (1 + 1 * secEig hA n k)⁻¹ * inner ℝ (secVec hA n k) u' ^ 2 / 2) := by
      intro u'
      rw [integral_exp_quadFin hA 1 u' hE, Real.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      ring
    have e : ∑ k, (1 + 1 * secEig hA n k)⁻¹ * inner ℝ (secVec hA n k) (WithLp.toLp 2 u) ^ 2 / 2 =
        u ⬝ᵥ (S *ᵥ u) / 2 := by
      rw [← hSum u, Finset.sum_div]
    rw [hform, hform, e]
    simp [mul_assoc]
  -- positivity of the base integral
  have hpos0 : 0 < ∫ y, Real.exp (inner ℝ (WithLp.toLp 2 (0 : Fin n → ℝ)) y -
      1 * quadFin (extMat X) n y / 2) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [integral_exp_quadFin hA 1 _ hE]
    exact prod_exp_quadFin_pos hA 1 _ hE
  have h0 : (fun y : Fin n → ℝ => Real.exp (-(y ⬝ᵥ (X *ᵥ y)) / 2)) =
      fun y => Real.exp ((0 : Fin n → ℝ) ⬝ᵥ y - (y ⬝ᵥ (X *ᵥ y)) / 2) := by
    funext y; simp [neg_div]
  have hI0 := hI 0
  rw [← h0] at hI0
  refine ⟨?_, (hI u).1, ?_⟩
  · rw [hI0.2]; exact mul_pos (Real.exp_pos _) hpos0
  · rw [(hI u).2, hI0.2, hZ u]; ring


/-! ### Characteristic functions on `Fin n → ℝ` -/

/-- The characteristic function of a measure on `Fin n → ℝ`. -/
def cfPi {n : ℕ} (μ : Measure (Fin n → ℝ)) (t : Fin n → ℝ) : ℂ :=
  ∫ y, Complex.exp (((t ⬝ᵥ y : ℝ) : ℂ) * Complex.I) ∂μ

theorem cfPi_eq_charFun {n : ℕ} (μ : Measure (Fin n → ℝ)) (t : Fin n → ℝ) :
    cfPi μ t = charFun (μ.map (WithLp.toLp 2)) (WithLp.toLp 2 t) := by
  rw [charFun_apply, integral_map (WithLp.measurable_toLp 2 _).aemeasurable (by fun_prop)]
  unfold cfPi
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [inner_eq_dot, WithLp.ofLp_toLp]
  rw [dotProduct_comm]

theorem ext_of_cfPi {n : ℕ} {μ ν : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t, cfPi μ t = cfPi ν t) : μ = ν := by
  have hm : μ.map (WithLp.toLp 2) = ν.map (WithLp.toLp 2) := by
    haveI : IsFiniteMeasure (μ.map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))) :=
      Measure.isFiniteMeasure_map _ _
    haveI : IsFiniteMeasure (ν.map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))) :=
      Measure.isFiniteMeasure_map _ _
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have := h (WithLp.ofLp t)
    rw [cfPi_eq_charFun, cfPi_eq_charFun] at this
    simpa using this
  have := congrArg (fun m : Measure (EuclideanSpace ℝ (Fin n)) => m.map (WithLp.ofLp)) hm
  simp only at this
  rw [Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _),
    Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)] at this
  have hid : (WithLp.ofLp ∘ WithLp.toLp 2 : (Fin n → ℝ) → Fin n → ℝ) = id := rfl
  rwa [hid, Measure.map_id, Measure.map_id] at this

theorem cfPi_gpi {n : ℕ} (t : Fin n → ℝ) :
    cfPi (gpi n) t = ((Real.exp (-(t ⬝ᵥ t) / 2) : ℝ) : ℂ) := by
  rw [cfPi_eq_charFun, map_pi_eq_stdGaussian, charFun_stdGaussian]
  have hn : ‖WithLp.toLp 2 t‖ ^ 2 = t ⬝ᵥ t := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rw [← hn]; push_cast; ring

theorem cfPi_map_mulVec {n m : ℕ} (μ : Measure (Fin n → ℝ)) (G : Matrix (Fin m) (Fin n) ℝ)
    (t : Fin m → ℝ) :
    cfPi (μ.map (fun y => G *ᵥ y)) t = cfPi μ (Gᵀ *ᵥ t) := by
  unfold cfPi
  have hm : Measurable fun y : Fin n → ℝ => G *ᵥ y :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [integral_map hm.aemeasurable (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show Complex.exp (((t ⬝ᵥ (G *ᵥ y) : ℝ) : ℂ) * Complex.I) =
    Complex.exp ((((Gᵀ *ᵥ t) ⬝ᵥ y : ℝ) : ℂ) * Complex.I)
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]


theorem map_mulVec_gpi {K M : ℕ} (G : Matrix (Fin K) (Fin M) ℝ) (hG : G * Gᵀ = 1) :
    (gpi M).map (fun y => G *ᵥ y) = gpi K := by
  have hm : Measurable fun y : Fin M → ℝ => G *ᵥ y :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  haveI : IsProbabilityMeasure ((gpi M).map fun y => G *ᵥ y) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine ext_of_cfPi fun t => ?_
  rw [cfPi_map_mulVec, cfPi_gpi, cfPi_gpi]
  congr 3
  have : (Gᵀ *ᵥ t) ⬝ᵥ (Gᵀ *ᵥ t) = t ⬝ᵥ t := by
    rw [dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]
  rw [this]

/-- The law of the collective variable is the standard Gaussian on `Fin J → ℝ`. -/
theorem Gc_law {N J : ℕ} {B : Finset (Fin N)} (hB : B.card < N) :
    (gpi (N * J)).map (Gc J B) = gpi J :=
  map_mulVec_gpi (Gcm J B) (Gcm_mul_transpose hB)

/-! ### The reshape `Fin N → Fin J → ℝ ≃ᵐ Fin (N*J) → ℝ` -/

/-- Flattening `(y_{i,m})` to `Fin (N*J) → ℝ` (index `finProdFinEquiv (i, m)`). -/
def reshape (N J : ℕ) : (Fin N → Fin J → ℝ) ≃ᵐ (Fin (N * J) → ℝ) :=
  (MeasurableEquiv.curry (Fin N) (Fin J) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (finProdFinEquiv : Fin N × Fin J ≃ Fin (N * J)))

theorem reshape_apply (N J : ℕ) (y : Fin N → Fin J → ℝ) (i : Fin N) (m : Fin J) :
    reshape N J y (finProdFinEquiv (i, m)) = y i m := by
  simp [reshape, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]

theorem reshape_symm_apply (N J : ℕ) (y : Fin (N * J) → ℝ) (i : Fin N) (m : Fin J) :
    (reshape N J).symm y i m = y (finProdFinEquiv (i, m)) := by
  conv_rhs => rw [← (reshape N J).apply_symm_apply y]
  rw [reshape_apply]

/-- `reshape` carries the product Gaussian onto `gpi (N*J)`. -/
theorem reshape_measurePreserving (N J : ℕ) :
    MeasurePreserving (reshape N J)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1)
      (gpi (N * J)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin J) ℝ).symm
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1)
      (Measure.pi fun _ : Fin N × Fin J => ProbabilityTheory.gaussianReal 0 1) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry_symm (ι := Fin N) (κ := Fin J) (X := ℝ)
      (fun _ _ => ProbabilityTheory.gaussianReal 0 1)
    simpa [Measure.infinitePi_eq_pi] using this
  exact (measurePreserving_piCongrLeft (fun _ : Fin (N * J) => ProbabilityTheory.gaussianReal 0 1)
    (finProdFinEquiv : Fin N × Fin J ≃ Fin (N * J))).comp h1


/-! ### Gaussian measures from their moment generating function -/

/-- A probability measure on `Fin n → ℝ` all of whose linear functionals `⟨v, ·⟩` have the mgf of
`N(0, vᵀSv)` has characteristic function `exp(-½ tᵀSt)`. -/
theorem cfPi_of_mgf {n : ℕ} (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν]
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hm : ∀ (v : Fin n → ℝ) (s : ℝ),
      mgf (fun y => v ⬝ᵥ y) ν s = Real.exp (s ^ 2 * (v ⬝ᵥ (S *ᵥ v)) / 2)) (t : Fin n → ℝ) :
    cfPi ν t = ((Real.exp (-(t ⬝ᵥ (S *ᵥ t)) / 2) : ℝ) : ℂ) := by
  set w : ℝ := t ⬝ᵥ (S *ᵥ t) with hw
  have hw0 : 0 ≤ w := by
    have := hS.dotProduct_mulVec_nonneg t
    simpa using this
  have hmeas : Measurable fun y : Fin n → ℝ => t ⬝ᵥ y := by
    simp only [dotProduct]; fun_prop
  have hL : AEMeasurable (fun y : Fin n → ℝ => t ⬝ᵥ y) ν := hmeas.aemeasurable
  haveI : IsProbabilityMeasure (ν.map fun y : Fin n → ℝ => t ⬝ᵥ y) :=
    (Measure.isProbabilityMeasure_map_iff hL).mpr inferInstance
  have hm' : mgf id (gaussianReal 0 w.toNNReal) = mgf id (ν.map fun y : Fin n → ℝ => t ⬝ᵥ y) := by
    rw [mgf_id_map hL]
    funext s
    rw [hm t s, show (id : ℝ → ℝ) = fun x => x from rfl, mgf_fun_id_gaussianReal,
      Real.coe_toNNReal _ hw0]
    congr 1; rw [hw]; ring
  have hset : interior (integrableExpSet id (gaussianReal 0 w.toNNReal)) = Set.univ := by
    rw [interior_eq_univ]
    ext s
    simp only [integrableExpSet, Set.mem_ofPred_eq, id, Set.mem_univ, iff_true]
    exact integrable_exp_mul_gaussianReal s
  have hlaw : ν.map (fun y : Fin n → ℝ => t ⬝ᵥ y) = gaussianReal 0 w.toNNReal := by
    refine (Measure.ext_of_complexMGF_id_eq ?_).symm
    funext z
    exact eqOn_complexMGF_of_mgf hm' (by simp)
  have h1 : cfPi ν t = charFun (ν.map fun y : Fin n → ℝ => t ⬝ᵥ y) 1 := by
    rw [charFun_apply, integral_map hL (by fun_prop)]
    unfold cfPi
    simp
  rw [h1, hlaw, charFun_gaussianReal]
  simp [Real.coe_toNNReal _ hw0]
  rw [neg_div]

end SharpLSI.FL
