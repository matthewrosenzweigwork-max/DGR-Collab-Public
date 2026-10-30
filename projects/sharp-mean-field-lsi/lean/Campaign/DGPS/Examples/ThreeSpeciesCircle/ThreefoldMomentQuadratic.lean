import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorAlgebra

/-! Finite C3 moment geometry. The phases are the standard positive rotations
by zero, 2*pi/3 and 4*pi/3. Feature and generator vectors remain arbitrary;
there is no evenness, parallelism or kernel-generator commutation premise. -/

noncomputable section
open MeasureTheory

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The standard positively oriented equilateral phases. -/
def threefoldPhase : Fin 3 → ℂ :=
  ![⟨1, 0⟩, ⟨-1 / 2, Real.sqrt 3 / 2⟩, ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩]

/-- Complex resultant of the three orbit weights. -/
def threefoldResultant (p : Fin 3 → ℝ) : ℂ :=
  ∑ j, (p j : ℂ) * threefoldPhase j

def threefoldMass (p : Fin 3 → ℝ) : ℝ := ∑ j, p j

def threefoldOrbitSum (p : Fin 3 → ℝ) (v : ℂ) : ℂ :=
  ∑ j, (p j : ℂ) * (threefoldPhase j * v)

/-- The usual real Euclidean dot product, written in complex coordinates. -/
def planeDot (v w : ℂ) : ℝ := v.re * w.re + v.im * w.im

theorem threefoldOrbitSum_eq (p : Fin 3 → ℝ) (v : ℂ) :
    threefoldOrbitSum p v = threefoldResultant p * v := by
  unfold threefoldOrbitSum threefoldResultant
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The orbit mixture scales the squared length of every vector by the same factor. -/
theorem threefoldOrbitSum_normSq (p : Fin 3 → ℝ) (v : ℂ) :
    Complex.normSq (threefoldOrbitSum p v) =
      Complex.normSq (threefoldResultant p) * Complex.normSq v := by
  rw [threefoldOrbitSum_eq, Complex.normSq_mul]

theorem threefoldOrbitSum_norm (p : Fin 3 → ℝ) (v : ℂ) :
    ‖threefoldOrbitSum p v‖ ^ 2 = ‖threefoldResultant p‖ ^ 2 * ‖v‖ ^ 2 := by
  simpa only [Complex.normSq_eq_norm_sq] using threefoldOrbitSum_normSq p v

/-- Two arbitrary vectors rotate together; no relation between them is required. -/
theorem threefoldOrbitSum_dot (p : Fin 3 → ℝ) (v w : ℂ) :
    planeDot (threefoldOrbitSum p v) (threefoldOrbitSum p w) =
      Complex.normSq (threefoldResultant p) * planeDot v w := by
  rw [threefoldOrbitSum_eq, threefoldOrbitSum_eq]
  simp only [planeDot, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem threefoldResultant_coordinates (p : Fin 3 → ℝ) :
    (threefoldResultant p).re = p 0 - (p 1 + p 2) / 2 ∧
      (threefoldResultant p).im = Real.sqrt 3 / 2 * (p 1 - p 2) := by
  simp only [threefoldResultant, Fin.sum_univ_three, threefoldPhase,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  constructor <;> ring

theorem threefoldResultant_normSq (p : Fin 3 → ℝ) :
    Complex.normSq (threefoldResultant p) =
      p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 - p 0 * p 1 - p 0 * p 2 - p 1 * p 2 := by
  rw [Complex.normSq_apply, (threefoldResultant_coordinates p).1, (threefoldResultant_coordinates p).2]
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  calc _ = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 - p 0 * p 1 - p 0 * p 2 - p 1 * p 2 +
      ((Real.sqrt 3) ^ 2 - 3) * (p 1 - p 2) ^ 2 / 4 := by ring
    _ = _ := by rw [hs]; ring

/-- Every mixture on at most two vertices stays away from the triangle center. -/
theorem threefoldResultant_binary (p : Fin 3 → ℝ) (hzero : ∃ j, p j = 0) :
    threefoldMass p ^ 2 / 4 ≤ Complex.normSq (threefoldResultant p) := by
  obtain ⟨j, hj⟩ := hzero
  rw [threefoldResultant_normSq]
  unfold threefoldMass
  rw [Fin.sum_univ_three]
  fin_cases j
  · change p 0 = 0 at hj
    rw [hj]
    nlinarith [sq_nonneg (p 1 - p 2)]
  · change p 1 = 0 at hj
    rw [hj]
    nlinarith [sq_nonneg (p 0 - p 2)]
  · change p 2 = 0 at hj
    rw [hj]
    nlinarith [sq_nonneg (p 0 - p 1)]

theorem threefoldResultant_of_support_card_le_two (p : Fin 3 → ℝ)
    (hcard : (Finset.univ.filter fun j => p j ≠ 0).card ≤ 2) :
    threefoldMass p ^ 2 / 4 ≤ Complex.normSq (threefoldResultant p) := by
  apply threefoldResultant_binary
  by_contra hn
  push_neg at hn
  have he : (Finset.univ.filter fun j => p j ≠ 0) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (hn j)
  rw [he] at hcard
  norm_num at hcard

/-- The pure moment polynomial after the factual C3 covariance identities. -/
def threefoldQuadratic (α β : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  β * Complex.normSq (threefoldResultant p) - α * threefoldMass p ^ 2

/-- The actual margins seven and five quarters give a uniform binary lower bound. -/
theorem threefoldQuadratic_binary_lower {α β : ℝ} (hβ : 7 ≤ β) (hα : α ≤ 5 / 4)
    (p : Fin 3 → ℝ) (hzero : ∃ j, p j = 0) :
    threefoldMass p ^ 2 / 2 ≤ threefoldQuadratic α β p := by
  have hz := threefoldResultant_binary p hzero
  have hn : 0 ≤ Complex.normSq (threefoldResultant p) := Complex.normSq_nonneg _
  have hb := mul_le_mul_of_nonneg_right hβ hn
  have ha := mul_le_mul_of_nonneg_right hα (sq_nonneg (threefoldMass p))
  unfold threefoldQuadratic
  nlinarith

theorem threefoldQuadratic_binary_card_lower {α β : ℝ} (hβ : 7 ≤ β) (hα : α ≤ 5 / 4)
    (p : Fin 3 → ℝ) (hcard : (Finset.univ.filter fun j => p j ≠ 0).card ≤ 2) :
    threefoldMass p ^ 2 / 2 ≤ threefoldQuadratic α β p := by
  have hz := threefoldResultant_of_support_card_le_two p hcard
  have hn : 0 ≤ Complex.normSq (threefoldResultant p) := Complex.normSq_nonneg _
  have hb := mul_le_mul_of_nonneg_right hβ hn
  have ha := mul_le_mul_of_nonneg_right hα (sq_nonneg (threefoldMass p))
  unfold threefoldQuadratic
  nlinarith

/-- Equal thirds cancel both arbitrary vector components exactly. -/
theorem threefoldResultant_equal_thirds : threefoldResultant (fun _ => (1 / 3 : ℝ)) = 0 := by
  apply Complex.ext
  · rw [(threefoldResultant_coordinates _).1]
    norm_num
  · rw [(threefoldResultant_coordinates _).2]
    simp

theorem threefoldQuadratic_equal_thirds (α β : ℝ) :
    threefoldQuadratic α β (fun _ => (1 / 3 : ℝ)) = -α := by
  unfold threefoldQuadratic threefoldMass
  rw [threefoldResultant_equal_thirds]
  norm_num [Fin.sum_univ_three]

/-- Physical coefficients associated with arbitrary feature/generator vectors. -/
def threefoldBeta (a : ℝ) (v w : ℂ) : ℝ :=
  (16 * planeDot v w - 8 * a * Complex.normSq v) / a0

def threefoldAlpha (a B D : ℝ) : ℝ := (2 * B * D - a * B ^ 2) / (17 * a0)

/-- Conditional factual-moment adapter only: the six rotation identities must be
supplied by the actual root producer. No root asymptotic or rate is assumed. -/
theorem elementaryC_of_threefold_moments (h a : ℝ) (τ : AbsoluteDensity 1)
    (p : Fin 3 → ℝ) (v w : ℂ) (B D : ℝ)
    (hC : momC h (densityMeasure τ) = (threefoldOrbitSum p v).re)
    (hS : momS h (densityMeasure τ) = (threefoldOrbitSum p v).im)
    (hAC : (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure τ : Measure (Torus 1))) =
      (threefoldOrbitSum p w).re)
    (hAS : (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure τ : Measure (Torus 1))) =
      (threefoldOrbitSum p w).im)
    (hB : momB h (densityMeasure τ) = B * threefoldMass p)
    (hAB : (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure τ : Measure (Torus 1))) =
      D * threefoldMass p) :
    elementaryC h a τ = threefoldQuadratic (threefoldAlpha a B D) (threefoldBeta a v w) p := by
  rw [elementaryC_moments, hC, hS, hAC, hAS, hB, hAB]
  have hnorm : (threefoldOrbitSum p v).re ^ 2 + (threefoldOrbitSum p v).im ^ 2 =
      Complex.normSq (threefoldOrbitSum p v) := by
    rw [Complex.normSq_apply]
    ring
  rw [hnorm]
  change 2 * kAlpha * planeDot (threefoldOrbitSum p v) (threefoldOrbitSum p w) -
    2 * kBeta * (B * threefoldMass p) * (D * threefoldMass p) -
    a * (kAlpha * Complex.normSq (threefoldOrbitSum p v) - kBeta * (B * threefoldMass p) ^ 2) = _
  rw [threefoldOrbitSum_dot, threefoldOrbitSum_normSq]
  unfold threefoldQuadratic threefoldAlpha threefoldBeta kAlpha kBeta
  field_simp [a0_pos.ne']
  <;> ring

end DGPS.Examples.ThreeSpeciesCircle
