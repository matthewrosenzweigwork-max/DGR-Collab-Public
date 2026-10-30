import DGPS.Frontier.STR029.T46

/-! Exact normalized Haar integrals of the two actual ordinary-root exponential jets.
Every coefficient is proved by finite polynomial identities and periodic integrals.
These identities supply coefficients for a separately proved uniform remainder. -/

noncomputable section
open MeasureTheory Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem cos3_poly (t : ℝ) : Real.cos (3 * t) = 4 * Real.cos t ^ 3 - 3 * Real.cos t :=
  b_cs_STR02946 t

private theorem cos6_poly (t : ℝ) : Real.cos (6 * t) =
    32 * Real.cos t ^ 6 - 48 * Real.cos t ^ 4 + 18 * Real.cos t ^ 2 - 1 := by
  rw [show (6 : ℝ) * t = 2 * (3 * t) by ring, Real.cos_two_mul, cos3_poly]
  ring

private theorem p_poly (t : ℝ) : vFun_STR02945 2 0 t = 4 * Real.cos t ^ 3 - Real.cos t := by
  rw [v_cs_STR02946]
  ring

private theorem q_poly (t : ℝ) : qFun_STR02945 (2 / 3) 0 (-1 / 5) 0 t =
    -(13 / 15 : ℝ) + (44 / 15 : ℝ) * Real.cos t ^ 2 - (8 / 5 : ℝ) * Real.cos t ^ 4 := by
  rw [q_cs_STR02946]
  ring

private theorem w10 : normInt_STR02933 (fun t => Real.cos t ^ 10) = (63 / 256 : ℝ) := by
  rw [cosW_STR02946 10 8 rfl, w8_STR02946]
  norm_num

private theorem w12 : normInt_STR02933 (fun t => Real.cos t ^ 12) = (231 / 1024 : ℝ) := by
  rw [cosW_STR02946 12 10 rfl, w10]
  norm_num

private theorem evenMean12 (x0 x2 x4 x6 x8 x10 x12 : ℝ) :
    normInt_STR02933 (fun t => x0 * Real.cos t ^ 0 + x2 * Real.cos t ^ 2 +
      x4 * Real.cos t ^ 4 + x6 * Real.cos t ^ 6 + x8 * Real.cos t ^ 8 +
      x10 * Real.cos t ^ 10 + x12 * Real.cos t ^ 12) =
    x0 + x2 / 2 + x4 * (3 / 8) + x6 * (5 / 16) + x8 * (35 / 128) +
      x10 * (63 / 256) + x12 * (231 / 1024) := by
  simp (disch := fun_prop) only [normInt_add_STR02944, normInt_mul_const_STR02933,
    w0_STR02946, w2_STR02946, w4_STR02946, w6_STR02946, w8_STR02946, w10, w12]
  ring

/-- The actual normalizer coefficients through cubic order. -/
theorem ordinaryRoot_exponentialJet_normalizer :
    let p := vFun_STR02945 2 0
    let q := qFun_STR02945 (2 / 3) 0 (-1 / 5) 0
    normInt_STR02933 p = 0 ∧ normInt_STR02933 q = 0 ∧
      normInt_STR02933 (fun t => q t + p t ^ 2 / 2) = (5 / 4 : ℝ) ∧
      normInt_STR02933 (fun t => p t * q t + p t ^ 3 / 6) = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply normInt_antiperiodic_STR02945 (by unfold vFun_STR02945 pFun_STR02945 bFun_STR02945; fun_prop)
    exact vFun_shift_STR02945 2 0
  · have he : qFun_STR02945 (2 / 3) 0 (-1 / 5) 0 = fun t =>
        (-(13 / 15) : ℝ) * Real.cos t ^ 0 + (44 / 15 : ℝ) * Real.cos t ^ 2 +
        (-(8 / 5) : ℝ) * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
        0 * Real.cos t ^ 10 + 0 * Real.cos t ^ 12 := by
      funext t; rw [q_poly]; ring
    rw [he, evenMean12]
    norm_num
  · have he : (fun t => qFun_STR02945 (2 / 3) 0 (-1 / 5) 0 t + (vFun_STR02945 2 0 t) ^ 2 / 2) =
        fun t => (-(13 / 15) : ℝ) * Real.cos t ^ 0 + (103 / 30 : ℝ) * Real.cos t ^ 2 +
        (-(28 / 5) : ℝ) * Real.cos t ^ 4 + 8 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
        0 * Real.cos t ^ 10 + 0 * Real.cos t ^ 12 := by
      funext t; rw [p_poly, q_poly]; ring
    rw [he, evenMean12]
    norm_num
  · apply normInt_antiperiodic_STR02945
      (by unfold vFun_STR02945 pFun_STR02945 bFun_STR02945 qFun_STR02945; fun_prop)
    intro t
    rw [vFun_shift_STR02945, qFun_shift_STR02945]
    ring

/-- The third-harmonic exponential coefficients, before the actual unknown cubic
logarithmic remainder is integrated. -/
theorem ordinaryRoot_exponentialJet_cos3 :
    let p := vFun_STR02945 2 0
    let q := qFun_STR02945 (2 / 3) 0 (-1 / 5) 0
    normInt_STR02933 (fun t => Real.cos (3 * t) * p t) = (1 / 2 : ℝ) ∧
      normInt_STR02933 (fun t => Real.cos (3 * t) * (q t + p t ^ 2 / 2)) = 0 ∧
      normInt_STR02933 (fun t => Real.cos (3 * t) * (p t * q t + p t ^ 3 / 6)) = (77 / 80 : ℝ) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have he : (fun t => Real.cos (3 * t) * vFun_STR02945 2 0 t) = fun t =>
        0 * Real.cos t ^ 0 + 3 * Real.cos t ^ 2 + (-16) * Real.cos t ^ 4 +
        16 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + 0 * Real.cos t ^ 10 + 0 * Real.cos t ^ 12 := by
      funext t; rw [cos3_poly, p_poly]; ring
    rw [he, evenMean12]
    norm_num
  · apply normInt_antiperiodic_STR02945
      (by unfold vFun_STR02945 pFun_STR02945 bFun_STR02945 qFun_STR02945; fun_prop)
    intro t
    have hc : Real.cos (3 * (t + π)) = -Real.cos (3 * t) := bFun_shift_STR02945 t
    rw [hc, vFun_shift_STR02945, qFun_shift_STR02945]
    ring
  · have he : (fun t => Real.cos (3 * t) *
        (vFun_STR02945 2 0 t * qFun_STR02945 (2 / 3) 0 (-1 / 5) 0 t +
          (vFun_STR02945 2 0 t) ^ 3 / 6)) = fun t =>
        0 * Real.cos t ^ 0 + (-(13 / 5) : ℝ) * Real.cos t ^ 2 +
        (139 / 6 : ℝ) * Real.cos t ^ 4 + (-(1084 / 15) : ℝ) * Real.cos t ^ 6 +
        (1568 / 15 : ℝ) * Real.cos t ^ 8 + (-(448 / 5) : ℝ) * Real.cos t ^ 10 +
        (128 / 3 : ℝ) * Real.cos t ^ 12 := by
      funext t; rw [cos3_poly, p_poly, q_poly]; ring
    rw [he, evenMean12]
    norm_num

/-- The second-order sixth-harmonic coefficient matches the reference coefficient. -/
theorem ordinaryRoot_exponentialJet_cos6 :
    let p := vFun_STR02945 2 0
    let q := qFun_STR02945 (2 / 3) 0 (-1 / 5) 0
    normInt_STR02933 (fun t => Real.cos (6 * t) * p t) = 0 ∧
      normInt_STR02933 (fun t => Real.cos (6 * t) * (q t + p t ^ 2 / 2)) = (1 / 8 : ℝ) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · apply normInt_antiperiodic_STR02945
      (by unfold vFun_STR02945 pFun_STR02945 bFun_STR02945; fun_prop)
    intro t
    simp only [cos6_poly, Real.cos_add_pi, vFun_shift_STR02945]
    ring
  · have he : (fun t => Real.cos (6 * t) *
        (qFun_STR02945 (2 / 3) 0 (-1 / 5) 0 t + (vFun_STR02945 2 0 t) ^ 2 / 2)) = fun t =>
        (13 / 15 : ℝ) * Real.cos t ^ 0 + (-(571 / 30) : ℝ) * Real.cos t ^ 2 +
        109 * Real.cos t ^ 4 + (-(904 / 3) : ℝ) * Real.cos t ^ 6 +
        (1568 / 3 : ℝ) * Real.cos t ^ 8 + (-(2816 / 5) : ℝ) * Real.cos t ^ 10 +
        256 * Real.cos t ^ 12 := by
      funext t; rw [cos6_poly, p_poly, q_poly]; ring
    rw [he, evenMean12]
    norm_num

/-- The two normalized first-feature leading coefficients. -/
theorem ordinaryRoot_exponentialJet_first :
    normInt_STR02933 (fun t => Real.cos t * vFun_STR02945 2 0 t) = 1 ∧
      normInt_STR02933 (fun t => Real.sin t * vFun_STR02945 2 0 t) = 0 := by
  constructor
  · have he : (fun t => Real.cos t * vFun_STR02945 2 0 t) = fun t =>
        0 * Real.cos t ^ 0 + (-1) * Real.cos t ^ 2 + 4 * Real.cos t ^ 4 +
        0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + 0 * Real.cos t ^ 10 + 0 * Real.cos t ^ 12 := by
      funext t; rw [p_poly]; ring
    rw [he, evenMean12]
    norm_num
  · have he : (fun t => Real.sin t * vFun_STR02945 2 0 t) =
        fun t => 4 * (Real.cos t ^ 3 * Real.sin t) + (-1 : ℝ) * (Real.cos t ^ 1 * Real.sin t) := by
      funext t; rw [p_poly]; ring
    rw [he, normInt_add_STR02944
      (f := fun t => 4 * (Real.cos t ^ 3 * Real.sin t))
      (g := fun t => (-1 : ℝ) * (Real.cos t ^ 1 * Real.sin t)) (by fun_prop) (by fun_prop),
      normInt_mul_const_STR02933, normInt_mul_const_STR02933, sinW_STR02946, sinW_STR02946]
    ring

end DGPS.Examples.ThreeSpeciesCircle
