import DGPS.Examples.PolynomialSpeciesScaledQuartic
import DGPS.Examples.PolynomialSpeciesScaledCoefficient
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Banach

/-! The finite three-equation Jacobian at the actual quartic minima.
The equations are the two amplitude derivatives and the physical quartic
value. This is coefficient calculus only, not an actual-factor identification
or optimizer/implicit-branch assertion. -/

noncomputable section
open scoped Topology
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- Unknown order: amplitude pair, then normalized rate shift. -/
abbrev PolynomialFactorUnknowns := (ℝ × ℝ) × ℝ

private def qA (z : PolynomialFactorUnknowns) : ℝ :=
  z.1.1 / 6 + (3 * z.1.1 ^ 2 + z.1.2 ^ 2) / 12 + z.1.1 ^ 3 / 6 - z.2 * z.1.1
private def qB (z : PolynomialFactorUnknowns) : ℝ :=
  z.1.2 / 6 + z.1.1 * z.1.2 / 6 + z.1.2 ^ 3 / 6 - z.2 * z.1.2

/-- Literal polynomial form of (amplitude gradient, value), with physical a0. -/
def polynomialQuarticCriticalSystem (z : PolynomialFactorUnknowns) : PolynomialFactorUnknowns :=
  ((a0 * qA z, a0 * qB z), polynomialScaledQuartic (z.1.1, z.1.2, z.2, 0))

private def LA : PolynomialFactorUnknowns →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
private def LB : PolynomialFactorUnknowns →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
private def LC : PolynomialFactorUnknowns →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
private def valueJac (z : PolynomialFactorUnknowns) : PolynomialFactorUnknowns →L[ℝ] ℝ :=
  a0 • ((qA z) • LA + (qB z) • LB - ((z.1.1 ^ 2 + z.1.2 ^ 2) / 2) • LC)
private def systemJac (z : PolynomialFactorUnknowns) :
    PolynomialFactorUnknowns →L[ℝ] PolynomialFactorUnknowns :=
  ((a0 • ((1 / 6 + z.1.1 / 2 + z.1.1 ^ 2 / 2 - z.2) • LA +
      (z.1.2 / 6) • LB - z.1.1 • LC)).prod
    (a0 • ((z.1.2 / 6) • LA +
      (1 / 6 + z.1.1 / 6 + z.1.2 ^ 2 / 2 - z.2) • LB - z.1.2 • LC))).prod (valueJac z)

private theorem coordinate_derivatives (z : PolynomialFactorUnknowns) :
    HasFDerivAt (fun w : PolynomialFactorUnknowns => w.1.1) LA z ∧
    HasFDerivAt (fun w : PolynomialFactorUnknowns => w.1.2) LB z ∧
    HasFDerivAt (fun w : PolynomialFactorUnknowns => w.2) LC z := by
  exact ⟨hasFDerivAt_fst.comp z hasFDerivAt_fst,
    hasFDerivAt_snd.comp z hasFDerivAt_fst, hasFDerivAt_snd⟩

private theorem value_hasFDerivAt (z : PolynomialFactorUnknowns) :
    HasFDerivAt (fun w : PolynomialFactorUnknowns =>
      polynomialScaledQuartic (w.1.1, w.1.2, w.2, 0)) (valueJac z) z := by
  obtain ⟨ha, hb, hc⟩ := coordinate_derivatives z
  have hr := (ha.pow 2).add (hb.pow 2)
  have hd := ((((hr.const_mul (1 / 12)).add ((ha.mul hr).const_mul (1 / 12))).add
    (((ha.pow 4).add (hb.pow 4)).const_mul (1 / 24))).sub
    ((hc.mul hr).const_mul (1 / 2))).const_mul a0
  have he : (fun w : PolynomialFactorUnknowns =>
      polynomialScaledQuartic (w.1.1, w.1.2, w.2, 0)) =
      fun w => a0 * ((1 / 12) * (w.1.1 ^ 2 + w.1.2 ^ 2) +
        (1 / 12) * (w.1.1 * (w.1.1 ^ 2 + w.1.2 ^ 2)) +
        (1 / 24) * (w.1.1 ^ 4 + w.1.2 ^ 4) -
        (1 / 2) * (w.2 * (w.1.1 ^ 2 + w.1.2 ^ 2))) := by
    funext w
    unfold polynomialScaledQuartic
    ring
  rw [he]
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [valueJac, qA, qB, LA, LB, LC, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  ring <;> simp

/-- The literal polynomial equations are EXACTLY the amplitude Frechet
partials and the physical quartic value, not a substitute critical map. -/
theorem polynomialQuarticCriticalSystem_eq (z : PolynomialFactorUnknowns) :
    polynomialQuarticCriticalSystem z =
      ((fderiv ℝ (fun x : ℝ × ℝ => polynomialScaledQuartic (x.1, x.2, z.2, 0)) z.1 (1, 0),
        fderiv ℝ (fun x : ℝ × ℝ => polynomialScaledQuartic (x.1, x.2, z.2, 0)) z.1 (0, 1)),
        polynomialScaledQuartic (z.1.1, z.1.2, z.2, 0)) := by
  have he := (value_hasFDerivAt z).comp z.1
    ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk (hasFDerivAt_const z.2 z.1))
  dsimp only [Function.comp_def, id_eq] at he
  rw [he.fderiv]
  simp [polynomialQuarticCriticalSystem, valueJac, LA, LB, LC,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem system_hasFDerivAt (z : PolynomialFactorUnknowns) :
    HasFDerivAt polynomialQuarticCriticalSystem (systemJac z) z := by
  obtain ⟨ha, hb, hc⟩ := coordinate_derivatives z
  have hquad := (((ha.pow 2).const_mul 3).add (hb.pow 2)).const_mul (1 / 12)
  have h1 := ((((ha.const_mul (1 / 6)).add hquad).add
    ((ha.pow 3).const_mul (1 / 6))).sub (hc.mul ha)).const_mul a0
  have h2 := ((((hb.const_mul (1 / 6)).add ((ha.mul hb).const_mul (1 / 6))).add
    ((hb.pow 3).const_mul (1 / 6))).sub (hc.mul hb)).const_mul a0
  have hd := (h1.prodMk h2).prodMk (value_hasFDerivAt z)
  have heF : polynomialQuarticCriticalSystem = fun w : PolynomialFactorUnknowns =>
      ((a0 * ((1/6)*w.1.1 + (1/12)*(3*w.1.1^2+w.1.2^2) + (1/6)*w.1.1^3 - w.2*w.1.1),
        a0 * ((1/6)*w.1.2 + (1/6)*(w.1.1*w.1.2) + (1/6)*w.1.2^3 - w.2*w.1.2)),
        polynomialScaledQuartic (w.1.1,w.1.2,w.2,0)) := by
    funext w
    apply Prod.ext
    · apply Prod.ext <;> simp only [polynomialQuarticCriticalSystem, qA, qB] <;> ring
    · rfl
  rw [heF]
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · apply Prod.ext <;> simp only [systemJac, LA, LB, LC, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul] <;> norm_num <;> ring <;> simp
  · rfl

/-- Both coefficient minima give a zero of the genuine three-equation system
and an invertible three-dimensional Frechet Jacobian. No desired
nondegeneracy, actual-model or branch premise is assumed. -/
theorem polynomialQuarticCriticalSystem_minimum_nondegenerate (a b : ℝ)
    (ha : a = -(1 + Real.sqrt 2) / 2) (hb : b ^ 2 = (1 + Real.sqrt 2) / 4) :
    let z : PolynomialFactorUnknowns := ((a, b), (3 - Real.sqrt 2) / 24)
    polynomialQuarticCriticalSystem z = 0 ∧ IsUnit (fderiv ℝ polynomialQuarticCriticalSystem z) := by
  let k : ℝ := (1 + Real.sqrt 2) / 2
  let α : ℝ := (3 - Real.sqrt 2) / 24
  let z : PolynomialFactorUnknowns := ((a, b), α)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk2 : k ^ 2 = k + 1 / 4 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [k]
    nlinarith
  have hk3 : k ^ 3 = 5 * k / 4 + 1 / 4 := by
    nlinarith [congrArg (fun t : ℝ => t * k) hk2]
  have ha' : a = -k := by simpa only [k, neg_div] using ha
  have hb' : b ^ 2 = k / 2 := by simpa only [k, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hb
  have hα : α = (2 - k) / 12 := by dsimp [α, k]; ring
  have hR : 0 < a ^ 2 + b ^ 2 := by rw [ha', neg_sq]; positivity
  have hqA : qA z = 0 := by
    dsimp only [qA, z]
    rw [ha', neg_sq, neg_pow, hb', hα]
    nlinarith only [hk2, hk3]
  have hqB : qB z = 0 := by
    have he : qB z = b * (1 / 6 + a / 6 + b ^ 2 / 6 - α) := by dsimp [qB, z]; ring
    rw [he, ha', hb', hα]
    ring
  have hfactor : polynomialScaledQuartic (a, b, α, 0) = 0 := by
    have hmin := (polynomialScaledCoefficient_minimum_iff a b hR).2 ⟨ha, hb⟩
    have hid : polynomialScaledQuartic (a, b, α, 0) =
        a0 * ((a ^ 2 + b ^ 2) / 2) * (polynomialScaledQuotientCoefficient a b - α) := by
      unfold polynomialScaledQuartic polynomialScaledQuotientCoefficient
      field_simp [hR.ne']
      <;> ring
    rw [hid, hmin]
    change a0 * ((a ^ 2 + b ^ 2) / 2) * (α - α) = 0
    ring
  have hz : polynomialQuarticCriticalSystem z = 0 := by
    simp only [polynomialQuarticCriticalSystem, hqA, hqB, mul_zero]
    exact Prod.ext (Prod.ext rfl rfl) hfactor
  let U : ℝ := k / 12 + 1 / 8
  let V : ℝ := b / 6
  let W : ℝ := k / 6
  have hdet : U * W - V ^ 2 = (6 * k + 1) / 288 := by
    dsimp [U, V, W]
    rw [div_pow, hb']
    nlinarith only [hk2]
  have hdetpos : 0 < U * W - V ^ 2 := by rw [hdet]; positivity
  have h11 : 1 / 6 + a / 2 + a ^ 2 / 2 - α = U := by
    rw [ha', neg_sq, hα, hk2]
    dsimp [U]
    ring
  have h22 : 1 / 6 + a / 6 + b ^ 2 / 2 - α = W := by
    rw [ha', hb', hα]
    dsimp [W]
    ring
  let L := fderiv ℝ polynomialQuarticCriticalSystem z
  have hL (v : PolynomialFactorUnknowns) :
      L v = ((a0 * (U * v.1.1 + V * v.1.2 - a * v.2),
        a0 * (V * v.1.1 + W * v.1.2 - b * v.2)),
        -a0 * ((a ^ 2 + b ^ 2) / 2) * v.2) := by
    dsimp only [L]
    rw [(system_hasFDerivAt z).fderiv]
    simp only [systemJac, valueJac, LA, LB, LC, z, h11, h22, hqA, hqB, V,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ext <;> ring <;> rfl
  have hinj : Function.Injective L := by
    intro v w hvw
    have hz0 : L (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    rw [hL] at hz0
    have h3 := congrArg Prod.snd hz0
    have h1 := congrArg (fun t : PolynomialFactorUnknowns => t.1.1) hz0
    have h2 := congrArg (fun t : PolynomialFactorUnknowns => t.1.2) hz0
    simp only [Prod.fst, Prod.snd, Prod.fst_zero, Prod.snd_zero] at h1 h2 h3
    have ht : (v - w).2 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (neg_ne_zero.mpr a0_pos.ne') (div_ne_zero hR.ne' (by norm_num)))
    rw [ht, mul_zero, sub_zero] at h1 h2
    have hx := (mul_eq_zero.mp h1).resolve_left a0_pos.ne'
    have hy := (mul_eq_zero.mp h2).resolve_left a0_pos.ne'
    have hx' : (U * W - V ^ 2) * (v - w).1.1 = 0 := by linear_combination W * hx - V * hy
    have hy' : (U * W - V ^ 2) * (v - w).1.2 = 0 := by linear_combination U * hy - V * hx
    have ha0 := (mul_eq_zero.mp hx').resolve_left hdetpos.ne'
    have hb0 := (mul_eq_zero.mp hy').resolve_left hdetpos.ne'
    exact sub_eq_zero.mp (Prod.ext (Prod.ext ha0 hb0) ht)
  refine ⟨hz, ContinuousLinearMap.isUnit_iff_bijective.mpr ?_⟩
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The two literal coefficient minima, in the SAME unknown order used by the
three-equation system. The sign index is zero for the positive sine amplitude. -/
def polynomialQuarticCriticalBase (j : Fin 2) : PolynomialFactorUnknowns :=
  ((-(1 + Real.sqrt 2) / 2,
    if j = 0 then Real.sqrt ((1 + Real.sqrt 2) / 4) else -Real.sqrt ((1 + Real.sqrt 2) / 4)),
    (3 - Real.sqrt 2) / 24)

/-- Both named base points are genuine nondegenerate zeros of the physical
three-equation quartic system. -/
theorem polynomialQuarticCriticalBase_nondegenerate (j : Fin 2) :
    polynomialQuarticCriticalSystem (polynomialQuarticCriticalBase j) = 0 ∧
      IsUnit (fderiv ℝ polynomialQuarticCriticalSystem (polynomialQuarticCriticalBase j)) := by
  have hnonneg : 0 ≤ (1 + Real.sqrt 2) / 4 := by positivity
  have hs := Real.sq_sqrt hnonneg
  apply polynomialQuarticCriticalSystem_minimum_nondegenerate
  · rfl
  · change (if j = 0 then Real.sqrt ((1 + Real.sqrt 2) / 4) else -Real.sqrt ((1 + Real.sqrt 2) / 4)) ^ 2 = _
    split_ifs <;> simpa only [neg_sq] using hs

end DGPS.Examples.PolynomialSpecies
