import SharpSymmetricLSI.Paper.Defective6
import SharpSymmetricLSI.Paper.CondForce4

/-!
# R03 (Proposition 2.2), part 9: conditional ratios

`condRatio F p x = ∫ F(p,x,z) Q(p,x,z) dz / margQ p x` is the conditional expectation of `F` under
`ν = Q · Leb` given `(past, X_j) = (p, x)`:
* `lintegral_condRatio_sq_le`: `∫ condRatio(F)(past, X_j)² dν ≤ ∫ F² dν` (Cauchy–Schwarz in `z`);
* `condRatio_ae_eq_condExp`: for bounded measurable `F`, `condRatio F (past X) (X_j) = ν[F | pastNextSA]`
  `ν`-a.e.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

section asm
variable {j : ℕ} (hj : j < N)

theorem rest_assemble (p : Config j d) (x : Torus d) (z : Config (N - j - 1) d) :
    restC j hj (assemble hj p x z) = z := by
  funext b k
  have h : (blockIdx (d := d) j hj).symm (⟨j + 1 + b, by have := b.2; omega⟩, k) = Sum.inr (b, k) :=
    (blockIdx j hj).symm_apply_eq.mpr rfl
  show join (join (flat p) x) (flat z) ((blockIdx j hj).symm (⟨j + 1 + b, _⟩, k)) = z b k
  rw [h]; rfl

/-- `assemble` as a measurable equivalence. -/
noncomputable def assembleEquiv : ((Config j d × Torus d) × Config (N - j - 1) d) ≃ᵐ Config N d where
  toFun q := assemble hj q.1.1 q.1.2 q.2
  invFun X := ((past j hj.le X, X ⟨j, hj⟩), restC j hj X)
  left_inv q := by
    obtain ⟨⟨p, x⟩, z⟩ := q
    simp only [past_assemble, cur_assemble, rest_assemble]
  right_inv X := assemble_eq hj X
  measurable_toFun := measurable_assemble hj
  measurable_invFun := ((measurable_past hj.le).prodMk (measurable_pi_apply _)).prodMk
    (measurable_restC j hj)

/-- Tonelli in the block coordinates. -/
theorem lintegral_assemble {G : Config N d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X, G X = ∫⁻ p, ∫⁻ x, ∫⁻ z, G (assemble hj p x z) ∂(volume : Measure (Config (N - j - 1) d))
      ∂haar d := by
  rw [← (measurePreserving_assemble hj).lintegral_comp hG,
    lintegral_prod (fun q : (Config j d × Torus d) × Config (N - j - 1) d =>
      G (assemble hj q.1.1 q.1.2 q.2)) (hG.comp (measurable_assemble hj)).aemeasurable,
    lintegral_prod (fun q : Config j d × Torus d => ∫⁻ z, G (assemble hj q.1 q.2 z)
      ∂(volume : Measure (Config (N - j - 1) d)))
      ((hG.comp (measurable_assemble hj)).lintegral_prod_right').aemeasurable]

end asm

section ratio
variable {j : ℕ} (hj : j < N)

/-- `E_ν[F | past = p, X_j = x]` for `ν = Q · Leb`. -/
noncomputable def condRatio (Q F : Config N d → ℝ) (p : Config j d) (x : Torus d) : ℝ :=
  (∫ z, F (assemble hj p x z) * Q (assemble hj p x z) ∂(volume : Measure (Config (N - j - 1) d))) /
    margQ hj Q p x

variable {Q : Config N d → ℝ} (hQm : Measurable Q) {c C : ℝ} (hc : 0 < c) (hQc : ∀ X, c ≤ Q X)
  (hQC : ∀ X, Q X ≤ C)

include hQm in
theorem measurable_condRatio {F : Config N d → ℝ} (hFm : Measurable F) :
    Measurable (Function.uncurry (condRatio hj Q F)) :=
  (((hFm.mul hQm).comp (measurable_assemble hj)).stronglyMeasurable.integral_prod_right'.measurable).div
    (measurable_margQ hj hQm)

include hQm hc hQc hQC in
/-- Pointwise Cauchy–Schwarz: `r² · m ≤ ∫ F² Q dz`. -/
theorem condRatio_sq_mul_le {F : Config N d → ℝ} (hFm : Measurable F) (p : Config j d) (x : Torus d) :
    ENNReal.ofReal (condRatio hj Q F p x ^ 2) * ENNReal.ofReal (margQ hj Q p x) ≤
      ∫⁻ z, ENNReal.ofReal (F (assemble hj p x z) ^ 2 * Q (assemble hj p x z))
        ∂(volume : Measure (Config (N - j - 1) d)) := by
  set μz := (volume : Measure (Config (N - j - 1) d))
  have hzm : Measurable fun z : Config (N - j - 1) d => assemble hj p x z :=
    (measurable_assemble hj).comp ((measurable_const (a := (p, x))).prodMk measurable_id)
  set A := ∫⁻ z, ENNReal.ofReal (F (assemble hj p x z) ^ 2 * Q (assemble hj p x z)) ∂μz
  by_cases hA : A = ⊤
  · rw [hA]; exact le_top
  have hQ0 : ∀ X, 0 ≤ Q X := fun X => hc.le.trans (hQc X)
  have hF2m : Measurable fun z => F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) :=
    ((hFm.comp hzm).pow_const 2).mul (hQm.comp hzm)
  have hF2i : Integrable (fun z => F (assemble hj p x z) ^ 2 * Q (assemble hj p x z)) μz := by
    refine (lintegral_ofReal_ne_top_iff_integrable hF2m.aestronglyMeasurable
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hQ0 _))).mp hA
  have hQi : Integrable (fun z => Q (assemble hj p x z)) μz :=
    Integrable.of_bound (hQm.comp hzm).aestronglyMeasurable C (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 _)]; exact hQC _)
  have hFQi : Integrable (fun z => F (assemble hj p x z) * Q (assemble hj p x z)) μz := by
    refine (hF2i.add hQi).mono' ((hFm.comp hzm).mul (hQm.comp hzm)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQ0 _)]
    have h1 := hQ0 (assemble hj p x z)
    have hF : |F (assemble hj p x z)| ≤ F (assemble hj p x z) ^ 2 + 1 := by
      nlinarith [sq_abs (F (assemble hj p x z)), sq_nonneg (|F (assemble hj p x z)| - 1),
        abs_nonneg (F (assemble hj p x z))]
    calc |F (assemble hj p x z)| * Q (assemble hj p x z)
        ≤ (F (assemble hj p x z) ^ 2 + 1) * Q (assemble hj p x z) :=
          mul_le_mul_of_nonneg_right hF h1
      _ = F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) + Q (assemble hj p x z) := by ring
  set m := margQ hj Q p x
  have hm : 0 < m := hc.trans_le (margQ_bounds hj hQm hQc hQC p x).1
  set B := ∫ z, F (assemble hj p x z) * Q (assemble hj p x z) ∂μz
  set r := condRatio hj Q F p x
  have hr : r = B / m := rfl
  have hmQ : m = ∫ z, Q (assemble hj p x z) ∂μz := rfl
  -- `0 ≤ ∫ (F - r)² Q`
  have h0 : 0 ≤ ∫ z, (F (assemble hj p x z) - r) ^ 2 * Q (assemble hj p x z) ∂μz :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hQ0 _)
  have hexp : ∫ z, (F (assemble hj p x z) - r) ^ 2 * Q (assemble hj p x z) ∂μz =
      (∫ z, F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) ∂μz) - 2 * r * B + r ^ 2 * m := by
    have e : ∀ z, (F (assemble hj p x z) - r) ^ 2 * Q (assemble hj p x z) =
        F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) -
          2 * r * (F (assemble hj p x z) * Q (assemble hj p x z)) +
          r ^ 2 * Q (assemble hj p x z) := fun z => by ring
    simp_rw [e]
    rw [integral_add (f := fun z => F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) -
        2 * r * (F (assemble hj p x z) * Q (assemble hj p x z)))
        (g := fun z => r ^ 2 * Q (assemble hj p x z)) (hF2i.sub (hFQi.const_mul _)) (hQi.const_mul _),
      integral_sub (f := fun z => F (assemble hj p x z) ^ 2 * Q (assemble hj p x z))
        (g := fun z => 2 * r * (F (assemble hj p x z) * Q (assemble hj p x z))) hF2i
        (hFQi.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  have hBr : B = r * m := by rw [hr]; field_simp
  have hle : r ^ 2 * m ≤ ∫ z, F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) ∂μz := by
    rw [hexp, hBr] at h0; nlinarith
  calc ENNReal.ofReal (r ^ 2) * ENNReal.ofReal m = ENNReal.ofReal (r ^ 2 * m) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (∫ z, F (assemble hj p x z) ^ 2 * Q (assemble hj p x z) ∂μz) :=
        ENNReal.ofReal_le_ofReal hle
    _ = A := ofReal_integral_eq_lintegral_ofReal hF2i
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hQ0 _))

include hQm hc hQc hQC in
/-- **Conditional Jensen for the explicit ratio.** -/
theorem lintegral_condRatio_sq_le {F : Config N d → ℝ} (hFm : Measurable F) :
    ∫⁻ X, ENNReal.ofReal (condRatio hj Q F (past j hj.le X) (X ⟨j, hj⟩) ^ 2) * ENNReal.ofReal (Q X) ≤
      ∫⁻ X, ENNReal.ofReal (F X ^ 2) * ENNReal.ofReal (Q X) := by
  have hR := measurable_condRatio hj hQm hFm
  rw [lintegral_pastCur hj hQm hc hQc hQC (F := fun p x => ENNReal.ofReal (condRatio hj Q F p x ^ 2))
    (ENNReal.measurable_ofReal.comp (hR.pow_const 2)),
    lintegral_assemble hj (G := fun X => ENNReal.ofReal (F X ^ 2) * ENNReal.ofReal (Q X))
      ((ENNReal.measurable_ofReal.comp (hFm.pow_const 2)).mul (ENNReal.measurable_ofReal.comp hQm))]
  refine lintegral_mono fun p => lintegral_mono fun x => ?_
  refine (condRatio_sq_mul_le hj hQm hc hQc hQC hFm p x).trans (le_of_eq ?_)
  refine lintegral_congr fun z => ?_
  rw [ENNReal.ofReal_mul (sq_nonneg _)]

end ratio

end SharpLSI
