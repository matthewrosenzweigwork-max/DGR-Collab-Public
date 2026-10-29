import SharpSymmetricLSI.Paper.CosineFiber

/-!
# The integrated Bochner formula (3.38) on `𝕋^ι` (Phase 3, lane C)

For smooth periodic `g`, `h` on the lift, with `L g = ∑ₚ (∂ₚ²g - ∂ₚh ∂ₚg)` and weight `e^{-h}`:
`∫ e^{-h} (Lg)² = ∫ e^{-h} (∑_{p,r} (∂_r∂_p g)² + ∑_{p,r} ∂_r∂_p h ∂_p g ∂_r g)` (`bochner`).
-/

open MeasureTheory Set Filter
open scoped Real ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Smooth periodic functions -/

/-- Smooth and periodic. -/
def SmPer (Φ : (ι → ℝ) → ℝ) : Prop := ContDiff ℝ ∞ Φ ∧ IsPer Φ

theorem SmPer.add {Φ Ψ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) (h2 : SmPer Ψ) :
    SmPer (fun x => Φ x + Ψ x) :=
  ⟨h1.1.add h2.1, fun m x => by simp only [h1.2 m x, h2.2 m x]⟩

theorem SmPer.sub {Φ Ψ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) (h2 : SmPer Ψ) :
    SmPer (fun x => Φ x - Ψ x) :=
  ⟨h1.1.sub h2.1, fun m x => by simp only [h1.2 m x, h2.2 m x]⟩

theorem SmPer.mul {Φ Ψ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) (h2 : SmPer Ψ) :
    SmPer (fun x => Φ x * Ψ x) :=
  ⟨h1.1.mul h2.1, fun m x => by simp only [h1.2 m x, h2.2 m x]⟩

theorem SmPer.const_mul {Φ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) (c : ℝ) : SmPer (fun x => c * Φ x) :=
  ⟨contDiff_const.mul h1.1, fun m x => by simp only [h1.2 m x]⟩

theorem SmPer.sum {α : Type*} (s : Finset α) {Φ : α → (ι → ℝ) → ℝ} (h : ∀ a, SmPer (Φ a)) :
    SmPer (fun x => ∑ a ∈ s, Φ a x) :=
  ⟨ContDiff.sum fun a _ => (h a).1, fun m x => by simp only [fun a => (h a).2 m x]⟩

theorem SmPer.expNeg {Φ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) : SmPer (fun x => Real.exp (-Φ x)) :=
  ⟨Real.contDiff_exp.comp h1.1.neg, fun m x => by simp only [h1.2 m x]⟩

theorem SmPer.Dk {Φ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) (k : ι) : SmPer (Dk Φ k) :=
  ⟨contDiff_Dk h1.1 k, h1.2.Dk k⟩

theorem SmPer.integrable {Φ : (ι → ℝ) → ℝ} (h1 : SmPer Φ) :
    Integrable (fun y => Φ (secT y)) volume :=
  integrable_secT h1.1.continuous h1.2

/-! ### Derivatives -/

theorem Dk_Dk_eq {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ι) (x : ι → ℝ) :
    Dk (Dk F a) b x = fderiv ℝ (fderiv ℝ F) x (Pi.single b 1) (Pi.single a 1) := by
  have h1 : Dk F a = (ContinuousLinearMap.apply ℝ ℝ (Pi.single a (1 : ℝ))) ∘ fderiv ℝ F := by
    funext z; rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) x
  show fderiv ℝ (Dk F a) x (Pi.single b 1) = _
  rw [h1, fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ _).differentiableAt hd,
    ContinuousLinearMap.fderiv]
  rfl

/-- Symmetry of mixed partials. -/
theorem Dk_comm {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ι) (x : ι → ℝ) :
    Dk (Dk F a) b x = Dk (Dk F b) a x := by
  rw [Dk_Dk_eq hF, Dk_Dk_eq hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem Dk_comm_fun {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ι) :
    Dk (Dk F a) b = Dk (Dk F b) a := funext (Dk_comm hF a b)

theorem Dk_sum {α : Type*} (s : Finset α) {Φ : α → (ι → ℝ) → ℝ}
    (h : ∀ a, Differentiable ℝ (Φ a)) (k : ι) (x : ι → ℝ) :
    Dk (fun x => ∑ a ∈ s, Φ a x) k x = ∑ a ∈ s, Dk (Φ a) k x := by
  simp only [SharpLSI.Dk]
  rw [fderiv_fun_sum fun a _ => h a x, ContinuousLinearMap.sum_apply]

theorem Dk_sub {Φ Ψ : (ι → ℝ) → ℝ} (h1 : Differentiable ℝ Φ) (h2 : Differentiable ℝ Ψ)
    (k : ι) (x : ι → ℝ) : Dk (fun x => Φ x - Ψ x) k x = Dk Φ k x - Dk Ψ k x := by
  simp only [SharpLSI.Dk]
  rw [fderiv_fun_sub (h1 x) (h2 x), ContinuousLinearMap.sub_apply]

theorem Dk_mul {Φ Ψ : (ι → ℝ) → ℝ} (h1 : Differentiable ℝ Φ) (h2 : Differentiable ℝ Ψ)
    (k : ι) (x : ι → ℝ) : Dk (fun x => Φ x * Ψ x) k x = Dk Φ k x * Ψ x + Φ x * Dk Ψ k x := by
  simp only [SharpLSI.Dk]
  rw [fderiv_fun_mul (h1 x) (h2 x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### The operator `L` and integration by parts -/

/-- `L g = ∑ₚ (∂ₚ²g - ∂ₚh ∂ₚg)`. -/
noncomputable def Lop (g h : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ p, (Dk (Dk g p) p x - Dk h p x * Dk g p x)

theorem SmPer.Lop {g h : (ι → ℝ) → ℝ} (hg : SmPer g) (hh : SmPer h) : SmPer (Lop g h) :=
  SmPer.sum _ fun p => ((hg.Dk p).Dk p).sub ((hh.Dk p).mul (hg.Dk p))

/-- `∫ e^{-h} (Lg) w = -∫ e^{-h} ∇g·∇w`. -/
theorem ibp_sum {g w h : (ι → ℝ) → ℝ} (hg : SmPer g) (hw : SmPer w) (hh : SmPer h) :
    ∫ y, Real.exp (-h (secT y)) * (Lop g h (secT y) * w (secT y)) =
      -∫ y, Real.exp (-h (secT y)) * ∑ p, Dk g p (secT y) * Dk w p (secT y) := by
  have e1 : ∀ y, Real.exp (-h (secT y)) * (Lop g h (secT y) * w (secT y)) =
      ∑ p, Real.exp (-h (secT y)) * ((Dk (Dk g p) p (secT y) -
        Dk h p (secT y) * Dk g p (secT y)) * w (secT y)) := fun y => by
    simp only [Lop, Finset.sum_mul, Finset.mul_sum]
  have e2 : ∀ y, Real.exp (-h (secT y)) * ∑ p, Dk g p (secT y) * Dk w p (secT y) =
      ∑ p, Real.exp (-h (secT y)) * (Dk g p (secT y) * Dk w p (secT y)) := fun y => by
    rw [Finset.mul_sum]
  simp_rw [e1, e2]
  rw [integral_finset_sum _ fun p _ => (hh.expNeg.mul ((((hg.Dk p).Dk p).sub
      ((hh.Dk p).mul (hg.Dk p))).mul hw)).integrable,
    integral_finset_sum _ fun p _ => (hh.expNeg.mul ((hg.Dk p).mul (hw.Dk p))).integrable,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => ibp_weighted hg.1 hw.1 hh.1 hg.2 hw.2 hh.2 p

/-- `∂ₚ (Lg) = L(∂ₚg) - ∑_r ∂_p∂_r h ∂_r g`. -/
theorem Dk_Lop {g h : (ι → ℝ) → ℝ} (hg : SmPer g) (hh : SmPer h) (p : ι) (x : ι → ℝ) :
    Dk (Lop g h) p x = Lop (Dk g p) h x - ∑ r, Dk (Dk h r) p x * Dk g r x := by
  have dif : ∀ {Φ : (ι → ℝ) → ℝ}, SmPer Φ → Differentiable ℝ Φ := fun hΦ =>
    hΦ.1.differentiable (by simp)
  rw [show Lop g h = fun x => ∑ r, (Dk (Dk g r) r x - Dk h r x * Dk g r x) from rfl,
    Dk_sum _ (fun r => dif (((hg.Dk r).Dk r).sub ((hh.Dk r).mul (hg.Dk r))))]
  simp only [Lop, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Dk_sub (dif ((hg.Dk r).Dk r)) (dif ((hh.Dk r).mul (hg.Dk r))),
    Dk_mul (dif (hh.Dk r)) (dif (hg.Dk r))]
  have c1 : Dk (Dk (Dk g r) r) p x = Dk (Dk (Dk g p) r) r x := by
    rw [Dk_comm (hg.Dk r).1 r p, Dk_comm_fun hg.1 r p]
  have c2 : Dk (Dk g r) p x = Dk (Dk g p) r x := Dk_comm hg.1 r p x
  rw [c1, c2]
  ring

/-- The integrated Bochner formula. -/
theorem bochner {g h : (ι → ℝ) → ℝ} (hg : SmPer g) (hh : SmPer h) :
    ∫ y, Real.exp (-h (secT y)) * Lop g h (secT y) ^ 2 =
      ∫ y, Real.exp (-h (secT y)) * (∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2 +
        ∑ p, ∑ r, Dk (Dk h r) p (secT y) * Dk g r (secT y) * Dk g p (secT y)) := by
  have hL := hg.Lop hh
  have I1 := ibp_sum hg hL hh
  have I2 : ∀ p, ∫ y, Real.exp (-h (secT y)) * (Lop (Dk g p) h (secT y) * Dk g p (secT y)) =
      -∫ y, Real.exp (-h (secT y)) * ∑ r, Dk (Dk g p) r (secT y) * Dk (Dk g p) r (secT y) :=
    fun p => ibp_sum (hg.Dk p) (hg.Dk p) hh
  -- pointwise rewriting of the right side of `I1`
  have hpt : ∀ y, Real.exp (-h (secT y)) * ∑ p, Dk g p (secT y) * Dk (Lop g h) p (secT y) =
      ∑ p, Real.exp (-h (secT y)) * (Lop (Dk g p) h (secT y) * Dk g p (secT y)) -
        Real.exp (-h (secT y)) *
          ∑ p, ∑ r, Dk (Dk h r) p (secT y) * Dk g r (secT y) * Dk g p (secT y) := fun y => by
    simp only [Dk_Lop hg hh, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun p _ => by ring
    · exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => by ring
  have iA : ∀ p, Integrable (fun y => Real.exp (-h (secT y)) *
      (Lop (Dk g p) h (secT y) * Dk g p (secT y))) volume := fun p =>
    (hh.expNeg.mul (((hg.Dk p).Lop hh).mul (hg.Dk p))).integrable
  have iH : Integrable (fun y => Real.exp (-h (secT y)) *
      ∑ p, ∑ r, Dk (Dk h r) p (secT y) * Dk g r (secT y) * Dk g p (secT y)) volume :=
    (hh.expNeg.mul (SmPer.sum _ fun p => SmPer.sum _ fun r =>
      (((hh.Dk r).Dk p).mul (hg.Dk r)).mul (hg.Dk p))).integrable
  have iS : Integrable (fun y => Real.exp (-h (secT y)) *
      ∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2) volume :=
    (hh.expNeg.mul (SmPer.sum Finset.univ fun p => SmPer.sum Finset.univ fun r =>
      ((hg.Dk p).Dk r).mul ((hg.Dk p).Dk r))).integrable.congr
      (Eventually.of_forall fun y => by simp only [sq])
  have hS : ∫ y, Real.exp (-h (secT y)) * ∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2 =
      ∑ p, -∫ y, Real.exp (-h (secT y)) * (Lop (Dk g p) h (secT y) * Dk g p (secT y)) := by
    simp_rw [I2, neg_neg]
    rw [← integral_finset_sum Finset.univ fun p _ => (hh.expNeg.mul (SmPer.sum _ fun r =>
      ((hg.Dk p).Dk r).mul ((hg.Dk p).Dk r))).integrable]
    congr 1; funext y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp only [sq]
  have hLL : ∫ y, Real.exp (-h (secT y)) * Lop g h (secT y) ^ 2 =
      ∫ y, Real.exp (-h (secT y)) * (Lop g h (secT y) * Lop g h (secT y)) := by
    congr 1; funext y; ring
  rw [hLL, I1]
  simp_rw [hpt]
  rw [integral_sub (integrable_finset_sum _ fun p _ => iA p) iH,
    integral_finset_sum _ fun p _ => iA p]
  have hsplit : ∫ y, Real.exp (-h (secT y)) * (∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2 +
      ∑ p, ∑ r, Dk (Dk h r) p (secT y) * Dk g r (secT y) * Dk g p (secT y)) =
      (∫ y, Real.exp (-h (secT y)) * ∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2) +
        ∫ y, Real.exp (-h (secT y)) *
          ∑ p, ∑ r, Dk (Dk h r) p (secT y) * Dk g r (secT y) * Dk g p (secT y) := by
    rw [← integral_add iS iH]; congr 1; funext y; ring
  rw [hsplit, hS, Finset.sum_neg_distrib]
  ring

end SharpLSI
