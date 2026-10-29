import FullLabeledLSI.Infra.HypercontrTorus1
import SharpSymmetricLSI.Paper.Gibbs
import SharpSymmetricLSI.Paper.R37Particle

/-!
# Slices of `C¹` functions on `(𝕋^d)^N` and the flat classical gradient

For `F : Config N d → ℝ` with `F ∘ unflat` of class `C¹` on the flat torus `𝕋^{N×d}` we show that every
slice `y ↦ F (update x i y)` is a `C¹` function on `𝕋^d`, with `∂_k` of the slice at `x i` equal to the
`(i,k)`-partial of `F ∘ unflat` at `flat x`. Consequently the product-level carré du champ
`∑_i Γ(slice_i F, slice_i H)(x_i)` is the flat Euclidean pairing of the gradients, which is measurable and
bounded, and agrees `Q`-a.e. with the weak gradient pairing used in `refEnergy`.
-/

open MeasureTheory SharpLSI

noncomputable section

namespace SharpLSI.FL.Gross

variable {N d : ℕ}

/-- `F` is `C¹` on `(𝕋^d)^N` (through the flat torus). -/
def C1C (F : Config N d → ℝ) : Prop := C1T (F ∘ unflat)

lemma C1C.contDiff {F : Config N d → ℝ} (h : C1C F) : ContDiff ℝ 1 ((F ∘ unflat) ∘ liftT) := h

/-- The slice of `F` through `x` in coordinate `i`. -/
def sliceF (F : Config N d → ℝ) (x : Config N d) (i : Fin N) : Torus d → ℝ :=
  fun y => F (Function.update x i y)

/-- The affine parametrization of the `i`-th coordinate slice in the flat lift. -/
def wLift (x : Config N d) (i : Fin N) (z : Fin d → ℝ) : Fin N × Fin d → ℝ :=
  fun p => if p.1 = i then z p.2 else secT (flat x) p

lemma unflat_liftT_wLift (x : Config N d) (i : Fin N) (z : Fin d → ℝ) :
    unflat (liftT (wLift x i z)) = Function.update x i (liftT z) := by
  funext m k
  by_cases hm : m = i
  · subst hm; simp [unflat, liftT, wLift]
  · have h1 := congrFun (liftT_secT (flat x)) (m, k)
    simp only [liftT] at h1
    simp [unflat, liftT, wLift, hm, Function.update_of_ne hm]
    simpa [flat] using h1

lemma sliceF_comp_liftT (F : Config N d → ℝ) (x : Config N d) (i : Fin N) :
    sliceF F x i ∘ liftT = (F ∘ unflat ∘ liftT) ∘ wLift x i := by
  funext z
  simp [sliceF, Function.comp, unflat_liftT_wLift]

lemma contDiff_wLift (x : Config N d) (i : Fin N) : ContDiff ℝ 1 (wLift x i) := by
  refine contDiff_pi.mpr fun p => ?_
  by_cases h : p.1 = i
  · simp only [wLift, h, if_true]
    exact contDiff_apply ℝ ℝ p.2
  · simp only [wLift, h, if_false]
    exact contDiff_const

lemma C1T_sliceF {F : Config N d → ℝ} (hF : C1C F) (x : Config N d) (i : Fin N) :
    C1T (sliceF F x i) := by
  unfold C1T
  rw [sliceF_comp_liftT]
  exact ContDiff.comp hF.contDiff (contDiff_wLift x i)

lemma fderiv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {x v : E}
    (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ g x v = deriv (fun t : ℝ => g (x + t • v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • v) := by
    simpa using hg.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv.symm

lemma dT_sliceF {F : Config N d → ℝ} (hF : C1C F) (x : Config N d) (i : Fin N) (k : Fin d) :
    dT (sliceF F x i) k (x i) = dT (F ∘ unflat) (i, k) (flat x) := by
  have hS := C1T_sliceF hF x i
  have hDs : DifferentiableAt ℝ (sliceF F x i ∘ liftT) (secT (x i)) :=
    hS.differentiable one_ne_zero _
  have hDF : DifferentiableAt ℝ ((F ∘ unflat) ∘ liftT) (secT (flat x)) :=
    hF.contDiff.differentiable one_ne_zero _
  unfold dT
  rw [fderiv_line hDs, fderiv_line hDF]
  congr 1
  funext t
  rw [sliceF_comp_liftT]
  simp only [Function.comp]
  congr 3
  funext p
  obtain ⟨m, k'⟩ := p
  by_cases hm : m = i
  · subst hm
    simp [wLift, secT, flat, Pi.single_apply, Prod.ext_iff]
  · simp [wLift, hm, Pi.single_apply, Prod.ext_iff]

/-- The flat classical gradient pairing. -/
noncomputable def gradPair (F H : Config N d → ℝ) (x : Config N d) : ℝ :=
  ∑ p : Fin N × Fin d, dT (F ∘ unflat) p (flat x) * dT (H ∘ unflat) p (flat x)

lemma sum_slice_Gamma {F H : Config N d → ℝ} (hF : C1C F) (hH : C1C H) (x : Config N d) :
    ∑ i, GammaT (sliceF F x i) (sliceF H x i) (x i) = gradPair F H x := by
  unfold gradPair GammaT
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [dT_sliceF hF x i k, dT_sliceF hH x i k]

lemma measurable_gradPair {F H : Config N d → ℝ} (hF : C1C F) (hH : C1C H) :
    Measurable (gradPair F H) := by
  unfold gradPair
  exact Finset.measurable_sum _ fun p _ =>
    ((hF.dT_measurable p).comp measurable_flat).mul ((hH.dT_measurable p).comp measurable_flat)

lemma bounded_gradPair {F H : Config N d → ℝ} (hF : C1C F) (hH : C1C H) :
    ∃ K, ∀ x, |gradPair F H x| ≤ K := by
  choose Kf hKf using fun p => hF.dT_bounded p
  choose Kg hKg using fun p => hH.dT_bounded p
  refine ⟨∑ p, Kf p * Kg p, fun x => ?_⟩
  unfold gradPair
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hKf p (flat x)) (hKg p (flat x)) (abs_nonneg _) ((abs_nonneg _).trans (hKf p (flat x)))

lemma measurable_Gamma_slice {F H : Config N d → ℝ} (hF : C1C F) (hH : C1C H) (i : Fin N) :
    Measurable fun x => GammaT (sliceF F x i) (sliceF H x i) (x i) := by
  have : (fun x : Config N d => GammaT (sliceF F x i) (sliceF H x i) (x i)) =
      fun x => ∑ k, dT (F ∘ unflat) (i, k) (flat x) * dT (H ∘ unflat) (i, k) (flat x) := by
    funext x; unfold GammaT
    exact Finset.sum_congr rfl fun k _ => by rw [dT_sliceF hF x i k, dT_sliceF hH x i k]
  rw [this]
  exact Finset.measurable_sum _ fun k _ =>
    ((hF.dT_measurable (i, k)).comp measurable_flat).mul
      ((hH.dT_measurable (i, k)).comp measurable_flat)

lemma bounded_Gamma_slice {F H : Config N d → ℝ} (hF : C1C F) (hH : C1C H) :
    ∃ K, ∀ x i, |GammaT (sliceF F x i) (sliceF H x i) (x i)| ≤ K := by
  choose Kf hKf using fun p => hF.dT_bounded p
  choose Kg hKg using fun p => hH.dT_bounded p
  refine ⟨∑ p, Kf p * Kg p, fun x i => ?_⟩
  have : GammaT (sliceF F x i) (sliceF H x i) (x i) =
      ∑ k, dT (F ∘ unflat) (i, k) (flat x) * dT (H ∘ unflat) (i, k) (flat x) := by
    unfold GammaT
    exact Finset.sum_congr rfl fun k _ => by rw [dT_sliceF hF x i k, dT_sliceF hH x i k]
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ k, |dT (F ∘ unflat) (i, k) (flat x) * dT (H ∘ unflat) (i, k) (flat x)| ≤
      Kf (i, k) * Kg (i, k) := fun k => by
    rw [abs_mul]
    exact mul_le_mul (hKf (i, k) (flat x)) (hKg (i, k) (flat x)) (abs_nonneg _) ((abs_nonneg _).trans (hKf (i, k) (flat x)))
  calc ∑ k, |dT (F ∘ unflat) (i, k) (flat x) * dT (H ∘ unflat) (i, k) (flat x)|
      ≤ ∑ k, Kf (i, k) * Kg (i, k) := Finset.sum_le_sum fun k _ => h1 k
    _ ≤ ∑ p : Fin N × Fin d, Kf p * Kg p := by
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun i => ∑ k, Kf (i, k) * Kg (i, k))
          (fun j _ => Finset.sum_nonneg fun k _ => by
            have a1 := (abs_nonneg _).trans (hKf (j, k) (flat x))
            have a2 := (abs_nonneg _).trans (hKg (j, k) (flat x))
            positivity) (Finset.mem_univ i)

end SharpLSI.FL.Gross

end
