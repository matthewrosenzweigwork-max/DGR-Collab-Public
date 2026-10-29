import SharpSymmetricLSI.Paper.CosineD2
import SharpSymmetricLSI.Paper.CosineDissipation

/-!
# The `d`-dimensional cosine model (3): the convolution and the weak Fourier relations

`(W_κ*ρ)(x) = κ (∑ₖ (Aₖ cos 2πxₖ + Bₖ sin 2πxₖ) - d)` with `Aₖ = ∫ cos 2πyₖ ρ`,
`Bₖ = ∫ sin 2πyₖ ρ` (`convDens_cosWd`), a smooth function whose `k`-th partial derivative is
`2πκ (-Aₖ sin 2πxₖ + Bₖ cos 2πxₖ)` (`fderiv_cosDT`). For a weak pair `(f, g)` on `𝕋^d`:
`∫ cos 2πxₖ gₖ = 2π ∫ sin 2πxₖ f`, `∫ sin 2πxₖ gₖ = -2π ∫ cos 2πxₖ f` (`weak_fourier_relations_d`).
-/

open MeasureTheory Set Filter
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ}

/-- `cos 2πxₖ`. -/
noncomputable def cosDc (k : Fin d) (x : Torus d) : ℝ := gCos (cosDproj k x)

/-- `sin 2πxₖ`. -/
noncomputable def cosDs (k : Fin d) (x : Torus d) : ℝ := sCos (cosDproj k x)

theorem continuous_cosDc (k : Fin d) : Continuous (cosDc k) :=
  continuous_gCos.comp (continuous_cosDproj k)

theorem continuous_cosDs (k : Fin d) : Continuous (cosDs k) :=
  continuous_sCos.comp (continuous_cosDproj k)

theorem abs_cosDc_le (k : Fin d) (x : Torus d) : |cosDc k x| ≤ 1 := abs_gCos_le _

theorem abs_cosDs_le (k : Fin d) (x : Torus d) : |cosDs k x| ≤ 1 := abs_sCos_le _

theorem cosDc_liftT (k : Fin d) (z : Fin d → ℝ) : cosDc k (liftT z) = Real.cos (2 * π * z k) :=
  gCos_coe _ (z k) rfl

theorem cosDs_liftT (k : Fin d) (z : Fin d → ℝ) : cosDs k (liftT z) = Real.sin (2 * π * z k) :=
  expT_im_coe _ (z k) rfl

theorem cosDc_secT (k : Fin d) (x : Torus d) : cosDc k x = Real.cos (2 * π * secT x k) := by
  conv_lhs => rw [← liftT_secT x]
  exact cosDc_liftT k _

theorem cosDs_secT (k : Fin d) (x : Torus d) : cosDs k x = Real.sin (2 * π * secT x k) := by
  conv_lhs => rw [← liftT_secT x]
  exact cosDs_liftT k _

theorem integrable_mul_bdd_d {ρ : Torus d → ℝ} (hi : Integrable ρ (haar d)) {F : Torus d → ℝ}
    (hF : Continuous F) (hFb : ∀ y, |F y| ≤ 1) : Integrable (fun y => F y * ρ y) (haar d) :=
  Integrable.mono' hi.norm (hF.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (hFb y))

/-- `Aₖ = ∫ cos 2πyₖ ρ(y) dm`. -/
noncomputable def cosDA (ρ : Torus d → ℝ) (k : Fin d) : ℝ := ∫ y, cosDc k y * ρ y ∂haar d

/-- `Bₖ = ∫ sin 2πyₖ ρ(y) dm`. -/
noncomputable def cosDB (ρ : Torus d → ℝ) (k : Fin d) : ℝ := ∫ y, cosDs k y * ρ y ∂haar d

theorem cosDQ_densMeasure {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (k : Fin d) : cosDQ k (densMeasure ρ) = cosDA ρ k ^ 2 + cosDB ρ k ^ 2 := by
  unfold cosDQ cosDA cosDB
  rw [integral_densMeasure' hρ0 hρ1, integral_densMeasure' hρ0 hρ1]
  simp only [cosDc, cosDs, mul_comm (ρ _)]

theorem convDens_cosWd (κ : ℝ) {ρ : Torus d → ℝ} (hρ1 : ∫ x, ρ x ∂haar d = 1) (x : Torus d) :
    convDens (cosWd κ) ρ x =
      κ * (∑ k, (cosDc k x * cosDA ρ k + cosDs k x * cosDB ρ k) - d) := by
  have hi := integrable_of_integral_eq_one' hρ1
  have ic := fun k => integrable_mul_bdd_d hi (continuous_cosDc k) (abs_cosDc_le k)
  have is := fun k => integrable_mul_bdd_d hi (continuous_cosDs k) (abs_cosDs_le k)
  unfold convDens
  have e : ∀ y, cosWd κ x y * ρ y = ∑ k, κ * (cosDc k x * (cosDc k y * ρ y) +
      cosDs k x * (cosDs k y * ρ y) - ρ y) := fun y => by
    rw [cosWd_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cosW, gCos_sub]
    simp only [cosDc, cosDs]
    ring
  simp_rw [e]
  rw [integral_finsetSum (f := fun k y => κ * (cosDc k x * (cosDc k y * ρ y) +
    cosDs k x * (cosDs k y * ρ y) - ρ y)) _ fun k _ =>
    ((((ic k).const_mul (cosDc k x)).add ((is k).const_mul (cosDs k x))).sub hi).const_mul κ]
  have e2 : ∀ k, ∫ y, κ * (cosDc k x * (cosDc k y * ρ y) + cosDs k x * (cosDs k y * ρ y) - ρ y)
      ∂haar d = κ * (cosDc k x * cosDA ρ k + cosDs k x * cosDB ρ k - 1) := fun k => by
    rw [integral_const_mul, integral_sub (f := fun y => cosDc k x * (cosDc k y * ρ y) +
        cosDs k x * (cosDs k y * ρ y)) (g := ρ)
        (((ic k).const_mul _).add ((is k).const_mul _)) hi,
      integral_add (f := fun y => cosDc k x * (cosDc k y * ρ y))
        (g := fun y => cosDs k x * (cosDs k y * ρ y)) ((ic k).const_mul _) ((is k).const_mul _),
      integral_const_mul, integral_const_mul, hρ1]
    rfl
  simp_rw [e2]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

/-- `T(z) = ∑ₖ (cos 2πzₖ Aₖ + sin 2πzₖ Bₖ)` on `ℝ^d`. -/
noncomputable def cosDT (A B : Fin d → ℝ) (z : Fin d → ℝ) : ℝ :=
  ∑ k, (Real.cos (2 * π * z k) * A k + Real.sin (2 * π * z k) * B k)

theorem hasDerivAt_trig1 (A B s : ℝ) :
    HasDerivAt (fun s => Real.cos (2 * π * s) * A + Real.sin (2 * π * s) * B)
      (2 * π * (-A * Real.sin (2 * π * s) + B * Real.cos (2 * π * s))) s := by
  have h := ((((hasDerivAt_id s).const_mul (2 * π)).cos.mul_const A).add
    (((hasDerivAt_id s).const_mul (2 * π)).sin.mul_const B))
  convert h using 1
  · funext y; simp only [Pi.add_apply, id]
  · simp only [id, mul_one]; ring

theorem hasFDerivAt_cosDT (A B : Fin d → ℝ) (z : Fin d → ℝ) :
    HasFDerivAt (cosDT A B) (∑ k, (2 * π * (-A k * Real.sin (2 * π * z k) +
      B k * Real.cos (2 * π * z k))) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => ℝ) k) z := by
  unfold cosDT
  refine HasFDerivAt.fun_sum fun k _ => ?_
  have := (hasDerivAt_trig1 (A k) (B k) (z k)).comp_hasFDerivAt z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).hasFDerivAt
  exact this

theorem contDiff_cosDT (A B : Fin d → ℝ) : ContDiff ℝ ⊤ (cosDT A B) := by
  unfold cosDT
  exact ContDiff.sum fun k _ =>
    ((Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ k))).mul contDiff_const).add
      ((Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ k))).mul contDiff_const)

theorem fderiv_cosDT (A B : Fin d → ℝ) (z : Fin d → ℝ) (j : Fin d) :
    fderiv ℝ (cosDT A B) z (Pi.single j 1) =
      2 * π * (-A j * Real.sin (2 * π * z j) + B j * Real.cos (2 * π * z j)) := by
  rw [(hasFDerivAt_cosDT A B z).fderiv, sum_apply]
  simp [Pi.single_apply]

/-- The potential `V + W_κ*ρ` lifted to `ℝ^d`. -/
theorem convDens_cosWd_lift (κ : ℝ) {ρ : Torus d → ℝ} (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    (fun x => (fun _ : Torus d => (0 : ℝ)) x + convDens (cosWd κ) ρ x) ∘ liftT =
      fun z => κ * (cosDT (cosDA ρ) (cosDB ρ) z - d) := by
  funext z
  simp only [Function.comp_apply, zero_add, convDens_cosWd κ hρ1, cosDT, cosDc_liftT,
    cosDs_liftT]

/-! ### The weak Fourier relations in coordinate `k` -/

theorem mFourier_neg_single (k : Fin d) (t : Torus d) :
    UnitAddTorus.mFourier (-(Pi.single k (1 : ℤ))) t = (starRingEnd ℂ) (fourier 1 (t k)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply]
  rw [Finset.prod_eq_single k (fun i _ hi => by simp [hi])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp only [Pi.single_eq_same]
  rw [fourier_neg]

theorem fourierCoeff_single_re_im (k : Fin d) {F : Torus d → ℝ} (hF : Integrable F (haar d)) :
    (UnitAddTorus.mFourierCoeff (fun y => (F y : ℂ)) (Pi.single k 1)).re =
        ∫ y, cosDc k y * F y ∂haar d ∧
    (UnitAddTorus.mFourierCoeff (fun y => (F y : ℂ)) (Pi.single k 1)).im =
      -∫ y, cosDs k y * F y ∂haar d := by
  have hie : Integrable (fun t => (starRingEnd ℂ) (fourier 1 (t k)) • (F t : ℂ)) (haar d) := by
    refine Integrable.mono' hF.norm ((continuous_star.comp ((fourier 1).continuous.comp
      (continuous_apply k))).aestronglyMeasurable.smul hF.ofReal.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    have h1 : ‖fourier 1 (x k)‖ = 1 := by simp [fourier_apply]
    rw [norm_smul, Complex.norm_conj, h1, one_mul, Complex.norm_real]
  rw [mFourierCoeff_eq_integral]
  simp_rw [mFourier_neg_single]
  have hr := integral_re hie
  have hm := integral_im hie
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hr hm
  rw [← hr, ← hm, ← integral_neg]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add, cosDc, cosDs,
    gCos, sCos, expT, cosDproj, neg_mul]
  exact ⟨trivial, trivial⟩

/-- For a weak pair `(f, g)` on `𝕋^d`, in coordinate `k`:
`∫ cos 2πxₖ gₖ = 2π ∫ sin 2πxₖ f` and `∫ sin 2πxₖ gₖ = -2π ∫ cos 2πxₖ f`. -/
theorem weak_fourier_relations_d {f : Torus d → ℝ} {g : Torus d → Fin d → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f (haar d))
    (hg : ∀ j, Integrable (fun y => g y j) (haar d)) (k : Fin d) :
    ∫ y, cosDc k y * g y k ∂haar d = 2 * π * ∫ y, cosDs k y * f y ∂haar d ∧
      ∫ y, cosDs k y * g y k ∂haar d = -(2 * π) * ∫ y, cosDc k y * f y ∂haar d := by
  have key := mFourierCoeff_grad h hf hg (Pi.single k 1) k
  have hG := fourierCoeff_single_re_im k (hg k)
  have hF := fourierCoeff_single_re_im k hf
  have hre := congrArg Complex.re key
  have him := congrArg Complex.im key
  simp only [Pi.single_eq_same, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Int.cast_one, mul_zero,
    zero_mul, sub_zero, add_zero, mul_one, zero_add, Complex.re_ofNat, Complex.im_ofNat] at hre him
  rw [hG.1, hF.2] at hre
  rw [hG.2, hF.1] at him
  constructor <;> nlinarith [hre, him]

end SharpLSI
