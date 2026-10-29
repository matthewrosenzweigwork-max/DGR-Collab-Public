import DGPS.Analysis.WeightedRateComparison
import DGPS.Lipschitz.WeightedSpectrum
import DGPS.Circle.BesselMoments
import DGPS.Circle.AngularNormalization
import DGPS.Equilibrium.GaussianBasisEquivalence

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace Real

namespace DGPS.Circle.VonMisesParity

open DGPS

instance haar_negInvariant (d : ℕ) : (haar d).IsNegInvariant := Pi.isNegInvariant_volume

section Covariance

variable {d : ℕ}

theorem fderiv_lift_periodic {φ : Torus d → ℝ} (z : Fin d → ℝ) (m : Fin d → ℤ) :
    fderiv ℝ (φ ∘ torusLift) (z + SharpLSI.intVec m) = fderiv ℝ (φ ∘ torusLift) z := by
  have h : (fun w => (φ ∘ torusLift) (w + SharpLSI.intVec m)) = φ ∘ torusLift := by
    funext w; simp [SharpLSI.liftT_add_intVec]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := φ ∘ torusLift) (SharpLSI.intVec m) (x := z)
  rw [h] at this
  exact this.symm

theorem translate_comp_lift (φ : Torus d → ℝ) (y : Torus d) :
    (fun x => φ (x + y)) ∘ torusLift = fun z => (φ ∘ torusLift) (z + SharpLSI.secT y) := by
  funext z
  simp only [Function.comp, SharpLSI.liftT_add, SharpLSI.liftT_secT]

theorem isSmoothPeriodic_translate {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (y : Torus d) :
    IsSmoothPeriodic (fun x => φ (x + y)) := by
  unfold IsSmoothPeriodic
  rw [translate_comp_lift]
  exact hφ.comp (contDiff_id.add contDiff_const)

theorem coordPartial_translate {φ : Torus d → ℝ} (j : Fin d) (y x : Torus d) :
    coordPartial j (fun x => φ (x + y)) x = coordPartial j φ (x + y) := by
  unfold coordPartial
  rw [translate_comp_lift]
  have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := φ ∘ torusLift) (SharpLSI.secT y)
    (x := SharpLSI.secT x)
  rw [h1]
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq (SharpLSI.secT x + SharpLSI.secT y)
  have e : SharpLSI.liftT (SharpLSI.secT x + SharpLSI.secT y) = x + y := by
    rw [SharpLSI.liftT_add, SharpLSI.liftT_secT, SharpLSI.liftT_secT]
  rw [e] at hm
  rw [hm, fderiv_lift_periodic]

theorem neg_comp_lift (φ : Torus d → ℝ) :
    (fun x => φ (-x)) ∘ torusLift = fun z => (φ ∘ torusLift) (-z) := by
  funext z
  rfl

theorem isSmoothPeriodic_neg {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    IsSmoothPeriodic (fun x => φ (-x)) := by
  unfold IsSmoothPeriodic
  rw [neg_comp_lift]
  exact hφ.comp contDiff_neg

theorem coordPartial_neg {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) (x : Torus d) :
    coordPartial j (fun x => φ (-x)) x = -coordPartial j φ (-x) := by
  unfold coordPartial
  rw [neg_comp_lift]
  have hd : DifferentiableAt ℝ (φ ∘ torusLift) (-SharpLSI.secT x) :=
    (hφ.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun z => (φ ∘ torusLift) (-z))
      ((fderiv ℝ (φ ∘ torusLift) (-SharpLSI.secT x)).comp (-ContinuousLinearMap.id ℝ _))
      (SharpLSI.secT x) :=
    hd.hasFDerivAt.comp (SharpLSI.secT x) (hasFDerivAt_id _).neg
  rw [h1.fderiv]
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq (-SharpLSI.secT x)
  have e : SharpLSI.liftT (-SharpLSI.secT x) = -x := by
    have : SharpLSI.liftT (-SharpLSI.secT x) = -SharpLSI.liftT (SharpLSI.secT x) := rfl
    rw [this, SharpLSI.liftT_secT]
  rw [e] at hm
  rw [hm, fderiv_lift_periodic]
  simp

theorem isWeakGradient_translate {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (y : Torus d) :
    IsWeakGradient (fun x => u (x - y)) (fun x => g (x - y)) where
  memLp := h.memLp.comp_measurePreserving (measurePreserving_sub_right _ y)
  memLp_grad := h.memLp_grad.comp_measurePreserving (measurePreserving_sub_right _ y)
  ibp φ hφ j := by
    have hs := h.ibp _ (isSmoothPeriodic_translate hφ y) j
    simp only [coordPartial_translate] at hs
    have e1 : ∫ x, u (x - y) * coordPartial j φ x ∂haar d =
        ∫ x, u x * coordPartial j φ (x + y) ∂haar d := by
      rw [← integral_add_right_eq_self (fun x => u (x - y) * coordPartial j φ x) y]
      simp
    have e2 : ∫ x, g (x - y) j * φ x ∂haar d = ∫ x, g x j * φ (x + y) ∂haar d := by
      rw [← integral_add_right_eq_self (fun x => g (x - y) j * φ x) y]
      simp
    rw [e1, hs, e2]

theorem isWeakGradient_neg {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) :
    IsWeakGradient (fun x => u (-x)) (fun x => -g (-x)) where
  memLp := h.memLp.comp_measurePreserving (Measure.measurePreserving_neg _)
  memLp_grad := (h.memLp_grad.comp_measurePreserving (Measure.measurePreserving_neg _)).neg
  ibp φ hφ j := by
    have hs := h.ibp _ (isSmoothPeriodic_neg hφ) j
    simp only [coordPartial_neg hφ] at hs
    have e1 : ∫ x, u (-x) * coordPartial j φ x ∂haar d =
        -∫ x, u x * -coordPartial j φ (-x) ∂haar d := by
      rw [← integral_neg_eq_self (fun x => u (-x) * coordPartial j φ x) (haar d), ← integral_neg]
      simp
    have e2 : ∫ x, (-g (-x)) j * φ x ∂haar d = -∫ x, g x j * φ (-x) ∂haar d := by
      rw [← integral_neg_eq_self (fun x => (-g (-x)) j * φ x) (haar d), ← integral_neg]
      simp
    rw [e1, hs, e2]

end Covariance

section Weight

open DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization

/-- The half-period point `1/2` of the unit torus `𝕋¹`. -/
noncomputable def half : Torus 1 := fun _ => ((1 / 2 : ℝ) : UnitAddCircle)

/-- The von Mises weight `q_h(x) = exp(h cos(2πx)) / I₀(h)` on the unit torus `𝕋¹`, a density with
respect to the Haar probability measure. -/
noncomputable def vmWeight (h : ℝ) (x : Torus 1) : ℝ := besselDensity h (angEquiv x)

theorem angEquiv_neg (x : Torus 1) : angEquiv (-x) = -angEquiv x := by
  simp [angEquiv_apply]

theorem angEquiv_add_half (x : Torus 1) :
    angEquiv (x + half) = angEquiv x + ((π : ℝ) : AngCircle) := by
  rw [angEquiv_apply, angEquiv_apply, Pi.add_apply, map_add]
  congr 1
  have : (half 0) = (((1 / 2 : ℝ)) : UnitAddCircle) := rfl
  rw [this, angRescale_mk]
  congr 1
  ring

theorem angCos_neg (θ : AngCircle) : angCos (-θ) = angCos θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    have : -((s : ℝ) : AngCircle) = ((-s : ℝ) : AngCircle) := by simp
    rw [this]
    simp only [angCos, angMode_coe]
    simp

theorem angCos_add_pi (θ : AngCircle) : angCos (θ + ((π : ℝ) : AngCircle)) = -angCos θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    have : ((s : ℝ) : AngCircle) + ((π : ℝ) : AngCircle) = ((s + π : ℝ) : AngCircle) := by simp
    rw [this]
    simp only [angCos, angMode_coe]
    simp [Real.cos_add_pi]

theorem vmWeight_neg (h : ℝ) (x : Torus 1) : vmWeight h (-x) = vmWeight h x := by
  simp [vmWeight, angEquiv_neg, besselDensity, angCos_neg]

/-- The shift identity `q_h(x) q_h(x + 1/2) = 1/I₀(h)²`: the von Mises potential is odd under the
half-period shift. -/
theorem vmWeight_mul_half (h : ℝ) (x : Torus 1) :
    vmWeight h x * vmWeight h (x + half) = (besselI 0 h)⁻¹ ^ 2 := by
  have hI := (besselI_zero_pos h).ne'
  simp only [vmWeight, angEquiv_add_half, besselDensity, angCos_add_pi]
  rw [mul_neg, Real.exp_neg]
  have := Real.exp_pos (h * angCos (angEquiv x))
  field_simp

theorem measurable_vmWeight (h : ℝ) : Measurable (vmWeight h) := by
  have : Continuous fun θ => besselDensity h θ := by
    unfold besselDensity
    have := continuous_angMode 1
    fun_prop
  exact this.measurable.comp angEquiv.measurable

theorem vmWeight_bounds (h : ℝ) (x : Torus 1) :
    Real.exp (-|h|) / besselI 0 h ≤ vmWeight h x ∧ vmWeight h x ≤ Real.exp |h| / besselI 0 h := by
  have hI := besselI_zero_pos h
  have hc := abs_angMode_le 1 (angEquiv x)
  have h1 : |h * angCos (angEquiv x)| ≤ |h| := by
    rw [abs_mul]
    calc |h| * |angCos (angEquiv x)| ≤ |h| * 1 := by gcongr
      _ = |h| := mul_one _
  have h2 := abs_le.mp h1
  unfold vmWeight besselDensity
  constructor
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h2.1) hI.le
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h2.2) hI.le

theorem integral_vmWeight (h : ℝ) : ∫ x, vmWeight h x ∂haar 1 = 1 := by
  have hI := besselI_zero_pos h
  unfold vmWeight
  rw [measurePreserving_angEquiv.integral_comp' (f := angEquiv) (fun θ => besselDensity h θ)]
  unfold besselDensity
  rw [integral_div]
  have : besselI 0 h = ∫ θ, Real.exp (h * angCos θ) ∂angHaar := by
    unfold besselI; simp [angMode_zero]
  rw [← this]
  exact div_self hI.ne'

/-- The von Mises reference measure `q_h dm` on `𝕋¹` as a bounded positive reference. -/
noncomputable def vmRef (h : ℝ) : BoundedPositiveReference 1 where
  density := vmWeight h
  measurable_density := measurable_vmWeight h
  lower := Real.exp (-|h|) / besselI 0 h
  upper := Real.exp |h| / besselI 0 h
  lower_pos := div_pos (Real.exp_pos _) (besselI_zero_pos h)
  lower_le := Filter.Eventually.of_forall fun x => (vmWeight_bounds h x).1
  le_upper := Filter.Eventually.of_forall fun x => (vmWeight_bounds h x).2
  mass_one := integral_vmWeight h

end Weight

section Shift

theorem half_add_half : half + half = 0 := by
  ext i
  have : (((1 / 2 : ℝ) : UnitAddCircle)) + ((1 / 2 : ℝ) : UnitAddCircle) = 0 := by
    rw [← AddCircle.coe_add]
    have : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    rw [this]
    exact AddCircle.coe_period 1
  exact this

theorem neg_half : -half = half := by
  rw [neg_eq_iff_add_eq_zero]; exact half_add_half

theorem add_half_add_half (x : Torus 1) : x + half + half = x := by
  rw [add_assoc, half_add_half, add_zero]

theorem neg_add_half (x : Torus 1) : -(x + half) = -x + half := by
  rw [neg_add, neg_half]

theorem isWeakGradient_shift {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (h : IsWeakGradient u g) : IsWeakGradient (fun x => u (x + half)) (fun x => g (x + half)) := by
  have := isWeakGradient_translate h half
  have e : ∀ x : Torus 1, x - half = x + half := fun x => by rw [sub_eq_add_neg, neg_half]
  simpa only [e] using this

theorem integral_shift (φ : Torus 1 → ℝ) : ∫ x, φ (x + half) ∂haar 1 = ∫ x, φ x ∂haar 1 :=
  integral_add_right_eq_self φ half

theorem ae_shift {P : Torus 1 → Prop} (h : ∀ᵐ x ∂haar 1, P x) : ∀ᵐ x ∂haar 1, P (x + half) :=
  (measurePreserving_add_right (haar 1) half).quasiMeasurePreserving.ae h

theorem ae_neg {P : Torus 1 → Prop} (h : ∀ᵐ x ∂haar 1, P x) : ∀ᵐ x ∂haar 1, P (-x) :=
  (Measure.measurePreserving_neg (haar 1)).quasiMeasurePreserving.ae h

end Shift

section Eigen

variable {w : Torus 1 → ℝ} {c C : ℝ}

/-- The vector of `Tangent 1` with the single coordinate `s`. -/
noncomputable def vec1 (s : ℝ) : Tangent 1 := EuclideanSpace.single 0 s

@[simp] theorem vec1_apply (s : ℝ) (j : Fin 1) : vec1 s j = s := by
  fin_cases j; simp [vec1]

theorem inner1 (a b : Tangent 1) : inner ℝ a b = a 0 * b 0 := by
  simp [PiLp.inner_apply, mul_comm]

theorem weightedForm_one (G Y : Torus 1 → Tangent 1) :
    weightedForm w G Y = ∫ x, G x 0 * Y x 0 * w x ∂haar 1 := by
  unfold weightedForm; simp_rw [inner1]

/-- `u` solves the weak eigenvalue equation `-L u = lam u` in the form sense for the weight `w`:
`u ∈ H¹` with weak gradient `G`, and `∫ u' f' w = lam ∫ u f w` for every `f ∈ H¹`. -/
def HasEigenEq (w : Torus 1 → ℝ) (lam : ℝ) (u : Torus 1 → ℝ) (G : Torus 1 → Tangent 1) : Prop :=
  IsWeakGradient u G ∧ ∀ (f : Torus 1 → ℝ) (Y : Torus 1 → Tangent 1), IsWeakGradient f Y →
    weightedForm w G Y = lam * ∫ x, u x * f x * w x ∂haar 1

/-- `lam` is an eigenvalue of `-L = -(w⁻¹ (w u')')` with eigenfunction `u` (weak form, `H¹` tests). -/
def IsEigenfunction (w : Torus 1 → ℝ) (lam : ℝ) (u : Torus 1 → ℝ) : Prop :=
  ¬ (u =ᵐ[haar 1] 0) ∧ ∃ G, HasEigenEq w lam u G

end Eigen

section Pairing

open DGPS.Examples DGPS.Lipschitz.WeightedGenerator

variable {w : Torus 1 → ℝ} {c C : ℝ}

theorem memLp_weight_mul (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) {p : Torus 1 → ℝ} (hp : MemLp p 2 (haar 1)) :
    MemLp (fun x => w x * p x) 2 (haar 1) := by
  refine hp.of_le_mul (c := C) (hw.aestronglyMeasurable.mul hp.aestronglyMeasurable) ?_
  filter_upwards [hwb] with x hx
  have h0 : 0 ≤ w x := hc.le.trans hx.1
  rw [norm_mul, Real.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)

theorem integrable_mul_mul_weight (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) {p q : Torus 1 → ℝ} (hp : MemLp p 2 (haar 1))
    (hq : MemLp q 2 (haar 1)) : Integrable (fun x => p x * q x * w x) (haar 1) :=
  integrable_mul_weight (hp.integrable_mul hq) hw hwb hc

theorem memLp_vec1 {s : Torus 1 → ℝ} (hs : MemLp s 2 (haar 1)) :
    MemLp (fun x => vec1 (s x)) 2 (haar 1) := by
  have e : (fun x => vec1 (s x)) = fun x => s x • (EuclideanSpace.single 0 (1 : ℝ) : Tangent 1) := by
    funext x; ext j; simp [vec1]
  rw [e]
  exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single 0 (1 : ℝ) : Tangent 1) :
      ℝ →L[ℝ] Tangent 1).comp_memLp' hs

/-- The flux `w u'` has weak derivative `-lam w u`. -/
theorem flux_weakGradient (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) {lam : ℝ} {u : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (h : HasEigenEq w lam u G) :
    IsWeakGradient (fun x => w x * G x 0) (fun x => vec1 (-(lam * (w x * u x)))) where
  memLp := memLp_weight_mul hw hc hwb (memLp_coord h.1.memLp_grad 0)
  memLp_grad := memLp_vec1 ((memLp_weight_mul hw hc hwb h.1.memLp).const_mul lam).neg
  ibp φ hφ j := by
    obtain rfl : j = 0 := Subsingleton.elim _ _
    have h2 := h.2 φ (smoothGrad φ) hφ.isWeakGradient
    rw [weightedForm_one] at h2
    simp only [smoothGrad_apply] at h2
    simp only [vec1_apply]
    have e1 : ∫ x, w x * G x 0 * coordPartial 0 φ x ∂haar 1 =
        ∫ x, G x 0 * coordPartial 0 φ x * w x ∂haar 1 := by
      congr 1; funext x; ring
    have e2 : ∫ x, -(lam * (w x * u x)) * φ x ∂haar 1 =
        -(lam * ∫ x, u x * φ x * w x ∂haar 1) := by
      rw [← integral_const_mul, ← integral_neg]
      congr 1; funext x; ring
    rw [e1, h2, e2, neg_neg]

theorem pairing_hasEigenEq (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) {κ : ℝ} (hκ : ∀ x, w x * w (x + half) = κ)
    {lam : ℝ} {u : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (h : HasEigenEq w lam u G) :
    HasEigenEq w lam (fun x => w (x + half) * G (x + half) 0)
      (fun x => vec1 (-(lam * (w (x + half) * u (x + half))))) := by
  have hF := flux_weakGradient hw hc hwb h
  refine ⟨isWeakGradient_shift hF, fun f Y hf => ?_⟩
  rw [weightedForm_one]
  simp only [vec1_apply]
  have e1 : ∫ x, -(lam * (w (x + half) * u (x + half))) * Y x 0 * w x ∂haar 1 =
      -(lam * κ) * ∫ x, u (x + half) * Y x 0 ∂haar 1 := by
    rw [← integral_const_mul]; congr 1; funext x
    rw [← hκ x]; ring
  have e2 : ∫ x, u (x + half) * Y x 0 ∂haar 1 = ∫ x, u x * Y (x + half) 0 ∂haar 1 := by
    have := integral_shift (fun x => u x * Y (x + half) 0)
    simp only [add_half_add_half] at this
    exact this
  have e3 := ibp_H1 h.1 (isWeakGradient_shift hf) 0
  have e4 : ∫ x, w (x + half) * G (x + half) 0 * f x * w x ∂haar 1 =
      κ * ∫ x, G (x + half) 0 * f x ∂haar 1 := by
    rw [← integral_const_mul]; congr 1; funext x
    rw [← hκ x]; ring
  have e5 : ∫ x, G (x + half) 0 * f x ∂haar 1 = ∫ x, G x 0 * f (x + half) ∂haar 1 := by
    have := integral_shift (fun x => G x 0 * f (x + half))
    simp only [add_half_add_half] at this
    exact this
  rw [e1, e2, e3, e4, e5]; ring

theorem gradient_parity {u : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (h : IsWeakGradient u G)
    {ε : ℝ} (hε : ∀ᵐ x ∂haar 1, u (-x) = ε * u x) :
    ∀ᵐ x ∂haar 1, G (-x) 0 = -ε * G x 0 := by
  have h1 := (isWeakGradient_neg h).congr_ae (u' := fun x => ε * u x)
    (hε.mono fun x hx => hx) (Filter.EventuallyEq.refl _ _)
  have h2 := h.smul ε
  filter_upwards [h1.ae_eq h2] with x hx
  have := congrArg (fun v : Tangent 1 => v 0) hx
  simp at this
  linarith

theorem hasEigenEq_neg (hev : ∀ x, w (-x) = w x) {lam : ℝ} {u : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (h : HasEigenEq w lam u G) :
    HasEigenEq w lam (fun x => u (-x)) (fun x => -G (-x)) := by
  refine ⟨isWeakGradient_neg h.1, fun f Y hf => ?_⟩
  have h2 := h.2 _ _ (isWeakGradient_neg hf)
  rw [weightedForm_one] at h2 ⊢
  have e1 : ∫ x, (-G (-x)) 0 * Y x 0 * w x ∂haar 1 = ∫ x, G x 0 * (-Y (-x)) 0 * w x ∂haar 1 := by
    rw [← integral_neg_eq_self (fun x => G x 0 * (-Y (-x)) 0 * w x) (haar 1)]
    congr 1; funext x
    simp [hev x]
  have e2 : ∫ x, u (-x) * f x * w x ∂haar 1 = ∫ x, u x * f (-x) * w x ∂haar 1 := by
    rw [← integral_neg_eq_self (fun x => u x * f (-x) * w x) (haar 1)]
    congr 1; funext x
    simp [hev x]
  rw [e1, e2]; exact h2

theorem hasEigenEq_comb (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) {lam : ℝ} {u u' : Torus 1 → ℝ}
    {G G' : Torus 1 → Tangent 1} (h : HasEigenEq w lam u G) (h' : HasEigenEq w lam u' G')
    (a b : ℝ) :
    HasEigenEq w lam (fun x => a * u x + b * u' x) (fun x => a • G x + b • G' x) := by
  refine ⟨(h.1.smul a).add (h'.1.smul b), fun f Y hf => ?_⟩
  have e1 := h.2 f Y hf
  have e2 := h'.2 f Y hf
  rw [weightedForm_one] at e1 e2 ⊢
  have i1 := integrable_mul_mul_weight hw hc hwb (memLp_coord h.1.memLp_grad 0)
    (memLp_coord hf.memLp_grad 0)
  have i2 := integrable_mul_mul_weight hw hc hwb (memLp_coord h'.1.memLp_grad 0)
    (memLp_coord hf.memLp_grad 0)
  have j1 := integrable_mul_mul_weight hw hc hwb h.1.memLp hf.memLp
  have j2 := integrable_mul_mul_weight hw hc hwb h'.1.memLp hf.memLp
  have l1 : ∫ x, (a • G x + b • G' x) 0 * Y x 0 * w x ∂haar 1 =
      a * ∫ x, G x 0 * Y x 0 * w x ∂haar 1 + b * ∫ x, G' x 0 * Y x 0 * w x ∂haar 1 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a) (i2.const_mul b)]
    congr 1; funext x; simp; ring
  have l2 : ∫ x, (a * u x + b * u' x) * f x * w x ∂haar 1 =
      a * ∫ x, u x * f x * w x ∂haar 1 + b * ∫ x, u' x * f x * w x ∂haar 1 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul a) (j2.const_mul b)]
    congr 1; funext x; ring
  rw [l1, l2, e1, e2]; ring

/-- The paired function is a nonzero eigenfunction of opposite parity. -/
theorem pairing_sector (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) (hev : ∀ x, w (-x) = w x) {κ : ℝ}
    (hκ : ∀ x, w x * w (x + half) = κ) {lam : ℝ} (hlam : 0 < lam) {u : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (h : HasEigenEq w lam u G) (hne : ¬ (u =ᵐ[haar 1] 0)) {ε : ℝ}
    (hε : ∀ᵐ x ∂haar 1, u (-x) = ε * u x) :
    IsEigenfunction w lam (fun x => w (x + half) * G (x + half) 0) ∧
      ∀ᵐ x ∂haar 1, (fun x => w (x + half) * G (x + half) 0) (-x) =
        -ε * (fun x => w (x + half) * G (x + half) 0) x := by
  refine ⟨⟨?_, _, pairing_hasEigenEq hw hc hwb hκ h⟩, ?_⟩
  · intro hv
    apply hne
    have hF0 : (fun x => w x * G x 0) =ᵐ[haar 1] 0 := by
      have := ae_shift (P := fun x => w (x + half) * G (x + half) 0 = 0) hv
      filter_upwards [this] with x hx
      simpa only [add_half_add_half, Pi.zero_apply] using hx
    have hF := flux_weakGradient hw hc hwb h
    have hF' := hF.congr_ae hF0 (Filter.EventuallyEq.refl _ _)
    have hz := hF'.ae_eq isWeakGradient_zero
    filter_upwards [hz, hwb] with x hx hx2
    have := congrArg (fun v : Tangent 1 => v 0) hx
    simp only [vec1_apply, PiLp.zero_apply] at this
    have hw0 : 0 < w x := hc.trans_le hx2.1
    have : lam * (w x * u x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hlam.ne'
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hw0.ne'
      · simpa using h2
  · have hg := gradient_parity h.1 hε
    have hg' := ae_shift (P := fun x => G (-x) 0 = -ε * G x 0) hg
    filter_upwards [hg'] with x hx
    show w (-x + half) * G (-x + half) 0 = -ε * (w (x + half) * G (x + half) 0)
    rw [← neg_add_half, hev, hx]; ring

theorem eigen_both_sectors (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) (hev : ∀ x, w (-x) = w x) {κ : ℝ}
    (hκ : ∀ x, w x * w (x + half) = κ) {lam : ℝ} (hlam : 0 < lam) {u : Torus 1 → ℝ}
    (h : IsEigenfunction w lam u) :
    (∃ v, IsEigenfunction w lam v ∧ ∀ᵐ x ∂haar 1, v (-x) = 1 * v x) ∧
      (∃ v, IsEigenfunction w lam v ∧ ∀ᵐ x ∂haar 1, v (-x) = -1 * v x) := by
  obtain ⟨hne, G, hG⟩ := h
  have hG' := hasEigenEq_neg hev hG
  have he := hasEigenEq_comb hw hc hwb hG hG' (1 / 2) (1 / 2)
  have ho := hasEigenEq_comb hw hc hwb hG hG' (1 / 2) (-1 / 2)
  have hee : ∀ x, (fun x => 1 / 2 * u x + 1 / 2 * u (-x)) (-x) =
      1 * (fun x => 1 / 2 * u x + 1 / 2 * u (-x)) x := by
    intro x; simp only [neg_neg]; ring
  have hoo : ∀ x, (fun x => 1 / 2 * u x + -1 / 2 * u (-x)) (-x) =
      -1 * (fun x => 1 / 2 * u x + -1 / 2 * u (-x)) x := by
    intro x; simp only [neg_neg]; ring
  by_cases hue : (fun x => 1 / 2 * u x + 1 / 2 * u (-x)) =ᵐ[haar 1] 0
  · have huo : ¬ (fun x => 1 / 2 * u x + -1 / 2 * u (-x)) =ᵐ[haar 1] 0 := by
      intro huo; apply hne
      filter_upwards [hue, huo] with x h1 h2
      simp only [Pi.zero_apply] at h1 h2 ⊢
      linarith
    obtain ⟨hv, hsec⟩ := pairing_sector hw hc hwb hev hκ hlam ho huo
      (Filter.Eventually.of_forall hoo)
    exact ⟨⟨_, hv, hsec.mono fun x hx => by simp only at hx ⊢; linarith⟩,
      ⟨_, ⟨huo, _, ho⟩, Filter.Eventually.of_forall hoo⟩⟩
  · obtain ⟨hv, hsec⟩ := pairing_sector hw hc hwb hev hκ hlam he hue
      (Filter.Eventually.of_forall hee)
    exact ⟨⟨_, ⟨hue, _, he⟩, Filter.Eventually.of_forall hee⟩, ⟨_, hv, hsec⟩⟩

end Pairing

section Bridge

open DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz.WeightedGenerator

variable (P : BoundedPositiveReference 1)

/-- An `L²(m)` function as an element of the weighted space `L²(P)`. -/
noncomputable def toHw {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) : Hw 1 P.density :=
  ((memLp_wMeasure_iff P.lower_pos (fou020_hwb P)).2 hf).toLp f

theorem toHw_ae_wMeasure {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) :
    (toHw P hf : Torus 1 → ℝ) =ᵐ[wMeasure 1 P.density] f :=
  MemLp.coeFn_toLp _

theorem toHw_ae {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) :
    (toHw P hf : Torus 1 → ℝ) =ᵐ[haar 1] f :=
  ae_eq_haar P.lower_pos (fou020_hwb P) (toHw_ae_wMeasure P hf)

theorem inner_toHw (a : Hw 1 P.density) {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) :
    ⟪a, toHw P hf⟫_ℝ = ∫ x, (a : Torus 1 → ℝ) x * f x * P.density x ∂haar 1 := by
  rw [inner_Lp_wMeasure P.measurable_density P.lower_pos (fou020_hwb P)]
  refine integral_congr_ae ?_
  filter_upwards [toHw_ae P hf] with x hx
  rw [hx]; simp [mul_comm]

/-- The output of LIP009 for the reference `P`. -/
structure SpecData (e : HilbertBasis ℕ ℝ (Hw 1 P.density)) (lam : ℕ → ℝ)
    (G : ℕ → Torus 1 → Tangent 1) : Prop where
  e0 : ((e 0 : Hw 1 P.density) : Torus 1 → ℝ) =ᵐ[wMeasure 1 P.density] fun _ => 1
  lam0 : lam 0 = 0
  lam01 : lam 0 < lam 1
  mono : Monotone lam
  grad : ∀ j, IsWeakGradient ((e j : Hw 1 P.density) : Torus 1 → ℝ) (G j)
  form : ∀ j (f : Hw 1 P.density) (Y : Torus 1 → Tangent 1),
    IsWeakGradient (f : Torus 1 → ℝ) Y → weightedForm P.density (G j) Y = lam j * ⟪e j, f⟫_ℝ
  energy : ∀ (f : Hw 1 P.density) (Y : Torus 1 → Tangent 1), IsWeakGradient (f : Torus 1 → ℝ) Y →
    HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm P.density Y Y)

theorem exists_specData : ∃ (e : HilbertBasis ℕ ℝ (Hw 1 P.density)) (lam : ℕ → ℝ)
    (G : ℕ → Torus 1 → Tangent 1), SpecData P e lam G := by
  obtain ⟨e, lam, G, he0, hl0, hl01, hmono, -, hgrad, hform, henergy, -⟩ :=
    DGPS.Lipschitz.WeightedSpectrum.weighted_eigenbasis_and_growth (d := 1) one_pos
      P.measurable_density P.lower_pos (fou020_hwb P) P.mass_one
  exact ⟨e, lam, G, ⟨he0, hl0, hl01, hmono, hgrad, hform, henergy⟩⟩

variable {P} {e : HilbertBasis ℕ ℝ (Hw 1 P.density)} {lam : ℕ → ℝ} {G : ℕ → Torus 1 → Tangent 1}

theorem SpecData.hasEigenEq (hS : SpecData P e lam G) (j : ℕ) :
    HasEigenEq P.density (lam j) ((e j : Hw 1 P.density) : Torus 1 → ℝ) (G j) := by
  refine ⟨hS.grad j, fun f Y hf => ?_⟩
  rw [hS.form j (toHw P hf.memLp) Y
    (hf.congr_ae (toHw_ae P hf.memLp).symm Filter.EventuallyEq.rfl), inner_toHw]

theorem SpecData.isEigenfunction (hS : SpecData P e lam G) (j : ℕ) :
    IsEigenfunction P.density (lam j) ((e j : Hw 1 P.density) : Torus 1 → ℝ) := by
  refine ⟨fun h0 => ?_, G j, hS.hasEigenEq j⟩
  have h1 : (e j : Hw 1 P.density) = 0 := Lp.eq_zero_iff_ae_eq_zero.2 (ae_eq_wMeasure h0)
  have := e.orthonormal.1 j
  rw [h1] at this
  simp at this

theorem SpecData.eigenvalue_mem (hS : SpecData P e lam G) {lam' : ℝ} {u : Torus 1 → ℝ}
    (h : IsEigenfunction P.density lam' u) : ∃ j, lam' = lam j := by
  obtain ⟨hne, Gu, hu⟩ := h
  have hmem := hu.1.memLp
  have hUne : toHw P hmem ≠ 0 := by
    intro h0; apply hne
    have : (toHw P hmem : Torus 1 → ℝ) =ᵐ[wMeasure 1 P.density] 0 :=
      Lp.eq_zero_iff_ae_eq_zero.1 h0
    exact (toHw_ae P hmem).symm.trans (ae_eq_haar P.lower_pos (fou020_hwb P) this)
  have hj : ∃ j, ⟪e j, toHw P hmem⟫_ℝ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hUne
    have hs := e.hasSum_repr (toHw P hmem)
    have h0 : ∀ i, e.repr (toHw P hmem) i • (e i : Hw 1 P.density) = 0 := fun i => by
      rw [HilbertBasis.repr_apply_apply, hcon i, zero_smul]
    simp only [h0] at hs
    exact (hasSum_zero.unique hs).symm
  obtain ⟨j, hj⟩ := hj
  refine ⟨j, ?_⟩
  have hUw : IsWeakGradient (toHw P hmem : Torus 1 → ℝ) Gu :=
    hu.1.congr_ae (toHw_ae P hmem).symm Filter.EventuallyEq.rfl
  have h1 := hS.form j (toHw P hmem) Gu hUw
  have h2 := hu.2 _ _ (hS.grad j)
  rw [weightedForm_comm, h2] at h1
  have h3 : ⟪e j, toHw P hmem⟫_ℝ = ∫ x, u x * (e j : Torus 1 → ℝ) x * P.density x ∂haar 1 := by
    rw [inner_toHw]; congr 1; funext x; ring
  rw [← h3] at h1
  exact mul_right_cancel₀ hj h1

theorem SpecData.variance_eq (hS : SpecData P e lam G) (f : WeakH1Test (fou020_prob P))
    (U : Hw 1 P.density) (hU : (U : Torus 1 → ℝ) =ᵐ[wMeasure 1 P.density] f.fn) :
    weightedVariance (fou020_prob P) f.fn =
      ‖U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density)‖ ^ 2 := by
  have hmean : ∫ y, f.fn y ∂((fou020_prob P : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) =
      ⟪e 0, U⟫_ℝ := by
    rw [fou020_inner_e0 e hS.e0 U]
    exact (integral_congr_ae hU).symm
  unfold weightedVariance
  generalize ⟪e 0, U⟫_ℝ = a0 at hmean ⊢
  rw [hmean, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hU, Lp.coeFn_sub U (a0 • (e 0 : Hw 1 P.density)),
    Lp.coeFn_smul a0 (e 0 : Hw 1 P.density), hS.e0] with x h1 h2 h3 h4
  have hx : ((U - a0 • (e 0 : Hw 1 P.density) : Hw 1 P.density) : Torus 1 → ℝ) x =
      f.fn x - a0 := by
    rw [h2, Pi.sub_apply, h3, Pi.smul_apply, h4, h1]; simp
  rw [hx]; simp [sq]

theorem SpecData.lam_one_mul_le (hS : SpecData P e lam G) (U : Hw 1 P.density)
    (Y : Torus 1 → Tangent 1) (hUY : IsWeakGradient (U : Torus 1 → ℝ) Y) :
    lam 1 * ‖U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density)‖ ^ 2 ≤ weightedForm P.density Y Y := by
  have hb : ∀ j, ⟪e j, U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density)⟫_ℝ =
      ⟪e j, U⟫_ℝ - if j = 0 then ⟪e 0, U⟫_ℝ else 0 := by
    intro j
    rw [inner_sub_right, inner_smul_right, orthonormal_iff_ite.mp e.orthonormal j 0]
    by_cases hj : j = 0 <;> simp [hj]
  have hP := e.hasSum_inner_mul_inner (U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density))
    (U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density))
  rw [real_inner_self_eq_norm_sq] at hP
  have hP' : HasSum (fun j => lam 1 *
      ⟪e j, U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density)⟫_ℝ ^ 2)
      (lam 1 * ‖U - ⟪e 0, U⟫_ℝ • (e 0 : Hw 1 P.density)‖ ^ 2) := by
    refine HasSum.mul_left (lam 1) ?_
    convert hP using 2 with j
    rw [real_inner_comm, sq]
  refine hasSum_le (fun j => ?_) hP' (hS.energy U Y hUY)
  rw [hb j]
  by_cases hj : j = 0
  · subst hj; simp [hS.lam0]
  · simp only [hj, ↓reduceIte, sub_zero]
    exact mul_le_mul_of_nonneg_right (hS.mono (Nat.one_le_iff_ne_zero.2 hj)) (sq_nonneg _)

theorem SpecData.poincareRate_eq (hS : SpecData P e lam G) :
    poincareRate (fou020_prob P) = ENNReal.ofReal (lam 1) := by
  have hl1 : 0 < lam 1 := by have := hS.lam0; have := hS.lam01; linarith
  apply le_antisymm
  · let f : WeakH1Test (fou020_prob P) :=
      ⟨((e 1 : Hw 1 P.density) : Torus 1 → ℝ), G 1,
        (fou020_isWeak_iff P (fou020_prob P) rfl).2 (hS.grad 1)⟩
    have h01 : ⟪e 0, (e 1 : Hw 1 P.density)⟫_ℝ = 0 := by
      rw [orthonormal_iff_ite.mp e.orthonormal]; simp
    have hvar : weightedVariance (fou020_prob P) f.fn = 1 := by
      rw [hS.variance_eq f (e 1) Filter.EventuallyEq.rfl, h01, zero_smul, sub_zero,
        e.orthonormal.1 1]
      simp
    have hE : dirichletEnergy (fou020_prob P) f = ENNReal.ofReal (lam 1) := by
      rw [fou020_dirichlet_eq P (fou020_prob P) rfl f]
      show ENNReal.ofReal (weightedForm P.density (G 1) (G 1)) = _
      rw [hS.form 1 (e 1) (G 1) (hS.grad 1), orthonormal_iff_ite.mp e.orthonormal]
      simp
    have := poincareRate_le_quotient (fou020_prob P) f (by rw [hvar]; exact one_pos)
    unfold poincareQuotient at this
    rw [hE, hvar] at this
    simpa using this
  · rw [le_poincareRate_iff_forall]
    intro f _
    have hg := (fou020_isWeak_iff P (fou020_prob P) rfl).1 f.isWeak
    have hmem := hg.memLp
    rw [fou020_dirichlet_eq P (fou020_prob P) rfl f,
      hS.variance_eq f (toHw P hmem) (toHw_ae_wMeasure P hmem), ← ENNReal.ofReal_mul hl1.le]
    exact ENNReal.ofReal_le_ofReal (hS.lam_one_mul_le (toHw P hmem) f.grad
      (hg.congr_ae (toHw_ae P hmem).symm Filter.EventuallyEq.rfl))

end Bridge

end DGPS.Circle.VonMisesParity

namespace DGPS.Examples

open DGPS DGPS.Circle.VonMisesParity DGPS.Circle.BesselMoments

/-- **EX008 (von Mises parity pairing).**  Let `q_h = exp(h cos(2πx)) / I₀(h)` be the von Mises
density on the unit torus `𝕋¹` (`h` arbitrary real) and `L_h u = q_h⁻¹ (q_h u')'` its reversible
generator, `-L_h` understood in the weak form sense (`u ∈ H¹`, `∫ u' f' q_h = λ ∫ u f q_h` for all
`f ∈ H¹`; `IsEigenfunction`).  Then:

* every strictly positive eigenvalue `λ` of `-L_h` has an even and an odd eigenfunction
  (`ex007_InParitySector 1`, resp. `ex007_InParitySector (-1)`);
* the least positive eigenvalue `λ₁` is also the least positive *odd* eigenvalue, and it equals the
  full Poincaré rate `poincareRate (q_h dm)`. -/
theorem von_mises_parity_pairing (h : ℝ) :
    (∀ lam : ℝ, 0 < lam → (∃ u, IsEigenfunction (vmWeight h) lam u) →
      (∃ u, IsEigenfunction (vmWeight h) lam u ∧ ex007_InParitySector (d := 1) 1 u) ∧
      (∃ u, IsEigenfunction (vmWeight h) lam u ∧ ex007_InParitySector (d := 1) (-1) u)) ∧
    ∃ lam1 : ℝ, 0 < lam1 ∧
      IsLeast {lam : ℝ | 0 < lam ∧ ∃ u, IsEigenfunction (vmWeight h) lam u} lam1 ∧
      IsLeast {lam : ℝ | 0 < lam ∧
        ∃ u, IsEigenfunction (vmWeight h) lam u ∧ ex007_InParitySector (d := 1) (-1) u} lam1 ∧
      poincareRate ⟨(vmRef h).measure, (vmRef h).isProbabilityMeasure⟩ = ENNReal.ofReal lam1 := by
  obtain ⟨e, lam, G, hS⟩ := exists_specData (vmRef h)
  have hl1 : 0 < lam 1 := by have := hS.lam0; have := hS.lam01; linarith
  have both : ∀ l : ℝ, 0 < l → (∃ u, IsEigenfunction (vmWeight h) l u) →
      (∃ u, IsEigenfunction (vmWeight h) l u ∧ ex007_InParitySector (d := 1) 1 u) ∧
      (∃ u, IsEigenfunction (vmWeight h) l u ∧ ex007_InParitySector (d := 1) (-1) u) :=
    fun l hl ⟨u, hu⟩ => eigen_both_sectors (measurable_vmWeight h) (vmRef h).lower_pos
      (DGPS.Analysis.fou020_hwb (vmRef h)) (vmWeight_neg h) (vmWeight_mul_half h) hl hu
  have least : ∀ l : ℝ, 0 < l → (∃ u, IsEigenfunction (vmWeight h) l u) → lam 1 ≤ l := by
    rintro l hl ⟨u, hu⟩
    obtain ⟨j, rfl⟩ := hS.eigenvalue_mem hu
    have hj : j ≠ 0 := by
      rintro rfl
      rw [hS.lam0] at hl
      exact lt_irrefl _ hl
    exact hS.mono (Nat.one_le_iff_ne_zero.2 hj)
  have e1 := hS.isEigenfunction 1
  refine ⟨both, lam 1, hl1, ⟨⟨hl1, _, e1⟩, fun l hl => least l hl.1 hl.2⟩,
    ⟨⟨hl1, (both _ hl1 ⟨_, e1⟩).2⟩, fun l hl => least l hl.1 ⟨hl.2.choose, hl.2.choose_spec.1⟩⟩,
    hS.poincareRate_eq⟩

end DGPS.Examples
