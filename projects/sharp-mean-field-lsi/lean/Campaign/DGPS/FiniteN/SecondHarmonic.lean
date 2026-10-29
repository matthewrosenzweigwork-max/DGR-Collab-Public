import DGPS.Model.FreeEnergy
import DGPS.Model.ScalarRate
import DGPS.Model.SpeciesRate
import DGPS.Analysis.CircleLSI
import SharpSymmetricLSI.Paper.FourierSynth
import DGPS.Particle.Symmetry

/-!
# The repulsive second-harmonic model and its free energy (FIN086)

On the circle `𝕋^1 = Torus 1` (points are `Fin 1 → AddCircle 1`, a point `x` has coordinate
`x 0`), fix `κ > 0`, `V = 0` and `W(x,y) = κ[cos 4π(x−y) − 1]`.

* `mode k x = e^{2πi k x}` (Mathlib `mFourier`), and `W x y = κ (Re mode 2 (x − y) − 1)`
  (`secondHarmonicW_lift` gives the explicit cosine on lifts).
* `ρ̂(2)` of a measure `ν` is `secondHarmonicCoeff ν = ∫ e^{-2πi·2x} dν`, a complex number; the
  statement uses `Complex.normSq (secondHarmonicCoeff ν) = |ρ̂(2)|²`.
* `secondHarmonicG κ ν := F(ν) − F_*` (in `EReal`), proved equal to `H(ν|m) + (κ/2)|ρ̂(2)|²`.

Main result `second_harmonic_model_and_free_energy`: `V = 0`, the cosine form of `W`, smoothness
and Lipschitz regularity, the free-energy formula, `F_* = −κ/2`, the formula for `G`, and that
Haar measure is the unique minimizer.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal ContDiff

namespace DGPS.FiniteN

noncomputable def mode (k : ℤ) : DGPS.Torus 1 → ℂ := fun x => mFourier (fun _ : Fin 1 => k) x

theorem mode_apply (k : ℤ) (x : DGPS.Torus 1) : mode k x = fourier k (x 0) := by
  simp [mode, mFourier]

theorem continuous_mode (k : ℤ) : Continuous (mode k) := (mFourier _).continuous

theorem mode_neg (k : ℤ) (x : DGPS.Torus 1) : mode (-k) x = (starRingEnd ℂ) (mode k x) := by
  simp only [mode_apply, fourier_neg]

theorem mode_sub (k : ℤ) (x y : DGPS.Torus 1) :
    mode k (x - y) = mode k x * (starRingEnd ℂ) (mode k y) := by
  simp only [mode_apply, Pi.sub_apply]
  rw [sub_eq_add_neg, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul, smul_neg,
    ← fourier_apply, fourier_neg']

theorem mode_re_sub (x y : DGPS.Torus 1) :
    (mode 2 (x - y)).re = (mode 2 x).re * (mode 2 y).re + (mode 2 x).im * (mode 2 y).im := by
  rw [mode_sub]; simp [Complex.mul_re]

theorem mode_lift (k : ℤ) (a : Fin 1 → ℝ) :
    mode k (DGPS.torusLift a) = Complex.exp (2 * Real.pi * Complex.I * k * a 0) := by
  simp [mode_apply, DGPS.torusLift, SharpLSI.liftT]

theorem mode_zero (k : ℤ) : mode k 0 = 1 := by
  simp [mode_apply]

/-- The repulsive second-harmonic interaction `W(x,y) = κ[cos 4π(x−y) − 1]`. -/
noncomputable def secondHarmonicW (κ : ℝ) (x y : DGPS.Torus 1) : ℝ :=
  κ * ((mode 2 (x - y)).re - 1)

theorem secondHarmonicW_lift (κ : ℝ) (a b : Fin 1 → ℝ) :
    secondHarmonicW κ (DGPS.torusLift a) (DGPS.torusLift b) =
      κ * (Real.cos (4 * Real.pi * (a 0 - b 0)) - 1) := by
  have h : DGPS.torusLift a - DGPS.torusLift b = DGPS.torusLift (a - b) := by
    ext i; simp [DGPS.torusLift, SharpLSI.liftT]
  have h2 : (2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) * ((a - b) 0 : ℝ) : ℂ) =
      ((4 * Real.pi * (a 0 - b 0) : ℝ) : ℂ) * Complex.I := by
    push_cast [Pi.sub_apply]; ring
  rw [secondHarmonicW, h, mode_lift, h2, Complex.exp_ofReal_mul_I_re]


/-- The model `V = 0`, `W = κ[cos 4π(x−y) − 1]` on the circle `𝕋^1`. -/
noncomputable def secondHarmonicData (κ : ℝ) : DGPS.InteractionData 1 where
  V := fun _ => 0
  W := secondHarmonicW κ
  V_continuous := continuous_const
  W_continuous :=
    continuous_const.mul ((Complex.continuous_re.comp
      ((continuous_mode 2).comp (continuous_fst.sub continuous_snd))).sub continuous_const)
  W_symm := fun x y => by simp only [secondHarmonicW, mode_re_sub]; ring
  W_diag := fun x => by simp [secondHarmonicW, mode_zero]

/-- The second Fourier coefficient `ρ̂(2) = ∫ e^{-2πi·2x} dν(x)` of a measure on `𝕋^1`. -/
noncomputable def secondHarmonicCoeff (ν : Measure (DGPS.Torus 1)) : ℂ :=
  ∫ x, mode (-2) x ∂ν

theorem normSq_secondHarmonicCoeff (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    Complex.normSq (secondHarmonicCoeff ν) =
      (∫ x, (mode 2 x).re ∂ν) ^ 2 + (∫ x, (mode 2 x).im ∂ν) ^ 2 := by
  have hint : Integrable (fun x => mode (-2) x) ν :=
    (continuous_mode (-2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr := integral_re hint
  have hm := integral_im hint
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hr hm
  rw [Complex.normSq_apply, secondHarmonicCoeff, ← hr, ← hm]
  simp only [mode_neg, Complex.conj_re, Complex.conj_im, integral_neg]
  ring

theorem secondHarmonicCoeff_haar : secondHarmonicCoeff (DGPS.haar 1) = 0 := by
  unfold secondHarmonicCoeff
  have h := SharpLSI.integral_mFourier (ι := Fin 1) (fun _ => (-2 : ℤ))
  have hne : (fun _ : Fin 1 => (-2 : ℤ)) ≠ 0 := fun h0 => by
    have := congrFun h0 0; simp at this
  rw [ite_eq_right_iff.mpr (fun h0 => absurd h0 hne)] at h
  exact h

theorem interactionEnergy_secondHarmonic (κ : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.interactionEnergy (secondHarmonicData κ) ν =
      κ * (Complex.normSq (secondHarmonicCoeff ν) - 1) := by
  have hc : Continuous fun x => (mode 2 x).re := Complex.continuous_re.comp (continuous_mode 2)
  have hs : Continuous fun x => (mode 2 x).im := Complex.continuous_im.comp (continuous_mode 2)
  have hP : ∀ {f g : DGPS.Torus 1 → ℝ}, Continuous f → Continuous g →
      Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 => f p.1 * g p.2)
        ((ν : Measure (DGPS.Torus 1)).prod ν) := fun hf hg =>
    ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hform : ∀ p : DGPS.Torus 1 × DGPS.Torus 1,
      (secondHarmonicData κ).W p.1 p.2 =
        κ * ((mode 2 p.1).re * (mode 2 p.2).re) + κ * ((mode 2 p.1).im * (mode 2 p.2).im) - κ := by
    intro p
    show secondHarmonicW κ p.1 p.2 = _
    rw [secondHarmonicW, mode_re_sub]; ring
  unfold DGPS.interactionEnergy
  simp_rw [hform]
  have h1 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 =>
      κ * ((mode 2 p.1).re * (mode 2 p.2).re)) ((ν : Measure (DGPS.Torus 1)).prod ν) :=
    (hP hc hc).const_mul κ
  have h2 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 =>
      κ * ((mode 2 p.1).im * (mode 2 p.2).im)) ((ν : Measure (DGPS.Torus 1)).prod ν) :=
    (hP hs hs).const_mul κ
  have h12 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 =>
      κ * ((mode 2 p.1).re * (mode 2 p.2).re) + κ * ((mode 2 p.1).im * (mode 2 p.2).im))
      ((ν : Measure (DGPS.Torus 1)).prod ν) := h1.add h2
  rw [integral_sub h12 (integrable_const κ), integral_add h1 h2,
    integral_const_mul, integral_const_mul,
    integral_prod_mul (fun x => (mode 2 x).re) (fun x => (mode 2 x).re),
    integral_prod_mul (fun x => (mode 2 x).im) (fun x => (mode 2 x).im),
    normSq_secondHarmonicCoeff]
  simp
  ring


/-- `|ρ̂(2)|²` as a real number. -/
noncomputable def secondHarmonicMass (ν : ProbabilityMeasure (DGPS.Torus 1)) : ℝ :=
  Complex.normSq (secondHarmonicCoeff ν)

theorem secondHarmonicMass_nonneg (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    0 ≤ secondHarmonicMass ν := Complex.normSq_nonneg _

/-- The relative entropy to Haar, as an extended real. -/
noncomputable def secondHarmonicEntropy (ν : ProbabilityMeasure (DGPS.Torus 1)) : EReal :=
  ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal)

theorem freeEnergy_secondHarmonic (κ : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.freeEnergy (secondHarmonicData κ) ν =
      secondHarmonicEntropy ν + ((κ / 2 * secondHarmonicMass ν - κ / 2 : ℝ) : EReal) := by
  unfold DGPS.freeEnergy secondHarmonicEntropy
  have hV : DGPS.potentialEnergy (secondHarmonicData κ) ν = 0 := by
    simp [DGPS.potentialEnergy, secondHarmonicData]
  rw [hV, interactionEnergy_secondHarmonic, EReal.coe_zero, add_zero, secondHarmonicMass]
  congr 2
  ring

theorem freeEnergy_haar_secondHarmonic (κ : ℝ) :
    DGPS.freeEnergy (secondHarmonicData κ) (DGPS.haarProbability 1) = ((-κ / 2 : ℝ) : EReal) := by
  rw [freeEnergy_secondHarmonic]
  have h0 : secondHarmonicMass (DGPS.haarProbability 1) = 0 := by
    unfold secondHarmonicMass
    exact (congrArg Complex.normSq secondHarmonicCoeff_haar).trans Complex.normSq_zero
  have hH : secondHarmonicEntropy (DGPS.haarProbability 1) = 0 := by
    unfold secondHarmonicEntropy
    show ((DGPS.relativeEntropy (DGPS.haar 1) (DGPS.haar 1) : ℝ≥0∞) : EReal) = 0
    rw [DGPS.relativeEntropy_self]; rfl
  rw [hH, h0, zero_add]
  congr 1; ring

theorem secondHarmonic_lower_bound {κ : ℝ} (hκ : 0 < κ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    ((-κ / 2 : ℝ) : EReal) ≤ DGPS.freeEnergy (secondHarmonicData κ) ν := by
  rw [freeEnergy_secondHarmonic]
  have hH : (0 : EReal) ≤ secondHarmonicEntropy ν := by
    unfold secondHarmonicEntropy; exact EReal.coe_ennreal_nonneg _
  have hr : (-κ / 2 : ℝ) ≤ κ / 2 * secondHarmonicMass ν - κ / 2 := by
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ κ / 2) (secondHarmonicMass_nonneg ν)
    linarith
  calc ((-κ / 2 : ℝ) : EReal) = 0 + ((-κ / 2 : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add hH (EReal.coe_le_coe_iff.mpr hr)

theorem freeEnergyMinimum_secondHarmonic {κ : ℝ} (hκ : 0 < κ) :
    DGPS.freeEnergyMinimum (secondHarmonicData κ) = ((-κ / 2 : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf fun ν => secondHarmonic_lower_bound hκ ν)
  exact (iInf_le _ (DGPS.haarProbability 1)).trans (freeEnergy_haar_secondHarmonic κ).le

theorem secondHarmonic_unique_minimizer {κ : ℝ} (hκ : 0 < κ) (μ : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.freeEnergy (secondHarmonicData κ) μ = DGPS.freeEnergyMinimum (secondHarmonicData κ) ↔
      μ = DGPS.haarProbability 1 := by
  rw [freeEnergyMinimum_secondHarmonic hκ]
  constructor
  · intro h
    rw [freeEnergy_secondHarmonic] at h
    have hne : DGPS.relativeEntropy (μ : Measure (DGPS.Torus 1)) (DGPS.haar 1) ≠ ⊤ := by
      intro hT
      have : secondHarmonicEntropy μ = ⊤ := by
        unfold secondHarmonicEntropy; rw [hT]; rfl
      rw [this, EReal.top_add_coe] at h
      exact EReal.coe_ne_top _ h.symm
    set H := DGPS.relativeEntropy (μ : Measure (DGPS.Torus 1)) (DGPS.haar 1) with hHdef
    have hH : secondHarmonicEntropy μ = ((H.toReal : ℝ) : EReal) := by
      unfold secondHarmonicEntropy
      rw [← hHdef]
      exact (EReal.coe_ennreal_toReal hne).symm
    rw [hH, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    have hm := mul_nonneg (by positivity : (0 : ℝ) ≤ κ / 2) (secondHarmonicMass_nonneg μ)
    have hT0 : H.toReal = 0 := by
      have := ENNReal.toReal_nonneg (a := H)
      linarith
    have hH0 : H = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff H).mp hT0 with h0 | h0
      · exact h0
      · exact absurd h0 hne
    exact ProbabilityMeasure.toMeasure_injective
      ((DGPS.relativeEntropy_zero_iff (ν := (μ : Measure (DGPS.Torus 1))) (P := DGPS.haar 1)).mp hH0)
  · rintro rfl
    exact freeEnergy_haar_secondHarmonic κ

/-- The gap `G(ρ) = F(ρ) − F_*`. -/
noncomputable def secondHarmonicG (κ : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) : EReal :=
  DGPS.freeEnergy (secondHarmonicData κ) ν - DGPS.freeEnergyMinimum (secondHarmonicData κ)

theorem secondHarmonicG_eq {κ : ℝ} (hκ : 0 < κ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    secondHarmonicG κ ν = secondHarmonicEntropy ν + ((κ / 2 * secondHarmonicMass ν : ℝ) : EReal) := by
  unfold secondHarmonicG
  rw [freeEnergyMinimum_secondHarmonic hκ, freeEnergy_secondHarmonic, sub_eq_add_neg,
    add_assoc, ← EReal.coe_neg, ← EReal.coe_add]
  congr 2; ring


/-! ### Smoothness and Lipschitz regularity -/

theorem fourier_two_re_coe (a : ℝ) :
    (fourier 2 (a : AddCircle (1 : ℝ))).re = Real.cos (4 * Real.pi * a) := by
  have h2 : (2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) * (a : ℂ) / ((1 : ℝ) : ℂ) : ℂ) =
      ((4 * Real.pi * a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [fourier_coe_apply, h2, Complex.exp_ofReal_mul_I_re]

theorem abs_fourier_two_re_sub_le (t t' : AddCircle (1 : ℝ)) :
    |(fourier 2 t).re - (fourier 2 t').re| ≤ 4 * Real.pi * ‖t - t'‖ := by
  induction t using QuotientAddGroup.induction_on with | _ a => ?_
  induction t' using QuotientAddGroup.induction_on with | _ b => ?_
  rw [← QuotientAddGroup.mk_sub, AddCircle.norm_eq, fourier_two_re_coe, fourier_two_re_coe]
  set n : ℤ := round ((1 : ℝ)⁻¹ * (a - b)) with hn
  have hcos : Real.cos (4 * Real.pi * a) = Real.cos (4 * Real.pi * (b + (a - b - n * 1))) := by
    have : 4 * Real.pi * a = 4 * Real.pi * (b + (a - b - n * 1)) + ((2 * n : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  rw [hcos]
  refine (Real.abs_cos_sub_cos_le _ _).trans ?_
  have : 4 * Real.pi * (b + (a - b - n * 1)) - 4 * Real.pi * b = 4 * Real.pi * (a - b - n * 1) := by
    ring
  rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]

theorem torusDist_one (x y : DGPS.Torus 1) : DGPS.torusDist x y = ‖x 0 - y 0‖ := by
  unfold DGPS.torusDist SharpLSI.flatDist
  simp [Real.sqrt_sq]

theorem secondHarmonicW_eq (κ : ℝ) (x y : DGPS.Torus 1) :
    secondHarmonicW κ x y = κ * ((fourier 2 (x 0 - y 0)).re - 1) := by
  rw [secondHarmonicW, mode_apply]; rfl

theorem lipschitzData_secondHarmonic (κ : ℝ) :
    DGPS.LipschitzData (secondHarmonicData κ) := by
  refine ⟨⟨0, fun x y => by simp [secondHarmonicData]⟩, ?_⟩
  rw [DGPS.LipschitzData.W_lipschitz_sum_iff]
  refine ⟨|κ| * (4 * Real.pi), fun x y x' y' => ?_⟩
  show |secondHarmonicW κ x y - secondHarmonicW κ x' y'| ≤ _
  rw [secondHarmonicW_eq, secondHarmonicW_eq, torusDist_one, torusDist_one]
  have h1 := abs_fourier_two_re_sub_le (x 0 - y 0) (x' 0 - y' 0)
  have h2 : ‖(x 0 - y 0) - (x' 0 - y' 0)‖ ≤ ‖x 0 - x' 0‖ + ‖y 0 - y' 0‖ := by
    have : (x 0 - y 0) - (x' 0 - y' 0) = (x 0 - x' 0) - (y 0 - y' 0) := by abel
    rw [this]; exact norm_sub_le _ _
  have h3 : κ * ((fourier 2 (x 0 - y 0)).re - 1) - κ * ((fourier 2 (x' 0 - y' 0)).re - 1) =
      κ * ((fourier 2 (x 0 - y 0)).re - (fourier 2 (x' 0 - y' 0)).re) := by ring
  rw [h3, abs_mul]
  calc |κ| * |(fourier 2 (x 0 - y 0)).re - (fourier 2 (x' 0 - y' 0)).re|
      ≤ |κ| * (4 * Real.pi * ‖(x 0 - y 0) - (x' 0 - y' 0)‖) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ |κ| * (4 * Real.pi * (‖x 0 - x' 0‖ + ‖y 0 - y' 0‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (abs_nonneg _)
    _ = _ := by ring

theorem contDiff_secondHarmonicW_lift (κ : ℝ) :
    ContDiff ℝ ∞ (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      secondHarmonicW κ (DGPS.torusLift p.1) (DGPS.torusLift p.2)) := by
  simp_rw [secondHarmonicW_lift]
  fun_prop


/-- **FIN086.** The repulsive second-harmonic model: `V = 0`, `W(x,y) = κ[cos 4π(x−y) − 1]` is a
smooth (hence Lipschitz) symmetric zero-diagonal interaction; `F(ρ) = H(ρ|m) + (κ/2)|ρ̂(2)|² − κ/2`,
`F_* = −κ/2`, `G = F − F_* = H(ρ|m) + (κ/2)|ρ̂(2)|²`, and Haar measure is the unique minimizer. -/
theorem second_harmonic_model_and_free_energy (κ : ℝ) (hκ : 0 < κ) :
    (∀ x, (secondHarmonicData κ).V x = 0) ∧
    (∀ a b : Fin 1 → ℝ, (secondHarmonicData κ).W (DGPS.torusLift a) (DGPS.torusLift b) =
      κ * (Real.cos (4 * Real.pi * (a 0 - b 0)) - 1)) ∧
    ContDiff ℝ ∞ (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      (secondHarmonicData κ).W (DGPS.torusLift p.1) (DGPS.torusLift p.2)) ∧
    DGPS.LipschitzData (secondHarmonicData κ) ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1),
      DGPS.freeEnergy (secondHarmonicData κ) ν =
        ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
          ((κ / 2 * Complex.normSq (secondHarmonicCoeff ν) - κ / 2 : ℝ) : EReal)) ∧
    DGPS.freeEnergyMinimum (secondHarmonicData κ) = ((-κ / 2 : ℝ) : EReal) ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1),
      secondHarmonicG κ ν =
        ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
          ((κ / 2 * Complex.normSq (secondHarmonicCoeff ν) : ℝ) : EReal)) ∧
    (∀ μ : ProbabilityMeasure (DGPS.Torus 1),
      DGPS.freeEnergy (secondHarmonicData κ) μ = DGPS.freeEnergyMinimum (secondHarmonicData κ) ↔
        μ = DGPS.haarProbability 1) :=
  ⟨fun _ => rfl, secondHarmonicW_lift κ, contDiff_secondHarmonicW_lift κ,
    lipschitzData_secondHarmonic κ, freeEnergy_secondHarmonic κ,
    freeEnergyMinimum_secondHarmonic hκ, secondHarmonicG_eq hκ,
    secondHarmonic_unique_minimizer hκ⟩

/-! ### Particle symmetries (FIN089) -/

/-- The half-period shift `(1/2, …)` of the circle `𝕋^1`. -/
noncomputable def halfShift : DGPS.Torus 1 := fun _ => ((1 / 2 : ℝ) : AddCircle (1 : ℝ))

theorem mode_add (k : ℤ) (x y : DGPS.Torus 1) : mode k (x + y) = mode k x * mode k y := by
  simp only [mode_apply, Pi.add_apply]
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem mode_two_halfShift : mode 2 halfShift = 1 := by
  rw [mode_apply, halfShift, fourier_coe_apply]
  have : (2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) * (((1 / 2 : ℝ)) : ℂ) / ((1 : ℝ) : ℂ) : ℂ) =
      2 * Real.pi * Complex.I := by push_cast; ring
  rw [this]; exact Complex.exp_two_pi_mul_I

theorem mode_one_halfShift : mode 1 halfShift = -1 := by
  rw [mode_apply, halfShift, fourier_coe_apply]
  have : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (((1 / 2 : ℝ)) : ℂ) / ((1 : ℝ) : ℂ) : ℂ) =
      Real.pi * Complex.I := by push_cast; ring
  rw [this]; exact Complex.exp_pi_mul_I

theorem normSq_mode (k : ℤ) (x : DGPS.Torus 1) : Complex.normSq (mode k x) = 1 := by
  rw [mode_apply, Complex.normSq_eq_norm_sq]
  simp

theorem hamiltonian_eq (κ : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian (secondHarmonicData κ) N x =
      κ * Complex.normSq (∑ i, mode 2 (x i)) / (2 * (N : ℝ)) - κ * (N : ℝ) / 2 := by
  have hN : (N : ℝ) ≠ 0 := by positivity
  have h1 : Complex.normSq (∑ i, mode 2 (x i)) = ∑ i, ∑ j, (mode 2 (x i - x j)).re := by
    have := Complex.mul_conj (∑ i, mode 2 (x i))
    have h2 := congrArg Complex.re this
    rw [Complex.ofReal_re] at h2
    rw [← h2, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mode_sub]
  unfold DGPS.particleHamiltonian
  simp only [secondHarmonicData, secondHarmonicW, Finset.sum_const_zero, zero_add]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, h1]
  simp
  field_simp

/-- Translation by `c` preserves the Gibbs law when it preserves `H_N`. -/
theorem map_add_particleLaw {d : ℕ} (A : DGPS.InteractionData d) (N : ℕ+)
    (c : DGPS.ParticleSpace d N)
    (hH : ∀ x, DGPS.particleHamiltonian A N (fun i => x i + c i) = DGPS.particleHamiltonian A N x) :
    (DGPS.particleLaw A N).map (fun x i => x i + c i) = DGPS.particleLaw A N := by
  have : (DGPS.particleHaar d N).IsAddRightInvariant := by
    have := Measure.pi.isAddLeftInvariant (fun _ : Fin N => (volume : Measure (DGPS.Torus d)))
    unfold DGPS.particleHaar
    infer_instance
  have hmp : MeasurePreserving (fun x : DGPS.ParticleSpace d N => fun i => x i + c i)
      (DGPS.particleHaar d N) (DGPS.particleHaar d N) :=
    measurePreserving_add_right (DGPS.particleHaar d N) c
  have hT : Measurable (fun x : DGPS.ParticleSpace d N => fun i => x i + c i) := hmp.measurable
  have hE : MeasurableEmbedding (fun x : DGPS.ParticleSpace d N => fun i => x i + c i) :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  ext s hs
  rw [Measure.map_apply hT hs, DGPS.particleLaw,
    withDensity_apply _ (hT hs), withDensity_apply _ hs]
  have hρ : Measurable fun x => ENNReal.ofReal (DGPS.particleDensity A N x) :=
    (DGPS.Particle.particleDensity_measurable A N).ennreal_ofReal
  rw [← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  have : (fun x => ((fun x : DGPS.ParticleSpace d N => fun i => x i + c i) ⁻¹' s).indicator
      (fun x => ENNReal.ofReal (DGPS.particleDensity A N x)) x) =
      fun x => s.indicator (fun x => ENNReal.ofReal (DGPS.particleDensity A N x))
        (fun i => x i + c i) := by
    funext x
    by_cases h : (fun i => x i + c i) ∈ s <;>
      simp [Set.indicator, h, DGPS.particleDensity, hH]
  rw [this]
  exact hmp.lintegral_comp_emb hE _

/-- The shift by a half period of exactly the coordinates in `s`. -/
noncomputable def halfShiftOn {N : ℕ+} (s : Finset (Fin N)) : DGPS.ParticleSpace 1 N :=
  fun i => if i ∈ s then halfShift else 0

theorem hamiltonian_rotate (κ : ℝ) (N : ℕ+) (t : DGPS.Torus 1) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian (secondHarmonicData κ) N (fun i => x i + t) =
      DGPS.particleHamiltonian (secondHarmonicData κ) N x := by
  rw [hamiltonian_eq, hamiltonian_eq]
  simp_rw [mode_add]
  rw [← Finset.sum_mul, Complex.normSq_mul, normSq_mode, mul_one]

theorem hamiltonian_halfShift (κ : ℝ) (N : ℕ+) (s : Finset (Fin N)) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian (secondHarmonicData κ) N (fun i => x i + halfShiftOn s i) =
      DGPS.particleHamiltonian (secondHarmonicData κ) N x := by
  rw [hamiltonian_eq, hamiltonian_eq]
  have : ∀ i, mode 2 (x i + halfShiftOn s i) = mode 2 (x i) := fun i => by
    unfold halfShiftOn
    split_ifs
    · rw [mode_add, mode_two_halfShift, mul_one]
    · rw [add_zero]
  simp_rw [this]

theorem hamiltonian_permute (κ : ℝ) (N : ℕ+) (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian (secondHarmonicData κ) N (DGPS.permuteParticles σ x) =
      DGPS.particleHamiltonian (secondHarmonicData κ) N x :=
  DGPS.particleHamiltonian_permute _ σ x

theorem integral_eq_zero_of_invariant_neg {N : ℕ+} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : Measure (DGPS.ParticleSpace 1 N))
    (T : DGPS.ParticleSpace 1 N → DGPS.ParticleSpace 1 N) (hT : Measurable T) (hP : P.map T = P)
    (F : DGPS.ParticleSpace 1 N → E) (hF : Continuous F) (hneg : ∀ x, F (T x) = -F x) :
    ∫ x, F x ∂P = 0 := by
  have h1 : ∫ x, F x ∂P = ∫ x, F (T x) ∂P := by
    conv_lhs => rw [← hP]
    exact integral_map hT.aemeasurable hF.aestronglyMeasurable
  simp_rw [hneg, integral_neg] at h1
  have : (2 : ℝ) • ∫ x, F x ∂P = 0 := by
    rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

theorem map_eval_particleLaw {N : ℕ+} (A : DGPS.InteractionData 1)
    (hrot : ∀ t : DGPS.Torus 1, (DGPS.particleLaw A N).map (fun x i => x i + t) = DGPS.particleLaw A N)
    (i : Fin N) :
    (DGPS.particleLaw A N).map (fun x => x i) = DGPS.haar 1 := by
  have : IsProbabilityMeasure (DGPS.particleLaw A N) :=
    DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  set μ := (DGPS.particleLaw A N).map (fun x => x i) with hμ
  have hev : Measurable (fun x : DGPS.ParticleSpace 1 N => x i) := measurable_pi_apply i
  have : IsProbabilityMeasure μ :=
    ⟨by rw [hμ, Measure.map_apply hev MeasurableSet.univ]; simp⟩
  have : μ.IsAddLeftInvariant := ⟨fun t => by
    have hsh : (fun y : DGPS.Torus 1 => t + y) ∘ (fun x : DGPS.ParticleSpace 1 N => x i) =
        (fun x : DGPS.ParticleSpace 1 N => x i) ∘ (fun x i => x i + t) := by
      funext x; simp [add_comm]
    rw [hμ, Measure.map_map (measurable_const_add t) hev, hsh,
      ← Measure.map_map hev (Measurable.of_eval fun j => (measurable_pi_apply j).add_const t),
      hrot t]⟩
  have hu := Measure.addHaarMeasure_unique μ (⊤ : TopologicalSpace.PositiveCompacts (DGPS.Torus 1))
  have hv := Measure.addHaarMeasure_unique (DGPS.haar 1)
    (⊤ : TopologicalSpace.PositiveCompacts (DGPS.Torus 1))
  have hu1 : μ ((⊤ : TopologicalSpace.PositiveCompacts (DGPS.Torus 1)) : Set (DGPS.Torus 1)) = 1 :=
    measure_univ
  have hv1 : DGPS.haar 1 ((⊤ : TopologicalSpace.PositiveCompacts (DGPS.Torus 1)) :
      Set (DGPS.Torus 1)) = 1 := measure_univ
  rw [hu1, one_smul] at hu
  rw [hv1, one_smul] at hv
  exact hu.trans hv.symm

/-- **FIN089.** For `H_N = κ|Σᵢ e^{4πi xᵢ}|²/(2N) − κN/2` (the Hamiltonian of the second-harmonic
model): the closed formula holds; `H_N` and the Gibbs law `P_N` are invariant under common
rotations, under the half-period shift of any set of coordinates, and under particle permutations;
every tagged marginal of `P_N` is Haar; and for distinct labels the first-harmonic cross moments
(`cos·cos`, and the complex `e^{2πi xᵢ}·e^{±2πi xⱼ}`) vanish. -/
theorem second_harmonic_particle_symmetries (κ : ℝ) (N : ℕ+) :
    (∀ x : DGPS.ParticleSpace 1 N,
      DGPS.particleHamiltonian (secondHarmonicData κ) N x =
        κ * Complex.normSq (∑ i, mode 2 (x i)) / (2 * (N : ℝ)) - κ * (N : ℝ) / 2) ∧
    (∀ (t : DGPS.Torus 1) (x : DGPS.ParticleSpace 1 N),
      DGPS.particleHamiltonian (secondHarmonicData κ) N (fun i => x i + t) =
        DGPS.particleHamiltonian (secondHarmonicData κ) N x) ∧
    (∀ (s : Finset (Fin N)) (x : DGPS.ParticleSpace 1 N),
      DGPS.particleHamiltonian (secondHarmonicData κ) N
          (fun i => if i ∈ s then x i + halfShift else x i) =
        DGPS.particleHamiltonian (secondHarmonicData κ) N x) ∧
    (∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
      DGPS.particleHamiltonian (secondHarmonicData κ) N (DGPS.permuteParticles σ x) =
        DGPS.particleHamiltonian (secondHarmonicData κ) N x) ∧
    (∀ t : DGPS.Torus 1,
      (DGPS.particleLaw (secondHarmonicData κ) N).map (fun x i => x i + t) =
        DGPS.particleLaw (secondHarmonicData κ) N) ∧
    (∀ s : Finset (Fin N),
      (DGPS.particleLaw (secondHarmonicData κ) N).map
          (fun x i => if i ∈ s then x i + halfShift else x i) =
        DGPS.particleLaw (secondHarmonicData κ) N) ∧
    (∀ σ : Equiv.Perm (Fin N),
      (DGPS.particleLaw (secondHarmonicData κ) N).map (DGPS.permuteParticles σ) =
        DGPS.particleLaw (secondHarmonicData κ) N) ∧
    (∀ i : Fin N,
      (DGPS.particleLaw (secondHarmonicData κ) N).map (fun x => x i) = DGPS.haar 1) ∧
    (∀ i j : Fin N, i ≠ j →
      ∫ x, (mode 1 (x i)).re * (mode 1 (x j)).re ∂DGPS.particleLaw (secondHarmonicData κ) N = 0 ∧
      ∫ x, mode 1 (x i) * mode 1 (x j) ∂DGPS.particleLaw (secondHarmonicData κ) N = 0 ∧
      ∫ x, mode 1 (x i) * (starRingEnd ℂ) (mode 1 (x j))
        ∂DGPS.particleLaw (secondHarmonicData κ) N = 0) := by
  have hshift : ∀ s : Finset (Fin N), (fun (x : DGPS.ParticleSpace 1 N) (i : Fin N) =>
      if i ∈ s then x i + halfShift else x i) = fun x i => x i + halfShiftOn s i := by
    intro s; funext x i; unfold halfShiftOn; split_ifs <;> simp
  have hrot := fun t : DGPS.Torus 1 => map_add_particleLaw (secondHarmonicData κ) N (fun _ => t)
    (hamiltonian_rotate κ N t)
  have hhalf : ∀ s : Finset (Fin N),
      (DGPS.particleLaw (secondHarmonicData κ) N).map
          (fun x i => if i ∈ s then x i + halfShift else x i) =
        DGPS.particleLaw (secondHarmonicData κ) N := fun s => by
    rw [hshift s]
    exact map_add_particleLaw (secondHarmonicData κ) N (halfShiftOn s) (hamiltonian_halfShift κ N s)
  refine ⟨hamiltonian_eq κ N, hamiltonian_rotate κ N, fun s x => ?_,
    hamiltonian_permute κ N, hrot, hhalf,
    fun σ => (DGPS.permutation_preserves_gibbs_energy _ N σ).1,
    map_eval_particleLaw _ hrot, fun i j hij => ?_⟩
  · have h := congrFun (hshift s) x
    rw [h]; exact hamiltonian_halfShift κ N s x
  · have hT := hhalf {i}
    have hTm : Measurable (fun (x : DGPS.ParticleSpace 1 N) (k : Fin N) =>
        if k ∈ ({i} : Finset (Fin N)) then x k + halfShift else x k) :=
      Measurable.of_eval fun k => by
        show Measurable fun x : DGPS.ParticleSpace 1 N =>
          if k ∈ ({i} : Finset (Fin N)) then x k + halfShift else x k
        split_ifs
        · exact (measurable_pi_apply k).add (measurable_const : Measurable fun _ : DGPS.ParticleSpace 1 N => halfShift)
        · exact measurable_pi_apply k
    have hci : ∀ x : DGPS.ParticleSpace 1 N, mode 1 ((fun (x : DGPS.ParticleSpace 1 N) (k : Fin N) =>
        if k ∈ ({i} : Finset (Fin N)) then x k + halfShift else x k) x i) = - mode 1 (x i) := by
      intro x; simp [mode_add, mode_one_halfShift]
    have hcj : ∀ x : DGPS.ParticleSpace 1 N, ((fun (x : DGPS.ParticleSpace 1 N) (k : Fin N) =>
        if k ∈ ({i} : Finset (Fin N)) then x k + halfShift else x k) x j) = x j := by
      intro x; simp [hij.symm]
    have hm1 := continuous_mode 1
    refine ⟨?_, ?_, ?_⟩
    · refine integral_eq_zero_of_invariant_neg _ _ hTm hT _ ?_ fun x => ?_
      · fun_prop
      · simp only [hci, hcj, Complex.neg_re]; ring
    · refine integral_eq_zero_of_invariant_neg _ _ hTm hT _ ?_ fun x => ?_
      · fun_prop
      · simp only [hci, hcj]; ring
    · refine integral_eq_zero_of_invariant_neg _ _ hTm hT _ ?_ fun x => ?_
      · fun_prop
      · simp only [hci, hcj]; ring

/-! ### FIN087: scalar and species dissipation -/

/-- `A cos 4πx + B sin 4πx + K` on the circle. -/
noncomputable def trig (A B K : ℝ) : DGPS.Torus 1 → ℝ :=
  fun x => A * (mode 2 x).re + B * (mode 2 x).im + K

theorem trig_lift (A B K : ℝ) (a : Fin 1 → ℝ) :
    trig A B K (DGPS.torusLift a) = A * Real.cos (4 * Real.pi * a 0) + B * Real.sin (4 * Real.pi * a 0) + K := by
  have h2 : (2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) * (a 0 : ℝ) : ℂ) =
      ((4 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  simp only [trig, mode_lift, h2, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem isSmoothPeriodic_trig (A B K : ℝ) : DGPS.IsSmoothPeriodic (trig A B K) := by
  unfold DGPS.IsSmoothPeriodic
  have : (trig A B K ∘ DGPS.torusLift) = fun a : Fin 1 → ℝ =>
      A * Real.cos (4 * Real.pi * a 0) + B * Real.sin (4 * Real.pi * a 0) + K := by
    funext a; exact trig_lift A B K a
  rw [this]
  fun_prop

theorem coordPartial_re_mode (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (fun y => (mode 2 y).re) x = -(4 * Real.pi) * (mode 2 x).im := by
  have := DGPS.coordPartial_re_mFourier (d := 1) (fun _ => (2 : ℤ)) 0 x
  simp only [mode]
  rw [this]
  have e : (2 * (Real.pi : ℂ) * Complex.I * (((fun _ : Fin 1 => (2 : ℤ)) 0 : ℤ) : ℂ) *
      (mFourier fun _ : Fin 1 => (2 : ℤ)) x) =
      ((4 * Real.pi : ℝ) : ℂ) * (Complex.I * (mFourier fun _ : Fin 1 => (2 : ℤ)) x) := by
    push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

theorem coordPartial_im_mode (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (fun y => (mode 2 y).im) x = (4 * Real.pi) * (mode 2 x).re := by
  have := DGPS.coordPartial_im_mFourier (d := 1) (fun _ => (2 : ℤ)) 0 x
  simp only [mode]
  rw [this]
  have e : (2 * (Real.pi : ℂ) * Complex.I * (((fun _ : Fin 1 => (2 : ℤ)) 0 : ℤ) : ℂ) *
      (mFourier fun _ : Fin 1 => (2 : ℤ)) x) =
      ((4 * Real.pi : ℝ) : ℂ) * (Complex.I * (mFourier fun _ : Fin 1 => (2 : ℤ)) x) := by
    push_cast; ring
  rw [e, Complex.im_ofReal_mul, Complex.I_mul_im]

theorem isSmoothPeriodic_re_mode : DGPS.IsSmoothPeriodic (fun y => (mode 2 y).re) := by
  have e : (fun y => (mode 2 y).re) = trig 1 0 0 := by
    funext y; simp [trig]
  rw [e]; exact isSmoothPeriodic_trig 1 0 0

theorem isSmoothPeriodic_im_mode : DGPS.IsSmoothPeriodic (fun y => (mode 2 y).im) := by
  have e : (fun y => (mode 2 y).im) = trig 0 1 0 := by
    funext y; simp [trig]
  rw [e]; exact isSmoothPeriodic_trig 0 1 0

theorem coordPartial_trig (A B K : ℝ) (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (trig A B K) x = trig (4 * Real.pi * B) (-(4 * Real.pi) * A) 0 x := by
  have h1 : DifferentiableAt ℝ ((fun y => (mode 2 y).re) ∘ DGPS.torusLift) (SharpLSI.secT x) :=
    (isSmoothPeriodic_re_mode.differentiable (by simp)) _
  have h2 : DifferentiableAt ℝ ((fun y => (mode 2 y).im) ∘ DGPS.torusLift) (SharpLSI.secT x) :=
    (isSmoothPeriodic_im_mode.differentiable (by simp)) _
  have e : (trig A B K ∘ DGPS.torusLift) = fun a =>
      A * ((fun y => (mode 2 y).re) ∘ DGPS.torusLift) a +
        B * ((fun y => (mode 2 y).im) ∘ DGPS.torusLift) a + K := rfl
  have hc1 := coordPartial_re_mode x
  have hc2 := coordPartial_im_mode x
  unfold DGPS.coordPartial at hc1 hc2 ⊢
  rw [e, fderiv_add_const, fderiv_fun_add (h1.const_mul A) (h2.const_mul B),
    fderiv_const_mul h1, fderiv_const_mul h2]
  simp only [add_apply, smul_apply, smul_eq_mul, hc1, hc2,
    trig]
  ring

/-- The cosine convolution `x ↦ ∫ cos 4π(x - y) dν(y)`. -/
noncomputable def secondHarmonicCosConv (ν : Measure (DGPS.Torus 1)) : DGPS.Torus 1 → ℝ :=
  fun x => ∫ y, (mode 2 (x - y)).re ∂ν

theorem integrable_mode_re (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    Integrable (fun y => (mode 2 y).re) ν :=
  (Complex.continuous_re.comp (continuous_mode 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_mode_im (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    Integrable (fun y => (mode 2 y).im) ν :=
  (Complex.continuous_im.comp (continuous_mode 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem cosConv_eq_trig (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    secondHarmonicCosConv ν = trig (∫ y, (mode 2 y).re ∂ν) (∫ y, (mode 2 y).im ∂ν) 0 := by
  funext x
  unfold secondHarmonicCosConv trig
  simp_rw [mode_re_sub]
  rw [integral_add ((integrable_mode_re ν).const_mul _) ((integrable_mode_im ν).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem interactionPotential_secondHarmonic (κ : ℝ) (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.interactionPotential (secondHarmonicData κ) ρ =
      trig (κ * ∫ y, (mode 2 y).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))
        (κ * ∫ y, (mode 2 y).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) (-κ) := by
  funext x
  have hc := congrFun (cosConv_eq_trig (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) x
  unfold secondHarmonicCosConv at hc
  unfold DGPS.interactionPotential
  have hW : ∀ y, (secondHarmonicData κ).W x y = κ * (mode 2 (x - y)).re - κ := fun y => by
    show secondHarmonicW κ x y = _
    rw [secondHarmonicW]; ring
  simp_rw [hW]
  have hi : Integrable (fun y => (mode 2 (x - y)).re) (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) := by
    simp_rw [mode_re_sub]
    exact ((integrable_mode_re _).const_mul _).add ((integrable_mode_im _).const_mul _)
  rw [integral_sub (hi.const_mul κ) (integrable_const κ), integral_const_mul, hc]
  simp only [secondHarmonicData, trig]
  simp
  ring

theorem coordPartial_coordPartial_trig (A B K : ℝ) (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (DGPS.coordPartial 0 (trig A B K)) x =
      -(16 * Real.pi ^ 2) * (trig A B 0 x) := by
  have e1 : DGPS.coordPartial 0 (trig A B K) = trig (4 * Real.pi * B) (-(4 * Real.pi) * A) 0 := by
    funext y; exact coordPartial_trig A B K y
  rw [e1, coordPartial_trig]
  simp only [trig]
  ring

theorem coordPartial_trig_fun (A B K : ℝ) :
    DGPS.coordPartial 0 (trig A B K) = trig (4 * Real.pi * B) (-(4 * Real.pi) * A) 0 := by
  funext y; exact coordPartial_trig A B K y

theorem isWeakGradientLp_one_of_smooth {φ : DGPS.Torus 1 → ℝ} (hφ : DGPS.IsSmoothPeriodic φ) :
    DGPS.IsWeakGradientLp 1 φ (DGPS.smoothGrad φ) := by
  have h := hφ.isWeakGradient
  exact ⟨h.memLp.mono_exponent (by norm_num), h.memLp_grad.mono_exponent (by norm_num), h.ibp⟩

theorem force_ae_secondHarmonic (κ : ℝ) (b : DGPS.AbsoluteDrift (secondHarmonicData κ))
    (ρ : DGPS.AbsoluteDensity 1) :
    ∀ᵐ x ∂DGPS.haar 1, (b.force ρ x) 0 =
      κ * DGPS.coordPartial 0
        (trig (∫ y, (mode 2 y).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))
          (∫ y, (mode 2 y).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) 0) x := by
  have hP := interactionPotential_secondHarmonic κ ρ
  have hg : DGPS.IsWeakGradientLp 1 (DGPS.interactionPotential (secondHarmonicData κ) ρ)
      (DGPS.smoothGrad (trig (κ * ∫ y, (mode 2 y).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))
        (κ * ∫ y, (mode 2 y).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) (-κ))) := by
    rw [hP]; exact isWeakGradientLp_one_of_smooth (isSmoothPeriodic_trig _ _ _)
  have := b.ae_eq_of_isWeakGradient ρ hg
  filter_upwards [this] with x hx
  rw [hx]
  simp only [DGPS.smoothGrad_apply]
  rw [coordPartial_trig, coordPartial_trig]
  simp only [trig]
  ring

theorem integral_densityMeasure (ρ : DGPS.AbsoluteDensity 1) (f : DGPS.Torus 1 → ℝ) :
    ∫ x, f x ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) =
      ∫ x, ρ.density x * f x ∂DGPS.haar 1 := by
  rw [DGPS.densityMeasure_coe]
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [DGPS.AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]
  · exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem exists_bound_trig (A B K : ℝ) : ∃ c : ℝ, ∀ x, ‖trig A B K x‖ ≤ c := by
  obtain ⟨c, hc⟩ := isCompact_univ.exists_bound_of_continuousOn
    (isSmoothPeriodic_trig A B K).continuous_torus.continuousOn
  exact ⟨c, fun x => hc x (Set.mem_univ x)⟩

theorem score_integral (ρ : DGPS.AbsoluteDensity 1) (C S κ : ℝ) (f : DGPS.Torus 1 → DGPS.Tangent 1)
    (hf : ∀ᵐ x ∂DGPS.haar 1, f x 0 = κ * trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x) :
    Integrable (fun x => ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • f x‖ ^ 2)
      (DGPS.haar 1) ∧
    ∫ x, ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • f x‖ ^ 2 ∂DGPS.haar 1 =
      DGPS.Analysis.circleFisherInformation ρ +
        2 * κ * (16 * Real.pi ^ 2) * ∫ x, ρ.density x * trig C S 0 x ∂DGPS.haar 1 +
        κ ^ 2 * ∫ x, ρ.density x * trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2 ∂DGPS.haar 1 := by
  set g := DGPS.weakGradient ρ.sqrt ρ.sqrt_mem with hgdef
  set ψ := trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 with hψdef
  have hψ : DGPS.IsSmoothPeriodic ψ := isSmoothPeriodic_trig _ _ _
  have hwg : DGPS.IsWeakGradient ρ.sqrt g := DGPS.isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨c, hc⟩ := exists_bound_trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0
  have hpt : ∀ᵐ x ∂DGPS.haar 1, ‖(2 : ℝ) • g x + ρ.sqrt x • f x‖ ^ 2 =
      4 * (g x 0) ^ 2 + (4 * κ) * (ρ.sqrt x * g x 0 * ψ x) + κ ^ 2 * (ρ.density x * ψ x ^ 2) := by
    filter_upwards [hf] with x hx
    rw [DGPS.tangent_norm_sq]
    simp only [Fin.sum_univ_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx,
      DGPS.AbsoluteDensity.density]
    ring
  have hg2 : Integrable (fun x => (g x 0) ^ 2) (DGPS.haar 1) :=
    (DGPS.haar_circle_lsi ρ).2.1.congr (Filter.Eventually.of_forall fun x => by
      show ‖g x‖ ^ 2 = _
      rw [DGPS.tangent_norm_sq]; simp)
  have hug : Integrable (fun x => ρ.sqrt x * g x 0) (DGPS.haar 1) :=
    ρ.memLp_sqrt.integrable_mul (DGPS.memLp_coord hwg.memLp_grad 0)
  have hI2 : Integrable (fun x => ρ.sqrt x * g x 0 * ψ x) (DGPS.haar 1) :=
    hug.mul_bdd hψ.continuous_torus.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hc x)
  have hI3 : Integrable (fun x => ρ.density x * ψ x ^ 2) (DGPS.haar 1) := by
    refine ρ.integrable_density.mul_bdd (c := c ^ 2)
      (hψ.continuous_torus.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have := hc x
    rw [Real.norm_eq_abs] at this ⊢
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hint : Integrable (fun x => 4 * (g x 0) ^ 2 + (4 * κ) * (ρ.sqrt x * g x 0 * ψ x) +
      κ ^ 2 * (ρ.density x * ψ x ^ 2)) (DGPS.haar 1) :=
    ((hg2.const_mul 4).add (hI2.const_mul _)).add (hI3.const_mul _)
  refine ⟨hint.congr (hpt.mono fun x hx => hx.symm), ?_⟩
  have h1 : Integrable (fun x => 4 * (g x 0) ^ 2) (DGPS.haar 1) := hg2.const_mul 4
  have h2 : Integrable (fun x => (4 * κ) * (ρ.sqrt x * g x 0 * ψ x)) (DGPS.haar 1) := hI2.const_mul _
  have h3 : Integrable (fun x => κ ^ 2 * (ρ.density x * ψ x ^ 2)) (DGPS.haar 1) := hI3.const_mul _
  have h12 : Integrable (fun x => 4 * (g x 0) ^ 2 + (4 * κ) * (ρ.sqrt x * g x 0 * ψ x)) (DGPS.haar 1) :=
    h1.add h2
  rw [integral_congr_ae hpt, integral_add h12 h3, integral_add h1 h2, integral_const_mul,
    integral_const_mul, integral_const_mul]
  -- the Fisher information
  have hF : DGPS.Analysis.circleFisherInformation ρ = 4 * ∫ x, (g x 0) ^ 2 ∂DGPS.haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖g x‖ ^ 2 = _
    rw [DGPS.tangent_norm_sq]; simp
  -- integration by parts against the smooth test function ψ
  have hib := (DGPS.density_gradient ρ).1.ibp ψ hψ 0
  have hψ' : DGPS.coordPartial 0 ψ = fun x => -(16 * Real.pi ^ 2) * trig C S 0 x := by
    funext x
    have := coordPartial_coordPartial_trig C S 0 x
    rw [coordPartial_trig_fun] at this
    exact this
  rw [hψ'] at hib
  simp only [PiLp.smul_apply, smul_eq_mul] at hib
  have hL : ∫ x, ρ.density x * (-(16 * Real.pi ^ 2) * trig C S 0 x) ∂DGPS.haar 1 =
      -(16 * Real.pi ^ 2) * ∫ x, ρ.density x * trig C S 0 x ∂DGPS.haar 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hR : ∫ x, 2 * ρ.sqrt x * g x 0 * ψ x ∂DGPS.haar 1 =
      2 * ∫ x, ρ.sqrt x * g x 0 * ψ x ∂DGPS.haar 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hL, hR] at hib
  rw [hF]
  linear_combination (2 * κ) * hib

theorem integrable_density_mul_trig (σ : DGPS.AbsoluteDensity 1) (A B K : ℝ) :
    Integrable (fun x => σ.density x * trig A B K x) (DGPS.haar 1) := by
  obtain ⟨c, hc⟩ := exists_bound_trig A B K
  exact σ.integrable_density.mul_bdd (isSmoothPeriodic_trig A B K).continuous_torus.aestronglyMeasurable
    (Filter.Eventually.of_forall hc)

theorem integrable_density_mul_trig_sq (σ : DGPS.AbsoluteDensity 1) (A B K : ℝ) :
    Integrable (fun x => σ.density x * trig A B K x ^ 2) (DGPS.haar 1) := by
  obtain ⟨c, hc⟩ := exists_bound_trig A B K
  refine σ.integrable_density.mul_bdd (c := c ^ 2)
    ((isSmoothPeriodic_trig A B K).continuous_torus.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have := hc x
  rw [Real.norm_eq_abs] at this ⊢
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

theorem integral_density_mul_trig (σ : DGPS.AbsoluteDensity 1) (A B : ℝ) :
    ∫ x, σ.density x * trig A B 0 x ∂DGPS.haar 1 =
      A * ∫ y, (mode 2 y).re ∂(DGPS.densityMeasure σ : Measure (DGPS.Torus 1)) +
        B * ∫ y, (mode 2 y).im ∂(DGPS.densityMeasure σ : Measure (DGPS.Torus 1)) := by
  rw [← integral_densityMeasure σ (trig A B 0)]
  simp only [trig, add_zero]
  rw [integral_add ((integrable_mode_re _).const_mul _) ((integrable_mode_im _).const_mul _),
    integral_const_mul, integral_const_mul]

theorem barycenter_integral (F : DGPS.SpeciesFamily 1) (φ : DGPS.Torus 1 → ℝ)
    (h : ∀ s, Integrable (fun x => (F.density s).density x * φ x) (DGPS.haar 1)) :
    ∑ s, F.weight s * ∫ x, (F.density s).density x * φ x ∂DGPS.haar 1 =
      ∫ x, (DGPS.barycenter F).density x * φ x ∂DGPS.haar 1 := by
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun s _ => (h s).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [F.barycenter_density_apply x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [DGPS.AbsoluteDensity.density]
  ring

/-- `|ρ̂(2)|²` of an absolute density. -/
noncomputable def secondHarmonicQ (ρ : DGPS.AbsoluteDensity 1) : ℝ :=
  Complex.normSq (secondHarmonicCoeff (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))

/-- `J(ρ) = ∫ |∇(cos 4π * ρ)|² dρ`. -/
noncomputable def secondHarmonicJ (ρ : DGPS.AbsoluteDensity 1) : ℝ :=
  ∫ x, ρ.density x *
    ‖DGPS.smoothGrad (secondHarmonicCosConv (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) x‖ ^ 2
    ∂DGPS.haar 1

theorem secondHarmonicQ_eq (ρ : DGPS.AbsoluteDensity 1) :
    secondHarmonicQ ρ = (∫ y, (mode 2 y).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) ^ 2 +
      (∫ y, (mode 2 y).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) ^ 2 :=
  normSq_secondHarmonicCoeff _

theorem secondHarmonicJ_eq (ρ : DGPS.AbsoluteDensity 1) (C S : ℝ)
    (hC : C = ∫ y, (mode 2 y).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))
    (hS : S = ∫ y, (mode 2 y).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) :
    secondHarmonicJ ρ = ∫ x, ρ.density x * trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2
      ∂DGPS.haar 1 := by
  unfold secondHarmonicJ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ρ.density x * _ = _
  rw [cosConv_eq_trig, ← hC, ← hS, DGPS.tangent_norm_sq]
  simp [coordPartial_trig]

theorem secondHarmonicJ_nonneg (ρ : DGPS.AbsoluteDensity 1) : 0 ≤ secondHarmonicJ ρ :=
  integral_nonneg fun x => mul_nonneg (ρ.density_nonneg x) (sq_nonneg _)

theorem score_integral_force (κ : ℝ) (b : DGPS.AbsoluteDrift (secondHarmonicData κ))
    (τ σ : DGPS.AbsoluteDensity 1) (C S : ℝ)
    (hC : C = ∫ y, (mode 2 y).re ∂(DGPS.densityMeasure τ : Measure (DGPS.Torus 1)))
    (hS : S = ∫ y, (mode 2 y).im ∂(DGPS.densityMeasure τ : Measure (DGPS.Torus 1))) :
    Integrable (fun x => ‖(2 : ℝ) • DGPS.weakGradient σ.sqrt σ.sqrt_mem x +
      σ.sqrt x • b.force τ x‖ ^ 2) (DGPS.haar 1) ∧
    ∫ x, ‖(2 : ℝ) • DGPS.weakGradient σ.sqrt σ.sqrt_mem x + σ.sqrt x • b.force τ x‖ ^ 2
        ∂DGPS.haar 1 =
      DGPS.Analysis.circleFisherInformation σ +
        2 * κ * (16 * Real.pi ^ 2) * ∫ x, σ.density x * trig C S 0 x ∂DGPS.haar 1 +
        κ ^ 2 * ∫ x, σ.density x * trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2
          ∂DGPS.haar 1 := by
  refine score_integral σ C S κ (b.force τ) ?_
  filter_upwards [force_ae_secondHarmonic κ b τ] with x hx
  rw [hx, ← hC, ← hS, coordPartial_trig]

theorem potentialEnergy_secondHarmonic (κ : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.potentialEnergy (secondHarmonicData κ) ν = 0 := by
  simp [DGPS.potentialEnergy, secondHarmonicData]

theorem freeEnergyMinimumReal_secondHarmonic {κ : ℝ} (hκ : 0 < κ) :
    DGPS.freeEnergyMinimumReal (secondHarmonicData κ) = -κ / 2 := by
  have h2 := DGPS.coe_freeEnergyMinimumReal (secondHarmonicData κ)
  rw [freeEnergyMinimum_secondHarmonic hκ, EReal.coe_eq_coe_iff] at h2
  exact h2

theorem scalarGap_secondHarmonic {κ : ℝ} (hκ : 0 < κ) (ρ : DGPS.AbsoluteDensity 1) :
    ((DGPS.scalarGap (secondHarmonicData κ) ρ : ℝ≥0) : ℝ) =
      DGPS.Analysis.circleEntropy ρ + κ / 2 * secondHarmonicQ ρ := by
  rw [DGPS.coe_scalarGap]
  have h1 := DGPS.coe_densityFreeEnergy (secondHarmonicData κ) ρ
  rw [DGPS.freeEnergy_eq_real _ _ (DGPS.absoluteDensity_entropy_finite ρ).2.2.1,
    EReal.coe_eq_coe_iff] at h1
  rw [h1, freeEnergyMinimumReal_secondHarmonic hκ, DGPS.circleEntropy_eq_relativeEntropy,
    potentialEnergy_secondHarmonic, interactionEnergy_secondHarmonic]
  unfold secondHarmonicQ
  ring

theorem scalarDissipation_secondHarmonic (κ : ℝ) (b : DGPS.AbsoluteDrift (secondHarmonicData κ))
    (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.scalarDissipation (secondHarmonicData κ) b ρ =
      ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ +
        8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ y, (mode 2 y).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∫ y, (mode 2 y).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) :=
    ⟨_, rfl⟩
  obtain ⟨hint, heq⟩ := score_integral_force κ b ρ ρ C S hC hS
  have key : ∫⁻ x, ENNReal.ofReal
      (‖DGPS.scalarScore (secondHarmonicData κ) b ρ x‖ ^ 2) ∂DGPS.haar 1 =
      ENNReal.ofReal (∫ x, ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x +
        ρ.sqrt x • b.force ρ x‖ ^ 2 ∂DGPS.haar 1) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  unfold DGPS.scalarDissipation
  rw [key, heq, integral_density_mul_trig, ← hC, ← hS, ← secondHarmonicJ_eq ρ C S hC hS,
    secondHarmonicQ_eq, ← hC, ← hS]
  congr 1
  ring

theorem speciesGap_secondHarmonic {κ : ℝ} (hκ : 0 < κ) (F : DGPS.SpeciesFamily 1) :
    ((DGPS.speciesGap (secondHarmonicData κ) F : ℝ≥0) : ℝ) =
      ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s) +
        κ / 2 * secondHarmonicQ (DGPS.barycenter F) := by
  rw [DGPS.coe_speciesGap]
  unfold DGPS.speciesRawGap
  simp only [← DGPS.circleEntropy_eq_relativeEntropy]
  rw [freeEnergyMinimumReal_secondHarmonic hκ, potentialEnergy_secondHarmonic,
    interactionEnergy_secondHarmonic]
  unfold secondHarmonicQ
  ring

theorem speciesDissipation_secondHarmonic (κ : ℝ) (b : DGPS.AbsoluteDrift (secondHarmonicData κ))
    (F : DGPS.SpeciesFamily 1) :
    DGPS.speciesDissipation (secondHarmonicData κ) b F =
      ENNReal.ofReal (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) +
        8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
        κ ^ 2 * secondHarmonicJ (DGPS.barycenter F)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ y, (mode 2 y).re
      ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∫ y, (mode 2 y).im
      ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := ⟨_, rfl⟩
  have hs := fun s => score_integral_force κ b (DGPS.barycenter F) (F.density s) C S hC hS
  have hR : ∀ s, ∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2)
        ∂DGPS.haar 1 =
      ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (F.density s) +
        2 * κ * (16 * Real.pi ^ 2) * ∫ x, (F.density s).density x * trig C S 0 x ∂DGPS.haar 1 +
        κ ^ 2 * ∫ x, (F.density s).density x *
          trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2 ∂DGPS.haar 1) := fun s => by
    rw [← (hs s).2]
    exact (ofReal_integral_eq_lintegral_ofReal (hs s).1
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hnn : ∀ s, 0 ≤ F.weight s * (DGPS.Analysis.circleFisherInformation (F.density s) +
        2 * κ * (16 * Real.pi ^ 2) * ∫ x, (F.density s).density x * trig C S 0 x ∂DGPS.haar 1 +
        κ ^ 2 * ∫ x, (F.density s).density x *
          trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2 ∂DGPS.haar 1) := fun s => by
    rw [← (hs s).2]
    exact mul_nonneg (F.weight_nonneg s) (integral_nonneg fun x => sq_nonneg _)
  unfold DGPS.speciesDissipation
  simp_rw [hR, ← ENNReal.ofReal_mul (F.weight_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => hnn s]
  congr 1
  have hX := barycenter_integral F (trig C S 0) fun s => integrable_density_mul_trig _ _ _ _
  have hY := barycenter_integral F (fun x => trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2)
    fun s => integrable_density_mul_trig_sq _ _ _ _
  have e : ∀ s, F.weight s * (DGPS.Analysis.circleFisherInformation (F.density s) +
        2 * κ * (16 * Real.pi ^ 2) * ∫ x, (F.density s).density x * trig C S 0 x ∂DGPS.haar 1 +
        κ ^ 2 * ∫ x, (F.density s).density x *
          trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2 ∂DGPS.haar 1) =
      F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) +
        2 * κ * (16 * Real.pi ^ 2) * (F.weight s * ∫ x, (F.density s).density x * trig C S 0 x ∂DGPS.haar 1) +
        κ ^ 2 * (F.weight s * ∫ x, (F.density s).density x *
          trig (4 * Real.pi * S) (-(4 * Real.pi) * C) 0 x ^ 2 ∂DGPS.haar 1) := fun s => by ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hX, hY]
  rw [integral_density_mul_trig, ← hC, ← hS, ← secondHarmonicJ_eq _ C S hC hS, secondHarmonicQ_eq,
    ← hC, ← hS]
  ring

theorem ofReal_a0_le_quotient {G : ℝ≥0} (hG : 0 < G) {D : ℝ≥0∞} {Dr : ℝ}
    (hD : D = ENNReal.ofReal Dr) (h : 4 * Real.pi ^ 2 * (2 * (G : ℝ)) ≤ Dr) :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ D / (2 * (G : ℝ≥0∞)) := by
  have h0 : (2 * (G : ℝ≥0∞)) ≠ 0 := by simpa using hG.ne'
  have h1 : (2 * (G : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl h1), hD]
  have : ENNReal.ofReal (4 * Real.pi ^ 2) * (2 * (G : ℝ≥0∞)) =
      ENNReal.ofReal (4 * Real.pi ^ 2 * (2 * (G : ℝ))) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)]
    congr 1
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_coe_nnreal]
    simp
  rw [this]
  exact ENNReal.ofReal_le_ofReal h

/-- **FIN087.** For the second-harmonic model with `κ > 0` and any absolute drift provider
`b`: on the absolute nonlinear domain `D(ρ) = I(ρ|m) + 8 a0 κ Q + κ² J` with `a0 = 4π²`,
`Q = |ρ̂(2)|²` and `J = ∫ |∇(cos 4π * ρ)|² dρ ≥ 0`, so `D − 2 a0 G = (I − 2 a0 H) + 7 a0 κ Q + κ² J ≥ 0`,
whence `D/(2G) ≥ a0` and `scalarRate ≥ a0`; the same for every finite positive-weight species
family (the cross and square terms depend on the barycenter, `H` and `I` are averaged), with
`speciesRate ≥ a0`. -/
theorem second_harmonic_scalar_and_species_dissipation (κ : ℝ) (hκ : 0 < κ)
    (b : DGPS.AbsoluteDrift (secondHarmonicData κ)) :
    (∀ ρ : DGPS.AbsoluteDensity 1,
      0 ≤ secondHarmonicJ ρ ∧
      DGPS.scalarDissipation (secondHarmonicData κ) b ρ =
        ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ +
          8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ) ∧
      ((DGPS.scalarGap (secondHarmonicData κ) ρ : ℝ≥0) : ℝ) =
        DGPS.Analysis.circleEntropy ρ + κ / 2 * secondHarmonicQ ρ ∧
      (DGPS.Analysis.circleFisherInformation ρ + 8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ +
          κ ^ 2 * secondHarmonicJ ρ) -
        2 * (4 * Real.pi ^ 2) * (DGPS.Analysis.circleEntropy ρ + κ / 2 * secondHarmonicQ ρ) =
      (DGPS.Analysis.circleFisherInformation ρ -
          2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ ∧
      0 ≤ (DGPS.Analysis.circleFisherInformation ρ -
          2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ ∧
      (0 < DGPS.scalarGap (secondHarmonicData κ) ρ →
        ENNReal.ofReal (4 * Real.pi ^ 2) ≤ DGPS.scalarQuotient (secondHarmonicData κ) b ρ)) ∧
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ DGPS.scalarRate (secondHarmonicData κ) b ∧
    (∀ F : DGPS.SpeciesFamily 1,
      0 ≤ secondHarmonicJ (DGPS.barycenter F) ∧
      DGPS.speciesDissipation (secondHarmonicData κ) b F =
        ENNReal.ofReal (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) +
          8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
          κ ^ 2 * secondHarmonicJ (DGPS.barycenter F)) ∧
      ((DGPS.speciesGap (secondHarmonicData κ) F : ℝ≥0) : ℝ) =
        ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s) +
          κ / 2 * secondHarmonicQ (DGPS.barycenter F) ∧
      (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) +
          8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
          κ ^ 2 * secondHarmonicJ (DGPS.barycenter F)) -
        2 * (4 * Real.pi ^ 2) * (∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s) +
          κ / 2 * secondHarmonicQ (DGPS.barycenter F)) =
      (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) -
          2 * (4 * Real.pi ^ 2) * ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s)) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
        κ ^ 2 * secondHarmonicJ (DGPS.barycenter F) ∧
      0 ≤ (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) -
          2 * (4 * Real.pi ^ 2) * ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s)) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
        κ ^ 2 * secondHarmonicJ (DGPS.barycenter F) ∧
      (0 < DGPS.speciesGap (secondHarmonicData κ) F →
        ENNReal.ofReal (4 * Real.pi ^ 2) ≤ DGPS.speciesQuotient (secondHarmonicData κ) b F)) ∧
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ DGPS.speciesRate (secondHarmonicData κ) b := by
  have hQ : ∀ ρ, 0 ≤ secondHarmonicQ ρ := fun ρ => Complex.normSq_nonneg _
  have scalar : ∀ ρ : DGPS.AbsoluteDensity 1,
      0 ≤ secondHarmonicJ ρ ∧
      DGPS.scalarDissipation (secondHarmonicData κ) b ρ =
        ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ +
          8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ) ∧
      ((DGPS.scalarGap (secondHarmonicData κ) ρ : ℝ≥0) : ℝ) =
        DGPS.Analysis.circleEntropy ρ + κ / 2 * secondHarmonicQ ρ ∧
      (DGPS.Analysis.circleFisherInformation ρ + 8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ +
          κ ^ 2 * secondHarmonicJ ρ) -
        2 * (4 * Real.pi ^ 2) * (DGPS.Analysis.circleEntropy ρ + κ / 2 * secondHarmonicQ ρ) =
      (DGPS.Analysis.circleFisherInformation ρ -
          2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ ∧
      0 ≤ (DGPS.Analysis.circleFisherInformation ρ -
          2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ ∧
      (0 < DGPS.scalarGap (secondHarmonicData κ) ρ →
        ENNReal.ofReal (4 * Real.pi ^ 2) ≤ DGPS.scalarQuotient (secondHarmonicData κ) b ρ) := by
    intro ρ
    have hJ := secondHarmonicJ_nonneg ρ
    have hlsi := (DGPS.haar_circle_lsi ρ).2.2
    have hnn : 0 ≤ (DGPS.Analysis.circleFisherInformation ρ -
          2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ + κ ^ 2 * secondHarmonicJ ρ := by
      have := hQ ρ
      have : 0 ≤ 7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ ρ := by positivity
      have : 0 ≤ κ ^ 2 * secondHarmonicJ ρ := by positivity
      linarith
    have hG := scalarGap_secondHarmonic hκ ρ
    have hD := scalarDissipation_secondHarmonic κ b ρ
    refine ⟨hJ, hD, hG, by ring, hnn, fun hpos => ?_⟩
    refine ofReal_a0_le_quotient hpos hD ?_
    rw [hG]
    linarith
  have species : ∀ F : DGPS.SpeciesFamily 1,
      0 ≤ secondHarmonicJ (DGPS.barycenter F) ∧
      DGPS.speciesDissipation (secondHarmonicData κ) b F =
        ENNReal.ofReal (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) +
          8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
          κ ^ 2 * secondHarmonicJ (DGPS.barycenter F)) ∧
      ((DGPS.speciesGap (secondHarmonicData κ) F : ℝ≥0) : ℝ) =
        ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s) +
          κ / 2 * secondHarmonicQ (DGPS.barycenter F) ∧
      (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) +
          8 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
          κ ^ 2 * secondHarmonicJ (DGPS.barycenter F)) -
        2 * (4 * Real.pi ^ 2) * (∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s) +
          κ / 2 * secondHarmonicQ (DGPS.barycenter F)) =
      (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) -
          2 * (4 * Real.pi ^ 2) * ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s)) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
        κ ^ 2 * secondHarmonicJ (DGPS.barycenter F) ∧
      0 ≤ (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) -
          2 * (4 * Real.pi ^ 2) * ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s)) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
        κ ^ 2 * secondHarmonicJ (DGPS.barycenter F) ∧
      (0 < DGPS.speciesGap (secondHarmonicData κ) F →
        ENNReal.ofReal (4 * Real.pi ^ 2) ≤ DGPS.speciesQuotient (secondHarmonicData κ) b F) := by
    intro F
    have hJ := secondHarmonicJ_nonneg (DGPS.barycenter F)
    have hlsi : 0 ≤ ∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) -
          2 * (4 * Real.pi ^ 2) * ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_nonneg fun s _ => ?_
      have := (DGPS.haar_circle_lsi (F.density s)).2.2
      have := F.weight_nonneg s
      nlinarith
    have hnn : 0 ≤ (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s) -
          2 * (4 * Real.pi ^ 2) * ∑ s, F.weight s * DGPS.Analysis.circleEntropy (F.density s)) +
        7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) +
        κ ^ 2 * secondHarmonicJ (DGPS.barycenter F) := by
      have := hQ (DGPS.barycenter F)
      have : 0 ≤ 7 * (4 * Real.pi ^ 2) * κ * secondHarmonicQ (DGPS.barycenter F) := by positivity
      have : 0 ≤ κ ^ 2 * secondHarmonicJ (DGPS.barycenter F) := by positivity
      linarith
    have hG := speciesGap_secondHarmonic hκ F
    have hD := speciesDissipation_secondHarmonic κ b F
    refine ⟨hJ, hD, hG, by ring, hnn, fun hpos => ?_⟩
    refine ofReal_a0_le_quotient hpos hD ?_
    rw [hG]
    linarith
  refine ⟨scalar, ?_, species, ?_⟩
  · refine le_iInf fun ρ => ?_
    exact (scalar ρ.1).2.2.2.2.2 ρ.2
  · refine le_iInf fun F => ?_
    exact (species F.1).2.2.2.2.2 F.2

end DGPS.FiniteN
