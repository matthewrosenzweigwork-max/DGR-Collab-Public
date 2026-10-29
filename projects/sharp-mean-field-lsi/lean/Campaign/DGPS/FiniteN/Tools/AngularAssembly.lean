import DGPS.FiniteN.Tools.ConditionalEntropyPinsker
import DGPS.FiniteN.Tools.AngularWeakClassical
import DGPS.FiniteN.Tools.EntropyChainRule
import DGPS.FiniteN.Tools.LSIExtension
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.FiniteN.Tools.UnitTorusNormalization
import Mathlib

/-!
# FIN015: from the auxiliary LSI to the particle entropy inequality

Assembly of the entropy chain rule (FIN015a), the extension of the Euclidean LSI to `C¹` bounded
functions (FIN015b), the classical form of the angular von Mises product LSI (FIN015c), the
conditional Pinsker gradient bound (FIN014), the angular/unit-torus normalization (FIN002) and the
`H¹` extension (FIN026).

## Design choices (R5 notes)

* `k = 2`, `M = AngCircle`, `U = 0`, `φ = phi = (cos, sin)`, `m = angHaar`.
* `vmGrad` is a `Classical.choose`, so measurability of the slice map cannot be derived; the final
  theorem keeps the FIN014-style tensorized conditional LSI (`TP` form) and the explicit hypothesis
  `haem` (a.e.-measurability of the slice carré du champ), and converts to classical partials with
  `tp_of_smooth` / `tp_vmGamma_eq_classical_ae`.
* The module `Tools.lean` does not exist, so the packet lives in this new file.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ContDiff

namespace DGPS.FiniteN.Tools.AngularAssembly

open DGPS DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.Tools.ConditionalEntropyPinsker DGPS.FiniteN.Tools.UniformVonMises
  DGPS.Circle.AngularNormalization DGPS.FiniteN.UnitTorusNormalization
  DGPS.FiniteN.Tools.StrongConvexityLSI DGPS.FiniteN.Tools DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.Tools.WeightedSobolev

section General

/-- Entropy under a measurable map (with a measurable test function). -/
theorem homogeneousEntropy_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {T : α → β} (hT : Measurable T) (μ : Measure α) {f : β → ℝ} (hf : Measurable f) :
    homogeneousEntropy (μ.map T) f = homogeneousEntropy μ (fun a => f (T a)) := by
  have hI : ∀ h : β → ℝ, Measurable h → ∫ b, h b ∂(μ.map T) = ∫ a, h (T a) ∂μ :=
    fun h hh => integral_map hT.aemeasurable hh.aestronglyMeasurable
  unfold homogeneousEntropy
  rw [hI f hf]
  split_ifs
  · rfl
  · rw [lintegral_map _ hT]
    refine Measurable.ennreal_ofReal ?_
    unfold entropyIntegrand
    fun_prop

end General

section Continuity

variable {k : ℕ} {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m]
  {U : M → ℝ} {φ : M → Fin k → ℝ} {N : ℕ+}

theorem continuous_tilt_field (hyp : HubbardHyp m U φ) {g : (Fin N → M) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Continuous (tilt (ν := Measure.pi fun _ : Fin N => m) g (potSum U) (fieldSum φ)) := by
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  obtain ⟨c0, hc0'⟩ := hyp.U_lower
  have hVm : Measurable (potSum U : (Fin N → M) → ℝ) :=
    Finset.measurable_sum _ fun i _ => hyp.U_meas.comp (measurable_pi_apply i)
  have hu : ∀ x : Fin N → M, -(N * |c0|) ≤ potSum U x := by
    intro x
    unfold potSum
    have : ∀ i : Fin N, -|c0| ≤ U (x i) := fun i => by
      linarith [hc0' (x i), neg_abs_le c0]
    calc -(N * |c0|) = ∑ _i : Fin N, -|c0| := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  refine continuous_iff_continuousAt.2 fun w => ?_
  exact (hasFDerivAt_tilt (ν := Measure.pi fun _ : Fin N => m) hg hVm
    (measurable_fieldSum hyp) (le_max_right B 0) hc0 (fun y => (hB y).trans (le_max_left _ _))
    hc hu w).continuousAt

theorem continuous_condGrad (hyp : HubbardHyp m U φ) {f : (Fin N → M) → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) (j : Fin k) :
    Continuous fun w => condGrad U φ m N f w j := by
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  have hfj : Measurable fun y => f y * fieldSum φ y j :=
    hf.mul (measurable_fieldSum_apply hyp j)
  have hBj : ∀ y, |f y * fieldSum φ y j| ≤ B * c := fun y => by
    rw [abs_mul]
    exact mul_le_mul (hB y) (hc y j) (abs_nonneg _) ((abs_nonneg _).trans (hB y))
  have h1 := continuous_tilt_field hyp hfj hBj
  have h2 := continuous_tilt_field hyp hf hB
  have h3 := continuous_tilt_field hyp (measurable_fieldSum_apply hyp (N := N) j)
    (fun y => hc y j)
  have hZ : Continuous (fun w => auxPartition U φ m w ^ (N : ℕ)) := by
    have h := continuous_tilt_field hyp (m := m) (U := U) (φ := φ) (N := N)
      (g := fun _ => (1 : ℝ)) measurable_const (B := 1) (fun _ => by simp)
    have e : (fun w => auxPartition U φ m w ^ (N : ℕ)) =
        tilt (ν := Measure.pi fun _ : Fin N => m) (fun _ => (1 : ℝ)) (potSum U) (fieldSum φ) :=
      funext fun w => (tilt_one hyp N w).symm
    rw [e]; exact h
  have hZ0 : ∀ w, auxPartition U φ m w ^ (N : ℕ) ≠ 0 := fun w =>
    (pow_pos (auxPartition_pos hyp w) _).ne'
  have e : (fun w => condGrad U φ m N f w j) = fun w =>
      tilt (ν := Measure.pi fun _ : Fin N => m) (fun y => f y * fieldSum φ y j) (potSum U)
          (fieldSum φ) w / auxPartition U φ m w ^ (N : ℕ) -
        (tilt (ν := Measure.pi fun _ : Fin N => m) f (potSum U) (fieldSum φ) w /
          auxPartition U φ m w ^ (N : ℕ)) *
        (tilt (ν := Measure.pi fun _ : Fin N => m) (fun y => fieldSum φ y j) (potSum U)
          (fieldSum φ) w / auxPartition U φ m w ^ (N : ℕ)) :=
    funext fun w => condGrad_eq hyp hf hB w j
  rw [e]
  exact (h1.div hZ hZ0).sub ((h2.div hZ hZ0).mul (h3.div hZ hZ0))

end Continuity

section Angular

variable (N : ℕ+)

theorem contDiff_sqrt_condMoment {g : (Fin N → AngCircle) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) (hpos : ∀ w, 0 < condMoment N g w) :
    ContDiff ℝ 1 (fun w : E2 => Real.sqrt (condMoment N g w)) := by
  have hd : ∀ w : E2, HasFDerivAt (fun w' : E2 => Real.sqrt (condMoment N g w'))
      ((1 / (2 * Real.sqrt (condMoment N g w))) •
        ((lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2)) w :=
    fun w => (hasFDerivAt_condMoment N hg hB w).sqrt (hpos w).ne'
  refine contDiff_one_iff_fderiv.2 ⟨fun w => (hd w).differentiableAt, ?_⟩
  have hf : fderiv ℝ (fun w' : E2 => Real.sqrt (condMoment N g w')) = fun w =>
      (1 / (2 * Real.sqrt (condMoment N g w))) •
        ((lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2) :=
    funext fun w => (hd w).fderiv
  rw [hf]
  have hm : Continuous (condMoment N g) :=
    continuous_iff_continuousAt.2 fun w => (hasFDerivAt_condMoment N hg hB w).continuousAt
  have hlin : ∀ a : Fin 2 → ℝ, (lin a).comp toFun2 =
      ∑ j, a j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp toFun2) := by
    intro a
    refine ContinuousLinearMap.ext fun v => ?_
    simp [lin_apply, toFun2_apply]
  have hL : Continuous fun w : E2 =>
      (lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2 := by
    simp_rw [hlin]
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun w : E2 =>
        condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp j :=
      (continuous_condGrad hubbardHyp_angular hg hB j).comp (PiLp.continuous_ofLp 2 _)
    exact Continuous.smul h1 continuous_const
  have h2 : Continuous fun w : E2 => 1 / (2 * Real.sqrt (condMoment N g w)) :=
    continuous_const.div (continuous_const.mul (Real.continuous_sqrt.comp hm))
      (fun w => by have := Real.sqrt_pos.2 (hpos w); positivity)
  exact Continuous.smul h2 hL

/-- Classical form of the product log-Sobolev inequality for smooth tests. -/
def ClassicalProductLSI (N : ℕ+) (γ : ℝ) : Prop :=
  ∀ (w : E2) (F : (Fin N → AngCircle) → ℝ), IsSmoothAngParticle F →
    homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) (fun x => F x ^ 2) ≤
      ENNReal.ofReal (2 / γ) *
        ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2)
          ∂Measure.pi fun _ : Fin N => vmLaw w

variable {N}

theorem fderiv_sqrt_condMoment_sq_le {γ : ℝ} (hγ : 0 < γ) (hlsi : ClassicalProductLSI N γ)
    {F : (Fin N → AngCircle) → ℝ} (hF : IsSmoothAngParticle F) {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    (w : E2) (hpos : 0 < condMoment N (fun x => F x ^ 2) w) :
    ENNReal.ofReal (‖fderiv ℝ (fun w' : E2 =>
        Real.sqrt (condMoment N (fun x => F x ^ 2) w')) w‖ ^ 2) ≤
      ENNReal.ofReal ((N : ℝ) / γ) *
        ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2)
          ∂Measure.pi fun _ : Fin N => vmLaw w := by
  have hf : Measurable F := measurable_liftAng_comp hF
  set g : (Fin N → AngCircle) → ℝ := fun x => F x ^ 2 with hgdef
  have hg : Measurable g := hf.pow_const 2
  have hg0 : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hB : ∀ x, |g x| ≤ C ^ 2 := fun x => by
    rw [abs_of_nonneg (hg0 x), hgdef]
    exact (sq_le_sq' (abs_le.1 (hC x)).1 (abs_le.1 (hC x)).2)
  have hprob : ∀ w' : E2,
      IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w') := fun w' => by
    rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hubbardHyp_angular N w'.ofLp
  rw [((hasFDerivAt_condMoment N hg hB w).sqrt hpos.ne').fderiv]
  set Lg := (lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2
    with hLg
  set a := condMoment N g w with ha
  set E := ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2)
    ∂Measure.pi fun _ : Fin N => vmLaw w with hE
  by_cases hEt : E = ⊤
  · rw [hEt, ENNReal.mul_top (by simp; positivity)]; exact le_top
  have hP := hprob w
  have hint : Integrable g (Measure.pi fun _ : Fin N => vmLaw w) :=
    Integrable.of_bound hg.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun x => by simpa using hB x)
  have hglog : Integrable (fun x => g x * Real.log (g x))
      (Measure.pi fun _ : Fin N => vmLaw w) :=
    integrable_mul_log_of_bdd hg hg0 (fun x => (abs_le.1 (hB x)).2)
  have hent := homogeneousEntropy_eq_formula (P := Measure.pi fun _ : Fin N => vmLaw w)
    (Filter.Eventually.of_forall hg0) hint hglog
  have hl := hlsi w F hF
  have hl' : ENNReal.ofReal (∫ x, g x * Real.log (g x) ∂(Measure.pi fun _ : Fin N => vmLaw w) -
      a * Real.log a) ≤ ENNReal.ofReal (2 / γ) * E := by
    have : homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) (fun x => F x ^ 2) =
        homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) g := rfl
    rw [this, hent] at hl
    exact hl
  set e := E.toReal with he
  have hEe : E = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEt).symm
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  rw [hEe, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hl'
  have hb := lin_sq_le N hg hB hg0 w hpos
  set ent := ∫ x, g x * Real.log (g x) ∂(Measure.pi fun _ : Fin N => vmLaw w) -
    a * Real.log a with hentdef
  rw [hEe, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 hpos
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hsq : (1 / (2 * Real.sqrt a)) ^ 2 = 1 / (4 * a) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hpos.le]; norm_num
  rw [hsq]
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  calc 1 / (4 * a) * ‖Lg‖ ^ 2 ≤ 1 / (4 * a) * (2 * (N : ℝ) * a * ent) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (N : ℝ) / 2 * ent := by field_simp; ring
    _ ≤ (N : ℝ) / 2 * (2 / γ * e) := mul_le_mul_of_nonneg_left hl' (by positivity)
    _ = (N : ℝ) / γ * e := by field_simp

end Angular

section Bounds

variable {N : ℕ+}

theorem exists_bound_angPartial {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F)
    (i : Fin N) : ∃ C : ℝ, ∀ θ, |angParticlePartial i F θ| ≤ C := by
  have hF' : ContDiff ℝ ∞ (liftAng F) := hF
  have hc : Continuous fun s : Fin N → ℝ => fderiv ℝ (liftAng F) s (Pi.single i 1) :=
    (hF'.continuous_fderiv (by simp)).clm_apply continuous_const
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin N => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun θ => ?_⟩
  have := hC (fun k => angSec (θ k)) fun k _ => by
    have := (AddCircle.equivIoc (2 * Real.pi) 0 (θ k)).property
    simp only [zero_add] at this
    exact ⟨this.1.le, this.2⟩
  rw [Real.norm_eq_abs] at this
  exact this

theorem exists_bound_sum_partial {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ, ∑ i, angParticlePartial i F θ ^ 2 ≤ K := by
  choose C hC using fun i => exists_bound_angPartial hF i
  refine ⟨∑ i, C i ^ 2, Finset.sum_nonneg fun i _ => sq_nonneg _, fun θ => ?_⟩
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC i θ) 2

end Bounds

section Core

variable {N : ℕ+}

theorem fderiv_sqrt_condMoment_bdd {γ : ℝ} (hγ : 0 < γ) (hlsi : ClassicalProductLSI N γ)
    {F : (Fin N → AngCircle) → ℝ} (hF : IsSmoothAngParticle F) {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    (hpos : ∀ w, 0 < condMoment N (fun x => F x ^ 2) w) :
    ∃ Gb : ℝ, ∀ w : E2,
      ‖fderiv ℝ (fun w' : E2 => Real.sqrt (condMoment N (fun x => F x ^ 2) w')) w‖ ≤ Gb := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_sum_partial hF
  refine ⟨Real.sqrt ((N : ℝ) / γ * K), fun w => ?_⟩
  have hprob : IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w) := by
    rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hubbardHyp_angular N w.ofLp
  have h1 := fderiv_sqrt_condMoment_sq_le hγ hlsi hF hC w (hpos w)
  have h2 : ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2)
      ∂(Measure.pi fun _ : Fin N => vmLaw w) ≤ ENNReal.ofReal K := by
    calc _ ≤ ∫⁻ _x, ENNReal.ofReal K ∂(Measure.pi fun _ : Fin N => vmLaw w) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hK x)
      _ = ENNReal.ofReal K := by simp
  have h3 := h1.trans (mul_le_mul_right h2 _)
  have hN : 0 ≤ (N : ℝ) / γ := by positivity
  rw [← ENNReal.ofReal_mul hN, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

theorem lintegral_cond_eq {D : Matrix (Fin 2) (Fin 2) ℝ} (hD : D.PosDef) (h : Fin 2 → ℝ)
    {e : (Fin N → AngCircle) → ℝ≥0∞} (he : Measurable e) :
    ∫⁻ w, ∫⁻ x, e x ∂(Measure.pi fun _ : Fin N =>
        siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)
      ∂(auxLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N) =
    ∫⁻ x, e x ∂(hubbardParticleLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N) := by
  have hyp := hubbardHyp_angular
  have := isProbabilityMeasure_auxLaw hyp hD h N
  rw [← hubbardJoint_map_snd hyp hD h N, lintegral_map he measurable_snd,
    hubbardJoint_eq_compProd hyp hD h N, Measure.lintegral_compProd (f := fun z => e z.2) (he.comp measurable_snd)]
  rfl

theorem smooth_entropy_le {D : Matrix (Fin 2) (Fin 2) ℝ} (hD : D.PosDef) (h : Fin 2 → ℝ)
    {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 < lam) (hlsi : ClassicalProductLSI N γ)
    (haux : HasLSIRate ((auxLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N).map
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) lam)
    {F : (Fin N → AngCircle) → ℝ} (hF : IsSmoothAngParticle F) :
    homogeneousEntropy (hubbardParticleLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N)
        (fun x => F x ^ 2) ≤
      ENNReal.ofReal (2 / γ * (1 + (N : ℝ) / lam)) *
        ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2)
          ∂(hubbardParticleLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N) := by
  have hyp := hubbardHyp_angular
  obtain ⟨C, hC⟩ := exists_bound_angParticle hF
  have hC' : ∀ x, |F x| ≤ C := fun x => by simpa using hC x
  have hf : Measurable F := measurable_liftAng_comp hF
  set g : (Fin N → AngCircle) → ℝ := fun x => F x ^ 2 with hgdef
  have hg : Measurable g := hf.pow_const 2
  have hg0 : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hB : ∀ x, |g x| ≤ C ^ 2 := fun x => by
    rw [abs_of_nonneg (hg0 x), hgdef]
    exact (sq_le_sq' (abs_le.1 (hC' x)).1 (abs_le.1 (hC' x)).2)
  set ē : (Fin N → AngCircle) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2) with hēdef
  have hē : Measurable ē :=
    (Finset.measurable_sum _ fun i _ => (measurable_angParticlePartial i).pow_const 2).ennreal_ofReal
  set P := hubbardParticleLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N with hPdef
  set η := auxLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N with hηdef
  set J := hubbardJoint D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N with hJdef
  have hJ : IsProbabilityMeasure J := isProbabilityMeasure_hubbardJoint hyp hD h N
  have hη : IsProbabilityMeasure η := isProbabilityMeasure_auxLaw hyp hD h N
  have step1 : homogeneousEntropy P g = homogeneousEntropy J (fun z => g z.2) := by
    rw [hPdef, ← hubbardJoint_map_snd hyp hD h N, homogeneousEntropy_map measurable_snd J hg]
  have hgm : Measurable fun z : (Fin 2 → ℝ) × (Fin N → AngCircle) => g z.2 :=
    hg.comp measurable_snd
  have hint : Integrable (fun z : (Fin 2 → ℝ) × (Fin N → AngCircle) => g z.2) J :=
    Integrable.of_bound hgm.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun z => by simpa using hB z.2)
  have hlog : Integrable (fun z : (Fin 2 → ℝ) × (Fin N → AngCircle) => g z.2 * Real.log (g z.2)) J :=
    integrable_mul_log_of_bdd hgm (fun z => hg0 z.2) (fun z => (abs_le.1 (hB z.2)).2)
  have chain := entropy_chain_rule_hubbardJoint hyp hD h N hgm (fun z => hg0 z.2) hint hlog
  have hsite : ∀ w : Fin 2 → ℝ,
      (Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w) =
        Measure.pi fun _ : Fin N => vmLaw (WithLp.toLp 2 w) := fun w =>
    (pi_vmLaw_eq_condLaw N (WithLp.toLp 2 w)).symm
  -- first term
  have t1 : ∫⁻ w, homogeneousEntropy
        (Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)
        (fun x => g x) ∂η ≤ ENNReal.ofReal (2 / γ) * ∫⁻ x, ē x ∂P := by
    calc _ ≤ ∫⁻ w, ENNReal.ofReal (2 / γ) * ∫⁻ x, ē x
            ∂(Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)
            ∂η :=
          lintegral_mono fun w => by rw [hsite w]; exact hlsi _ F hF
      _ = ENNReal.ofReal (2 / γ) * ∫⁻ w, ∫⁻ x, ē x
            ∂(Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)
            ∂η := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by rw [lintegral_cond_eq hD h hē]
  -- second term
  have hmom : (fun w : Fin 2 → ℝ => ∫ x, g (x) ∂(Measure.pi fun _ : Fin N =>
      siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)) =
      fun w => condMoment N g (WithLp.toLp 2 w) := funext fun w => by
    unfold condMoment; rw [hsite w]
  have t2 : homogeneousEntropy η (fun w : Fin 2 → ℝ => ∫ x, g x ∂(Measure.pi fun _ : Fin N =>
      siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)) ≤
      ENNReal.ofReal (2 / lam) * (ENNReal.ofReal ((N : ℝ) / γ) * ∫⁻ x, ē x ∂P) := by
    rw [hmom]
    have hm0 : ∀ w, 0 ≤ condMoment N g w := fun w => integral_nonneg hg0
    by_cases hz : ∃ w, condMoment N g w = 0
    · obtain ⟨w0, hw0⟩ := hz
      have hz' : ∀ w, condMoment N g w = 0 := fun w => by
        have := integral_eq_zero_of_integral_eq_zero N hg0 hB hg w0 w hw0
        exact this
      have : (fun w : Fin 2 → ℝ => condMoment N g (WithLp.toLp 2 w)) = fun _ => 0 :=
        funext fun w => hz' _
      rw [this, homogeneousEntropy_of_integral_eq_zero (by simp)]
      exact bot_le
    · have hz := not_exists.mp hz
      have hpos : ∀ w, 0 < condMoment N g w := fun w => lt_of_le_of_ne (hm0 w) fun h => hz w h.symm
      have hcd : ContDiff ℝ 1 (fun w : E2 => Real.sqrt (condMoment N g w)) :=
        contDiff_sqrt_condMoment N hg hB hpos
      obtain ⟨Gb, hGb⟩ := fderiv_sqrt_condMoment_bdd hγ hlsi hF hC' hpos
      have hμ : IsProbabilityMeasure (η.map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) :=
        inferInstance
      have hmB : ∀ w, condMoment N g w ≤ C ^ 2 := fun w => by
        have hprob : IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w) := by
          rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hyp N w.ofLp
        have hi : Integrable g (Measure.pi fun _ : Fin N => vmLaw w) :=
          Integrable.of_bound hg.aestronglyMeasurable (C ^ 2)
            (Filter.Eventually.of_forall fun x => by simpa using hB x)
        calc condMoment N g w ≤ ∫ _x, C ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw w) :=
              integral_mono hi (integrable_const _) fun x => (le_abs_self _).trans (hB x)
          _ = C ^ 2 := by simp
      have hGM : ∀ y : E2, |Real.sqrt (condMoment N g y)| ≤ |C| := fun y => by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (condMoment N g y) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt (hmB y)
          _ = |C| := Real.sqrt_sq_eq_abs C
      have hl := LSIExtension.hasLSIRate_of_C1_bounded haux hcd hGM hGb
      have e1 : (fun y : E2 => Real.sqrt (condMoment N g y) ^ 2) = condMoment N g :=
        funext fun y => Real.sq_sqrt (hm0 y)
      rw [e1] at hl
      rw [← homogeneousEntropy_map_toLp η (condMoment N g)]
      refine hl.trans (mul_le_mul_right ?_ _)
      have hgsm : Measurable (gradSq (fun y : E2 => Real.sqrt (condMoment N g y))) :=
        ((measurable_fderiv ℝ _).enorm).pow_const 2
      rw [lintegral_map hgsm (MeasurableEquiv.measurable _)]
      calc ∫⁻ w, gradSq (fun y : E2 => Real.sqrt (condMoment N g y)) (WithLp.toLp 2 w) ∂η
          ≤ ∫⁻ w, ENNReal.ofReal ((N : ℝ) / γ) * ∫⁻ x, ē x
            ∂(Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)
            ∂η := by
            refine lintegral_mono fun w => ?_
            rw [hsite w]
            have := fderiv_sqrt_condMoment_sq_le hγ hlsi hF hC' (WithLp.toLp 2 w) (hpos _)
            unfold gradSq
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            exact this
        _ = ENNReal.ofReal ((N : ℝ) / γ) * ∫⁻ w, ∫⁻ x, ē x
            ∂(Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w)
            ∂η := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = _ := by rw [lintegral_cond_eq hD h hē]
  have hfin : ENNReal.ofReal (2 / γ * (1 + (N : ℝ) / lam)) * ∫⁻ x, ē x ∂P =
      ENNReal.ofReal (2 / γ) * ∫⁻ x, ē x ∂P +
        ENNReal.ofReal (2 / lam) * (ENNReal.ofReal ((N : ℝ) / γ) * ∫⁻ x, ē x ∂P) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← add_mul,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    field_simp
  rw [hfin, step1, chain]
  exact add_le_add t1 t2

theorem classical_of_tp {γ : ℝ}
    (hlsi : ∀ (w : E2) (F : (Fin N → AngCircle) → ℝ),
      TP AngularH1 vmGamma (fun _ : Fin N => vmLaw w) F →
        homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) (fun x => F x ^ 2) ≤
          ENNReal.ofReal (2 / γ) *
            ∫⁻ x, ∑ i, vmGamma (slice i F x) (x i) ∂Measure.pi fun _ : Fin N => vmLaw w)
    (haem : ∀ (w : E2) (F : (Fin N → AngCircle) → ℝ), IsSmoothAngParticle F → ∀ i,
      AEMeasurable (dens vmGamma F i) (Measure.pi fun _ : Fin N => vmLaw w)) :
    ClassicalProductLSI N γ := by
  intro w F hF
  have hT := tp_of_smooth (fun _ : Fin N => vmLaw w) hF (haem w F hF)
  have e := (tp_vmGamma_eq_classical_ae (fun _ : Fin N => vmLaw w)
    (fun _ => vmLaw_absolutelyContinuous w) hF hT).2.2
  exact (hlsi w F hT).trans (mul_le_mul_right (le_of_eq e) _)

end Core

section Transfer

variable {N : ℕ+}

theorem lintegral_sum_partial_eq {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F)
    (μ : Measure (AngParticleSpace N)) [IsProbabilityMeasure μ] :
    ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2) ∂μ =
      ENNReal.ofReal (∫ x, ∑ i, angParticlePartial i F x ^ 2 ∂μ) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_sum_partial hF
  have hm : Measurable fun x => ∑ i, angParticlePartial i F x ^ 2 :=
    Finset.measurable_sum _ fun i _ => (measurable_angParticlePartial i).pow_const 2
  have hint : Integrable (fun x => ∑ i, angParticlePartial i F x ^ 2) μ :=
    Integrable.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      exact hK x)
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]

theorem smooth_periodic_entropy_le (A : InteractionData 1) {c : ℝ} (hc : 0 ≤ c)
    (hsm : ∀ ψ : AngParticleSpace N → ℝ, IsSmoothAngParticle ψ →
      homogeneousEntropy (angParticleLaw (angV A) (angW A) N) (fun x => ψ x ^ 2) ≤
        ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i ψ x ^ 2)
          ∂angParticleLaw (angV A) (angW A) N)
    (φ : ParticleSpace 1 N → ℝ) (hφ : IsSmoothPeriodicParticle φ) :
    homogeneousEntropy (particleLaw A N) (fun y => φ y ^ 2) ≤
      ENNReal.ofReal (c / Circle.AngularNormalization.a0 * particleSmoothEnergy A φ) := by
  set ψ : AngParticleSpace N → ℝ := φ ∘ (angEquivN N).symm with hψdef
  have hφψ : ψ ∘ angEquivN N = φ := by
    funext y; simp [hψdef]
  have hψ : IsSmoothAngParticle ψ := by
    rw [← isSmoothPeriodicParticle_comp_iff, hφψ]; exact hφ
  have : IsProbabilityMeasure (angParticleLaw (angV A) (angW A) N) := by
    rw [← map_particleLaw A N]
    exact (Measure.isProbabilityMeasure_map_iff (angEquivN N).measurable.aemeasurable).2
      inferInstance
  have hent : homogeneousEntropy (particleLaw A N) (fun y => φ y ^ 2) =
      homogeneousEntropy (angParticleLaw (angV A) (angW A) N) (fun x => ψ x ^ 2) := by
    rw [← map_particleLaw A N, ← homogeneousEntropy_map_equiv]
    rw [← hφψ]; rfl
  have hen : particleSmoothEnergy A φ =
      Circle.AngularNormalization.a0 * ∫ x, ∑ i, angParticlePartial i ψ x ^ 2 ∂angParticleLaw (angV A) (angW A) N := by
    unfold particleSmoothEnergy
    rw [← map_particleLaw A N,
      integral_map_equiv (angEquivN N) (fun x => ∑ i, angParticlePartial i ψ x ^ 2),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∑ i, ∑ j, particlePartial i j φ x ^ 2 = Circle.AngularNormalization.a0 * ∑ i, angParticlePartial i ψ (angEquivN N x) ^ 2
    have key : ∀ i : Fin N, particlePartial i 0 φ x =
        2 * Real.pi * angParticlePartial i ψ (angEquivN N x) := fun i => by
      rw [← hφψ]; exact particlePartial_comp_angEquivN hψ i x
    simp only [Fin.sum_univ_one, key, mul_pow, Finset.mul_sum, Circle.AngularNormalization.a0]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hent, hen]
  refine (hsm ψ hψ).trans ?_
  rw [lintegral_sum_partial_eq hψ, ← ENNReal.ofReal_mul hc]
  refine le_of_eq ?_
  congr 1
  have := Circle.AngularNormalization.a0_pos.ne'
  field_simp

end Transfer

end DGPS.FiniteN.Tools.AngularAssembly

namespace DGPS.FiniteN

open MeasureTheory
open scoped ENNReal
open DGPS DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.Tools.ConditionalEntropyPinsker DGPS.FiniteN.Tools.UniformVonMises
  DGPS.Circle.AngularNormalization DGPS.FiniteN.UnitTorusNormalization
  DGPS.FiniteN.Tools.StrongConvexityLSI DGPS.FiniteN.Tools DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.Tools.WeightedSobolev DGPS.FiniteN.Tools.AngularAssembly

/-- FIN015: from the auxiliary Euclidean LSI (rate `lam`) and the tensorized conditional angular
LSI (rate `γ`) to the particle entropy inequality, for every angular `H¹` test, every unit-period
`H¹` test, and the rate lower bound `r_N^all ≥ a0 γ / (1 + N/lam)`. -/
theorem auxiliary_lsi_to_particle_entropy (A : InteractionData 1) (N : ℕ+)
    {D : Matrix (Fin 2) (Fin 2) ℝ} (hD : D.PosDef) (h : Fin 2 → ℝ)
    (hP : angParticleLaw (angV A) (angW A) N =
      hubbardParticleLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N)
    {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 < lam)
    (hlsi : ∀ (w : E2) (F : (Fin N → AngCircle) → ℝ),
      TP AngularH1 vmGamma (fun _ : Fin N => vmLaw w) F →
        homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) (fun x => F x ^ 2) ≤
          ENNReal.ofReal (2 / γ) *
            ∫⁻ x, ∑ i, vmGamma (slice i F x) (x i) ∂Measure.pi fun _ : Fin N => vmLaw w)
    (haem : ∀ (w : E2) (F : (Fin N → AngCircle) → ℝ), IsSmoothAngParticle F → ∀ i,
      AEMeasurable (dens vmGamma F i) (Measure.pi fun _ : Fin N => vmLaw w))
    (haux : HasLSIRate ((auxLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N).map
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) lam) :
    (∀ u : AngParticleH1 (angV A) (angW A) N,
      angParticleEntropy u ≤
        ENNReal.ofReal (2 / γ * (1 + (N : ℝ) / lam) * angParticleEnergy u)) ∧
    (∀ f : ParticleH1 A N,
      particleEntropy A N f ≤
        ENNReal.ofReal (2 / γ * (1 + (N : ℝ) / lam) / Circle.AngularNormalization.a0 * particleEnergy A N f)) ∧
    ENNReal.ofReal (Circle.AngularNormalization.a0 * γ / (1 + (N : ℝ) / lam)) ≤ particleRateAll A N := by
  have hc : 0 < 2 / γ * (1 + (N : ℝ) / lam) := by positivity
  set c : ℝ := 2 / γ * (1 + (N : ℝ) / lam) with hcdef
  have hcl := classical_of_tp hlsi haem
  have hsm : ∀ ψ : AngParticleSpace N → ℝ, IsSmoothAngParticle ψ →
      homogeneousEntropy (angParticleLaw (angV A) (angW A) N) (fun x => ψ x ^ 2) ≤
        ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i ψ x ^ 2)
          ∂angParticleLaw (angV A) (angW A) N := by
    intro ψ hψ
    rw [hP]
    exact smooth_entropy_le hD h hγ hlam hcl haux hψ
  have hK := smooth_periodic_entropy_le A hc.le hsm
  have h2 : ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal (c / Circle.AngularNormalization.a0 * particleEnergy A N f) :=
    fun f => (fixed_n_weighted_sobolev_extension A N).2.1 (c / Circle.AngularNormalization.a0) hK f
  have hKpos : 0 < c / Circle.AngularNormalization.a0 := div_pos hc Circle.AngularNormalization.a0_pos
  refine ⟨fun u => ?_, h2, ?_⟩
  · have := h2 (angParticleH1Equiv A N u)
    rw [particleEntropy_angParticleH1Equiv, particleEnergy_angParticleH1Equiv] at this
    have e : c / Circle.AngularNormalization.a0 *
        (Circle.AngularNormalization.a0 * angParticleEnergy u) = c * angParticleEnergy u := by
      field_simp [Circle.AngularNormalization.a0_pos.ne']
    rwa [e] at this
  · refine le_iInf fun f => ?_
    have hf := f.2
    unfold particleQuotient
    rw [ENNReal.le_div_iff_mul_le (Or.inl hf.ne') (Or.inr ENNReal.ofReal_ne_top)]
    calc ENNReal.ofReal (Circle.AngularNormalization.a0 * γ / (1 + (N : ℝ) / lam)) * particleEntropy A N f.1
        ≤ ENNReal.ofReal (Circle.AngularNormalization.a0 * γ / (1 + (N : ℝ) / lam)) *
            ENNReal.ofReal (c / Circle.AngularNormalization.a0 * particleEnergy A N f.1) := by
          gcongr
          exact h2 f.1
      _ = ENNReal.ofReal (2 * particleEnergy A N f.1) := by
          have ha := Circle.AngularNormalization.a0_pos
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hcdef]
          field_simp [Circle.AngularNormalization.a0_pos.ne']

end DGPS.FiniteN
