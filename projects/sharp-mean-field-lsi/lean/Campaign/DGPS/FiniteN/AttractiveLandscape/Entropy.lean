import DGPS.FiniteN.AttractiveLandscape.Calculus
import DGPS.Variational.EquilibriumGibbs

/-!
# Entropy completion for the attractive finite-rank model (FIN047)

The attractive model with data `V = U - ‖Φ‖²/2`, `W(x,y) = ‖Φ x - Φ y‖²/2` has free energy
`F(ν) = H(ν | q_w) + ψ(w) - ‖w - m_ν‖²/2` for every `w`; at `w = m_ν` this is the entropy
completion `F(ν) = H(ν | q_{m_ν}) + ψ(m_ν)`.  Consequently minimizers of `F` and of `ψ`
correspond in both directions, and critical points of `ψ` correspond to stationary fixed points.
-/

open MeasureTheory InformationTheory
open scoped RealInnerProductSpace ENNReal

namespace DGPS.FiniteN.AttractiveLandscape

variable {d r : ℕ} {U : Torus d → ℝ} {Φ : Torus d → Feature r}

/-- The attractive finite-rank interaction data `V = U - ‖Φ‖²/2`, `W(x,y) = ‖Φ x - Φ y‖²/2`. -/
noncomputable def attractiveData (hU : Continuous U) (hΦ : Continuous Φ) : InteractionData d where
  V x := U x - ‖Φ x‖ ^ 2 / 2
  W x y := ‖Φ x - Φ y‖ ^ 2 / 2
  V_continuous := hU.sub ((hΦ.norm.pow 2).div_const 2)
  W_continuous := (((hΦ.comp continuous_fst).sub (hΦ.comp continuous_snd)).norm.pow 2).div_const 2
  W_symm := fun x y => by rw [norm_sub_rev]
  W_diag := fun x => by simp

/-- The feature mean `∫ Φ dρ` of a measure. -/
noncomputable def measureMean (Φ : Torus d → Feature r) (ρ : Measure (Torus d)) : Feature r :=
  ∫ x, Φ x ∂ρ

theorem featureMean_eq_measureMean (z : Feature r) :
    featureMean U Φ z = measureMean Φ (gibbs U Φ z) := rfl

section Algebra

variable (hU : Continuous U) (hΦ : Continuous Φ)
variable (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ]

theorem integrable_feature (hΦ : Continuous Φ) : Integrable Φ ρ :=
  Continuous.integrable_of_hasCompactSupport hΦ (HasCompactSupport.of_compactSpace _)

theorem integrable_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f ρ :=
  Continuous.integrable_of_hasCompactSupport hf (HasCompactSupport.of_compactSpace _)

/-- The mean of the squared norm term. -/
noncomputable def sqMean (Φ : Torus d → Feature r) (ρ : Measure (Torus d)) : ℝ :=
  ∫ x, ‖Φ x‖ ^ 2 / 2 ∂ρ

theorem interactionConvolution_attractive (x : Torus d) :
    DGPS.Lipschitz.interactionConvolution (attractiveData hU hΦ) ρ x =
      ‖Φ x‖ ^ 2 / 2 + sqMean Φ ρ - ⟪Φ x, measureMean Φ ρ⟫ := by
  unfold DGPS.Lipschitz.interactionConvolution sqMean measureMean
  have h1 : ∀ y, (attractiveData hU hΦ).W x y =
      ‖Φ x‖ ^ 2 / 2 + ‖Φ y‖ ^ 2 / 2 - ⟪Φ x, Φ y⟫ := fun y => by
    show ‖Φ x - Φ y‖ ^ 2 / 2 = _
    rw [norm_sub_sq_real]; ring
  simp_rw [h1]
  have i1 : Integrable (fun y => ‖Φ y‖ ^ 2 / 2) ρ :=
    integrable_cont ρ ((hΦ.norm.pow 2).div_const 2)
  have i2 : Integrable (fun y => ⟪Φ x, Φ y⟫) ρ :=
    integrable_cont ρ (continuous_const.inner hΦ)
  have i3 : Integrable (fun y => ‖Φ x‖ ^ 2 / 2 + ‖Φ y‖ ^ 2 / 2) ρ := (integrable_const _).add i1
  rw [integral_sub i3 i2, integral_add (integrable_const _) i1, integral_const,
    integral_inner (integrable_feature ρ hΦ)]
  simp [probReal_univ]

theorem potentialPart_attractive :
    potentialEnergy (attractiveData hU hΦ) ρ +
        (1 / 2 : ℝ) * interactionEnergy (attractiveData hU hΦ) ρ =
      ∫ x, U x ∂ρ - ‖measureMean Φ ρ‖ ^ 2 / 2 := by
  have i1 : Integrable (fun y => ‖Φ y‖ ^ 2 / 2) ρ :=
    integrable_cont ρ ((hΦ.norm.pow 2).div_const 2)
  have iU : Integrable U ρ := integrable_cont ρ hU
  have e1 : potentialEnergy (attractiveData hU hΦ) ρ = ∫ x, U x ∂ρ - sqMean Φ ρ := by
    unfold potentialEnergy sqMean
    exact integral_sub iU i1
  have e2 : interactionEnergy (attractiveData hU hΦ) ρ =
      2 * sqMean Φ ρ - ‖measureMean Φ ρ‖ ^ 2 := by
    rw [← DGPS.Lipschitz.interactionPairing_self, DGPS.Lipschitz.interactionPairing_eq_integral]
    simp_rw [interactionConvolution_attractive hU hΦ ρ, real_inner_comm (measureMean Φ ρ)]
    have i2 : Integrable (fun x => ⟪measureMean Φ ρ, Φ x⟫) ρ :=
      integrable_cont ρ (continuous_const.inner hΦ)
    have i3 : Integrable (fun x => ‖Φ x‖ ^ 2 / 2 + sqMean Φ ρ) ρ := i1.add (integrable_const _)
    rw [integral_sub i3 i2, integral_add i1 (integrable_const _),
      integral_const, integral_inner (integrable_feature ρ hΦ)]
    simp only [probReal_univ, one_smul]
    have hm : ⟪measureMean Φ ρ, ∫ x, Φ x ∂ρ⟫ = ‖measureMean Φ ρ‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    rw [hm]
    unfold sqMean
    ring
  rw [e1, e2]
  ring

theorem equilibriumPotential_attractive (x : Torus d) :
    DGPS.Lipschitz.equilibriumPotential (attractiveData hU hΦ) ρ x =
      U x + sqMean Φ ρ - ⟪measureMean Φ ρ, Φ x⟫ := by
  unfold DGPS.Lipschitz.equilibriumPotential
  rw [interactionConvolution_attractive hU hΦ ρ, real_inner_comm]
  show U x - ‖Φ x‖ ^ 2 / 2 + _ = _
  ring

end Algebra

theorem tilted_add_const {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (c : ℝ) :
    μ.tilted (fun x => f x + c) = μ.tilted f := by
  unfold Measure.tilted
  have h : ∫ x, Real.exp (f x + c) ∂μ = (∫ x, Real.exp (f x) ∂μ) * Real.exp c := by
    simp_rw [Real.exp_add]
    exact integral_mul_const _ _
  congr 1
  ext x
  rw [h, Real.exp_add, mul_div_mul_right _ _ (Real.exp_pos c).ne']

theorem gibbsMeasure_attractive (hU : Continuous U) (hΦ : Continuous Φ)
    (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ] :
    DGPS.Lipschitz.gibbsMeasure (attractiveData hU hΦ) ρ = gibbs U Φ (measureMean Φ ρ) := by
  unfold DGPS.Lipschitz.gibbsMeasure gibbs
  rw [← tilted_add_const _ (fun x => ⟪measureMean Φ ρ, Φ x⟫ - U x) (-sqMean Φ ρ)]
  congr 1
  ext x
  rw [equilibriumPotential_attractive hU hΦ ρ]
  ring

section EntropyCompletion

variable (hU : Continuous U) (hΦ : Continuous Φ)

/-- The Gibbs measure `q_z` as a bundled probability measure. -/
noncomputable def gibbsPM (z : Feature r) : ProbabilityMeasure (Torus d) :=
  ⟨gibbs U Φ z, isProbabilityMeasure_gibbs hU hΦ z⟩

theorem coe_gibbsPM (z : Feature r) : ((gibbsPM hU hΦ z : ProbabilityMeasure (Torus d)) :
    Measure (Torus d)) = gibbs U Φ z := rfl

theorem measureMean_gibbsPM (z : Feature r) :
    measureMean Φ (gibbsPM hU hΦ z : Measure (Torus d)) = featureMean U Φ z := rfl

/-- Entropy completion, general form:
`F(ν) = H(ν | q_w) + ψ(w) - ‖w - m_ν‖²/2` for every `w`. -/
theorem freeEnergy_eq_entropy_add_psi (ν : ProbabilityMeasure (Torus d)) (w : Feature r) :
    freeEnergy (attractiveData hU hΦ) ν =
      ((relativeEntropy (ν : Measure (Torus d)) (gibbs U Φ w) : ℝ≥0∞) : EReal) +
        ((psi U Φ w - ‖w - measureMean Φ (ν : Measure (Torus d))‖ ^ 2 / 2 : ℝ) : EReal) := by
  have := isProbabilityMeasure_gibbs hU hΦ w
  rw [freeEnergy_eq_klDiv, Analysis.relativeEntropy_eq_klDiv,
    potentialPart_attractive hU hΦ (ν : Measure (Torus d))]
  have hf : Continuous fun x => ⟪w, Φ x⟫ - U x := (continuous_const.inner hΦ).sub hU
  obtain ⟨B, -, hB⟩ := exists_bound_of_continuous hf
  have hB' : ∀ x, |⟪w, Φ x⟫ - U x| ≤ B := fun x => by simpa [Real.norm_eq_abs] using hB x
  have hfm : Measurable fun x => ⟪w, Φ x⟫ - U x := hf.measurable
  by_cases h : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤
  · obtain ⟨hne, heq⟩ := DGPS.Lipschitz.klDiv_tilted_forward (ρ := (ν : Measure (Torus d)))
      (ν := haar d) hfm hB' h
    have hne' : klDiv (ν : Measure (Torus d)) (gibbs U Φ w) ≠ ⊤ := hne
    rw [← EReal.coe_ennreal_toReal h, ← EReal.coe_ennreal_toReal hne', ← EReal.coe_add,
      ← EReal.coe_add, EReal.coe_eq_coe_iff]
    have hint : ∫ x, (⟪w, Φ x⟫ - U x) ∂(ν : Measure (Torus d)) =
        ⟪w, measureMean Φ (ν : Measure (Torus d))⟫ - ∫ x, U x ∂(ν : Measure (Torus d)) := by
      rw [integral_sub (integrable_cont _ (continuous_const.inner hΦ)) (integrable_cont _ hU)]
      unfold measureMean
      rw [integral_inner (integrable_feature _ hΦ)]
    have heq' : (klDiv (ν : Measure (Torus d)) (gibbs U Φ w)).toReal =
        (klDiv (ν : Measure (Torus d)) (haar d)).toReal -
          (⟪w, measureMean Φ (ν : Measure (Torus d))⟫ - ∫ x, U x ∂(ν : Measure (Torus d))) +
          Real.log (zeta U Φ w) := by
      rw [← hint]; exact heq
    rw [heq', norm_sub_sq_real]
    unfold psi
    ring
  · rw [not_not] at h
    have h2 : klDiv (ν : Measure (Torus d)) (gibbs U Φ w) = ⊤ := by
      by_contra hc
      exact ((DGPS.Lipschitz.klDiv_tilted_ne_top_iff hfm hB').1 hc) h
    rw [h, h2]
    simp only [EReal.coe_ennreal_top]
    rw [EReal.top_add_coe, EReal.top_add_coe]

theorem freeEnergy_eq_entropy_add_psi_mean (ν : ProbabilityMeasure (Torus d)) :
    freeEnergy (attractiveData hU hΦ) ν =
      ((relativeEntropy (ν : Measure (Torus d))
        (gibbs U Φ (measureMean Φ (ν : Measure (Torus d)))) : ℝ≥0∞) : EReal) +
        ((psi U Φ (measureMean Φ (ν : Measure (Torus d))) : ℝ) : EReal) := by
  rw [freeEnergy_eq_entropy_add_psi hU hΦ ν (measureMean Φ (ν : Measure (Torus d)))]
  simp

end EntropyCompletion

theorem eq_zero_of_innerR_eq_zero {u : Feature r} (h : innerR u = 0) : u = 0 := by
  have := congrArg (fun L : Feature r →L[ℝ] ℝ => L u) h
  simpa using this

section Minimizers

variable (hU : Continuous U) (hΦ : Continuous Φ)

include hU hΦ

/-- `μ` is a global minimizer of the free energy of the attractive model. -/
def IsFreeEnergyMinimizer (μ : ProbabilityMeasure (Torus d)) : Prop :=
  ∀ ν : ProbabilityMeasure (Torus d),
    freeEnergy (attractiveData hU hΦ) μ ≤ freeEnergy (attractiveData hU hΦ) ν

/-- A stationary fixed point of the attractive mean-field map: `ρ = gibbsMeasure A ρ`. -/
def IsStationaryFixedPoint (ρ : ProbabilityMeasure (Torus d)) : Prop :=
  (ρ : Measure (Torus d)) = DGPS.Lipschitz.gibbsMeasure (attractiveData hU hΦ) (ρ : Measure (Torus d))

theorem psi_le_freeEnergy (ν : ProbabilityMeasure (Torus d)) :
    ((psi U Φ (measureMean Φ (ν : Measure (Torus d))) : ℝ) : EReal) ≤
      freeEnergy (attractiveData hU hΦ) ν := by
  rw [freeEnergy_eq_entropy_add_psi_mean hU hΦ ν]
  have h : (0 : EReal) ≤ ((relativeEntropy (ν : Measure (Torus d))
      (gibbs U Φ (measureMean Φ (ν : Measure (Torus d)))) : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_nonneg _
  calc _ = (0 : EReal) + _ := (zero_add _).symm
    _ ≤ _ := add_le_add h le_rfl

theorem freeEnergy_gibbsPM (z : Feature r) :
    freeEnergy (attractiveData hU hΦ) (gibbsPM hU hΦ z) =
      ((psi U Φ z - ‖z - featureMean U Φ z‖ ^ 2 / 2 : ℝ) : EReal) := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  rw [freeEnergy_eq_entropy_add_psi hU hΦ (gibbsPM hU hΦ z) z]
  have h0 : relativeEntropy ((gibbsPM hU hΦ z : ProbabilityMeasure (Torus d)) : Measure (Torus d))
      (gibbs U Φ z) = 0 := relativeEntropy_self _
  rw [h0, EReal.coe_ennreal_zero, zero_add]
  rfl

theorem measure_eq_gibbs_of_minimizer (μ : ProbabilityMeasure (Torus d))
    (hmin : IsFreeEnergyMinimizer hU hΦ μ) :
    (μ : Measure (Torus d)) = gibbs U Φ (measureMean Φ (μ : Measure (Torus d))) := by
  rw [← gibbsMeasure_attractive hU hΦ]
  exact DGPS.Lipschitz.minimizer_eq_gibbs _ μ hmin

theorem freeEnergy_minimizer (μ : ProbabilityMeasure (Torus d))
    (hmin : IsFreeEnergyMinimizer hU hΦ μ) :
    freeEnergy (attractiveData hU hΦ) μ =
      ((psi U Φ (measureMean Φ (μ : Measure (Torus d))) : ℝ) : EReal) := by
  rw [freeEnergy_eq_entropy_add_psi_mean hU hΦ μ]
  have h0 : relativeEntropy (μ : Measure (Torus d))
      (gibbs U Φ (measureMean Φ (μ : Measure (Torus d)))) = 0 := by
    rw [← measure_eq_gibbs_of_minimizer hU hΦ μ hmin]
    exact relativeEntropy_self _
  rw [h0, EReal.coe_ennreal_zero, zero_add]

theorem psi_min_of_minimizer (μ : ProbabilityMeasure (Torus d))
    (hmin : IsFreeEnergyMinimizer hU hΦ μ) (z : Feature r) :
    psi U Φ (measureMean Φ (μ : Measure (Torus d))) ≤ psi U Φ z := by
  have h1 := hmin (gibbsPM hU hΦ z)
  rw [freeEnergy_minimizer hU hΦ μ hmin, freeEnergy_gibbsPM hU hΦ z,
    EReal.coe_le_coe_iff] at h1
  have : 0 ≤ ‖z - featureMean U Φ z‖ ^ 2 / 2 := by positivity
  linarith

theorem fderiv_psi_eq_zero_iff (z : Feature r) :
    fderiv ℝ (psi U Φ) z = 0 ↔ featureMean U Φ z = z := by
  rw [fderiv_psi hU hΦ]
  constructor
  · intro h
    exact (sub_eq_zero.1 (eq_zero_of_innerR_eq_zero h)).symm
  · intro h
    simp [h]

theorem featureMean_eq_of_psi_min {z : Feature r} (hz : ∀ y, psi U Φ z ≤ psi U Φ y) :
    featureMean U Φ z = z :=
  (fderiv_psi_eq_zero_iff hU hΦ z).1 (IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall hz))

theorem isFreeEnergyMinimizer_gibbs_of_psi_min {z : Feature r}
    (hz : ∀ y, psi U Φ z ≤ psi U Φ y) :
    IsFreeEnergyMinimizer hU hΦ (gibbsPM hU hΦ z) := by
  intro ν
  have hm := featureMean_eq_of_psi_min hU hΦ hz
  rw [freeEnergy_gibbsPM, hm]
  have e : psi U Φ z - ‖z - z‖ ^ 2 / 2 = psi U Φ z := by simp
  rw [e]
  refine (EReal.coe_le_coe_iff.2 (hz _)).trans (psi_le_freeEnergy hU hΦ ν)

/-- Critical points of `ψ` give stationary fixed points `q_z`. -/
theorem isStationaryFixedPoint_gibbs_of_critical {z : Feature r}
    (hz : fderiv ℝ (psi U Φ) z = 0) : IsStationaryFixedPoint hU hΦ (gibbsPM hU hΦ z) := by
  have hm := (fderiv_psi_eq_zero_iff hU hΦ z).1 hz
  unfold IsStationaryFixedPoint
  rw [gibbsMeasure_attractive hU hΦ]
  show gibbs U Φ z = gibbs U Φ (measureMean Φ (gibbs U Φ z))
  rw [← featureMean_eq_measureMean, hm]

/-- Stationary fixed points are of the form `q_z`, with `z = m_ρ` a critical point of `ψ`. -/
theorem eq_gibbs_of_fixedPoint {ρ : ProbabilityMeasure (Torus d)}
    (hρ : IsStationaryFixedPoint hU hΦ ρ) :
    (ρ : Measure (Torus d)) = gibbs U Φ (measureMean Φ (ρ : Measure (Torus d))) := by
  have := hρ
  unfold IsStationaryFixedPoint at this
  rw [gibbsMeasure_attractive hU hΦ] at this
  exact this

theorem critical_of_fixedPoint {ρ : ProbabilityMeasure (Torus d)}
    (hρ : IsStationaryFixedPoint hU hΦ ρ) :
    fderiv ℝ (psi U Φ) (measureMean Φ (ρ : Measure (Torus d))) = 0 := by
  rw [fderiv_psi_eq_zero_iff hU hΦ, featureMean_eq_measureMean]
  rw [← eq_gibbs_of_fixedPoint hU hΦ hρ]

end Minimizers

end DGPS.FiniteN.AttractiveLandscape
