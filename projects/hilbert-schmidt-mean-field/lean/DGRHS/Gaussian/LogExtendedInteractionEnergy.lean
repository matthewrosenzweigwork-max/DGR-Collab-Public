import DGRHS.Commutator.SourceLogTransportFamilyLog
import DGRHS.Kernel.Centering

/-! Extended logarithmic interaction energy of the source and its pair-integrability bridge.

Source: arXiv:2609.02743v1, `I_mu = (1/2) iint W dmu dmu` (TeX 371-378) with `W = -log|x-y|`
(s = 0), and the Theorem 2.13 hypothesis `inf_{0<=t<=T} I_{mu^t} > -infty` (TeX 871-874).
For the logarithmic kernel the double integral `iint W dmu dmu` is an improper (extended)
integral `int W^+ - int W^-` in `EReal`; the real totalized Bochner integral `interactionEnergy`
(owner convention (b), OWNER_DECISIONS_20261006) only agrees with it once the pair is integrable.
Here `sourceLogExtendedInteractionEnergy` is the source's `I_mu` in the extended convention; a
finite lower bound on it forces the negative part of the pair kernel to be integrable. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian

section Extended
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The source's double integral `iint -log|x-y| dmu dmu` as the extended value
`int W^+ - int W^-` in `EReal` (TeX 371-378, `s = 0`). -/
def sourceLogExtendedPairEnergy (μ : Measure E) : EReal :=
  ((∫⁻ p : E × E, ENNReal.ofReal ((logPhysicalPair p)⁺) ∂μ.prod μ : ℝ≥0∞) : EReal)
    - ((∫⁻ p : E × E, ENNReal.ofReal ((logPhysicalPair p)⁻) ∂μ.prod μ : ℝ≥0∞) : EReal)

/-- The source's `I_mu = (1/2) iint W dmu dmu` for `W = -log|x-y|`, in the extended convention. -/
def sourceLogExtendedInteractionEnergy (μ : Measure E) : EReal :=
  (1/2 : EReal) * sourceLogExtendedPairEnergy μ

end Extended

variable {ι : Type*} [Fintype ι]

lemma ereal_half_eq : (1/2 : EReal) = ((1/2 : ℝ) : EReal) := by
  rw [one_div, one_div, EReal.coe_inv]
  norm_cast

lemma ereal_half_pos : (0 : EReal) < 1/2 := by
  rw [ereal_half_eq]
  exact EReal.coe_pos.2 (by norm_num)

lemma ofReal_posPart_eq (x : ℝ) : ENNReal.ofReal (x⁺) = ENNReal.ofReal x := by
  rcases le_total 0 x with h | h
  · rw [posPart_eq_self.2 h]
  · rw [posPart_eq_zero.2 h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

lemma ofReal_negPart_eq (x : ℝ) : ENNReal.ofReal (x⁻) = ENNReal.ofReal (-x) := by
  rcases le_total 0 x with h | h
  · rw [negPart_eq_zero.2 h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos (by linarith)]
  · rw [negPart_eq_neg.2 h]

/-- Bounded density gives integrability of the positive part of the pair logarithmic kernel. -/
lemma sourceLog_positivePart_pair_integrable
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Integrable
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (logPhysicalPair p)⁺)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let C := M * ∫ z : EuclideanSpace ℝ ι, DGRHS.Commutator.positiveLocalLog (ι := ι) z ∂volume
  have hpt : ∀ x y : EuclideanSpace ℝ ι,
      (logPhysicalPair (x, y))⁺ = DGRHS.Commutator.positiveLocalLog (x - y) := by
    intro x y
    simp [logPhysicalPair, DGRHS.Commutator.positiveLocalLog, posPart_def]
  have hm : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (logPhysicalPair p)⁺) := by
    fun_prop [logPhysicalPair]
  have hslice : ∀ᵐ x ∂μ,
      Integrable (fun y : EuclideanSpace ℝ ι => (logPhysicalPair (x, y))⁺) μ := by
    refine Filter.Eventually.of_forall fun x => ?_
    simp_rw [hpt]
    exact (DGRHS.Commutator.positiveLocalLog_section_bound hd ρ M hM hρ x).1
  have hnorm : Integrable
      (fun x : EuclideanSpace ℝ ι => ∫ y : EuclideanSpace ℝ ι, ‖(logPhysicalPair (x, y))⁺‖ ∂μ) μ := by
    apply (integrable_const C).mono'
      (hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    have h2 := (DGRHS.Commutator.positiveLocalLog_section_bound hd ρ M hM hρ x).2
    have h3 : (∫ y : EuclideanSpace ℝ ι, ‖(logPhysicalPair (x, y))⁺‖ ∂μ) =
        ∫ y : EuclideanSpace ℝ ι, DGRHS.Commutator.positiveLocalLog (x - y) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [hpt, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    rw [h3]
    exact h2
  exact (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨hslice, hnorm⟩

/-- A finite lower bound on the extended source energy makes the pair kernel integrable, and the
real totalized interaction energy then satisfies the same lower bound. -/
lemma sourceLog_pair_integrable_of_extended_energy_lower_bound
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M J : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hI : ((-J : ℝ) : EReal) ≤ sourceLogExtendedInteractionEnergy (gaussianRieszDensityMeasure ρ)) :
    Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
    -J ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b => logPhysicalPair (a, b)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hpos := sourceLog_positivePart_pair_integrable hd ρ M hM hρ
  have hmpos : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (logPhysicalPair p)⁺) (μ.prod μ) :=
    hpos.aestronglyMeasurable
  have hPne : (∫⁻ p, ENNReal.ofReal ((logPhysicalPair p)⁺) ∂μ.prod μ) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hmpos
      (Filter.Eventually.of_forall fun p => posPart_nonneg _)).2 hpos
  have hQne : (∫⁻ p, ENNReal.ofReal ((logPhysicalPair p)⁻) ∂μ.prod μ) ≠ ∞ := by
    intro hQ
    apply EReal.coe_ne_bot (-J)
    refine le_bot_iff.1 ?_
    have : sourceLogExtendedInteractionEnergy μ = ⊥ := by
      unfold sourceLogExtendedInteractionEnergy sourceLogExtendedPairEnergy
      rw [hQ]
      have : ((⊤ : ℝ≥0∞) : EReal) = ⊤ := rfl
      rw [this, EReal.sub_top]
      exact EReal.mul_bot_of_pos ereal_half_pos
    rw [← this]
    exact hI
  have hmneg : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (logPhysicalPair p)⁻) (μ.prod μ) := by
    have hlog : Measurable (logPhysicalPair (E := EuclideanSpace ℝ ι)) := by
      fun_prop [logPhysicalPair]
    exact (hlog.neg.max measurable_const).aestronglyMeasurable
  have hneg : Integrable
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (logPhysicalPair p)⁻) (μ.prod μ) :=
    (lintegral_ofReal_ne_top_iff_integrable hmneg
      (Filter.Eventually.of_forall fun p => negPart_nonneg _)).1 hQne
  have hint : Integrable logPhysicalPair (μ.prod μ) := by
    have := hpos.sub hneg
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply]
    exact posPart_sub_negPart _
  refine ⟨hint, ?_⟩
  -- identify the real totalized value with the extended one
  have hreal : (∫ p, logPhysicalPair p ∂μ.prod μ) =
      (∫⁻ p, ENNReal.ofReal ((logPhysicalPair p)⁺) ∂μ.prod μ).toReal -
        (∫⁻ p, ENNReal.ofReal ((logPhysicalPair p)⁻) ∂μ.prod μ).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
    simp_rw [ofReal_posPart_eq, ofReal_negPart_eq]
  have hext : sourceLogExtendedInteractionEnergy μ =
      ((DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a, b)) : ℝ) : EReal) := by
    unfold sourceLogExtendedInteractionEnergy sourceLogExtendedPairEnergy DGRHS.interactionEnergy
    rw [← EReal.coe_ennreal_toReal hPne, ← EReal.coe_ennreal_toReal hQne, ← EReal.coe_sub]
    have hreal' : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
        logPhysicalPair (z.1, z.2) ∂μ.prod μ) = _ := hreal
    rw [hreal']
    rw [ereal_half_eq, ← EReal.coe_mul]
  rw [hext] at hI
  exact EReal.coe_le_coe_iff.1 hI

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sourceLog_positivePart_pair_integrable
#print axioms DGRHS.Gaussian.sourceLog_pair_integrable_of_extended_energy_lower_bound
