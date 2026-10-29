import DGRHS.Gaussian.LogPhysicalConvolution
import Batteries.Tactic.Alias

/-! Remark `rem:oneBodyExpIntegrability` (TeX lines 598-602 of
`source/extracted/DGR_PFunc_Current_20260902_145019_UTC.tex`):

  "Since `μ ∈ L^∞`, the potential `h_μ` is always bounded above, so the first condition in
  (eq:logRateExtraAssumptions) constrains only its lower tail, that is, the decay of `μ`."

Setting (logarithmic case `s = 0`, `W = g = -log |x-y|`, `h_μ(x) = ∫ W(x,y) dμ(y)`, eq:hmuImuDef):
`μ = gaussianRieszDensityMeasure ρ` is a probability measure with density `ρ ≤ M` a.e. (`μ ∈ L^∞ ∩ P`),
`d = Fintype.card ι ≥ 1`, and eq:logEnergyAssumption (`∫ |log|x-y|| dμ⊗μ < ∞`) holds.
The potential is `DGRHS.Gaussian.logPhysicalPotential μ` (the diagonal is totalized by `log 0 = 0`; for bounded densities `μ` has no atoms, so this convention is
immaterial).

* `logOneBodyPotential_bddAbove`: `h_μ` is bounded above, everywhere in `x`.
* `exp_neg_integrable_iff_truncated`: for `β ≥ 0`, `e^{-4β h} ∈ L¹(μ)` iff `e^{-4β min(h,c)} ∈ L¹(μ)`, for
  every real `c` (the integrability of the first condition of eq:logRateExtraAssumptions depends only on
  the lower tail of `h`: the values of `h` above any level `c` are irrelevant).
* `sq_integrable_of_exp_neg_integrable_of_bddAbove` and `logOneBodyPotential_sq_integrable`: the use made of
  the remark at TeX line 2106 (`x² ≤ C_β(1+e^{-4βx})` on a half line): `h_μ ∈ L²(μ)`.

Nothing here is an assumption of the first condition itself: `e^{-4β h_μ} ∈ L¹(μ)` is a hypothesis of the
last two statements exactly as printed. -/
noncomputable section
open MeasureTheory Real
namespace DGRHS.Gaussian

variable {ι : Type*} [Fintype ι]

/-- rem:oneBodyExpIntegrability, first half: for `μ ∈ L^∞ ∩ P` (density `ρ ≤ M` a.e.), `d ≥ 1`, and
eq:logEnergyAssumption, the logarithmic potential `h_μ = -log |·| * μ` is bounded above (for every `x`). -/
theorem logOneBodyPotential_bddAbove (hι : 0 < Fintype.card ι)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hlog : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => |Real.log ‖p.1 - p.2‖|)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ C : ℝ, ∀ x, logPhysicalPotential (gaussianRieszDensityMeasure ρ) x ≤ C := by
  have hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
    refine hlog.mono' ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact ((Real.measurable_log.comp (measurable_norm.comp
        (measurable_fst.sub measurable_snd))).neg).aestronglyMeasurable
    · simp [logPhysicalPair]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  have hq : (0 : ℝ) < (Fintype.card ι : ℝ) / 4 := by positivity
  have hd : 0 < (Fintype.card ι : ℝ) / 2 - (Fintype.card ι : ℝ) / 4 := by linarith
  refine ⟨gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ) / 4) (max M 0) ι,
    fun x => ?_⟩
  exact (logPhysicalPotential_proper_bounds ((Fintype.card ι : ℝ) / 4) hq hd ρ (max M 0)
    (le_max_right _ _) (hρ.mono fun y hy => hy.trans (le_max_left _ _)) hpair x).2.2

/-- rem:oneBodyExpIntegrability, second half (precise form): the first condition of
eq:logRateExtraAssumptions only involves `h` through its values below an arbitrary level `c`. -/
theorem exp_neg_integrable_iff_truncated {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] (h : E → ℝ) (hh : AEStronglyMeasurable h μ) (β c : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun x => Real.exp (-(4 * β) * h x)) μ ↔
      Integrable (fun x => Real.exp (-(4 * β) * min (h x) c)) μ := by
  have hm1 : AEStronglyMeasurable (fun x => Real.exp (-(4 * β) * h x)) μ :=
    (Real.continuous_exp.comp_aestronglyMeasurable (hh.const_mul _))
  have hm2 : AEStronglyMeasurable (fun x => Real.exp (-(4 * β) * min (h x) c)) μ :=
    (Real.continuous_exp.comp_aestronglyMeasurable
      ((continuous_id.min continuous_const).comp_aestronglyMeasurable hh |>.const_mul _))
  have hk : ∀ x, Real.exp (-(4 * β) * h x) ≤ Real.exp (-(4 * β) * min (h x) c) := by
    intro x
    refine Real.exp_le_exp.mpr ?_
    have : min (h x) c ≤ h x := min_le_left _ _
    nlinarith
  have hk2 : ∀ x, Real.exp (-(4 * β) * min (h x) c) ≤
      Real.exp (-(4 * β) * h x) + Real.exp (-(4 * β) * c) := by
    intro x
    rcases le_total (h x) c with hx | hx
    · rw [min_eq_left hx]; have := Real.exp_pos (-(4 * β) * c); linarith
    · rw [min_eq_right hx]
      have := Real.exp_pos (-(4 * β) * h x); linarith
  constructor
  · intro hi
    refine (hi.add (integrable_const (Real.exp (-(4 * β) * c)))).mono' hm2
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hk2 x
  · intro hi
    refine hi.mono' hm1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hk x

/-- rem:oneBodyExpIntegrability, second half, with the lower-tail set named: the first condition of
eq:logRateExtraAssumptions holds on `μ` iff it holds on the restriction of `μ` to the lower tail `{h < c}`
(on `{h ≥ c}` the integrand is bounded by the constant `e^{-4βc}`). -/
theorem exp_neg_integrable_iff_restrict_lowerTail {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (h : α → ℝ) (hh : AEStronglyMeasurable h μ) (β c : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun x => Real.exp (-(4 * β) * h x)) μ ↔
      Integrable (fun x => Real.exp (-(4 * β) * h x)) (μ.restrict {x | h x < c}) := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (-(4 * β) * h x)) μ :=
    (Real.continuous_exp.comp_aestronglyMeasurable (hh.const_mul _))
  have hs : NullMeasurableSet {x | h x < c} μ :=
    nullMeasurableSet_lt hh.aemeasurable aemeasurable_const
  constructor
  · intro hi
    exact hi.integrableOn
  · intro hi
    have hc : IntegrableOn (fun x => Real.exp (-(4 * β) * h x)) {x | h x < c}ᶜ μ := by
      refine (integrable_const (Real.exp (-(4 * β) * c))).mono' hm.restrict ?_
      refine (ae_restrict_iff'₀ hs.compl).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx' : c ≤ h x := not_lt.mp hx
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_nonneg hβ (sub_nonneg.2 hx')]
    have hu := integrableOn_union.2 ⟨hi, hc⟩
    rwa [Set.union_compl_self, integrableOn_univ] at hu

/-- Logarithmic-potential form of `exp_neg_integrable_iff_restrict_lowerTail` (hypotheses of
`logOneBodyPotential_bddAbove`): `e^{-4β h_μ} ∈ L¹(μ)` iff it is integrable on the lower tail `{h_μ < c}`. -/
theorem logOneBodyPotential_exp_neg_integrable_iff_restrict_lowerTail
    (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hlog : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => |Real.log ‖p.1 - p.2‖|)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (β c : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun x => Real.exp (-(4 * β) * logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
        (gaussianRieszDensityMeasure ρ) ↔
      Integrable (fun x => Real.exp (-(4 * β) * logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
        ((gaussianRieszDensityMeasure ρ).restrict
          {x | logPhysicalPotential (gaussianRieszDensityMeasure ρ) x < c}) := by
  have hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
    refine hlog.mono' ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact ((Real.measurable_log.comp (measurable_norm.comp
        (measurable_fst.sub measurable_snd))).neg).aestronglyMeasurable
    · simp [logPhysicalPair]
  exact exp_neg_integrable_iff_restrict_lowerTail _
    (logPhysicalPotential_integrable _ hpair).aestronglyMeasurable β c hβ

/-- The use of the remark at TeX line 2106: if `h ≤ C` and `e^{-4β h} ∈ L¹(μ)` (`β > 0`), then `h ∈ L²(μ)`
(from `x² ≤ C² + (8β²)⁻¹ e^{-4βx}` for `x ≤ C`). -/
theorem sq_integrable_of_exp_neg_integrable_of_bddAbove {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (h : E → ℝ) (hh : AEStronglyMeasurable h μ)
    (β C : ℝ) (hβ : 0 < β) (hC : ∀ x, h x ≤ C)
    (hexp : Integrable (fun x => Real.exp (-(4 * β) * h x)) μ) :
    Integrable (fun x => h x ^ 2) μ := by
  have hpt : ∀ x, h x ^ 2 ≤ C ^ 2 + (8 * β ^ 2)⁻¹ * Real.exp (-(4 * β) * h x) := by
    intro x
    have hE := Real.exp_pos (-(4 * β) * h x)
    have hpos : 0 < (8 * β ^ 2)⁻¹ := by positivity
    rcases le_or_gt 0 (h x) with hx | hx
    · have : h x ^ 2 ≤ C ^ 2 := by nlinarith [hC x]
      nlinarith [mul_pos hpos hE]
    · have ht : 0 ≤ -(4 * β) * h x := by nlinarith
      have hq := Real.quadratic_le_exp_of_nonneg ht
      have h2 : h x ^ 2 ≤ (8 * β ^ 2)⁻¹ * Real.exp (-(4 * β) * h x) := by
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (4 * β * h x)]
      nlinarith [sq_nonneg C]
  refine ((integrable_const (C ^ 2)).add (hexp.const_mul (8 * β ^ 2)⁻¹)).mono'
    (hh.pow 2) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hpt x

/-- Line 2106 of the TeX in the logarithmic case: under `μ ∈ L^∞ ∩ P`, eq:logEnergyAssumption and the first
condition of eq:logRateExtraAssumptions (`e^{-4β h_μ} ∈ L¹(μ)`, `β > 0`), the potential satisfies `h_μ ∈ L²(μ)`;
the upper bound needed is `logOneBodyPotential_bddAbove` (rem:oneBodyExpIntegrability). -/
theorem logOneBodyPotential_sq_integrable (hι : 0 < Fintype.card ι)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hlog : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => |Real.log ‖p.1 - p.2‖|)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (β : ℝ) (hβ : 0 < β)
    (hexp : Integrable (fun x => Real.exp (-(4 * β) * logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    Integrable (fun x => logPhysicalPotential (gaussianRieszDensityMeasure ρ) x ^ 2)
      (gaussianRieszDensityMeasure ρ) := by
  obtain ⟨C, hC⟩ := logOneBodyPotential_bddAbove hι ρ M hρ hlog
  have hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
    refine hlog.mono' ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact ((Real.measurable_log.comp (measurable_norm.comp
        (measurable_fst.sub measurable_snd))).neg).aestronglyMeasurable
    · simp [logPhysicalPair]
  exact sq_integrable_of_exp_neg_integrable_of_bddAbove _ _
    (logPhysicalPotential_integrable _ hpair).aestronglyMeasurable β C hβ hC hexp

end DGRHS.Gaussian

/-- rem:oneBodyExpIntegrability (source 598-602), upper bound of `h_μ`. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.bddAbove := DGRHS.Gaussian.logOneBodyPotential_bddAbove

/-- rem:oneBodyExpIntegrability: the first condition of eq:logRateExtraAssumptions depends only on the lower
tail of `h_μ`. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.exp_integrable_iff_truncated := DGRHS.Gaussian.exp_neg_integrable_iff_truncated

/-- rem:oneBodyExpIntegrability: the first condition of eq:logRateExtraAssumptions holds iff it holds on the
lower tail `{h < c}` (restricted measure). -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.exp_integrable_iff_restrict_lowerTail := DGRHS.Gaussian.exp_neg_integrable_iff_restrict_lowerTail

/-- Logarithmic-potential form of the lower-tail restriction. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.log_exp_integrable_iff_restrict_lowerTail := DGRHS.Gaussian.logOneBodyPotential_exp_neg_integrable_iff_restrict_lowerTail

/-- rem:oneBodyExpIntegrability, consequence used at source line 2106: `h ≤ C`, `e^{-4βh} ∈ L¹` imply `h ∈ L²`. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.sq_integrable_of_bddAbove := DGRHS.Gaussian.sq_integrable_of_exp_neg_integrable_of_bddAbove

/-- Source line 2106 in the logarithmic case: `h_μ ∈ L²(μ)`. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.log_sq_integrable := DGRHS.Gaussian.logOneBodyPotential_sq_integrable

#print axioms DGRHS.Gaussian.logOneBodyPotential_bddAbove
#print axioms DGRHS.Gaussian.exp_neg_integrable_iff_truncated
#print axioms DGRHS.Gaussian.exp_neg_integrable_iff_restrict_lowerTail
#print axioms DGRHS.Gaussian.logOneBodyPotential_exp_neg_integrable_iff_restrict_lowerTail
#print axioms DGRHS.Gaussian.sq_integrable_of_exp_neg_integrable_of_bddAbove
#print axioms DGRHS.Gaussian.logOneBodyPotential_sq_integrable
