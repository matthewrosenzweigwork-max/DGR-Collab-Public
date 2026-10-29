import DGPS.Analysis.CircleLSI
import DGPS.Analysis.RelativeFisher
import DGPS.Foundations.Entropy
import DGPS.Variational.FrozenGibbs

/-!
# Bounded-potential LSI comparison (DEF025)

Source: `campaign/frozen_gibbs_rate_comparison.md` Section 2; INTERFACES/definitions.md §5.

* `DGPS.a0 = 4π²`, the sharp Haar rate (DEF024).
* `DGPS.potentialOscillation A = osc V`, `DGPS.interactionOscillation A = osc W` (full product
  torus), `DGPS.totalOscillation A = osc V + osc W`, `DGPS.frozenLSLowerBound A = a0 e^{-M}`.
* `DGPS.boundedPerturbation_lsi`: if `P = Z⁻¹ exp(-Φ) m` is a bounded positive reference with
  `Φ x - Φ y ≤ M` for all `x, y` (oscillation of `Φ` at most `M`), then
  `a0 e^{-M} ≤ r_LS(P)`.
* `DGPS.frozenLSRateInf_lower_bound`: `a0 e^{-M} ≤ ℓ = inf_ν r_LS(P_ν)` for every continuous data
  `A`; the infimum runs over all Borel probabilities `ν`, including singular ones.

Route: entropy variational formula (`Ent_P(v) ≤ ∫ E_b(v) dP` for every `b > 0`), entropy
comparison by the upper density bound and energy comparison by the lower density bound,
`sup p / inf p ≤ e^M`, and `osc (V + W*ν) ≤ osc V + osc W` uniformly in `ν`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-! ### Definitions -/

/-- The sharp Haar logarithmic Sobolev rate `a0 = 4π²` of the unit torus. -/
noncomputable def a0 : ℝ := 4 * Real.pi ^ 2

theorem a0_pos : 0 < a0 := by unfold a0; positivity

/-- The oscillation `osc V = sup V - inf V` of the one-body potential on the full torus. -/
noncomputable def potentialOscillation (A : InteractionData d) : ℝ :=
  sSup (Set.range A.V) - sInf (Set.range A.V)

/-- The oscillation `osc W = sup W - inf W` of the interaction on the FULL product torus. -/
noncomputable def interactionOscillation (A : InteractionData d) : ℝ :=
  sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) -
    sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2)

/-- The total oscillation `M = osc V + osc W`. -/
noncomputable def totalOscillation (A : InteractionData d) : ℝ :=
  potentialOscillation A + interactionOscillation A

/-- The explicit lower bound `ℓ₀ = a0 e^{-M}` for the frozen rate infimum. -/
noncomputable def frozenLSLowerBound (A : InteractionData d) : ℝ :=
  a0 * Real.exp (-totalOscillation A)

theorem frozenLSLowerBound_pos (A : InteractionData d) : 0 < frozenLSLowerBound A :=
  mul_pos a0_pos (Real.exp_pos _)

theorem def025_V_le (A : InteractionData d) (x : Torus d) : A.V x ≤ sSup (Set.range A.V) :=
  le_csSup (isCompact_range A.V_continuous).bddAbove ⟨x, rfl⟩

theorem def025_le_V (A : InteractionData d) (x : Torus d) : sInf (Set.range A.V) ≤ A.V x :=
  csInf_le (isCompact_range A.V_continuous).bddBelow ⟨x, rfl⟩

theorem def025_W_le (A : InteractionData d) (x y : Torus d) :
    A.W x y ≤ sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) :=
  le_csSup (isCompact_range A.W_continuous).bddAbove ⟨(x, y), rfl⟩

theorem def025_le_W (A : InteractionData d) (x y : Torus d) :
    sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) ≤ A.W x y :=
  csInf_le (isCompact_range A.W_continuous).bddBelow ⟨(x, y), rfl⟩

theorem potentialOscillation_nonneg (A : InteractionData d) : 0 ≤ potentialOscillation A := by
  have := (def025_le_V A (Classical.arbitrary _)).trans (def025_V_le A (Classical.arbitrary _))
  unfold potentialOscillation
  linarith

theorem interactionOscillation_nonneg (A : InteractionData d) : 0 ≤ interactionOscillation A := by
  have := (def025_le_W A (Classical.arbitrary _) (Classical.arbitrary _)).trans
    (def025_W_le A (Classical.arbitrary _) (Classical.arbitrary _))
  unfold interactionOscillation
  linarith

theorem totalOscillation_nonneg (A : InteractionData d) : 0 ≤ totalOscillation A :=
  add_nonneg (potentialOscillation_nonneg A) (interactionOscillation_nonneg A)

/-! ### The entropy variational inequality -/

theorem def025_entropyIntegrand_sub {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) :
    entropyIntegrand a t = entropyIntegrand b t - t * Real.log (a / b) - b + a := by
  by_cases ht : t = 0
  · simp [entropyIntegrand, ht]
  · unfold entropyIntegrand
    rw [Real.log_div ht ha.ne', Real.log_div ht hb.ne', Real.log_div ha.ne' hb.ne']
    ring

theorem def025_measurable_entropyIntegrand (b : ℝ) : Measurable (entropyIntegrand b) := by
  unfold entropyIntegrand
  exact ((measurable_id.mul ((measurable_id.div_const b).log)).sub measurable_id).add_const b

/-- Entropy variational inequality: `Ent_P(v) ≤ ∫ (v log (v/b) - v + b) dP` for every `b > 0`. -/
theorem def025_entropy_le_lintegral {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {v : α → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hv : Integrable v P) {b : ℝ}
    (hb : 0 < b) :
    homogeneousEntropy P v ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand b (v x)) ∂P := by
  by_cases ha0 : ∫ x, v x ∂P = 0
  · rw [homogeneousEntropy_of_integral_eq_zero ha0]; exact bot_le
  by_cases htop : ∫⁻ x, ENNReal.ofReal (entropyIntegrand b (v x)) ∂P = ⊤
  · rw [htop]; exact le_top
  set a := ∫ x, v x ∂P with ha
  have hapos : 0 < a := lt_of_le_of_ne (integral_nonneg hv0) (Ne.symm ha0)
  have hmeas : AEStronglyMeasurable (fun x => entropyIntegrand b (v x)) P :=
    ((def025_measurable_entropyIntegrand b).comp_aemeasurable hv.aemeasurable).aestronglyMeasurable
  have hnn : ∀ x, 0 ≤ entropyIntegrand b (v x) := fun x => entropyIntegrand_nonneg hb (hv0 x)
  have hIb : Integrable (fun x => entropyIntegrand b (v x)) P := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ x, ‖entropyIntegrand b (v x)‖ₑ = ENNReal.ofReal (entropyIntegrand b (v x)) :=
      fun x => Real.enorm_eq_ofReal (hnn x)
    simp_rw [this]
    exact lt_top_iff_ne_top.2 htop
  have hpt : ∀ x, entropyIntegrand a (v x) =
      entropyIntegrand b (v x) - v x * Real.log (a / b) - b + a :=
    fun x => def025_entropyIntegrand_sub hapos hb
  have hIa : Integrable (fun x => entropyIntegrand a (v x)) P := by
    simp_rw [hpt]
    exact (((hIb.sub (hv.mul_const _)).sub (integrable_const b)).add (integrable_const a))
  have hint : ∫ x, entropyIntegrand a (v x) ∂P =
      ∫ x, entropyIntegrand b (v x) ∂P - (a * Real.log (a / b) + b - a) := by
    simp_rw [hpt]
    have i1 : Integrable (fun x => entropyIntegrand b (v x) - v x * Real.log (a / b)) P :=
      hIb.sub (hv.mul_const _)
    have i2 : Integrable (fun x => entropyIntegrand b (v x) - v x * Real.log (a / b) - b) P :=
      i1.sub (integrable_const b)
    rw [integral_add i2 (integrable_const a), integral_sub i1 (integrable_const b),
      integral_sub hIb (hv.mul_const _), integral_mul_const]
    simp [ha]
    ring
  have hc : 0 ≤ a * Real.log (a / b) + b - a := by
    have := entropyIntegrand_nonneg hb hapos.le
    unfold entropyIntegrand at this
    linarith
  rw [homogeneousEntropy_of_integral_ne_zero ha0, ← ha,
    ← ofReal_integral_eq_lintegral_ofReal hIa (Eventually.of_forall fun x =>
      entropyIntegrand_nonneg hapos (hv0 x)),
    ← ofReal_integral_eq_lintegral_ofReal hIb (Eventually.of_forall hnn)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Comparison of reference measures -/

theorem def025_measure_le_smul (P : BoundedPositiveReference d) {C : ℝ}
    (h : ∀ᵐ x ∂haar d, P.density x ≤ C) : P.measure ≤ ENNReal.ofReal C • haar d := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [BoundedPositiveReference.measure, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul,
    ← setLIntegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae h] with x hx
  exact ENNReal.ofReal_le_ofReal hx

theorem def025_haar_le_smul (P : BoundedPositiveReference d) {c : ℝ} (hc : 0 < c)
    (h : ∀ᵐ x ∂haar d, c ≤ P.density x) : haar d ≤ ENNReal.ofReal c⁻¹ • P.measure := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [BoundedPositiveReference.measure, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul _ P.measurable_ofReal_density, ← setLIntegral_one]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  linarith

/-- Entropy comparison by the upper density bound: `Ent_P(v) ≤ C · Ent_m(v)`, provided `Ent_P(v)`
is not the trivial zero case. -/
theorem def025_entropy_comparison (P : BoundedPositiveReference d) {C : ℝ}
    (hC : ∀ᵐ x ∂haar d, P.density x ≤ C) {v : Torus d → ℝ} (hv0 : ∀ x, 0 ≤ v x)
    (hv : Integrable v (haar d)) :
    homogeneousEntropy P.measure v ≤ ENNReal.ofReal C * homogeneousEntropy (haar d) v := by
  have hvP : Integrable v P.measure := P.memLp_measure_iff.2
    (memLp_one_iff_integrable.2 hv) |>.integrable le_rfl
  by_cases haP : ∫ x, v x ∂P.measure = 0
  · rw [homogeneousEntropy_of_integral_eq_zero haP]; exact bot_le
  have hbpos : 0 < ∫ x, v x ∂haar d := by
    refine lt_of_le_of_ne (integral_nonneg hv0) fun h0 => haP ?_
    have hz : v =ᵐ[haar d] 0 := (integral_eq_zero_iff_of_nonneg hv0 hv).1 h0.symm
    exact integral_eq_zero_of_ae (P.measure_ac_haar.ae_le hz)
  calc homogeneousEntropy P.measure v
      ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂haar d) (v x)) ∂P.measure :=
        def025_entropy_le_lintegral hv0 hvP hbpos
    _ ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂haar d) (v x))
          ∂(ENNReal.ofReal C • haar d) := lintegral_mono' (def025_measure_le_smul P hC) le_rfl
    _ = ENNReal.ofReal C * homogeneousEntropy (haar d) v := by
        rw [lintegral_smul_measure, smul_eq_mul,
          homogeneousEntropy_of_integral_ne_zero hbpos.ne']

/-! ### LSI transfer under two-sided density bounds -/

/-- If the density of `P` lies a.e. between `c > 0` and `C`, then `r_LS(P) ≥ a0 c / C`. -/
theorem def025_lsi_of_density_bounds (P : BoundedPositiveReference d) {c C : ℝ} (hc : 0 < c)
    (hcl : ∀ᵐ x ∂haar d, c ≤ P.density x) (hCu : ∀ᵐ x ∂haar d, P.density x ≤ C) :
    ENNReal.ofReal (a0 * c / C) ≤ ordinaryLSRate P := by
  have hCpos : 0 < C := by
    obtain ⟨x, h1, h2⟩ := (hcl.and hCu).exists
    linarith
  unfold ordinaryLSRate
  refine le_iInf fun ⟨f, hf, hent⟩ => ?_
  have hW := isWeightedWeakGradient_weightedGradient P hf
  have hg : IsWeakGradient f (weightedGradient P f hf) := (isWeightedWeakGradient_iff P).1 hW
  set g := weightedGradient P f hf with hgdef
  have hLSI := haar_torus_lsi d f g hg
  have hv : Integrable (fun x => f x ^ 2) (haar d) := hg.memLp.integrable_sq
  have hent1 := def025_entropy_comparison P hCu (fun x => sq_nonneg (f x)) hv
  -- energy comparison by the lower bound
  have hen : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure := by
    calc ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d
        ≤ ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂(ENNReal.ofReal c⁻¹ • P.measure) :=
          lintegral_mono' (def025_haar_le_smul P hc hcl) le_rfl
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure := by
          rw [lintegral_smul_measure, smul_eq_mul]
          congr 1
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  set E := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure with hE
  have hEtop : E ≠ ⊤ := by
    have hi : Integrable (fun x => ‖g x‖ ^ 2) P.measure := hW.memLp_grad.norm.integrable_sq
    have := hi.lintegral_lt_top
    rw [hE]
    refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr fun x => ?_) this)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hchain : homogeneousEntropy P.measure (fun x => f x ^ 2) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) * (ENNReal.ofReal c⁻¹ * E)) :=
    hent1.trans (mul_le_mul' le_rfl (hLSI.trans (mul_le_mul' le_rfl hen)))
  have hchaintop : homogeneousEntropy P.measure (fun x => f x ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEtop))) hchain
  show ENNReal.ofReal (a0 * c / C) ≤ 2 * (∫⁻ x, ‖weightedGradient P f hf x‖ₑ ^ 2 ∂P.measure) /
      homogeneousEntropy P.measure (fun x => f x ^ 2)
  rw [← hgdef, ← hE, ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hchaintop)]
  calc ENNReal.ofReal (a0 * c / C) * homogeneousEntropy P.measure (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (a0 * c / C) *
          (ENNReal.ofReal C * (ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) * (ENNReal.ofReal c⁻¹ * E))) :=
        mul_le_mul' le_rfl hchain
    _ = (ENNReal.ofReal (a0 * c / C) * ENNReal.ofReal C * ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) *
          ENNReal.ofReal c⁻¹) * E := by ring
    _ = 2 * E := by
        have h1 : 0 ≤ a0 * c / C := div_nonneg (mul_nonneg a0_pos.le hc.le) hCpos.le
        have h2 : 0 ≤ a0 * c / C * C := mul_nonneg h1 hCpos.le
        have h3 : 0 ≤ a0 * c / C * C * (2 / (4 * Real.pi ^ 2)) := mul_nonneg h2 (by positivity)
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3]
        have : a0 * c / C * C * (2 / (4 * Real.pi ^ 2)) * c⁻¹ = 2 := by
          unfold a0
          field_simp
        rw [this]
        simp

/-! ### The bounded-perturbation LSI -/

/-- **DEF025 (bounded-potential LSI comparison).** If `P = Z⁻¹ exp(-Φ) m` is a bounded positive
reference on the unit torus and the oscillation of `Φ` is at most `M` (`Φ x - Φ y ≤ M` for all
`x, y`), then the ordinary logarithmic Sobolev rate of `P` is at least `a0 e^{-M}`. -/
theorem boundedPerturbation_lsi (P : BoundedPositiveReference d) (Φ : Torus d → ℝ) (Z M : ℝ)
    (hP : ∀ᵐ x ∂haar d, P.density x = Real.exp (-Φ x) / Z)
    (hosc : ∀ x y, Φ x - Φ y ≤ M) :
    ENNReal.ofReal (a0 * Real.exp (-M)) ≤ ordinaryLSRate P := by
  set q : Torus d → ℝ := fun x => Real.exp (-Φ x) / Z with hq
  have hZ : 0 < Z := by
    obtain ⟨x, h1, h2⟩ := (P.lower_le.and hP).exists
    have hp : 0 < P.density x := lt_of_lt_of_le P.lower_pos h1
    rw [h2] at hp
    by_contra hZ
    exact absurd hp (not_lt.2 (div_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (not_lt.1 hZ)))
  have hqpos : ∀ x, 0 < q x := fun x => div_pos (Real.exp_pos _) hZ
  have hqle : ∀ x y, q x ≤ Real.exp M * q y := by
    intro x y
    simp only [hq]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hZ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hosc y x])
  set pmin : ℝ := ⨅ y, q y with hpmin
  have hbdd : BddBelow (Set.range q) := ⟨0, by rintro _ ⟨y, rfl⟩; exact (hqpos y).le⟩
  have hpmin_le : ∀ x, pmin ≤ q x := fun x => ciInf_le hbdd x
  have hle_pmin : ∀ x, q x ≤ Real.exp M * pmin := by
    intro x
    have : q x / Real.exp M ≤ pmin := le_ciInf fun y => by
      rw [div_le_iff₀ (Real.exp_pos M), mul_comm]
      exact hqle x y
    rwa [div_le_iff₀ (Real.exp_pos M), mul_comm] at this
  have hpminpos : 0 < pmin := by
    have := hle_pmin (Classical.arbitrary _)
    have h2 := hqpos (Classical.arbitrary _)
    by_contra h
    have : Real.exp M * pmin ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos M).le
      (not_lt.1 h)
    linarith
  have key := def025_lsi_of_density_bounds P (c := pmin) (C := Real.exp M * pmin) hpminpos
    (hP.mono fun x hx => by rw [hx]; exact hpmin_le x)
    (hP.mono fun x hx => by rw [hx]; exact hle_pmin x)
  have heq : a0 * pmin / (Real.exp M * pmin) = a0 * Real.exp (-M) := by
    rw [Real.exp_neg]
    field_simp
  rwa [heq] at key

/-! ### Uniform oscillation of the frozen potential -/

/-- `osc (V + W*ν) ≤ osc V + osc W`, uniformly in the probability measure `ν`. -/
theorem frozenPotential_oscillation_le (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] (x y : Torus d) :
    frozenPotential A ν x - frozenPotential A ν y ≤ totalOscillation A := by
  have hcont : ∀ x : Torus d, Continuous (fun z => A.W x z) := fun x =>
    A.W_continuous.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x : Torus d, Integrable (fun z => A.W x z) ν := fun x =>
    (hcont x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hW : (∫ z, A.W x z ∂ν) - ∫ z, A.W y z ∂ν ≤ interactionOscillation A := by
    rw [← integral_sub (hint x) (hint y)]
    have := integral_mono ((hint x).sub (hint y)) (integrable_const (interactionOscillation A))
      (fun z => by
        show A.W x z - A.W y z ≤ interactionOscillation A
        unfold interactionOscillation
        linarith [def025_W_le A x z, def025_le_W A y z])
    simpa using this
  have hV : A.V x - A.V y ≤ potentialOscillation A := by
    unfold potentialOscillation
    linarith [def025_V_le A x, def025_le_V A y]
  unfold frozenPotential totalOscillation
  linarith

/-- **DEF025 (frozen-rate lower bound).** For all continuous model data `A`, the exact frozen-rate
infimum over every Borel probability `ν` (singular allowed) satisfies `ℓ ≥ a0 e^{-M}`,
`M = osc V + osc W`. -/
theorem def025_frozenLSRateInf_lower_bound (A : InteractionData d) :
    ENNReal.ofReal (a0 * Real.exp (-totalOscillation A)) ≤ frozenLSRateInf A := by
  rw [le_frozenLSRateInf_iff]
  intro ν
  exact boundedPerturbation_lsi (frozenGibbs A ν) (frozenPotential A (ν : Measure (Torus d)))
    (frozenPartition A (ν : Measure (Torus d))) (totalOscillation A)
    (Eventually.of_forall fun x => rfl)
    (fun x y => frozenPotential_oscillation_le A (ν : Measure (Torus d)) x y)

theorem frozenLSRateInf_lower_bound (d : ℕ) (_hd : 0 < d) (A : InteractionData d) :
    ENNReal.ofReal (a0 * Real.exp (-totalOscillation A)) ≤ frozenLSRateInf A :=
  def025_frozenLSRateInf_lower_bound A

theorem frozenLSRateInf_lower_bound_explicit (A : InteractionData d) :
    ENNReal.ofReal (frozenLSLowerBound A) ≤ frozenLSRateInf A :=
  def025_frozenLSRateInf_lower_bound A

/-- The frozen-rate infimum is strictly positive. -/
theorem frozenLSRateInf_pos (A : InteractionData d) : 0 < frozenLSRateInf A :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.2 (frozenLSLowerBound_pos A))
    (frozenLSRateInf_lower_bound_explicit A)

end DGPS
