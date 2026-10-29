import DGPS.Analysis.BoundedPerturbation
import DGPS.Analysis.RelativeFisher
import DGPS.Equilibrium.GaussianRate
import DGPS.Variational.FrozenGibbs

/-!
# Bounded-density comparison of the ordinary LSI and Poincare rates (EX007)

Source: `campaign/a5_fully_elementary_polynomial.md` Section 3; counterexample report S8--S10.

If `P` and `Q` are bounded positive reference probabilities whose log density ratio
`log (Q.density / P.density)` has essential oscillation at most `ω`, then
`exp (-ω) * r_LS(P) ≤ r_LS(Q) ≤ exp ω * r_LS(P)`; the same two-sided factors hold for the
Poincare rates and for the rates restricted to a parity sector `{u | u (-x) = ε u x}`.

Route: the competitors (`WeightedH1`) of both rates coincide with the Haar `H¹`; the
homogeneous entropy is compared above by the upper density ratio, the Dirichlet energy below by
the lower density ratio, and the variance by `Var_ν u ≤ ∫ (u - c)² dν` for the best constant.
The sector is a condition on the competitor only, so the same invariant subspace is used for both
laws (no comparison of even and odd spectra is made).
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace DGPS.Examples

variable {d : ℕ}

/-! ### Rates restricted to a class of competitors -/

/-- The ordinary LS rate of `P` restricted to competitors satisfying `S`. -/
noncomputable def ex007_lsRateOn (P : BoundedPositiveReference d) (S : (Torus d → ℝ) → Prop) :
    ℝ≥0∞ :=
  ⨅ f : {f : Torus d → ℝ // f ∈ WeightedH1 P ∧ S f ∧
      0 < homogeneousEntropy P.measure (fun x => f x ^ 2)},
    2 * (∫⁻ x, ‖weightedGradient P f.1 f.2.1 x‖ₑ ^ 2 ∂P.measure) /
      homogeneousEntropy P.measure (fun x => f.1 x ^ 2)

/-- The Poincare rate of `μ` restricted to competitors satisfying `S`. -/
noncomputable def ex007_poincareRateOn (μ : ProbabilityMeasure (Torus d))
    (S : (Torus d → ℝ) → Prop) : ℝ≥0∞ :=
  ⨅ f : {f : WeakH1Test μ // S f.fn ∧ 0 < weightedVariance μ f.fn}, poincareQuotient μ f.1

/-- The parity sector `{u | u (-x) = ε u x a.e.}` (`ε = 1` even, `ε = -1` odd). -/
def ex007_InParitySector (ε : ℝ) (u : Torus d → ℝ) : Prop :=
  ∀ᵐ x ∂haar d, u (-x) = ε * u x

/-- The reference law `P` preserves parity: its density is even a.e. -/
def ex007_ParityPreserving (P : BoundedPositiveReference d) : Prop :=
  ∀ᵐ x ∂haar d, P.density (-x) = P.density x

theorem ex007_lsRate_eq_on (P : BoundedPositiveReference d) :
    ordinaryLSRate P = ex007_lsRateOn P (fun _ => True) := by
  unfold ordinaryLSRate ex007_lsRateOn
  refine le_antisymm (le_iInf fun f => ?_) (le_iInf fun f => ?_)
  · exact iInf_le_of_le ⟨f.1, f.2.1, f.2.2.2⟩ le_rfl
  · exact iInf_le_of_le ⟨f.1, f.2.1, trivial, f.2.2⟩ le_rfl

theorem ex007_poincareRate_eq_on (μ : ProbabilityMeasure (Torus d)) :
    poincareRate μ = ex007_poincareRateOn μ (fun _ => True) := by
  unfold poincareRate ex007_poincareRateOn
  refine le_antisymm (le_iInf fun f => ?_) (le_iInf fun f => ?_)
  · exact iInf_le_of_le ⟨f.1, f.2.2⟩ le_rfl
  · exact iInf_le_of_le ⟨f.1, trivial, f.2⟩ le_rfl

/-! ### Elementary quotient step -/

theorem ex007_div_step {a A : ℝ} (ha : 0 < a) (hA : 0 < A) {EP EQ nP nQ : ℝ≥0∞}
    (hE : ENNReal.ofReal a * EP ≤ EQ) (hn : nQ ≤ ENNReal.ofReal A * nP) (hnQ : nQ ≠ 0) :
    ENNReal.ofReal (a / A) * (EP / nP) ≤ EQ / nQ := by
  by_cases hP : nP = ⊤
  · simp [hP]
  have hP0 : nP ≠ 0 := by
    rintro rfl
    simp at hn
    exact hnQ hn
  have hQtop : nQ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP) hn
  rw [ENNReal.le_div_iff_mul_le (Or.inl hnQ) (Or.inl hQtop)]
  calc ENNReal.ofReal (a / A) * (EP / nP) * nQ
      ≤ ENNReal.ofReal (a / A) * (EP / nP) * (ENNReal.ofReal A * nP) := mul_le_mul' le_rfl hn
    _ = (ENNReal.ofReal (a / A) * ENNReal.ofReal A) * ((EP / nP) * nP) := by ring
    _ = ENNReal.ofReal a * EP := by
        rw [ENNReal.div_mul_cancel hP0 hP, ← ENNReal.ofReal_mul (div_nonneg ha.le hA.le),
          div_mul_cancel₀ _ hA.ne']
    _ ≤ EQ := hE

/-! ### Comparison of reference measures -/

theorem ex007_measure_le (P Q : BoundedPositiveReference d) {A : ℝ}
    (h : ∀ᵐ x ∂haar d, Q.density x ≤ A * P.density x) :
    Q.measure ≤ ENNReal.ofReal A • P.measure := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [BoundedPositiveReference.measure, BoundedPositiveReference.measure, withDensity_apply _ hs,
    Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul _ P.measurable_ofReal_density]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae h, ae_restrict_of_ae P.ae_pos] with x hx hp
  rw [← ENNReal.ofReal_mul'  (hp.le)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem ex007_le_measure (P Q : BoundedPositiveReference d) {a : ℝ} (ha : 0 < a)
    (h : ∀ᵐ x ∂haar d, a * P.density x ≤ Q.density x) :
    ENNReal.ofReal a • P.measure ≤ Q.measure := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [BoundedPositiveReference.measure, BoundedPositiveReference.measure, withDensity_apply _ hs,
    Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul _ P.measurable_ofReal_density]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [← ENNReal.ofReal_mul ha.le]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Entropy comparison by an upper measure bound. -/
theorem ex007_entropy_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C : ℝ}
    (hle : ν ≤ ENNReal.ofReal C • μ) {v : α → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hv : Integrable v μ) :
    homogeneousEntropy ν v ≤ ENNReal.ofReal C * homogeneousEntropy μ v := by
  have hvν : Integrable v ν := hv.of_measure_le_smul (by simp) hle
  by_cases hν : ∫ x, v x ∂ν = 0
  · rw [homogeneousEntropy_of_integral_eq_zero hν]; exact bot_le
  have hbpos : 0 < ∫ x, v x ∂μ := by
    refine lt_of_le_of_ne (integral_nonneg hv0) fun h0 => hν ?_
    have hz : v =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hv0 hv).1 h0.symm
    have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hle
    exact integral_eq_zero_of_ae (hac.ae_le hz)
  calc homogeneousEntropy ν v
      ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂μ) (v x)) ∂ν :=
        def025_entropy_le_lintegral hv0 hvν hbpos
    _ ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂μ) (v x))
          ∂(ENNReal.ofReal C • μ) := lintegral_mono' hle le_rfl
    _ = ENNReal.ofReal C * homogeneousEntropy μ v := by
        rw [lintegral_smul_measure, smul_eq_mul,
          homogeneousEntropy_of_integral_ne_zero hbpos.ne']

/-! ### LS core -/

theorem ex007_lsRateOn_core (P Q : BoundedPositiveReference d) (S : (Torus d → ℝ) → Prop)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (h1 : ∀ᵐ x ∂haar d, a * P.density x ≤ Q.density x)
    (h2 : ∀ᵐ x ∂haar d, Q.density x ≤ A * P.density x) :
    ENNReal.ofReal (a / A) * ex007_lsRateOn P S ≤ ex007_lsRateOn Q S := by
  unfold ex007_lsRateOn
  refine le_iInf fun f => ?_
  obtain ⟨f, hfQ, hS, hEntQ⟩ := f
  have hfP : f ∈ WeightedH1 P := (mem_weightedH1_iff P).2 ((mem_weightedH1_iff Q).1 hfQ)
  have hWP := isWeightedWeakGradient_weightedGradient P hfP
  have hWQ := isWeightedWeakGradient_weightedGradient Q hfQ
  have hv : Integrable (fun x => f x ^ 2) P.measure := hWP.memLp.integrable_sq
  have hEnt : homogeneousEntropy Q.measure (fun x => f x ^ 2) ≤
      ENNReal.ofReal A * homogeneousEntropy P.measure (fun x => f x ^ 2) :=
    ex007_entropy_le (ex007_measure_le P Q h2) (fun x => sq_nonneg (f x)) hv
  have hEntP : 0 < homogeneousEntropy P.measure (fun x => f x ^ 2) := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hEnt
    exact hEntQ.ne' (le_antisymm hEnt bot_le)
  have hg : weightedGradient P f hfP =ᵐ[haar d] weightedGradient Q f hfQ :=
    weightedGradient_ae_eq P hfP ((isWeightedWeakGradient_iff Q).1 hWQ)
  have hgQ : weightedGradient P f hfP =ᵐ[Q.measure] weightedGradient Q f hfQ :=
    Q.measure_ac_haar.ae_le hg
  have hEn : ENNReal.ofReal a * (∫⁻ x, ‖weightedGradient P f hfP x‖ₑ ^ 2 ∂P.measure) ≤
      ∫⁻ x, ‖weightedGradient Q f hfQ x‖ₑ ^ 2 ∂Q.measure := by
    calc ENNReal.ofReal a * (∫⁻ x, ‖weightedGradient P f hfP x‖ₑ ^ 2 ∂P.measure)
        = ∫⁻ x, ‖weightedGradient P f hfP x‖ₑ ^ 2 ∂(ENNReal.ofReal a • P.measure) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ x, ‖weightedGradient P f hfP x‖ₑ ^ 2 ∂Q.measure :=
          lintegral_mono' (ex007_le_measure P Q ha h1) le_rfl
      _ = _ := lintegral_congr_ae (hgQ.mono fun x hx => by simp only [hx])
  calc ENNReal.ofReal (a / A) * (⨅ g : {f : Torus d → ℝ // f ∈ WeightedH1 P ∧ S f ∧
        0 < homogeneousEntropy P.measure (fun x => f x ^ 2)},
        2 * (∫⁻ x, ‖weightedGradient P g.1 g.2.1 x‖ₑ ^ 2 ∂P.measure) /
          homogeneousEntropy P.measure (fun x => g.1 x ^ 2))
      ≤ ENNReal.ofReal (a / A) * (2 * (∫⁻ x, ‖weightedGradient P f hfP x‖ₑ ^ 2 ∂P.measure) /
          homogeneousEntropy P.measure (fun x => f x ^ 2)) :=
        mul_le_mul' le_rfl (iInf_le (fun g : {f : Torus d → ℝ // f ∈ WeightedH1 P ∧ S f ∧
          0 < homogeneousEntropy P.measure (fun x => f x ^ 2)} =>
            2 * (∫⁻ x, ‖weightedGradient P g.1 g.2.1 x‖ₑ ^ 2 ∂P.measure) /
              homogeneousEntropy P.measure (fun x => g.1 x ^ 2)) ⟨f, hfP, hS, hEntP⟩)
    _ ≤ _ := ex007_div_step ha hA (by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal a) 2, mul_assoc]
          exact mul_le_mul' le_rfl hEn) hEnt hEntQ.ne'

/-! ### Poincare core -/

theorem ex007_var_le_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {u : α → ℝ} (hu : MemLp u 2 ν) (c : ℝ) :
    ∫ x, (u x - ∫ y, u y ∂ν) ^ 2 ∂ν ≤ ∫ x, (u x - c) ^ 2 ∂ν := by
  set m := ∫ y, u y ∂ν with hm
  have hi : Integrable u ν := hu.integrable one_le_two
  have h2 : Integrable (fun x => (u x - m) ^ 2) ν := (hu.sub (memLp_const m)).integrable_sq
  have hl : Integrable (fun x => u x - m) ν := hi.sub (integrable_const m)
  have hexp : ∀ x, (u x - c) ^ 2 = (u x - m) ^ 2 + 2 * (m - c) * (u x - m) + (m - c) ^ 2 := by
    intro x; ring
  rw [show (fun x => (u x - c) ^ 2) = fun x => (u x - m) ^ 2 + 2 * (m - c) * (u x - m) +
    (m - c) ^ 2 from funext hexp]
  have h3 : Integrable (fun x => (u x - m) ^ 2 + 2 * (m - c) * (u x - m)) ν :=
    h2.add (hl.const_mul _)
  have h4 : Integrable (fun x => 2 * (m - c) * (u x - m)) ν := hl.const_mul _
  rw [integral_add h3 (integrable_const _), integral_add h2 h4,
    integral_const_mul, integral_sub hi (integrable_const m)]
  simp [hm]
  positivity

theorem ex007_variance_le {μ ν : ProbabilityMeasure (Torus d)} {A : ℝ} (hA : 0 < A)
    (hle : (ν : Measure (Torus d)) ≤ ENNReal.ofReal A • (μ : Measure (Torus d)))
    {u : Torus d → ℝ} (huν : MemLp u 2 (ν : Measure (Torus d)))
    (huμ : MemLp u 2 (μ : Measure (Torus d))) :
    weightedVariance ν u ≤ A * weightedVariance μ u := by
  set c := ∫ y, u y ∂(μ : Measure (Torus d)) with hc
  have hint : Integrable (fun x => (u x - c) ^ 2) (μ : Measure (Torus d)) :=
    (huμ.sub (memLp_const c)).integrable_sq
  calc weightedVariance ν u ≤ ∫ x, (u x - c) ^ 2 ∂(ν : Measure (Torus d)) :=
        ex007_var_le_sq huν c
    _ ≤ ∫ x, (u x - c) ^ 2 ∂(ENNReal.ofReal A • (μ : Measure (Torus d))) :=
        integral_mono_measure hle (Eventually.of_forall fun x => sq_nonneg _)
          (hint.smul_measure (by simp))
    _ = A * weightedVariance μ u := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hA.le, smul_eq_mul]
        rfl

theorem ex007_poincareRateOn_core {μP μQ : ProbabilityMeasure (Torus d)}
    (S : (Torus d → ℝ) → Prop) {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (h1 : ENNReal.ofReal a • (μP : Measure (Torus d)) ≤ (μQ : Measure (Torus d)))
    (h2 : (μQ : Measure (Torus d)) ≤ ENNReal.ofReal A • (μP : Measure (Torus d)))
    (htrans : ∀ f : WeakH1Test μQ, IsMeasureWeakGradient μP f.fn f.grad) :
    ENNReal.ofReal (a / A) * ex007_poincareRateOn μP S ≤ ex007_poincareRateOn μQ S := by
  unfold ex007_poincareRateOn
  refine le_iInf fun f => ?_
  obtain ⟨f, hS, hvarQ⟩ := f
  have hwP := htrans f
  let f' : WeakH1Test μP := ⟨f.fn, f.grad, hwP⟩
  have hvar : weightedVariance μQ f.fn ≤ A * weightedVariance μP f'.fn :=
    ex007_variance_le hA h2 f.isWeak.memLp hwP.memLp
  have hvarP : 0 < weightedVariance μP f'.fn := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hA.le (not_lt.1 hneg)
    linarith
  have hEn : ENNReal.ofReal a * dirichletEnergy μP f' ≤ dirichletEnergy μQ f := by
    unfold dirichletEnergy
    calc ENNReal.ofReal a * (∫⁻ x, ‖f'.grad x‖ₑ ^ 2 ∂(μP : Measure (Torus d)))
        = ∫⁻ x, ‖f'.grad x‖ₑ ^ 2 ∂(ENNReal.ofReal a • (μP : Measure (Torus d))) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ _ := lintegral_mono' h1 le_rfl
  calc ENNReal.ofReal (a / A) * (⨅ g : {g : WeakH1Test μP // S g.fn ∧ 0 < weightedVariance μP g.fn},
        poincareQuotient μP g.1)
      ≤ ENNReal.ofReal (a / A) * poincareQuotient μP f' :=
        mul_le_mul' le_rfl (iInf_le (fun g : {g : WeakH1Test μP //
          S g.fn ∧ 0 < weightedVariance μP g.fn} => poincareQuotient μP g.1) ⟨f', hS, hvarP⟩)
    _ ≤ poincareQuotient μQ f := by
        unfold poincareQuotient
        refine ex007_div_step ha hA hEn ?_ (ENNReal.ofReal_pos.2 hvarQ).ne'
        rw [← ENNReal.ofReal_mul hA.le]
        exact ENNReal.ofReal_le_ofReal hvar

/-! ### From essential oscillation to a density sandwich -/

private theorem ex007_ess_osc (P Q : BoundedPositiveReference d) (ω : ℝ)
    (hosc : ∀ᵐ x ∂haar d, ∀ᵐ y ∂haar d,
      Real.log (Q.density x / P.density x) - Real.log (Q.density y / P.density y) ≤ ω) :
    ∃ m : ℝ, ∀ᵐ x ∂haar d, m ≤ Real.log (Q.density x / P.density x) ∧
      Real.log (Q.density x / P.density x) ≤ m + ω := by
  set L : Torus d → ℝ := fun x => Real.log (Q.density x / P.density x) with hL
  have hLm : Measurable L := (Q.measurable_density.div P.measurable_density).log
  have hosc' : ∀ᵐ y ∂haar d, ∀ᵐ x ∂haar d, L x - L y ≤ ω := by
    have hms : MeasurableSet {p : Torus d × Torus d | L p.1 - L p.2 ≤ ω} :=
      measurableSet_le ((hLm.comp measurable_fst).sub (hLm.comp measurable_snd)) measurable_const
    exact (Measure.ae_ae_comm hms).1 hosc
  have hbd : ∀ᵐ x ∂haar d, Real.log (Q.lower / P.upper) ≤ L x ∧
      L x ≤ Real.log (Q.upper / P.lower) := by
    filter_upwards [P.lower_le, P.le_upper, Q.lower_le, Q.le_upper] with x h1 h2 h3 h4
    have hP := P.lower_pos
    have hQ := Q.lower_pos
    have hPx : 0 < P.density x := lt_of_lt_of_le hP h1
    have hQx : 0 < Q.density x := lt_of_lt_of_le hQ h3
    have hPu : 0 < P.upper := lt_of_lt_of_le hPx h2
    have hQu : 0 < Q.upper := lt_of_lt_of_le hQx h4
    exact ⟨Real.log_le_log (div_pos hQ hPu) (div_le_div₀ hQx.le h3 hPx h2),
      Real.log_le_log (div_pos hQx hPx) (div_le_div₀ hQu.le h4 hP h1)⟩
  set T : Set ℝ := {t | ∀ᵐ x ∂haar d, t ≤ L x} with hT
  have hTne : T.Nonempty := ⟨Real.log (Q.lower / P.upper), hbd.mono fun x h => h.1⟩
  have hTbdd : BddAbove T := by
    refine ⟨Real.log (Q.upper / P.lower), fun t ht => ?_⟩
    obtain ⟨x, h1, h2, h3⟩ := ((show ∀ᵐ x ∂haar d, t ≤ L x from ht).and hbd).exists
    exact h1.trans h3
  refine ⟨sSup T, ?_⟩
  have hlow : ∀ᵐ x ∂haar d, sSup T ≤ L x := by
    have h : ∀ᵐ x ∂haar d, ∀ n : ℕ, sSup T - 1 / ((n : ℝ) + 1) < L x := by
      rw [ae_all_iff]
      intro n
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hTne
        (show sSup T - 1 / ((n : ℝ) + 1) < sSup T by linarith)
      filter_upwards [ht] with x hx
      linarith
    filter_upwards [h] with x hx
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    have := hx n
    linarith
  have key : ∀ t, sSup T < t → ∀ᵐ x ∂haar d, L x ≤ t + ω := by
    intro t ht
    have hnT : t ∉ T := fun h => absurd (le_csSup hTbdd h) (not_le.2 ht)
    by_contra hcon
    apply hnT
    filter_upwards [hosc'] with y hy
    by_contra hlt
    push Not at hlt
    exact hcon (hy.mono fun x hx => by linarith)
  have hup : ∀ᵐ x ∂haar d, L x ≤ sSup T + ω := by
    have h : ∀ᵐ x ∂haar d, ∀ n : ℕ, L x ≤ sSup T + 1 / ((n : ℝ) + 1) + ω := by
      rw [ae_all_iff]
      intro n
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact key (sSup T + 1 / ((n : ℝ) + 1)) (by linarith)
    filter_upwards [h] with x hx
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    have := hx n
    linarith
  filter_upwards [hlow, hup] with x h1 h2 using ⟨h1, h2⟩

private theorem ex007_sandwich (P Q : BoundedPositiveReference d) (ω m : ℝ)
    (h : ∀ᵐ x ∂haar d, m ≤ Real.log (Q.density x / P.density x) ∧
      Real.log (Q.density x / P.density x) ≤ m + ω) :
    (∀ᵐ x ∂haar d, Real.exp m * P.density x ≤ Q.density x) ∧
      (∀ᵐ x ∂haar d, Q.density x ≤ Real.exp (m + ω) * P.density x) := by
  constructor
  · filter_upwards [h, P.ae_pos, Q.ae_pos] with x hx hp hq
    exact (le_div_iff₀ hp).1 ((Real.le_log_iff_exp_le (div_pos hq hp)).1 hx.1)
  · filter_upwards [h, P.ae_pos, Q.ae_pos] with x hx hp hq
    exact (div_le_iff₀ hp).1 ((Real.log_le_iff_le_exp (div_pos hq hp)).1 hx.2)

theorem ex007_two_sided {R : BoundedPositiveReference d → ℝ≥0∞}
    (hcore : ∀ (P Q : BoundedPositiveReference d) (a A : ℝ), 0 < a → 0 < A →
      (∀ᵐ x ∂haar d, a * P.density x ≤ Q.density x) →
      (∀ᵐ x ∂haar d, Q.density x ≤ A * P.density x) →
      ENNReal.ofReal (a / A) * R P ≤ R Q)
    (P Q : BoundedPositiveReference d) (ω : ℝ)
    (hosc : ∀ᵐ x ∂haar d, ∀ᵐ y ∂haar d,
      Real.log (Q.density x / P.density x) - Real.log (Q.density y / P.density y) ≤ ω) :
    ENNReal.ofReal (Real.exp (-ω)) * R P ≤ R Q ∧
      R Q ≤ ENNReal.ofReal (Real.exp ω) * R P := by
  obtain ⟨m, hm⟩ := ex007_ess_osc P Q ω hosc
  obtain ⟨h1, h2⟩ := ex007_sandwich P Q ω m hm
  have hfwd : ENNReal.ofReal (Real.exp (-ω)) * R P ≤ R Q := by
    have := hcore P Q (Real.exp m) (Real.exp (m + ω)) (Real.exp_pos _) (Real.exp_pos _) h1 h2
    have e : Real.exp m / Real.exp (m + ω) = Real.exp (-ω) := by
      rw [← Real.exp_sub]; congr 1; ring
    rwa [e] at this
  refine ⟨hfwd, ?_⟩
  have h1' : ∀ᵐ x ∂haar d, Real.exp (-(m + ω)) * Q.density x ≤ P.density x := by
    filter_upwards [h2] with x hx
    calc Real.exp (-(m + ω)) * Q.density x
        ≤ Real.exp (-(m + ω)) * (Real.exp (m + ω) * P.density x) :=
          mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = P.density x := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have h2' : ∀ᵐ x ∂haar d, P.density x ≤ Real.exp (-m) * Q.density x := by
    filter_upwards [h1] with x hx
    calc P.density x = Real.exp (-m) * (Real.exp m * P.density x) := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (-m) * Q.density x := mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
  have hbwd := hcore Q P (Real.exp (-(m + ω))) (Real.exp (-m)) (Real.exp_pos _) (Real.exp_pos _)
    h1' h2'
  have e : Real.exp (-(m + ω)) / Real.exp (-m) = Real.exp (-ω) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [e] at hbwd
  calc R Q = ENNReal.ofReal (Real.exp ω) * (ENNReal.ofReal (Real.exp (-ω)) * R Q) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp
    _ ≤ ENNReal.ofReal (Real.exp ω) * R P := mul_le_mul' le_rfl hbwd

/-! ### The comparison theorem -/

private theorem ex007_poincare_trans (P Q : BoundedPositiveReference d)
    (f : WeakH1Test (⟨Q.measure, Q.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d))) :
    IsMeasureWeakGradient (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d))
      f.fn f.grad :=
  (isMeasureWeakGradient_iff P).2 ((isWeightedWeakGradient_iff P).2
    ((isWeightedWeakGradient_iff Q).1 ((isMeasureWeakGradient_iff Q).1 f.isWeak)))

private theorem ex007_poincare_core' (S : (Torus d → ℝ) → Prop) (P Q : BoundedPositiveReference d)
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A)
    (h1 : ∀ᵐ x ∂haar d, a * P.density x ≤ Q.density x)
    (h2 : ∀ᵐ x ∂haar d, Q.density x ≤ A * P.density x) :
    ENNReal.ofReal (a / A) * ex007_poincareRateOn ⟨P.measure, P.isProbabilityMeasure⟩ S ≤
      ex007_poincareRateOn ⟨Q.measure, Q.isProbabilityMeasure⟩ S :=
  ex007_poincareRateOn_core S ha hA (ex007_le_measure P Q ha h1) (ex007_measure_le P Q h2)
    (ex007_poincare_trans P Q)

/-- **EX007.** Ordinary LSI bounded-density comparison. If `P`, `Q` are bounded positive
reference probabilities with `osc (log (Q.density / P.density)) ≤ ω` (essential oscillation, i.e.
for almost every pair of points), then
`exp (-ω) r_LS(P) ≤ r_LS(Q) ≤ exp ω r_LS(P)`, the same holds for the Poincare rates, and, when
both laws preserve parity, for the LS and Poincare rates restricted to the common parity sector
`{u | u (-x) = ε u x}`, `ε = ±1`. -/
theorem ordinary_lsi_bounded_density_comparison (P Q : BoundedPositiveReference d) (ω : ℝ)
    (hosc : ∀ᵐ x ∂haar d, ∀ᵐ y ∂haar d,
      Real.log (Q.density x / P.density x) - Real.log (Q.density y / P.density y) ≤ ω) :
    (ENNReal.ofReal (Real.exp (-ω)) * ordinaryLSRate P ≤ ordinaryLSRate Q ∧
      ordinaryLSRate Q ≤ ENNReal.ofReal (Real.exp ω) * ordinaryLSRate P) ∧
    (ENNReal.ofReal (Real.exp (-ω)) * poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ ≤
        poincareRate ⟨Q.measure, Q.isProbabilityMeasure⟩ ∧
      poincareRate ⟨Q.measure, Q.isProbabilityMeasure⟩ ≤
        ENNReal.ofReal (Real.exp ω) * poincareRate ⟨P.measure, P.isProbabilityMeasure⟩) ∧
    (ex007_ParityPreserving P → ex007_ParityPreserving Q → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (ENNReal.ofReal (Real.exp (-ω)) * ex007_lsRateOn P (ex007_InParitySector ε) ≤
          ex007_lsRateOn Q (ex007_InParitySector ε) ∧
        ex007_lsRateOn Q (ex007_InParitySector ε) ≤
          ENNReal.ofReal (Real.exp ω) * ex007_lsRateOn P (ex007_InParitySector ε)) ∧
      (ENNReal.ofReal (Real.exp (-ω)) *
            ex007_poincareRateOn ⟨P.measure, P.isProbabilityMeasure⟩ (ex007_InParitySector ε) ≤
          ex007_poincareRateOn ⟨Q.measure, Q.isProbabilityMeasure⟩ (ex007_InParitySector ε) ∧
        ex007_poincareRateOn ⟨Q.measure, Q.isProbabilityMeasure⟩ (ex007_InParitySector ε) ≤
          ENNReal.ofReal (Real.exp ω) *
            ex007_poincareRateOn ⟨P.measure, P.isProbabilityMeasure⟩
              (ex007_InParitySector ε))) := by
  have hLS : ∀ S : (Torus d → ℝ) → Prop,
      ENNReal.ofReal (Real.exp (-ω)) * ex007_lsRateOn P S ≤ ex007_lsRateOn Q S ∧
        ex007_lsRateOn Q S ≤ ENNReal.ofReal (Real.exp ω) * ex007_lsRateOn P S := fun S =>
    ex007_two_sided (R := fun P => ex007_lsRateOn P S)
      (fun P Q a A ha hA h1 h2 => ex007_lsRateOn_core P Q S ha hA h1 h2) P Q ω hosc
  have hPC : ∀ S : (Torus d → ℝ) → Prop,
      ENNReal.ofReal (Real.exp (-ω)) *
          ex007_poincareRateOn ⟨P.measure, P.isProbabilityMeasure⟩ S ≤
        ex007_poincareRateOn ⟨Q.measure, Q.isProbabilityMeasure⟩ S ∧
      ex007_poincareRateOn ⟨Q.measure, Q.isProbabilityMeasure⟩ S ≤
        ENNReal.ofReal (Real.exp ω) *
          ex007_poincareRateOn ⟨P.measure, P.isProbabilityMeasure⟩ S := fun S =>
    ex007_two_sided
      (R := fun P => ex007_poincareRateOn ⟨P.measure, P.isProbabilityMeasure⟩ S)
      (fun P Q a A ha hA h1 h2 => ex007_poincare_core' S P Q a A ha hA h1 h2) P Q ω hosc
  refine ⟨?_, ?_, fun _ _ ε _ => ⟨hLS _, hPC _⟩⟩
  · rw [ex007_lsRate_eq_on, ex007_lsRate_eq_on]; exact hLS _
  · rw [ex007_poincareRate_eq_on ⟨P.measure, P.isProbabilityMeasure⟩,
      ex007_poincareRate_eq_on ⟨Q.measure, Q.isProbabilityMeasure⟩]
    exact hPC _

end DGPS.Examples
