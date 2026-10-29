import FullLabeledLSI.Paper.Sec5MFA
import FullLabeledLSI.Infra.RevealKL

/-!
# Mean-field step C: the gap identity (M5)
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {β : Type*}

theorem klDiv_map_swap_loc {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (M R : Measure (A × B)) [IsFiniteMeasure M] [IsFiniteMeasure R] :
    klDiv (M.map Prod.swap) (R.map Prod.swap) = klDiv M R :=
  SharpLSI.klDiv_map_equiv' M R MeasurableEquiv.prodComm

open ProbabilityTheory in
/-- Local copy of `klDiv_bind_decomp` (Sec5Perm), which cannot be imported here because
`Sec5Perm` (via `PermAvg`) clashes with `Sec5MFA` on the name `avgDensR`. -/
theorem klDiv_bind_decomp_loc {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [Nonempty ι]
    (lam : Measure ι) [IsProbabilityMeasure lam]
    (κ : ProbabilityTheory.Kernel ι α) [ProbabilityTheory.IsMarkovKernel κ]
    (Q : Measure α) [IsProbabilityMeasure Q] :
    ∫⁻ i, klDiv (κ i) Q ∂lam =
      klDiv (lam.bind κ) Q + ∫⁻ i, klDiv (κ i) (lam.bind κ) ∂lam := by
  set νb := lam.bind κ with hνb
  have : IsProbabilityMeasure νb := by
    rw [hνb]; infer_instance
  have h1 := klDiv_compProd_same_all lam κ (ProbabilityTheory.Kernel.const ι Q)
  have h2 := klDiv_compProd_same_all lam κ (ProbabilityTheory.Kernel.const ι νb)
  simp only [ProbabilityTheory.Kernel.const_apply] at h1 h2
  rw [← h1]
  set M := lam ⊗ₘ κ with hM
  set M' := M.map Prod.swap with hM'
  have hfst : M'.fst = νb := by
    rw [hM', Measure.fst_map_swap, hM, Measure.snd_compProd]
  have hdis : νb ⊗ₘ M'.condKernel = M' := by
    have := Measure.disintegrate M' M'.condKernel
    rwa [hfst] at this
  have hchain := klDiv_compProd_eq_add νb Q M'.condKernel (ProbabilityTheory.Kernel.const α lam)
  rw [hdis, Measure.compProd_const, Measure.compProd_const] at hchain
  have e1 : Q.prod lam = (lam.prod Q).map Prod.swap := (Measure.prod_swap).symm
  have e2 : νb.prod lam = (lam.prod νb).map Prod.swap := (Measure.prod_swap).symm
  have hrw : (lam ⊗ₘ ProbabilityTheory.Kernel.const ι Q) = lam.prod Q := Measure.compProd_const
  have hrw2 : (lam ⊗ₘ ProbabilityTheory.Kernel.const ι νb) = lam.prod νb :=
    Measure.compProd_const
  rw [e1, e2, hM', klDiv_map_swap_loc, klDiv_map_swap_loc] at hchain
  rw [hrw, hchain, ← hrw2, h2]

/-- `klFun r ≤ M² + 1` for `0 ≤ r ≤ M`. -/
theorem klFun_le_aux {r M : ℝ} (hr : 0 ≤ r) (hM : r ≤ M) : klFun r ≤ M ^ 2 + 1 := by
  have h1 : klFun r ≤ (r - 1) ^ 2 := by
    rw [klFun_apply]
    rcases hr.eq_or_lt with h | h
    · rw [← h]; simp
    · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) hr
      nlinarith
  nlinarith

/-! ### E-F. (M5) the gap identity -/

/-- A bounded probability density has finite relative entropy to a minimizer `μ`
(`dμ/dm = elDens ≥ c_m > 0`, so `dρ/dμ ≤ C / c_m`). -/
theorem klDiv_densMeasure_minimizer_ne_top (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {ρ : Torus d → ℝ} (hm : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    {C : ℝ} (hC : ∀ x, ρ x ≤ C) (h1 : ∫ x, ρ x ∂haar d = 1) :
    klDiv (densMeasure ρ) (μ : Measure (Torus d)) ≠ ⊤ := by
  obtain ⟨c, C', L, hc, hb⟩ := elDensity_bounds (d := d) hyp
  obtain ⟨e, hμe, hbe, hem⟩ : ∃ e : Torus d → ℝ, (μ : Measure (Torus d)) = densMeasure e ∧
      (∀ x, c ≤ e x) ∧ Measurable e := by
    refine ⟨elDens V W (μ : Measure (Torus d)), minimizer_eq_elDensity hyp hμ,
      fun x => (hb _ inferInstance).1 x |>.1, ?_⟩
    exact (hb _ inferInstance).2.continuous.measurable
  have hρ1' : IsProbabilityMeasure (densMeasure ρ) := isProbabilityMeasure_densMeasure' h0 h1
  have hμpm : IsProbabilityMeasure (densMeasure e) := hμe ▸ inferInstance
  rw [hμe]
  have hρmo : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hm
  have hemo : Measurable fun x => ENNReal.ofReal (e x) := ENNReal.measurable_ofReal.comp hem
  have hac1 : densMeasure ρ ≪ haar d := withDensity_absolutelyContinuous _ _
  have hac2 : densMeasure e ≪ haar d := withDensity_absolutelyContinuous _ _
  have hac3 : haar d ≪ densMeasure e :=
    withDensity_absolutelyContinuous' hemo.aemeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa using (ENNReal.ofReal_pos.2 (lt_of_lt_of_le hc (hbe x))).ne')
  have hac : densMeasure ρ ≪ densMeasure e := hac1.trans hac3
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hdiv := Measure.rnDeriv_eq_div (μ := densMeasure ρ) (ν := densMeasure e) (ξ := haar d)
    hac1 hac2
  have hr1 : (densMeasure ρ).rnDeriv (haar d) =ᵐ[haar d] fun x => ENNReal.ofReal (ρ x) :=
    Measure.rnDeriv_withDensity _ hρmo
  have hr2 : (densMeasure e).rnDeriv (haar d) =ᵐ[haar d] fun x => ENNReal.ofReal (e x) :=
    Measure.rnDeriv_withDensity _ hemo
  have hC0 : 0 ≤ C := (h0 0).trans (hC 0)
  have hbd : ∀ᵐ x ∂densMeasure e,
      ENNReal.ofReal (klFun ((densMeasure ρ).rnDeriv (densMeasure e) x).toReal) ≤
        ENNReal.ofReal ((C / c) ^ 2 + 1) := by
    filter_upwards [hdiv, hac2.ae_le hr1, hac2.ae_le hr2] with x hx h1x h2x
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hx, h1x, h2x, ENNReal.toReal_div, ENNReal.toReal_ofReal (h0 x),
      ENNReal.toReal_ofReal (hc.le.trans (hbe x))]
    exact klFun_le_aux (div_nonneg (h0 x) (hc.le.trans (hbe x)))
      (by rw [div_le_div_iff₀ (lt_of_lt_of_le hc (hbe x)) hc]
          nlinarith [h0 x, hC x, hbe x, hc])
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hbd) ?_)
  simp

/-- The compensation identity under `AEMeasurable` densities (`densMeasure` only sees the a.e.
class of the density).  `sum_klDiv_compensation` is the `Measurable` special case. -/
theorem sum_klDiv_compensation_ae {q : ℕ} (θ : Fin q → ℝ) (ρ : Fin q → Torus d → ℝ)
    (hθ0 : ∀ a, 0 ≤ θ a) (hθ1 : ∑ a, θ a = 1) (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hρ1 : ∀ a, ∫ x, ρ a x ∂haar d = 1) (hρm : ∀ a, AEMeasurable (ρ a) (haar d))
    (Q : Measure (Torus d)) [IsProbabilityMeasure Q] :
    ∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρ a)) Q =
      klDiv (densMeasure (fun x => ∑ a, θ a * ρ a x)) Q +
        ∑ a, ENNReal.ofReal (θ a) *
          klDiv (densMeasure (ρ a)) (densMeasure (fun x => ∑ a, θ a * ρ a x)) := by
  classical
  have hq : Nonempty (Fin q) := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hθ1
    · exact ⟨⟨0, h⟩⟩
  set lam : Measure (Fin q) := ∑ a, ENNReal.ofReal (θ a) • Measure.dirac a with hlam
  have hint : ∀ f : Fin q → ℝ≥0∞, ∫⁻ i, f i ∂lam = ∑ a, ENNReal.ofReal (θ a) * f a := by
    intro f
    rw [hlam, lintegral_finsetSum_measure]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac' _ (measurable_of_finite f), smul_eq_mul]
  have : IsProbabilityMeasure lam := by
    refine ⟨?_⟩
    have := hint (fun _ => 1)
    simp only [lintegral_const, one_mul, mul_one] at this
    rw [this, ← ENNReal.ofReal_sum_of_nonneg (fun a _ => hθ0 a), hθ1, ENNReal.ofReal_one]
  have hpm : ∀ a, IsProbabilityMeasure (densMeasure (ρ a)) := fun a =>
    isProbabilityMeasure_densMeasure' (hρ0 a) (hρ1 a)
  let κ : ProbabilityTheory.Kernel (Fin q) (Torus d) :=
    ⟨fun a => densMeasure (ρ a), measurable_of_finite _⟩
  have : ProbabilityTheory.IsMarkovKernel κ := ⟨fun a => hpm a⟩
  have hκ : ∀ a, κ a = densMeasure (ρ a) := fun a => rfl
  have hbind : lam.bind κ = densMeasure (fun x => ∑ a, θ a * ρ a x) := by
    ext t ht
    rw [Measure.bind_apply ht κ.aemeasurable, hint]
    simp only [hκ]
    unfold densMeasure
    simp only [withDensity_apply' _ t]
    have hm : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (ρ a x)) (haar d) := fun a =>
      ENNReal.measurable_ofReal.comp_aemeasurable (hρm a)
    have : ∀ x, ENNReal.ofReal (∑ a, θ a * ρ a x) =
        ∑ a, ENNReal.ofReal (θ a) * ENNReal.ofReal (ρ a x) := fun x => by
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hθ0 a) (hρ0 a x))]
      exact Finset.sum_congr rfl fun a _ => ENNReal.ofReal_mul (hθ0 a)
    simp only [this]
    rw [lintegral_finsetSum' _ (fun a _ => ((hm a).restrict).const_mul _)]
    exact Finset.sum_congr rfl fun a _ => (lintegral_const_mul'' _ (hm a).restrict).symm
  have key := klDiv_bind_decomp_loc lam κ Q
  rw [hint, hbind, hint] at key
  simpa only [hκ] using key

/-- **(M5a) The compensation identity for densities:** for nonnegative weights `θₐ` summing to one,
probability densities `ρₐ` (any `Fintype` index) and any probability measure `Q`,
`∑ θₐ H(ρₐ|Q) = H(ρ̄|Q) + ∑ θₐ H(ρₐ|ρ̄)` in `ℝ≥0∞` (both sides possibly `⊤`).
Proof: `klDiv_bind_decomp` (Sec5Perm:35) with `lam = ∑ θₐ δₐ` on the finite discrete index type
(or on `Fin q`), `κ a = densMeasure (ρ a)`, and `κ ∘ₘ lam = densMeasure ρ̄`.  With `Q = haar d` this
is the first half of `species_decomposition`; with `Q = μ` it gives (M5). -/
theorem sum_klDiv_compensation {q : ℕ} (θ : Fin q → ℝ) (ρ : Fin q → Torus d → ℝ)
    (hθ0 : ∀ a, 0 ≤ θ a) (hθ1 : ∑ a, θ a = 1) (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hρ1 : ∀ a, ∫ x, ρ a x ∂haar d = 1) (hρm : ∀ a, Measurable (ρ a))
    (Q : Measure (Torus d)) [IsProbabilityMeasure Q] :
    ∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρ a)) Q =
      klDiv (densMeasure (fun x => ∑ a, θ a * ρ a x)) Q +
        ∑ a, ENNReal.ofReal (θ a) *
          klDiv (densMeasure (ρ a)) (densMeasure (fun x => ∑ a, θ a * ρ a x)) :=
  sum_klDiv_compensation_ae θ ρ hθ0 hθ1 hρ0 hρ1 (fun a => (hρm a).aemeasurable) Q

/-- **(M5) The gap identity** (4.4) + compensation: for an admissible family and a minimizer `μ`,
`G_θ(ρ) = ∑ₐ θₐ H(ρₐ|μ) + J(ρ̄)` in `EReal`, where `J = Jfun W μ`.  (Both sides are finite by
`msGap_bounds_of_admissible`; the proof does not need that.)  Sketch: `species_decomposition` gives
`G_θ = G(ρ̄) + ∑ θₐ H(ρₐ|ρ̄)`; `gap_eq_aux hyp hμ ⟨densMeasure ρ̄, _⟩` gives
`G(ρ̄) = H(ρ̄|μ) + J(ρ̄)`; `sum_klDiv_compensation` with `Q = μ`; `EReal.coe_ennreal_add`.  -/
theorem msGap_eq_entropy_add_J (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {F : Family d} (hF : F.Admissible) :
    msGap V W F =
      ((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) :
        ℝ≥0∞) : EReal) + ((Jfun W μ (densMeasure F.bar) : ℝ) : EReal) := by
  classical
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  have hρ0 : ∀ a x, 0 ≤ F.ρ a x := fun a => (hF.2.2 a).1
  have hρ1 : ∀ a, ∫ x, F.ρ a x ∂haar d = 1 := fun a => (hF.2.2 a).2.1
  have hbar0 : ∀ x, 0 ≤ F.bar x := fun x =>
    Finset.sum_nonneg fun a _ => mul_nonneg (hθ0 a) (hρ0 a x)
  have hbar1 : ∫ x, F.bar x ∂haar d = 1 := by
    show ∫ x, ∑ a, F.θ a * F.ρ a x ∂haar d = 1
    rw [integral_finsetSum _ (fun a _ =>
      (integrable_of_integral_eq_one' (hρ1 a)).const_mul _)]
    simp only [integral_const_mul, hρ1, mul_one]
    exact hF.2.1
  have hbarpm : IsProbabilityMeasure (densMeasure F.bar) :=
    isProbabilityMeasure_densMeasure' hbar0 hbar1
  have hρam : ∀ a, AEMeasurable (F.ρ a) (haar d) := fun a => by
    have h2 := (hF.2.2 a).2.2.2.1.aestronglyMeasurable.aemeasurable.pow_const 2
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.sq_sqrt (hρ0 a x)]
  -- the two compensation identities
  have comp1 : ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) =
      klDiv (densMeasure F.bar) (haar d) +
        ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) :=
    sum_klDiv_compensation_ae F.θ F.ρ hθ0 hF.2.1 hρ0 hρ1 hρam (haar d)
  have comp2 : ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) =
      klDiv (densMeasure F.bar) (μ : Measure (Torus d)) +
        ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) :=
    sum_klDiv_compensation_ae F.θ F.ρ hθ0 hF.2.1 hρ0 hρ1 hρam (μ : Measure (Torus d))
  rw [comp2]
  have hSh : ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => by
      obtain ⟨h0, h1, hH⟩ := hF.2.2 a
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (klDiv_densMeasure_ne_top_of_memH1 h0 h1 hH)
  rw [comp1] at hSh
  set A := klDiv (densMeasure F.bar) (haar d) with hA
  set B := ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) with hB
  set K := klDiv (densMeasure F.bar) (μ : Measure (Torus d)) with hK
  have hAt : A ≠ ⊤ := fun h => hSh (by rw [h, top_add])
  have hBt : B ≠ ⊤ := fun h => hSh (by rw [h, add_top])
  set P : ℝ := potE V (densMeasure F.bar) + interE W (densMeasure F.bar) (densMeasure F.bar) / 2
    with hP
  have hFs := Fstar_eq_coe hyp (V := V) (W := W)
  set F' := (Fstar V W).toReal with hF'
  have hgap := gap_eq_aux hyp hμ ⟨densMeasure F.bar, hbarpm⟩
  have hgap' : ((A : ℝ≥0∞) : EReal) + (P : EReal) - (F' : EReal) =
      ((K : ℝ≥0∞) : EReal) + ((Jfun W μ (densMeasure F.bar) : ℝ) : EReal) := by
    rw [← hFs]; exact hgap
  have hKt : K ≠ ⊤ := by
    intro h
    rw [h] at hgap'
    rw [EReal.coe_ennreal_top, EReal.top_add_coe] at hgap'
    rw [← EReal.coe_ennreal_toReal hAt, ← EReal.coe_add, ← EReal.coe_sub] at hgap'
    exact EReal.coe_ne_top _ hgap'
  have eA := (EReal.coe_ennreal_toReal hAt).symm
  have eB := (EReal.coe_ennreal_toReal hBt).symm
  have eK := (EReal.coe_ennreal_toReal hKt).symm
  rw [eA, eK] at hgap'
  have hgap'' : A.toReal + P - F' = K.toReal + Jfun W μ (densMeasure F.bar) := by
    norm_cast at hgap'
  unfold msGap
  rw [comp1, hFs]
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_add, eA, eB, eK]
  have : A.toReal + B.toReal + P - F' = K.toReal + B.toReal + Jfun W μ (densMeasure F.bar) := by
    linarith
  exact_mod_cast congrArg ((↑) : ℝ → EReal) this

/-- **(M5R) Real form for the conditional family:**
`G_θ = (1/n) ∑_{i∈R} H(ρᵢ|μ) + J(ρ̄)` with every `H(ρᵢ|μ)` finite, written with `toReal` so that it
can be averaged.  Uses (M5), `klDiv_densMeasure_minimizer_ne_top`, `finFamily_sum`,
`finFamily_bar`, and `ENNReal.toReal_sum`. -/
theorem msGap_finFamily_eq (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {R : Finset β} (hR : R.Nonempty)
    {ρ : β → Torus d → ℝ} {g : β → Torus d → Fin d → ℝ} {c C : ℝ}
    (h : ∀ i ∈ R, IsBddH1Dens (ρ i) (g i) c C) :
    msGap V W (finFamily R ρ) =
      (((R.card : ℝ)⁻¹ * ∑ i ∈ R, (klDiv (densMeasure (ρ i)) (μ : Measure (Torus d))).toReal +
        Jfun W μ (densMeasure (avgDensR R ρ)) : ℝ) : EReal) := by
  classical
  rw [msGap_eq_entropy_add_J hyp hμ (finFamily_admissible hR h), finFamily_bar]
  have hsum := finFamily_sum (M := ℝ≥0∞) R ρ
    (fun r => ENNReal.ofReal (R.card : ℝ)⁻¹ * klDiv (densMeasure r) (μ : Measure (Torus d)))
  have hfin : ∀ i ∈ R, klDiv (densMeasure (ρ i)) (μ : Measure (Torus d)) ≠ ⊤ := fun i hi =>
    klDiv_densMeasure_minimizer_ne_top hyp hμ (h i hi).meas
      (fun x => ((h i hi).pos.trans_le ((h i hi).ge x)).le) (h i hi).le (h i hi).int_one
  have hT : (∑ i ∈ R, ENNReal.ofReal (R.card : ℝ)⁻¹ *
      klDiv (densMeasure (ρ i)) (μ : Measure (Torus d))) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i hi => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin i hi)
  have hsum' : ∑ a, ENNReal.ofReal ((finFamily R ρ).θ a) *
      klDiv (densMeasure ((finFamily R ρ).ρ a)) (μ : Measure (Torus d)) =
      ∑ i ∈ R, ENNReal.ofReal (R.card : ℝ)⁻¹ *
        klDiv (densMeasure (ρ i)) (μ : Measure (Torus d)) := hsum
  rw [hsum', ← EReal.coe_ennreal_toReal hT, ← EReal.coe_add, ENNReal.toReal_sum
    (fun i hi => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin i hi)), Finset.mul_sum]
  refine congrArg (fun t : ℝ => ((t + Jfun W μ (densMeasure (avgDensR R ρ)) : ℝ) : EReal))
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg _))]


end SharpLSI.FL
