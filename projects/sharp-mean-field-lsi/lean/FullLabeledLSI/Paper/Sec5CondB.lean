import FullLabeledLSI.Paper.Sec5CondA

/-!
# Conditional laws for a random subset, part B: disintegration, the law is the density
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-! ### Disintegration of `ν = Q · volume` along `(X_S, X_i)` -/

section disint
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) {S : Finset (Fin N)} {i : Fin N}
  (hi : i ∉ S)

/-- `restrictS S` pushes `volume` to `volume`. -/
theorem volume_map_restrictS (S : Finset (Fin N)) :
    (volume : Measure (Config N d)).map (restrictS S) = volume := by
  classical
  have h : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Torus d)
      (· ∈ S)) volume ((volume : Measure (S → Torus d)).prod
        (volume : Measure ({k : Fin N // ¬ k ∈ S} → Torus d))) :=
    by rw [← Measure.volume_eq_prod]
       convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => Torus d) (· ∈ S)
  have h2 := (measurePreserving_fst (μ := (volume : Measure (S → Torus d)))
    (ν := (volume : Measure ({k : Fin N // ¬ k ∈ S} → Torus d)))).comp h
  exact h2.map_eq

/-- `ν.map (restrictS S) ≪ volume` for every `ν ≪ volume` (no hypothesis on `i`, `Q`). -/
theorem absolutelyContinuous_map_restrictS (S : Finset (Fin N)) {Q : Config N d → ℝ}
    (hQm : Measurable Q) :
    (qMeasure Q).map (restrictS S) ≪ (volume : Measure (S → Torus d)) := by
  have h := (withDensity_absolutelyContinuous (volume : Measure (Config N d))
    (fun X => ENNReal.ofReal (Q X))).map (measurable_restrictS (d := d) S)
  rwa [volume_map_restrictS] at h

/-- Transfer of an a.e. statement in the revealed values from `volume` to `ν`. -/
theorem ae_restrictS_of_ae_volume (S : Finset (Fin N)) {Q : Config N d → ℝ}
    (hQm : Measurable Q) {P : (S → Torus d) → Prop}
    (h : ∀ᵐ a ∂(volume : Measure (S → Torus d)), P a) :
    ∀ᵐ X ∂(qMeasure Q), P (restrictS S X) :=
  ae_of_ae_map (measurable_restrictS S).aemeasurable
    ((absolutelyContinuous_map_restrictS S hQm).ae_le h)

include hQ in
theorem isFiniteMeasure_qMeasure : IsFiniteMeasure (qMeasure Q) := by
  refine isFiniteMeasure_withDensity_ofReal ?_
  refine (Integrable.of_bound hQ.meas.aestronglyMeasurable (|c| + |C|)
    (Eventually.of_forall fun X => ?_)).hasFiniteIntegral
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hQ.lower X, hQ.upper X, abs_nonneg c, abs_nonneg C, le_abs_self c,
    le_abs_self C, neg_abs_le c]

include hQ in
theorem measurable_margQS_x (a : S → Torus d) :
    Measurable fun x => margQS Q S i a x :=
  (measurable_margQS hQ S i).comp (measurable_const.prodMk measurable_id)

include hQ in
theorem integrable_margQS_x (a : S → Torus d) :
    Integrable (fun x => margQS Q S i a x) (haar d) :=
  Integrable.of_bound (measurable_margQS_x hQ a).aestronglyMeasurable C
    (Eventually.of_forall fun x => by
      have := margQS_bounds hQ S i a x
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hQ.pos])

include hQ hi in
/-- **The basic disintegration identity** (`SharpLSI.lintegral_pastCur`). -/
theorem lintegral_revealCur {F : (S → Torus d) → Torus d → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ X, F (restrictS S X) (X i) * ENNReal.ofReal (Q X) =
      ∫⁻ a, ∫⁻ x, F a x * ENNReal.ofReal (margQS Q S i a x) ∂haar d := by
  have hQm := hQ.meas
  have hG : Measurable fun X : Config N d => F (restrictS S X) (X i) * ENNReal.ofReal (Q X) :=
    (hF.comp ((measurable_restrictS S).prodMk (measurable_pi_apply i))).mul
      (ENNReal.measurable_ofReal.comp hQm)
  rw [lintegral_assembleS hi hG]
  refine lintegral_congr fun a => lintegral_congr fun x => ?_
  have hzm : Measurable fun z : RestIdx S i → Torus d => Q (assembleS S i a x z) :=
    hQm.comp ((measurable_assembleS S i).comp
      ((measurable_const (a := (a, x))).prodMk measurable_id))
  simp only [restrictS_assembleS, assembleS_cur hi]
  rw [lintegral_const_mul (F a x) (f := fun z => ENNReal.ofReal (Q (assembleS S i a x z)))
    (ENNReal.measurable_ofReal.comp hzm), margQS, ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_bound hzm.aestronglyMeasurable
      (|c| + |C|) (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hQ.lower (assembleS S i a x z), hQ.upper (assembleS S i a x z),
          abs_nonneg c, abs_nonneg C, le_abs_self c, le_abs_self C, neg_abs_le c])
  · exact Eventually.of_forall fun z => hQ.pos.le.trans (hQ.lower _)

include hQ hi in
/-- The law of `X_S` has density `ZcS` (`SharpLSI.map_past_eq`). -/
theorem map_restrictS_eq :
    (qMeasure Q).map (restrictS S) =
      (volume : Measure (S → Torus d)).withDensity fun a => ENNReal.ofReal (ZcS Q S i a) := by
  have hs0 := measurable_restrictS (d := d) S
  ext s hs
  rw [Measure.map_apply hs0 hs, withDensity_apply _ (hs0 hs),
    withDensity_apply _ hs, ← lintegral_indicator (hs0 hs),
    ← lintegral_indicator hs]
  have h := lintegral_revealCur hQ hi (F := fun p _ => s.indicator 1 p)
    ((measurable_const.indicator hs).comp measurable_fst)
  have e1 : ∀ X, (restrictS S ⁻¹' s).indicator (fun X => ENNReal.ofReal (Q X)) X =
      s.indicator 1 (restrictS S X) * ENNReal.ofReal (Q X) := fun X => by
    by_cases hX : restrictS S X ∈ s
    · simp [Set.indicator_of_mem, hX]
    · simp [Set.indicator_of_notMem, hX]
  simp_rw [e1, h]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s
  · simp only [Set.indicator_of_mem hp, Pi.one_apply, one_mul]
    rw [ZcS, ofReal_integral_eq_lintegral_ofReal (integrable_margQS_x hQ p)]
    exact Eventually.of_forall fun x => hQ.pos.le.trans (margQS_bounds hQ S i p x).1
  · simp [Set.indicator_of_notMem hp]

/-- The conditional kernel `a ↦ condDensS a · haar`. -/
noncomputable def condKerS (Q : Config N d → ℝ) (S : Finset (Fin N)) (i : Fin N) :
    Kernel (S → Torus d) (Torus d) :=
  Kernel.withDensity (Kernel.const _ (haar d))
    (fun a x => ENNReal.ofReal (condDensS Q S i a x))

include hQ in
theorem condKerS_apply (a : S → Torus d) : condKerS Q S i a = densMeasure (condDensS Q S i a) := by
  unfold condKerS
  rw [Kernel.withDensity_apply (f := fun a x => ENNReal.ofReal (condDensS Q S i a x)) _
    (ENNReal.measurable_ofReal.comp (measurable_condDensS hQ S i) :
      Measurable fun q : (S → Torus d) × Torus d => ENNReal.ofReal (condDensS Q S i q.1 q.2)),
    Kernel.const_apply]
  rfl

include hQ in
theorem isMarkovKernel_condKerS : IsMarkovKernel (condKerS Q S i) := by
  refine ⟨fun a => ?_⟩
  rw [condKerS_apply hQ]
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower (Classical.arbitrary _)).trans
    (hQ.upper _))
  exact isProbabilityMeasure_densMeasure' (fun x =>
    le_trans (div_pos hQ.pos hC).le (condDensS_bounds hQ S i a x).1)
    (integral_condDensS hQ S i a)

include hQ hi in
/-- The law of `(X_S, X_i)` is `(law of X_S) ⊗ condKerS` (`SharpLSI.map_pastCur_eq`). -/
theorem map_restrictS_pair_eq :
    (qMeasure Q).map (fun X => (restrictS S X, X i)) =
      ((qMeasure Q).map (restrictS S)) ⊗ₘ condKerS Q S i := by
  have := isMarkovKernel_condKerS (i := i) (S := S) hQ
  have := isFiniteMeasure_qMeasure hQ
  have hpc : Measurable fun X : Config N d => (restrictS S X, X i) :=
    (measurable_restrictS S).prodMk (measurable_pi_apply _)
  have hs0 := measurable_restrictS (d := d) S
  refine Measure.ext_prod fun {s t} hs ht => ?_
  rw [Measure.map_apply hpc (hs.prod ht), withDensity_apply _ (hpc (hs.prod ht)),
    ← lintegral_indicator (hpc (hs.prod ht)), Measure.compProd_apply_prod hs ht,
    map_restrictS_eq hQ hi, setLIntegral_withDensity_eq_setLIntegral_mul _
      (f := fun p => ENNReal.ofReal (ZcS Q S i p)) (g := fun p => condKerS Q S i p t)
      (ENNReal.measurable_ofReal.comp (measurable_ZcS hQ S i)) ((Kernel.measurable_coe _ ht)) hs]
  have h := lintegral_revealCur hQ hi (F := fun p x => s.indicator 1 p * t.indicator 1 x)
    (((measurable_const.indicator hs).comp measurable_fst).mul
      ((measurable_const.indicator ht).comp measurable_snd))
  have e1 : ∀ X, ((fun X => (restrictS S X, X i)) ⁻¹' s ×ˢ t).indicator
      (fun X => ENNReal.ofReal (Q X)) X =
      (s.indicator 1 (restrictS S X) * t.indicator 1 (X i)) * ENNReal.ofReal (Q X) :=
    fun X => by
      by_cases h1 : restrictS S X ∈ s <;> by_cases h2 : X i ∈ t <;>
        simp [Set.indicator, h1, h2]
  simp_rw [e1, h]
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s
  · simp only [Set.indicator_of_mem hp, Pi.one_apply, one_mul]
    have hZ := (ZcS_bounds hQ S i p).1
    have hdm : Measurable fun x => ENNReal.ofReal (condDensS Q S i p x) :=
      ENNReal.measurable_ofReal.comp ((measurable_condDensS hQ S i).comp
        (measurable_const.prodMk measurable_id))
    simp only [Pi.mul_apply]
    rw [condKerS_apply hQ, densMeasure, withDensity_apply _ ht,
      ← lintegral_const_mul _ hdm, ← lintegral_indicator ht]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ t
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      rw [← ENNReal.ofReal_mul (hQ.pos.le.trans hZ)]
      congr 1
      unfold condDensS
      field_simp [(hQ.pos.trans_le hZ).ne']
    · simp [Set.indicator_of_notMem hx]
  · simp [Set.indicator_of_notMem hp]

end disint

/-! ### (T2) The conditional law is the explicit density -/

section condlaw
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) {S : Finset (Fin N)} {i : Fin N}
  (hi : i ∉ S) {ν : Measure (Config N d)} [IsFiniteMeasure ν] (hν : ν = qMeasure Q)

include hQ hi hν in
/-- **`ρ_{S,i}(a) = condDensS a · haar`** for `ν.map (restrictS S)`-a.e. `a` (analogue of
`SharpLSI.condNext_ae_eq`). -/
theorem condLawS_ae_eq :
    ∀ᵐ a ∂(ν.map (restrictS S)), condLawS ν S i a = densMeasure (condDensS Q S i a) := by
  subst hν
  have := isMarkovKernel_condKerS (i := i) (S := S) hQ
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (measurable_restrictS S)
    (measurable_pi_apply i) (map_restrictS_pair_eq hQ hi)
  filter_upwards [h] with a ha
  rw [condLawS, ha, condKerS_apply hQ]

include hQ hi hν in
/-- The same, along `X` (`ν`-a.e.). -/
theorem condLawS_ae_eq_X :
    ∀ᵐ X ∂ν, condLawS ν S i (restrictS S X) =
      densMeasure (condDensS Q S i (restrictS S X)) :=
  ae_of_ae_map (measurable_restrictS S).aemeasurable (condLawS_ae_eq hQ hi hν)

/-- The density of `ρ̄_S = n⁻¹ ∑_{i ∈ R} ρ_{S,i}` at the revealed values `a`
(`0` if `R = Sᶜ` is empty). -/
noncomputable def barDensS (Q : Config N d → ℝ) (S : Finset (Fin N)) (a : S → Torus d)
    (x : Torus d) : ℝ :=
  ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, condDensS Q S i a x

include hQ in
theorem densMeasure_barDensS (a : S → Torus d) :
    densMeasure (barDensS Q S a) =
      ((Sᶜ.card : ℝ≥0∞)⁻¹) • ∑ i ∈ Sᶜ, densMeasure (condDensS Q S i a) := by
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower (Classical.arbitrary _)).trans
    (hQ.upper _))
  have hnn : ∀ (j : Fin N) x, 0 ≤ condDensS Q S j a x := fun j x =>
    le_trans (div_pos hQ.pos hC).le (condDensS_bounds hQ S j a x).1
  have hdm : ∀ j : Fin N, Measurable fun x => ENNReal.ofReal (condDensS Q S j a x) :=
    fun j => ENNReal.measurable_ofReal.comp ((measurable_condDensS hQ S j).comp
      (measurable_const.prodMk measurable_id))
  by_cases hn : Sᶜ.card = 0
  · have he : Sᶜ = ∅ := Finset.card_eq_zero.mp hn
    have : barDensS Q S a = fun _ => 0 := by
      funext x; simp [barDensS, he]
    rw [this, he]
    simp [densMeasure]
  · have hnpos : (0 : ℝ) < (Sᶜ.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    ext t ht
    simp only [densMeasure, withDensity_apply _ ht, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, smul_eq_mul]
    have e1 : ∀ x, ENNReal.ofReal (barDensS Q S a x) =
        (Sᶜ.card : ℝ≥0∞)⁻¹ * ∑ j ∈ Sᶜ, ENNReal.ofReal (condDensS Q S j a x) := by
      intro x
      rw [barDensS, ENNReal.ofReal_mul (inv_nonneg.mpr hnpos.le),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn j x),
        ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
    simp_rw [e1]
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hdm j),
      lintegral_finsetSum _ fun j _ => hdm j]

include hQ hν in
/-- The barycentre `ρ̄_S` of the manuscript (5.6) as a sum of explicit densities. -/
theorem barCond_ae_eq :
    ∀ᵐ X ∂ν, barCond ν S X = ((Sᶜ.card : ℝ≥0∞)⁻¹) •
      ∑ i ∈ Sᶜ, densMeasure (condDensS Q S i (restrictS S X)) := by
  have h : ∀ᵐ X ∂ν, ∀ i ∈ Sᶜ, condLawS ν S i (restrictS S X) =
      densMeasure (condDensS Q S i (restrictS S X)) := by
    refine (Filter.eventually_all_finset _).mpr fun i hi' => ?_
    exact condLawS_ae_eq_X hQ (Finset.mem_compl.mp hi') hν
  filter_upwards [h] with X hX
  unfold barCond
  rw [Finset.sum_congr rfl hX]

include hQ hν in
/-- ... and as a single density `barDensS` (the form needed to compute `B_S(x) = ∫ b(x,y) ρ̄_S(y)`). -/
theorem barCond_ae_eq_densMeasure :
    ∀ᵐ X ∂ν, barCond ν S X = densMeasure (barDensS Q S (restrictS S X)) := by
  filter_upwards [barCond_ae_eq hQ hν] with X hX
  rw [hX, densMeasure_barDensS hQ]

end condlaw

end SharpLSI.FL
