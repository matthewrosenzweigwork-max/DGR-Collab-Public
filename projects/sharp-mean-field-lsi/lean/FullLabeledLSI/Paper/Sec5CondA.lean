import FullLabeledLSI.Infra.RevealChain
import SharpSymmetricLSI.Paper.Defective22

/-!
# Conditional laws for a random subset, part A: assembly, explicit densities, bounds
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-! ### Bounded densities and the law `ν = Q · volume` -/

/-- `Q` is a measurable density with `0 < c ≤ Q ≤ C`. -/
structure IsBddDens (Q : Config N d → ℝ) (c C : ℝ) : Prop where
  meas : Measurable Q
  pos : 0 < c
  lower : ∀ X, c ≤ Q X
  upper : ∀ X, Q X ≤ C

/-- The measure `Q · volume` on `(𝕋^d)^N`. -/
noncomputable abbrev qMeasure (Q : Config N d → ℝ) : Measure (Config N d) :=
  (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)

/-! ### Assembling a configuration from revealed values, current value and the rest -/

/-- The labels that are neither revealed (`∈ S`) nor the current label `i`. -/
abbrev RestIdx (S : Finset (Fin N)) (i : Fin N) : Type := {k : Fin N // k ∉ S ∧ k ≠ i}

/-- The configuration with `a` on `S`, `x` at `i` and `z` on the remaining labels
(`a` wins if `i ∈ S`; every statement needing `i ∉ S` says so). -/
def assembleS (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d)
    (z : RestIdx S i → Torus d) : Config N d :=
  fun k => if hk : k ∈ S then a ⟨k, hk⟩ else if hki : k = i then x else z ⟨k, hk, hki⟩

/-- The unrevealed, non-current coordinates `X_{(S ∪ {i})ᶜ}` of a configuration. -/
def restS (S : Finset (Fin N)) (i : Fin N) (X : Config N d) : RestIdx S i → Torus d :=
  fun k => X k.1

theorem restrictS_assembleS (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d)
    (z : RestIdx S i → Torus d) : restrictS S (assembleS S i a x z) = a := by
  funext k
  simp [restrictS, assembleS, k.2]

theorem assembleS_cur {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (a : S → Torus d)
    (x : Torus d) (z : RestIdx S i → Torus d) : assembleS S i a x z i = x := by
  simp [assembleS, hi]

theorem restS_assembleS (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d)
    (z : RestIdx S i → Torus d) : restS S i (assembleS S i a x z) = z := by
  funext k
  simp [restS, assembleS, k.2.1, k.2.2]

theorem assembleS_eq (S : Finset (Fin N)) (i : Fin N) (X : Config N d) :
    assembleS S i (restrictS S X) (X i) (restS S i X) = X := by
  funext k
  by_cases hk : k ∈ S
  · simp [assembleS, restrictS, hk]
  · by_cases hki : k = i
    · subst hki; simp [assembleS, hk]
    · simp [assembleS, restS, hk, hki]

theorem measurable_assembleS (S : Finset (Fin N)) (i : Fin N) :
    Measurable (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
      assembleS S i q.1.1 q.1.2 q.2) := by
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hk : k ∈ S
  · have e : (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
        assembleS S i q.1.1 q.1.2 q.2 k) = fun q => q.1.1 ⟨k, hk⟩ := by
      funext q; simp [assembleS, hk]
    rw [e]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)
  · by_cases hki : k = i
    · have e : (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
          assembleS S i q.1.1 q.1.2 q.2 k) = fun q => q.1.2 := by
        funext q; subst hki; simp [assembleS, hk]
      rw [e]
      exact measurable_snd.comp measurable_fst
    · have e : (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
          assembleS S i q.1.1 q.1.2 q.2 k) = fun q => q.2 ⟨k, hk, hki⟩ := by
        funext q; simp [assembleS, hk, hki]
      rw [e]
      exact (measurable_pi_apply _).comp measurable_snd

/-- Reindexing of `Fin N` as `(S ⊕ Unit) ⊕ RestIdx S i`. -/
noncomputable def blockEquivS {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    (S ⊕ Unit) ⊕ RestIdx S i ≃ Fin N :=
  Equiv.ofBijective (Sum.elim (Sum.elim (fun s => s.1) (fun _ => i)) (fun r => r.1))
    ⟨by
      rintro ((s | u) | r) ((s' | u') | r') h <;> simp at h
      · exact congrArg (fun t => Sum.inl (Sum.inl t)) h
      · exact absurd (h ▸ s.2) hi
      · exact absurd s.2 (h ▸ r'.2.1)
      · exact absurd (h.symm ▸ s'.2) hi
      · rfl
      · exact absurd h.symm r'.2.2
      · exact absurd s'.2 (h.symm ▸ r.2.1)
      · exact absurd h r.2.2
      · exact congrArg Sum.inr (Subtype.ext h),
     fun k => by
      by_cases hk : k ∈ S
      · exact ⟨Sum.inl (Sum.inl ⟨k, hk⟩), rfl⟩
      · by_cases hki : k = i
        · exact ⟨Sum.inl (Sum.inr ()), hki.symm⟩
        · exact ⟨Sum.inr ⟨k, hk, hki⟩, rfl⟩⟩

theorem blockEquivS_inl {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (s : S) :
    blockEquivS hi (Sum.inl (Sum.inl s)) = s.1 := rfl

theorem blockEquivS_cur {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (u : Unit) :
    blockEquivS hi (Sum.inl (Sum.inr u)) = i := rfl

theorem blockEquivS_inr {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (r : RestIdx S i) :
    blockEquivS hi (Sum.inr r) = r.1 := rfl

/-- The block decomposition is measure preserving (this is where `i ∉ S` is needed). -/
theorem measurePreserving_assembleS {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    MeasurePreserving (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
      assembleS S i q.1.1 q.1.2 q.2)
      (((volume : Measure (S → Torus d)).prod (volume : Measure (Torus d))).prod
        (volume : Measure (RestIdx S i → Torus d))) volume := by
  have h0 : MeasurePreserving (fun q : (S → Torus d) × Torus d => (q.1, fun _ : Unit => q.2))
      ((volume : Measure (S → Torus d)).prod (volume : Measure (Torus d)))
      ((volume : Measure (S → Torus d)).prod (volume : Measure (Unit → Torus d))) :=
    MeasurePreserving.prod (MeasurePreserving.id (volume : Measure (S → Torus d)))
      (volume_preserving_funUnique Unit (Torus d)).symm
  have h1 : MeasurePreserving (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
      ((q.1.1, fun _ : Unit => q.1.2), q.2))
      (((volume : Measure (S → Torus d)).prod (volume : Measure (Torus d))).prod
        (volume : Measure (RestIdx S i → Torus d)))
      (((volume : Measure (S → Torus d)).prod (volume : Measure (Unit → Torus d))).prod
        (volume : Measure (RestIdx S i → Torus d))) :=
    MeasurePreserving.prod h0 (MeasurePreserving.id _)
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : S ⊕ Unit => Torus d)).prod
    (MeasurePreserving.id (volume : Measure (RestIdx S i → Torus d)))
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : (S ⊕ Unit) ⊕ RestIdx S i => Torus d)
  have h4 := volume_measurePreserving_piCongrLeft (fun _ : Fin N => Torus d) (blockEquivS hi)
  have h5 := h4.comp (h3.comp (h2.comp h1))
  convert h5 using 1
  funext q
  obtain ⟨⟨a, x⟩, z⟩ := q
  funext k
  obtain ⟨m, rfl⟩ := (blockEquivS hi).surjective k
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rcases m with (s | u) | r
  · rw [blockEquivS_inl]
    simp only [assembleS, s.2, ↓reduceDIte]
    rfl
  · rw [blockEquivS_cur]
    simp only [assembleS, hi, ↓reduceDIte]
    rfl
  · rw [blockEquivS_inr]
    simp only [assembleS, r.2.1, r.2.2, ↓reduceDIte]
    rfl

/-- `assembleS` as a measurable equivalence (for `integral_comp`-type rewriting). -/
def assembleSEquiv {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    (((S → Torus d) × Torus d) × (RestIdx S i → Torus d)) ≃ᵐ Config N d where
  toFun q := assembleS S i q.1.1 q.1.2 q.2
  invFun X := ((restrictS S X, X i), restS S i X)
  left_inv q := by
    obtain ⟨⟨a, x⟩, z⟩ := q
    simp only [restrictS_assembleS, assembleS_cur hi, restS_assembleS]
  right_inv X := assembleS_eq S i X
  measurable_toFun := measurable_assembleS S i
  measurable_invFun :=
    (((measurable_restrictS S).prodMk (measurable_pi_apply i)).prodMk
      (measurable_pi_iff.mpr fun k => measurable_pi_apply k.1))

/-- Tonelli in the block coordinates. -/
theorem lintegral_assembleS {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S)
    {G : Config N d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X, G X = ∫⁻ a, ∫⁻ x, ∫⁻ z, G (assembleS S i a x z)
      ∂(volume : Measure (RestIdx S i → Torus d)) ∂haar d ∂(volume : Measure (S → Torus d)) := by
  rw [← (measurePreserving_assembleS hi).lintegral_comp hG,
    lintegral_prod (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
      G (assembleS S i q.1.1 q.1.2 q.2)) (hG.comp (measurable_assembleS S i)).aemeasurable,
    lintegral_prod (fun q : (S → Torus d) × Torus d => ∫⁻ z, G (assembleS S i q.1 q.2 z)
      ∂(volume : Measure (RestIdx S i → Torus d)))
      ((hG.comp (measurable_assembleS S i)).lintegral_prod_right').aemeasurable]

/-- Fubini in the block coordinates (`SharpLSI.integral_assemble` for a general `S`). -/
theorem integral_assembleS {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S)
    {G : Config N d → ℝ} (hG : Integrable G volume) :
    ∫ X, G X = ∫ q : (S → Torus d) × Torus d, ∫ z, G (assembleS S i q.1 q.2 z)
      ∂(volume : Measure (RestIdx S i → Torus d))
      ∂((volume : Measure (S → Torus d)).prod (volume : Measure (Torus d))) := by
  have hmp := measurePreserving_assembleS (d := d) hi
  have hGi := hmp.integrable_comp_of_integrable hG
  rw [← MeasurePreserving.integral_comp' (f := assembleSEquiv hi) hmp G]
  exact integral_prod (fun q : ((S → Torus d) × Torus d) × (RestIdx S i → Torus d) =>
    G (assembleS S i q.1.1 q.1.2 q.2)) hGi

/-! ### (T1) Explicit conditional densities -/

/-- The marginal density `∫ Q(a, x, z) dz` of `(X_S, X_i)`. -/
noncomputable def margQS (Q : Config N d → ℝ) (S : Finset (Fin N)) (i : Fin N)
    (a : S → Torus d) (x : Torus d) : ℝ :=
  ∫ z, Q (assembleS S i a x z) ∂(volume : Measure (RestIdx S i → Torus d))

/-- The marginal density `∫ margQS a x dx` of `X_S`. -/
noncomputable def ZcS (Q : Config N d → ℝ) (S : Finset (Fin N)) (i : Fin N)
    (a : S → Torus d) : ℝ :=
  ∫ x, margQS Q S i a x ∂haar d

/-- The conditional density of `X_i` given `X_S = a`. -/
noncomputable def condDensS (Q : Config N d → ℝ) (S : Finset (Fin N)) (i : Fin N)
    (a : S → Torus d) (x : Torus d) : ℝ :=
  margQS Q S i a x / ZcS Q S i a

/-! ### (T3) Bounds, probability, measurability (no hypothesis `i ∉ S` needed) -/

section bounds
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) (S : Finset (Fin N)) (i : Fin N)

include hQ in
theorem measurable_margQS : Measurable (Function.uncurry (margQS Q S i)) := by
  exact (hQ.meas.comp (measurable_assembleS S i)).stronglyMeasurable.integral_prod_right'.measurable

include hQ in
theorem margQS_bounds (a : S → Torus d) (x : Torus d) :
    c ≤ margQS Q S i a x ∧ margQS Q S i a x ≤ C := by
  exact integral_mem_Icc (ρ := (volume : Measure (RestIdx S i → Torus d)))
    (f := fun z => Q (assembleS S i a x z)) ((hQ.meas.comp ((measurable_assembleS S i).comp
    ((measurable_const (a := (a, x))).prodMk measurable_id))).aestronglyMeasurable)
    (fun z => hQ.lower _) (fun z => hQ.upper _)

include hQ in
theorem ZcS_bounds (a : S → Torus d) : c ≤ ZcS Q S i a ∧ ZcS Q S i a ≤ C := by
  exact integral_mem_Icc ((measurable_margQS hQ S i).comp (measurable_const.prodMk measurable_id)
    |>.aestronglyMeasurable) (fun x => (margQS_bounds hQ S i a x).1)
    (fun x => (margQS_bounds hQ S i a x).2)

include hQ in
theorem condDensS_bounds (a : S → Torus d) (x : Torus d) :
    c / C ≤ condDensS Q S i a x ∧ condDensS Q S i a x ≤ C / c := by
  obtain ⟨h1, h2⟩ := margQS_bounds hQ S i a x
  obtain ⟨h3, h4⟩ := ZcS_bounds hQ S i a
  have hc := hQ.pos
  have hC : 0 < C := hc.trans_le (h1.trans h2)
  unfold condDensS
  constructor
  · exact div_le_div₀ (hc.trans_le h1).le h1 (hc.trans_le h3) h4
  · exact div_le_div₀ hC.le h2 hc h3

include hQ in
theorem integral_condDensS (a : S → Torus d) : ∫ x, condDensS Q S i a x ∂haar d = 1 := by
  unfold condDensS
  rw [integral_div]
  exact div_self (hQ.pos.trans_le (ZcS_bounds hQ S i a).1).ne'

include hQ in
theorem measurable_ZcS : Measurable (ZcS (d := d) Q S i) := by
  exact (measurable_margQS hQ S i).stronglyMeasurable.integral_prod_right'.measurable

include hQ in
theorem measurable_condDensS : Measurable (Function.uncurry (condDensS (d := d) Q S i)) := by
  exact (measurable_margQS hQ S i).div ((measurable_ZcS hQ S i).comp measurable_fst)

include hQ in
theorem isProbabilityMeasure_densMeasure_condDensS (a : S → Torus d) :
    IsProbabilityMeasure (densMeasure (condDensS Q S i a)) := by
  refine isProbabilityMeasure_densMeasure' (fun x => ?_) (integral_condDensS hQ S i a)
  exact div_nonneg (hQ.pos.trans_le (margQS_bounds hQ S i a x).1).le
    (hQ.pos.trans_le (ZcS_bounds hQ S i a).1).le

end bounds

end SharpLSI.FL
