/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the preserved BROWNIAN_MOTION_LICENSE.
Authors: Kexing Ying, Greg Neustroev, Shehzad Hathi
Adapted for DGR by Codex: namespaced extraction; proof unchanged except declaration names.
-/
import DGRHS.Commutator.SourceRieszBrownianEnergyPaths

/-! Predictable version of a strongly adapted real process with almost-surely
continuous paths, without completing or augmenting its filtration. The finite
round-down approximation is the selected licensed proof already attributed in
SourceRieszPredictableContinuous. The real limsup construction and its common
all-time almost-sure equality are the continuation here. -/
noncomputable section
open Filter Function MeasureTheory Order Set TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {ι : Type*} [LinearOrder ι] [OrderBot ι]
/-- helper function which (strictly) rounds down `i` onto the set `{⊥} ∪ s` -/
private def versionRoundDown (s : Finset ι) (i : ι) :=
  (insert ⊥ {j ∈ s | j < i}).max' (by simp)

private lemma versionRoundDown_bot {s : Finset ι} : versionRoundDown s ⊥ = ⊥ :=
  eq_bot_iff.mpr <| Finset.max'_le _ _ _ (by simp)

private lemma versionRoundDown_lt_of_ne_bot {s : Finset ι} {i : ι} (h : i ≠ ⊥) :
    versionRoundDown s i < i := by
  apply lt_of_le_of_ne
  · apply Finset.max'_le _ _ _ (fun _ _ ↦ by grind)
  · contrapose! h
    simp [versionRoundDown, Finset.max'_eq_iff] at h
    aesop

private lemma versionRoundDown_le_of_subset {s t : Finset ι} {i : ι} (h : s ⊆ t) :
    versionRoundDown s i ≤ versionRoundDown t i :=
  Finset.max'_le _ _ _ <| fun _ _ ↦ by apply Finset.le_max'; aesop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ}

variable {β : Type*} {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β]
variable {X : ι → Ω → β}

/- a 'rounded down' function is predictable -/
private lemma versionRounded_predictable {times : Finset ι}
    (h_adap : StronglyAdapted 𝓕 X) :
    IsStronglyPredictable 𝓕 (fun i ω ↦ X (versionRoundDown times i) ω) := by
  letI : MeasurableSpace (ι × Ω) := 𝓕.predictable
  -- `X_ap i` approximates X at times `i`
  let X_ap n i := (h_adap i).approx n
  -- For `Y` and `Y_ap`, we keep `s` as a variable for use in the induction step
  -- `Y` is the uncurried version of the rounded down `X`
  let Y s (x : ι × Ω) := X (versionRoundDown s x.1) x.2
  -- `Y_ap` approximates `Y`
  let Y_ap n s (x : ι × Ω) := X_ap n (versionRoundDown s x.1) x.2
  apply stronglyMeasurable_of_tendsto (u := atTop) (f := fun n x ↦ Y_ap n times x)
  · intro n
    refine SimpleFunc.mk (Y_ap n times) ?_ ?_ |>.stronglyMeasurable
    · intro b
      -- induction on the largest element of `times`
      refine times.induction_on_max ?_ ?_
      · apply MeasurableSet.congr (s := univ ×ˢ (X_ap n ⊥ ⁻¹' {b})) _ (by aesop)
        exact measurableSet_predictable_univ_prod (by measurability)
      intro t times ht_max hm
      apply MeasurableSet.congr
        (s := ((Y_ap n times ⁻¹' {b}) ∩ (Iic t ×ˢ univ)) ∪ (Ioi t) ×ˢ (X_ap n t ⁻¹' {b}))
      · apply MeasurableSet.union
        · apply MeasurableSet.inter (by assumption)
          exact measurableSet_predictable_Iic_prod (by measurability)
        · exact measurableSet_predictable_Ioi_prod (by measurability)
      · ext ⟨i, ω⟩
        simp_rw [Y_ap, mem_preimage]
        by_cases! hi : i ≤ t
        · have : versionRoundDown (insert t times) i = versionRoundDown times i := by
            rw [versionRoundDown]; congr 2; grind
          rw [this]; aesop
        · have : versionRoundDown (insert t times) i = t := by
            rw [versionRoundDown, Finset.max'_eq_iff]; grind
          rw [this]; aesop
    · apply Finite.subset (s := (⋃ i ∈ (range (versionRoundDown times)), range (X_ap n i))) _
        <| fun _ _ ↦ by aesop
      apply Finite.biUnion _ <| fun i _ ↦ by apply @(X_ap n i).finite_range
      apply Finite.subset (s := insert ⊥ times) (by aesop)
      intro i hi
      obtain ⟨j, rfl⟩ := mem_range.mp hi
      rw [← Finset.coe_insert, Finset.mem_coe]
      apply Finset.mem_of_subset (s₁ := insert ⊥ ({s ∈ times | s < j})) (by simp)
      apply Finset.max'_mem
  · simpa [Y_ap, tendsto_pi_nhds] using fun _ ↦ by apply StronglyMeasurable.tendsto_approx


variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [DenselyOrdered ι]

private lemma predictableApprox (F : Filtration ι mΩ) (X : ι→Ω→ℝ)
    (hX : StronglyAdapted F X) :
    ∃ Y : ℕ→ι→Ω→ℝ,(∀ n,IsStronglyPredictable F (Y n)) ∧
      (∀ n ω,Y n ⊥ ω=X ⊥ ω) ∧
      (∀ ω,Continuous (fun t=>X t ω) → ∀ t,Tendsto (fun n=>Y n t ω) atTop (𝓝 (X t ω))) := by
  obtain ⟨d,hd_count,hd_dense⟩ := exists_countable_dense ι
  let times n := Finset.image (enumerateCountable hd_count ⊥) (Finset.range n)
  refine ⟨fun n t ω=>X (versionRoundDown (times n) t) ω,
    fun n=>versionRounded_predictable hX,?_,?_⟩
  · intro n ω
    simp [versionRoundDown_bot]
  · intro ω hω i
    apply (hω.tendsto i).comp
    by_cases hi_bot : i=⊥
    · simp [hi_bot,versionRoundDown_bot]
    apply tendsto_atTop_isLUB
      (fun _ _ _ ↦ versionRoundDown_le_of_subset <| Finset.image_subset_image (by aesop))
    apply (isLUB_congr _).mp (isLUB_Iio (a:=i))
    ext j
    simp_rw [mem_upperBounds,mem_Iio]
    constructor
    · intro hj k hk
      apply hj
      obtain ⟨y,rfl⟩ := mem_range.mp hk
      apply versionRoundDown_lt_of_ne_bot hi_bot
    · intro hj k hk
      obtain ⟨r,hr_mem,hr_lt⟩ := hd_dense.exists_between hk
      obtain ⟨n,h_rn⟩ := mem_range.mp <| subset_range_enumerate hd_count ⊥ hr_mem
      trans versionRoundDown (times (n+1)) i
      · trans r
        · exact le_of_lt (by aesop)
        · apply Finset.le_max' _ _ (by aesop)
      · apply hj _ (by aesop)

def sourceRieszPredictableVersion (F : Filtration ι mΩ) (X : ι→Ω→ℝ)
    (hX : StronglyAdapted F X) (t : ι) (ω : Ω) : ℝ :=
  limsup (fun n=>(predictableApprox F X hX).choose n t ω) atTop

lemma sourceRieszPredictableVersion_predictable (F : Filtration ι mΩ) (X : ι→Ω→ℝ)
    (hX : StronglyAdapted F X) :
    IsStronglyPredictable F (sourceRieszPredictableVersion F X hX) := by
  exact (Measurable.limsup (fun n=>((predictableApprox F X hX).choose_spec.1 n).measurable)).stronglyMeasurable

lemma sourceRieszPredictableVersion_bot (F : Filtration ι mΩ) (X : ι→Ω→ℝ)
    (hX : StronglyAdapted F X) (ω : Ω) :
    sourceRieszPredictableVersion F X hX ⊥ ω=X ⊥ ω := by
  unfold sourceRieszPredictableVersion
  simp_rw [(predictableApprox F X hX).choose_spec.2.1]
  simp

lemma sourceRieszPredictableVersion_eq_of_continuous (F : Filtration ι mΩ) (X : ι→Ω→ℝ)
    (hX : StronglyAdapted F X) (ω : Ω) (hω : Continuous (fun t=>X t ω)) (t : ι) :
    sourceRieszPredictableVersion F X hX t ω=X t ω :=
  ((predictableApprox F X hX).choose_spec.2.2 ω hω t).limsup_eq

lemma sourceRieszPredictableVersion_ae_eq (P : Measure Ω) (F : Filtration ι mΩ) (X : ι→Ω→ℝ)
    (hX : StronglyAdapted F X) (hcont : ∀ᵐ ω ∂P,Continuous (fun t=>X t ω)) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszPredictableVersion F X hX t ω=X t ω := by
  filter_upwards [hcont] with ω hω using sourceRieszPredictableVersion_eq_of_continuous F X hX ω hω

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPredictableVersion
#print axioms DGRHS.Commutator.sourceRieszPredictableVersion
#check @DGRHS.Commutator.sourceRieszPredictableVersion_predictable
#print axioms DGRHS.Commutator.sourceRieszPredictableVersion_predictable
#check @DGRHS.Commutator.sourceRieszPredictableVersion_bot
#print axioms DGRHS.Commutator.sourceRieszPredictableVersion_bot
#check @DGRHS.Commutator.sourceRieszPredictableVersion_eq_of_continuous
#print axioms DGRHS.Commutator.sourceRieszPredictableVersion_eq_of_continuous
#check @DGRHS.Commutator.sourceRieszPredictableVersion_ae_eq
#print axioms DGRHS.Commutator.sourceRieszPredictableVersion_ae_eq
