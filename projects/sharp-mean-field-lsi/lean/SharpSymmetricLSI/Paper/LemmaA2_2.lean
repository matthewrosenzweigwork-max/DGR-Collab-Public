import SharpSymmetricLSI.Paper.LemmaA2_1

/-!
# R25 (A.9), part 2: the semiconvexity clause for an arbitrary density of `μ`

The statement allows any `p > 0` with `μ = p m`, not assumed measurable. Two such densities need
not agree a.e., but where `(-log p ∘ liftT) s` is integrable (`s` continuous) they do agree a.e. on
`{s ≠ 0}` (`ae_eq_negLog`): on a positive-measure set where `p ≤ aρ` (`a < 1`) or `p ≥ bρ` (`b > 1`)
the two densities would give different masses (`haar_eq_zero_of_le`, `haar_eq_zero_of_ge`), and
sets of `ℝ^d` are transferred to the torus box by box (`volume_eq_zero_of_bad`). If the product is
not integrable its integral is `0` and the inequality is trivial. (`semiconvex_negLog`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

section dens

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q ρ : Torus d → ℝ}
  (hq : μ = densMeasure q) (hρ : μ = densMeasure ρ) {c : ℝ} (hc : 0 < c) (hρc : ∀ y, c ≤ ρ y)
include hq hρ hc hρc

theorem setLIntegral_eq_of_dens {E : Set (Torus d)} :
    ∫⁻ y in E, ENNReal.ofReal (q y) ∂haar d = ∫⁻ y in E, ENNReal.ofReal (ρ y) ∂haar d := by
  rw [← withDensity_apply' _ E, ← withDensity_apply' _ E]
  change densMeasure q E = densMeasure ρ E
  rw [← hq, ← hρ]

theorem setLIntegral_dens_lt_top {E : Set (Torus d)} :
    ∫⁻ y in E, ENNReal.ofReal (ρ y) ∂haar d < ⊤ := by
  rw [← withDensity_apply' _ E]
  change densMeasure ρ E < ⊤
  rw [← hρ]; exact measure_lt_top μ E

theorem haar_eq_zero_of_dens_zero {E : Set (Torus d)} (hE : MeasurableSet E)
    (h0 : ∫⁻ y in E, ENNReal.ofReal (ρ y) ∂haar d = 0) : haar d E = 0 := by
  have : ∫⁻ _y in E, ENNReal.ofReal c ∂haar d ≤ ∫⁻ y in E, ENNReal.ofReal (ρ y) ∂haar d :=
    lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hρc y)
  rw [h0, setLIntegral_const, nonpos_iff_eq_zero, mul_eq_zero] at this
  rcases this with h | h
  · exact absurd h (ENNReal.ofReal_pos.mpr hc).ne'
  · exact h

theorem haar_eq_zero_of_le {E : Set (Torus d)} (hE : MeasurableSet E) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1) (h : ∀ y ∈ E, q y ≤ a * ρ y) : haar d E = 0 := by
  refine haar_eq_zero_of_dens_zero hq hρ hc hρc hE ?_
  set I := ∫⁻ y in E, ENNReal.ofReal (ρ y) ∂haar d
  have hI := setLIntegral_dens_lt_top hq hρ hc hρc (E := E)
  have h1 : I ≤ ENNReal.ofReal a * I := by
    calc I = ∫⁻ y in E, ENNReal.ofReal (q y) ∂haar d := (setLIntegral_eq_of_dens hq hρ hc hρc).symm
      _ ≤ ∫⁻ y in E, ENNReal.ofReal (a * ρ y) ∂haar d :=
          lintegral_mono_ae ((ae_restrict_iff' hE).mpr (Eventually.of_forall fun y hy =>
            ENNReal.ofReal_le_ofReal (h y hy)))
      _ = ENNReal.ofReal a * I := by
          simp_rw [ENNReal.ofReal_mul ha0]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0] at h2
  have h3 : I.toReal = 0 := le_antisymm (by nlinarith [ENNReal.toReal_nonneg (a := I)])
    ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp h3 |>.resolve_right hI.ne

theorem haar_eq_zero_of_ge {E : Set (Torus d)} (hE : MeasurableSet E) {b : ℝ} (hb : 1 < b)
    (h : ∀ y ∈ E, b * ρ y ≤ q y) : haar d E = 0 := by
  refine haar_eq_zero_of_dens_zero hq hρ hc hρc hE ?_
  set I := ∫⁻ y in E, ENNReal.ofReal (ρ y) ∂haar d
  have hI := setLIntegral_dens_lt_top hq hρ hc hρc (E := E)
  have h1 : ENNReal.ofReal b * I ≤ I := by
    calc ENNReal.ofReal b * I = ∫⁻ y in E, ENNReal.ofReal (b * ρ y) ∂haar d := by
          simp_rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ b)]
          exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ y in E, ENNReal.ofReal (q y) ∂haar d :=
          lintegral_mono_ae ((ae_restrict_iff' hE).mpr (Eventually.of_forall fun y hy =>
            ENNReal.ofReal_le_ofReal (h y hy)))
      _ = I := setLIntegral_eq_of_dens hq hρ hc hρc
  have h2 := ENNReal.toReal_mono hI.ne h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h2
  have h3 : I.toReal = 0 := le_antisymm (by nlinarith [ENNReal.toReal_nonneg (a := I)])
    ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp h3 |>.resolve_right hI.ne

end dens

/-- A measurable set of `ℝ^d` whose points all lift to `Bad` points is null, if every measurable
set of `Bad` torus points is. -/
theorem volume_eq_zero_of_bad {Bad : Torus d → Prop}
    (hBad : ∀ E, MeasurableSet E → (∀ y ∈ E, Bad y) → haar d E = 0) {A : Set (Fin d → ℝ)}
    (hA : MeasurableSet A) (h : ∀ x ∈ A, Bad (liftT x)) : volume A = 0 := by
  -- the part in the unit box
  have hbox : ∀ A' : Set (Fin d → ℝ), MeasurableSet A' → A' ⊆ unitBox (Fin d) →
      (∀ x ∈ A', Bad (liftT x)) → volume A' = 0 := by
    intro A' hA' hsub hA'b
    set E := secT ⁻¹' A'
    have hE : MeasurableSet E := measurable_secT hA'
    have h0 : haar d E = 0 := hBad E hE fun y hy => by
      have := hA'b _ hy; rwa [liftT_secT] at this
    have hpres := measurePreserving_liftT (ι := Fin d)
    have h1 : (volume.restrict (unitBox (Fin d))) (liftT ⁻¹' E) = 0 := by
      rw [hpres.measure_preimage hE.nullMeasurableSet]; exact h0
    have hsub' : A' ⊆ liftT ⁻¹' E := fun x hx => by
      show secT (liftT x) ∈ A'
      rw [secT_liftT (hsub hx)]; exact hx
    have h2 := measure_mono_null hsub' h1
    rwa [Measure.restrict_apply hA', inter_eq_left.mpr hsub] at h2
  -- translates
  have hcov : A ⊆ ⋃ m : Fin d → ℤ, (fun x => x + -intVec m) ⁻¹'
      ((fun x => x + intVec m) ⁻¹' A ∩ unitBox (Fin d)) := by
    intro x hx
    refine mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1, ?_, ?_⟩
    · simp only [mem_preimage, neg_add_cancel_right]
      exact hx
    · simp only [mem_preimage, unitBox, Set.mem_pi, mem_univ, true_implies, Set.mem_Ioc]
      intro i
      simp only [intVec, Pi.add_apply, Pi.neg_apply, Int.cast_sub, Int.cast_one]
      constructor
      · linarith [Int.ceil_lt_add_one (x i)]
      · linarith [Int.le_ceil (x i)]
  refine measure_mono_null hcov (measure_iUnion_null fun m => ?_)
  rw [measure_preimage_add_right]
  refine hbox _ ((measurable_add_const _ hA).inter (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)) inter_subset_right
    fun x hx => ?_
  have := h _ hx.1
  rwa [liftT_add_intVec] at this

end SharpLSI
