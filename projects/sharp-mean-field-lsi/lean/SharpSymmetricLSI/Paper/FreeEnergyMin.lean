import SharpSymmetricLSI.Paper.KLLsc
import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Defs.D02_Hypotheses

/-!
# Existence of a minimizer of the free energy (D5 sanity lemma)

`F(ρ) = H(ρ|m) + ρ(V) + ½W(ρ,ρ)` is weakly lower semicontinuous on the compact space
`𝒫(𝕋^d)` (entropy: Donsker–Varadhan; energy: continuous, by uniform continuity of `W`), hence
attains its infimum. The definitions of `D5` are copied (`freeEnergyAux`, `FstarAux`) so that
`D05` can import this file.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

section energy
variable {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
  {W : α → α → ℝ}

/-- `Φ_η(y) = ∫ W(x,y) dη(x)`. -/
def convAux (W : α → α → ℝ) (η : Measure α) (y : α) : ℝ := ∫ x, W x y ∂η

theorem convAux_close (hW : Continuous (Function.uncurry W)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (η : ProbabilityMeasure α) (y y' : α), dist y y' < δ →
      |convAux W η y - convAux W η y'| ≤ ε := by
  have hu := CompactSpace.uniformContinuous_of_continuous hW
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ, hδ, fun η y y' hyy' => ?_⟩
  obtain ⟨BW, hBW⟩ := (isCompact_univ.image hW).isBounded.exists_norm_le
  have hbd : ∀ z, Integrable (fun x => W x z) (η : Measure α) := fun z =>
    Integrable.of_bound (hW.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable BW
      (Eventually.of_forall fun x => hBW _ ⟨(x, z), Set.mem_univ _, rfl⟩)
  unfold convAux
  rw [← integral_sub (hbd y) (hbd y')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |W x y - W x y'| ∂(η : Measure α) ≤ ∫ _x, ε ∂(η : Measure α) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          (Eventually.of_forall fun x => by
            have h := hδε (a := (x, y)) (b := (x, y')) (by
              rw [Prod.dist_eq, dist_self]; simpa using hyy')
            rw [Real.dist_eq] at h; exact h.le)
    _ = ε := by simp

theorem continuous_convAux (hW : Continuous (Function.uncurry W)) (η : ProbabilityMeasure α) :
    Continuous (convAux W η) := by
  rw [Metric.continuous_iff]
  intro y ε hε
  obtain ⟨δ, hδ, h⟩ := convAux_close hW (half_pos hε)
  refine ⟨δ, hδ, fun y' hy' => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (h η y y' (by rwa [dist_comm])) (half_lt_self hε)

theorem abs_convAux_le (hW : Continuous (Function.uncurry W)) :
    ∃ B, ∀ (η : ProbabilityMeasure α) y, |convAux W η y| ≤ B := by
  obtain ⟨BW, hBW⟩ := (isCompact_univ.image hW).isBounded.exists_norm_le
  refine ⟨BW, fun η y => (abs_integral_le_integral_abs).trans ?_⟩
  calc ∫ x, |W x y| ∂(η : Measure α) ≤ ∫ _x, BW ∂(η : Measure α) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          (Eventually.of_forall fun x => hBW _ ⟨(x, y), Set.mem_univ _, rfl⟩)
    _ = BW := by simp

/-- **`ρ ↦ ∬ W dρ dρ` is weakly continuous.** -/
theorem continuous_interAux (hW : Continuous (Function.uncurry W)) :
    Continuous fun ρ : ProbabilityMeasure α => ∫ y, ∫ x, W x y ∂(ρ : Measure α) ∂(ρ : Measure α) := by
  obtain ⟨B, hB⟩ := abs_convAux_le hW
  have hint : ∀ (η ρ' : ProbabilityMeasure α), Integrable (convAux W η) (ρ' : Measure α) :=
    fun η ρ' => Integrable.of_bound (continuous_convAux hW η).aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB η y)
  rw [continuous_iff_continuousAt]
  intro ρ
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := convAux_close hW (show 0 < ε / 4 by positivity)
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := α)) hδ
  -- each center: weak convergence of `∫ W(x,z) dη(x)`
  have hc : ∀ z, Continuous fun η : ProbabilityMeasure α => convAux W η z := fun z => by
    obtain ⟨BW, hBW⟩ := (isCompact_univ.image hW).isBounded.exists_norm_le
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨fun x => W x z,
        hW.comp (continuous_id.prodMk continuous_const)⟩)
  have hev1 : ∀ᶠ η : ProbabilityMeasure α in 𝓝 ρ, ∀ z ∈ t,
      |convAux W η z - convAux W ρ z| < ε / 4 :=
    (htf.eventually_all).mpr fun z _ => by
      have := (hc z).continuousAt.eventually (Metric.ball_mem_nhds (convAux W ρ z)
        (show 0 < ε / 4 by positivity))
      filter_upwards [this] with η hη
      rwa [Real.dist_eq] at hη
  -- the outer integral of the fixed function `Φ_ρ`
  have hev2 : ∀ᶠ η : ProbabilityMeasure α in 𝓝 ρ, |∫ y, convAux W ρ y ∂(η : Measure α) - ∫ y, convAux W ρ y ∂(ρ : Measure α)|
      < ε / 4 := by
    have := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨convAux W ρ, continuous_convAux hW ρ⟩)).continuousAt
      (x := ρ) |>.eventually (Metric.ball_mem_nhds _ (show 0 < ε / 4 by positivity))
    filter_upwards [this] with η hη
    rwa [Real.dist_eq] at hη
  filter_upwards [hev1, hev2] with η h1 h2
  -- uniform closeness of `Φ_η` and `Φ_ρ`
  have hunif : ∀ y, |convAux W η y - convAux W ρ y| ≤ 3 * (ε / 4) := fun y => by
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_univ y))
    have a1 := hclose η y z (by rwa [Metric.mem_ball] at hyz)
    have a2 := hclose ρ y z (by rwa [Metric.mem_ball] at hyz)
    have a3 := (h1 z hz).le
    calc |convAux W η y - convAux W ρ y|
        = |(convAux W η y - convAux W η z) + (convAux W η z - convAux W ρ z) -
            (convAux W ρ y - convAux W ρ z)| := by ring_nf
      _ ≤ _ := by
          refine (abs_sub _ _).trans ?_
          linarith [abs_add_le (convAux W η y - convAux W η z) (convAux W η z - convAux W ρ z)]
  rw [Real.dist_eq]
  change |∫ y, convAux W η y ∂(η : Measure α) - ∫ y, convAux W ρ y ∂(ρ : Measure α)| < ε
  have hsplit : ∫ y, convAux W η y ∂(η : Measure α) - ∫ y, convAux W ρ y ∂(ρ : Measure α) =
      (∫ y, (convAux W η y - convAux W ρ y) ∂(η : Measure α)) +
        (∫ y, convAux W ρ y ∂(η : Measure α) - ∫ y, convAux W ρ y ∂(ρ : Measure α)) := by
    rw [integral_sub (hint η η) (hint ρ η)]; ring
  rw [hsplit]
  have h3 : |∫ y, (convAux W η y - convAux W ρ y) ∂(η : Measure α)| ≤ 3 * (ε / 4) := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |convAux W η y - convAux W ρ y| ∂(η : Measure α) ≤ ∫ _y, 3 * (ε / 4) ∂(η : Measure α) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall hunif)
      _ = 3 * (ε / 4) := by simp
  calc _ ≤ _ := abs_add_le _ _
    _ < 3 * (ε / 4) + ε / 4 := add_lt_add_of_le_of_lt h3 h2
    _ = ε := by ring

end energy

section freeEnergy
variable {d : ℕ}

/-- A copy of `potE` (D5). -/
def potEAux (V : Torus d → ℝ) (ρ : Measure (Torus d)) : ℝ := ∫ x, V x ∂ρ

/-- A copy of `interE` (D5). -/
def interEAux (W : Torus d → Torus d → ℝ) (ρ η : Measure (Torus d)) : ℝ :=
  ∫ y, ∫ x, W x y ∂ρ ∂η

/-- A copy of `freeEnergy` (D5). -/
def freeEnergyAux (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Measure (Torus d)) : EReal :=
  ((klDiv ρ (haar d) : ENNReal) : EReal) + ((potEAux V ρ + interEAux W ρ ρ / 2 : ℝ) : EReal)

/-- A copy of `Fstar` (D5). -/
def FstarAux (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : EReal :=
  ⨅ ρ : ProbabilityMeasure (Torus d), freeEnergyAux V W ρ

theorem exists_minimizer_aux {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) :
    (∃ μ : ProbabilityMeasure (Torus d), freeEnergyAux V W μ = FstarAux V W) ∧
      FstarAux V W ≠ ⊤ ∧ FstarAux V W ≠ ⊥ := by
  set F : ProbabilityMeasure (Torus d) → EReal := fun ρ => freeEnergyAux V W ρ
  obtain ⟨BV, hBV⟩ := (isCompact_univ.image hyp.continuous_V).isBounded.exists_norm_le
  have hreal : Continuous fun ρ : ProbabilityMeasure (Torus d) =>
      potEAux V ρ + interEAux W ρ ρ / 2 := by
    refine Continuous.add ?_ ((continuous_interAux hyp.continuous_W).div_const 2)
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨V, hyp.continuous_V⟩)
  have hlsc : LowerSemicontinuous F := by
    refine LowerSemicontinuous.add' (lowerSemicontinuous_klDiv (haar d))
      (continuous_coe_real_ereal.comp hreal).lowerSemicontinuous fun ρ => ?_
    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have hne : (Set.univ : Set (ProbabilityMeasure (Torus d))).Nonempty :=
    ⟨⟨haar d, inferInstance⟩, Set.mem_univ _⟩
  obtain ⟨μ, -, hμ⟩ := (hlsc.lowerSemicontinuousOn Set.univ).exists_isMinOn hne isCompact_univ
  have hμF : F μ = FstarAux V W :=
    le_antisymm (le_iInf fun ρ => hμ (Set.mem_univ ρ)) (iInf_le _ μ)
  refine ⟨⟨μ, hμF⟩, ?_, ?_⟩
  · refine ne_top_of_le_ne_top ?_ (iInf_le _ (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)))
    simp only [freeEnergyAux, ProbabilityMeasure.coe_mk, klDiv_self, ENNReal.coe_zero,
      EReal.coe_ennreal_zero, zero_add]
    exact EReal.coe_ne_top _
  · rw [← hμF]
    simp only [F, freeEnergyAux, ne_eq, EReal.add_eq_bot_iff, not_or]
    exact ⟨EReal.coe_ennreal_ne_bot _, EReal.coe_ne_bot _⟩

end freeEnergy

end SharpLSI
