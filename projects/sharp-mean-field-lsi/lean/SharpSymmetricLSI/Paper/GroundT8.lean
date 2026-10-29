import SharpSymmetricLSI.Paper.GroundT7

/-!
# R30: `ground_state_transform_of` ((7.6)–(7.7)), conditional on (5.14) and Proposition 2.2
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memLp_two_of_lintegral {α : Type*} [MeasurableSpace α] {P : Measure α} {G : α → ℝ}
    (hG : AEStronglyMeasurable G P) (h : ∫⁻ x, ENNReal.ofReal (G x ^ 2) ∂P < ⊤) : MemLp G 2 P :=
  (memLp_two_iff_integrable_sq hG).2 ⟨hG.pow 2,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2 h⟩

/-- The final constant bookkeeping in `ℝ≥0∞`. -/
theorem ennreal_bookkeeping {E M J ent : ℝ≥0∞} {CF r : ℝ} (hr : 0 < r) {B : ℝ≥0}
    (hJ : J ≤ ENNReal.ofReal CF * (ent + M))
    (hent : ent ≤ ENNReal.ofReal (2 / r) * E + (B : ℝ≥0∞) * M) :
    ENNReal.ofReal 2 * E + ENNReal.ofReal (1 / 2) * J ≤
      ENNReal.ofReal (2 + max CF 0 / r + max CF 0 * ((B : ℝ) + 1) / 2) * (E + M) := by
  set a := max CF 0
  have ha : 0 ≤ a := le_max_right _ _
  have hJ' : J ≤ ENNReal.ofReal a * (ENNReal.ofReal (2 / r) * E + (B : ℝ≥0∞) * M + M) :=
    hJ.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      (add_le_add hent le_rfl))
  have hB : (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  rw [hB] at hJ'
  have e1 : ENNReal.ofReal (1 / 2) * (ENNReal.ofReal a * (ENNReal.ofReal (2 / r) * E +
      ENNReal.ofReal (B : ℝ) * M + M)) =
      ENNReal.ofReal (a / r) * E + ENNReal.ofReal (a * ((B : ℝ) + 1) / 2) * M := by
    have h1 : ENNReal.ofReal (1 / 2) * ENNReal.ofReal a * ENNReal.ofReal (2 / r) =
        ENNReal.ofReal (a / r) := by
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    have h2 : ENNReal.ofReal (1 / 2) * ENNReal.ofReal a * (ENNReal.ofReal (B : ℝ) + 1) =
        ENNReal.ofReal (a * ((B : ℝ) + 1) / 2) := by
      rw [← ENNReal.ofReal_one, (ENNReal.ofReal_add (NNReal.coe_nonneg B) zero_le_one).symm,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    rw [← h1, ← h2]
    ring
  calc ENNReal.ofReal 2 * E + ENNReal.ofReal (1 / 2) * J
      ≤ ENNReal.ofReal 2 * E + (ENNReal.ofReal (a / r) * E +
          ENNReal.ofReal (a * ((B : ℝ) + 1) / 2) * M) := by
        rw [← e1]; gcongr
    _ = ENNReal.ofReal (2 + a / r) * E + ENNReal.ofReal (a * ((B : ℝ) + 1) / 2) * M := by
        rw [ENNReal.ofReal_add zero_le_two (by positivity)]; ring
    _ ≤ ENNReal.ofReal (2 + a / r + a * ((B : ℝ) + 1) / 2) * E +
          ENNReal.ofReal (2 + a / r + a * ((B : ℝ) + 1) / 2) * M := by
        have h3 : 0 ≤ a * ((B : ℝ) + 1) / 2 := by positivity
        have h4 : 0 ≤ a / r := by positivity
        refine add_le_add ?_ ?_
        · gcongr ENNReal.ofReal ?_ * _
          linarith
        · gcongr ENNReal.ofReal ?_ * _
          linarith
    _ = _ := (mul_add _ E M).symm

/-- **(7.6)–(7.7)**, conditional on the force bound (5.14) and the defective inequality. -/
theorem ground_state_transform_of (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {CF : ℝ}
    (hForce : ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      IsSymmetricMeasure ν → klDiv ν (gibbs V W N) ≠ ⊤ →
      ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
        ENNReal.ofReal CF * (klDiv ν (gibbs V W N) + 1))
    {r : ℝ} (hr : 0 < r) {B : ℝ≥0}
    (hDef : ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f → IsSymmetric f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤
        ENNReal.ofReal (2 / r) * energy V W N f + (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f → IsSymmetric f →
      let Ψ : Config N d → ℝ := fun X =>
        f X * Real.sqrt (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N)
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ ∧
      ∫⁻ X, ENNReal.ofReal (Ψ X ^ 2) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N ∧
      ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal C * (energy V W N f + ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) := by
  refine ⟨2 + max CF 0 / r + max CF 0 * ((B : ℝ) + 1) / 2, fun N hN f hf hs => ?_⟩
  intro Ψ
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have hfL := memLp_of_memH1C hyp hf
  have hE := energy_lt_top hyp hf
  have hM : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).1 hfL.integrable_sq.2
  have hent := hDef N hN f hf hs
  have hent' : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤ :=
    (hent.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE,
      ENNReal.mul_lt_top ENNReal.coe_lt_top hM⟩)).ne
  have hJ := lintegral_sq_gradU_le hyp (hForce N hN) hf hs hent'
  have hgrad : ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q ≤
      ENNReal.ofReal (2 + max CF 0 / r + max CF 0 * ((B : ℝ) + 1) / 2) *
        (energy V W N f + ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) :=
    (lintegral_gradSqC_psi_le hyp hμ hN hf).trans (ennreal_bookkeeping hr hJ hent)
  have hiso := lintegral_psi_sq hyp hμ f (N := N)
  refine ⟨?_, hiso, hgrad⟩
  -- `H¹(μ^{⊗N})`
  have hpair := isWeakGrad_psi hyp hμ hN hf
  have hac := pi_map_flat_ac hyp hμ (N := N)
  have hemb := measurableEmbedding_flat (N := N) (d := d)
  refine ⟨⟨_, hpair⟩, ?_, ?_⟩
  · refine memLp_two_of_lintegral (hpair.aestronglyMeasurable_fun.mono_ac hac) ?_
    rw [hemb.lintegral_map]
    exact (hiso.trans_lt hM)
  · have hw := isWeakGrad_weakGrad ⟨_, hpair⟩
    have hm : AEStronglyMeasurable (fun y => Real.sqrt (sqNorm (weakGrad (Ψ ∘ unflat) y))) volume := by
      unfold sqNorm
      exact Real.continuous_sqrt.comp_aestronglyMeasurable
        (Finset.aestronglyMeasurable_fun_sum _ fun p _ => (hw.aestronglyMeasurable_grad p).pow 2)
    refine memLp_two_of_lintegral (hm.mono_ac hac) ?_
    rw [hemb.lintegral_map]
    have : ∀ X, Real.sqrt (sqNorm (weakGrad (Ψ ∘ unflat) (flat X))) ^ 2 = gradSqC Ψ X := fun X => by
      have hn : 0 ≤ sqNorm (weakGrad (Ψ ∘ unflat) (flat X)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [Real.sq_sqrt hn, gradSqC_eq_sqNorm]
    simp_rw [this]
    exact hgrad.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hE, hM⟩))

end SharpLSI
