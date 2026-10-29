import SharpSymmetricLSI.Paper.GroundT11

/-!
# R30 groundwork: rescaled ground states `Ψ' = f √(e^{-U_N}/K')`
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sqrt_rescale {a K K' : ℝ} (_ha : 0 ≤ a) (hK : 0 < K) (hK' : 0 < K') :
    Real.sqrt (a / K') = Real.sqrt (K / K') * Real.sqrt (a / K) := by
  rw [← Real.sqrt_mul (div_nonneg hK.le hK'.le)]
  congr 1; field_simp

/-- **Rescaled ground states.** -/
theorem rescaled_ground_state (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {CF : ℝ}
    (hForce : ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      IsSymmetricMeasure ν → klDiv ν (gibbs V W N) ≠ ⊤ →
      ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
        ENNReal.ofReal CF * (klDiv ν (gibbs V W N) + 1))
    {r : ℝ} (hr : 0 < r) {B : ℝ≥0}
    (hDef : ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f → IsSymmetric f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤
        ENNReal.ofReal (2 / r) * energy V W N f + (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ K' : ℝ, 0 < K' → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f → IsSymmetric f →
      IsSymmetric (fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) ∧
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))
        (fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) ∧
      ∫⁻ X, ENNReal.ofReal ((f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) ^ 2 +
          gradSqC (fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) X)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal (centeredPartition W μ N / K' * C) *
          (energy V W N f + ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) := by
  obtain ⟨Cg, hCg⟩ := ground_state_transform_of hyp hμ hForce hr hDef
  refine ⟨max Cg 0 + 1, by positivity, fun N hN K' hK' f hf hs => ?_⟩
  set Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set K := centeredPartition W μ N
  have hK : 0 < K := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  obtain ⟨hH, hiso, hgr⟩ := hCg N hN f hf hs
  set Ψ : Config N d → ℝ := fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / K)
  set c := Real.sqrt (K / K')
  have hΨ' : (fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')) = fun X => c * Ψ X := by
    funext X
    simp only [Ψ, c]
    rw [sqrt_rescale (Real.exp_pos _).le hK hK']; ring
  have hc2 : c ^ 2 = K / K' := Real.sq_sqrt (div_nonneg hK.le hK'.le)
  refine ⟨fun σ X => ?_, ?_, ?_⟩
  · show f (X ∘ σ) * Real.sqrt (rexp (-Ucentered W μ N (X ∘ σ)) / K') =
      f X * Real.sqrt (rexp (-Ucentered W μ N X) / K')
    rw [hs σ X, Ucentered_perm]
  · rw [hΨ']; exact memH1C_pi_const_mul hyp hμ hH c
  · have hpt : ∀ X, f X * Real.sqrt (rexp (-Ucentered W μ N X) / K') = c * Ψ X :=
      fun X => congrFun hΨ' X
    simp only [hpt]
    have hm : AEMeasurable (fun X => ENNReal.ofReal ((c * Ψ X) ^ 2)) Q :=
      (((memLp_of_memH1C_pi hH).aestronglyMeasurable.const_mul c).pow 2).aemeasurable.ennreal_ofReal
    have h1 : ∫⁻ X, ENNReal.ofReal ((c * Ψ X) ^ 2 + gradSqC (fun X => c * Ψ X) X) ∂Q ≤
        ∫⁻ X, ENNReal.ofReal ((c * Ψ X) ^ 2) ∂Q + ∫⁻ X, ENNReal.ofReal (gradSqC (fun X => c * Ψ X) X) ∂Q :=
      (lintegral_mono fun X => ENNReal.ofReal_add_le).trans (le_of_eq
        (lintegral_add_left' (f := fun X => ENNReal.ofReal ((c * Ψ X) ^ 2)) hm
          (fun X => ENNReal.ofReal (gradSqC (fun X => c * Ψ X) X))))
    have h2 : ∫⁻ X, ENNReal.ofReal ((c * Ψ X) ^ 2) ∂Q =
        ENNReal.ofReal (K / K') * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
      rw [← hiso, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun X => ?_
      rw [← ENNReal.ofReal_mul (div_nonneg hK.le hK'.le), ← hc2, mul_pow]
    have h3 : ∫⁻ X, ENNReal.ofReal (gradSqC (fun X => c * Ψ X) X) ∂Q =
        ENNReal.ofReal (K / K') * ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae ?_
      filter_upwards [gradSqC_const_mul_ae hyp hμ hH.1 c] with X hX
      rw [hX, ← ENNReal.ofReal_mul (div_nonneg hK.le hK'.le), hc2]
    refine h1.trans ?_
    rw [h2, h3]
    set E := energy V W N f
    set M := ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N
    have hgr' : ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q ≤ ENNReal.ofReal (max Cg 0) * (E + M) :=
      hgr.trans (by gcongr; exact le_max_left _ _)
    calc ENNReal.ofReal (K / K') * M + ENNReal.ofReal (K / K') * ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Q
        ≤ ENNReal.ofReal (K / K') * (E + M) +
            ENNReal.ofReal (K / K') * (ENNReal.ofReal (max Cg 0) * (E + M)) := by
          gcongr
          exact le_add_self
      _ = ENNReal.ofReal (K / K' * (max Cg 0 + 1)) * (E + M) := by
          rw [ENNReal.ofReal_mul (div_nonneg hK.le hK'.le), ENNReal.ofReal_add (le_max_right _ _)
            zero_le_one, ENNReal.ofReal_one]
          ring

/-- **Chebyshev** for `U_N`. -/
theorem measure_Ucentered_gt_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    {N : ℕ} {CU : ℝ}
    (hCU : ∫ X, Ucentered W μ N X ^ 2 ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ CU)
    {t : ℝ} (ht : 0 < t) :
    Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) {X | t < Ucentered W μ N X} ≤
      ENNReal.ofReal (CU / t ^ 2) := by
  set μm := (μ : Measure (Torus d))
  set Q := Measure.pi fun _ : Fin N => μm
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm N
  have hUi : Integrable (fun X => Ucentered W μ N X ^ 2) Q :=
    integrable_of_bdd ((measurable_Ucentered hyp μm N).pow_const 2) (C := BU ^ 2) fun X => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBU X) 2
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun X => sq_nonneg
    (Ucentered W μ N X)) hUi (t ^ 2)
  have hsub : {X | t < Ucentered W μ N X} ⊆ {X | t ^ 2 ≤ Ucentered W μ N X ^ 2} := fun X hX => by
    simp only [mem_ofPred_eq] at hX ⊢; nlinarith
  have hfin : Q {X | t ^ 2 ≤ Ucentered W μ N X ^ 2} ≠ ⊤ := measure_ne_top _ _
  calc Q {X | t < Ucentered W μ N X} ≤ Q {X | t ^ 2 ≤ Ucentered W μ N X ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal (Q.real {X | t ^ 2 ≤ Ucentered W μ N X ^ 2}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hfin]
    _ ≤ ENNReal.ofReal (CU / t ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact h.trans hCU

end SharpLSI
