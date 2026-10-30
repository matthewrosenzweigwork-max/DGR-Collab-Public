import DGPS.Lipschitz.T01MinimizerEuler

/-!
# The direct-Lipschitz local minimizer chart

The flat graph and its local uniqueness below use the same implicit-function witnesses.
Probability measures carry their weak topology.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The complementary projection of a kernel component plus a complement is the complement. -/
theorem t01_projY_phi_add {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}
    {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    (a : Par k) (w : Ysub A μ) :
    projY hφ (phiMap φ a + (w : C(Torus d, ℝ))) = w := by
  apply Subtype.ext
  ext x
  change projRaw (μ : Measure (Torus d)) φ (phiMap φ a + (w : C(Torus d, ℝ))) x = w.1 x
  rw [projRaw_apply]
  have hz := lip034_int_phi_add hφ w.2 a
  have hp := lip034_pair_phi_add hφ w.2 a
  simp only [intCLM_apply, pairCLM_apply] at hz hp
  simp_rw [hp]
  rw [hz]
  simp only [zero_mul, sub_zero, ContinuousMap.add_apply, phiMap_apply]
  ring

/-- A positive scalar rate gives an actual weak-topology local chart at every minimizing
probability, with dimension equal to the chosen nullspace basis dimension. -/
theorem t01_minimizer_topological_chart {A : InteractionData d}
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    ∃ U : Set (ProbabilityMeasure (Torus d)), IsOpen U ∧ μ ∈ U ∧
      ∃ O : Set (Par k), IsOpen O ∧
        Nonempty ({ν : ProbabilityMeasure (Torus d) //
          ν ∈ U ∧ freeEnergy A ν = freeEnergyMinimum A} ≃ₜ O) := by
  classical
  obtain ⟨r, hr0, hrrate⟩ := exists_between hrate
  have hrTop : r ≠ ⊤ := ne_top_of_lt hrrate
  have hr : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hrTop
  have hmin := DGPS.Structural.minimizer_le A hμ
  obtain ⟨U, hUo, h0U, y, hy0, hyd, hsm, Wn, hWno, h0Wn, hgr, huniq,
    hpos, ε, hε, hsub, hflat⟩ :=
    flat_reduced_energy_from_positive_nonlinear_rate_with_uniqueness
      hLip hφ hmin b hr (by simpa only [ENNReal.ofReal_toReal hrTop] using hrrate)
  let O : Set (Par k) := Metric.ball 0 ε
  have hOU : O ⊆ U := hsub
  let H : Par k → C(Torus d, ℝ) := fun a => phiMap φ a + (y a : C(Torus d, ℝ))
  have hHc : ContinuousOn H O :=
    ((phiMap φ).continuous.continuousOn.add
      ((Ysub A μ).subtypeL.continuous.comp_continuousOn hsm.continuousOn)).mono hOU
  choose ρ hρ hgap using fun a : O => (hflat a a.2).2
  let R : O → ProbabilityMeasure (Torus d) := fun a => densityMeasure (ρ a)
  have hRm : ∀ a : O, freeEnergy A (R a) = freeEnergyMinimum A := fun a =>
    (scalarGap_eq_zero_iff_minimizer A (ρ a)).mp (hgap a)
  have hRmeasure : ∀ a : O, (R a : Measure (Torus d)) =
      perturb (μ : Measure (Torus d)) (fun x => 1 + H a x) := fun a => hρ a
  have hRratio : ∀ a : O, t01GibbsRatio A μ (R a) = H a := fun a =>
    t01GibbsRatio_eq_of_perturb A hμ (hRm a) (H a) (hpos a (hOU a.2)) (hRmeasure a)
  have hRcoord : ∀ a : O, t01MinimizerCoords φ (R a) = a := by
    intro a
    ext i
    rw [t01MinimizerCoords_eq_pair hφ hμ (hRm a) i, hRratio a]
    exact lip034_pair_phi_add hφ (y a).2 a i
  have hRcomp : ∀ a : O, t01MinimizerComplement hφ (R a) = y a := by
    intro a
    unfold t01MinimizerComplement
    rw [hRratio a]
    exact t01_projY_phi_add hφ a (y a)
  let Θ : ProbabilityMeasure (Torus d) → Par k × Ysub A μ :=
    fun ν => (t01MinimizerCoords φ ν, t01MinimizerComplement hφ ν)
  have hΘc : Continuous Θ :=
    (t01_continuous_minimizerCoords φ).prodMk (t01_continuous_minimizerComplement hφ)
  let V : Set (ProbabilityMeasure (Torus d)) := Θ ⁻¹' (O ×ˢ Wn)
  have hVo : IsOpen V := (Metric.isOpen_ball.prod hWno).preimage hΘc
  have hμV : μ ∈ V := by
    change t01MinimizerCoords φ μ ∈ O ∧ t01MinimizerComplement hφ μ ∈ Wn
    rw [t01MinimizerCoords_self hφ, t01MinimizerComplement_self hφ]
    exact ⟨Metric.mem_ball_self hε, h0Wn⟩
  have hRV : ∀ a : O, R a ∈ V := by
    intro a
    change t01MinimizerCoords φ (R a) ∈ O ∧ t01MinimizerComplement hφ (R a) ∈ Wn
    rw [hRcoord a, hRcomp a]
    exact ⟨a.2, (hgr a (hOU a.2)).1⟩
  have hinv : ∀ ν : ProbabilityMeasure (Torus d),
      (hνV : ν ∈ V) → freeEnergy A ν = freeEnergyMinimum A →
      R ⟨t01MinimizerCoords φ ν, hνV.1⟩ = ν := by
    intro ν hνV hν
    change t01MinimizerCoords φ ν ∈ O ∧ t01MinimizerComplement hφ ν ∈ Wn at hνV
    have hw := huniq (t01MinimizerCoords φ ν) (hOU hνV.1)
      (t01MinimizerComplement hφ ν) hνV.2 (t01_minimizer_redMap hφ hμ hν)
    have hratio : t01GibbsRatio A μ ν = H (t01MinimizerCoords φ ν) := by
      rw [t01GibbsRatio_decomposition hφ hμ hν, hw]
    apply Subtype.ext
    change (R (⟨t01MinimizerCoords φ ν, hνV.1⟩ : O) : Measure (Torus d)) =
      (ν : Measure (Torus d))
    rw [hRmeasure ⟨t01MinimizerCoords φ ν, hνV.1⟩,
      t01_minimizer_eq_perturb A hμ hν, hratio]
  have hRc : Continuous R := by
    rw [continuous_iff_continuousAt]
    intro a₀
    rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hint : ∀ a : O, ∫ x, f x ∂(R a : Measure (Torus d)) =
        intCLM (μ : Measure (Torus d)) ((1 + H a) * f.toContinuousMap) := by
      intro a
      rw [hRmeasure a]
      exact integral_perturb (u := fun x => 1 + H a x)
        (continuous_const.add (H a).continuous)
        (fun x => (hpos a (hOU a.2) x).le) f
    simp_rw [hint]
    have hc : Continuous (fun a : O => H a) := hHc.restrict
    exact ((intCLM (μ : Measure (Torus d))).continuous.comp
      ((continuous_const.add hc).mul continuous_const)).continuousAt
  refine ⟨V, hVo, hμV, O, Metric.isOpen_ball, ⟨?_⟩⟩
  exact
    { toFun := fun ν => ⟨t01MinimizerCoords φ ν, ν.2.1.1⟩
      invFun := fun a => ⟨R a, hRV a, hRm a⟩
      left_inv := fun ν => Subtype.ext (hinv ν ν.2.1 ν.2.2)
      right_inv := fun a => Subtype.ext (hRcoord a)
      continuous_toFun := ((t01_continuous_minimizerCoords φ).comp
        continuous_subtype_val).subtype_mk _
      continuous_invFun := hRc.subtype_mk _ }

end DGPS.Lipschitz
