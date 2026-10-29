import SharpSymmetricLSI.Paper.GroundT15

/-!
# R30: Section 7.2, (7.8)–(7.10), conditional on Prop. 2.1, Lemma 5.2, (5.14) and Prop. 2.2

The joint law of `(f_N, Z_N)` under `P_N` (step 1 of the assembly).
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The joint law of `(f, Z)` under `P_N` from the joint law of `(Ψ', U_N, Z)` under `μ^{⊗N}`. -/
theorem tendsto_gibbs_joint (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) {Q : (ℕ → ℝ) → ℝ}
    (hQ : IsSecondChaos (Tmat W μ e) Q)
    {K' : ℝ} (hK' : 0 < K') {q Bq : ℝ} (hq : 1 < q)
    (hBq : ∀ N : ℕ, 1 ≤ N → ∫ X, rexp (-Ucentered W μ N X) ^ q
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bq)
    (hint : Integrable (fun z => rexp (-Uinf W μ Q z)) gammaRef)
    (Ns : ℕ → ℕ) (hN1 : ∀ k, 1 ≤ Ns k) (f : (k : ℕ) → Config (Ns k) d → ℝ)
    (hfm : ∀ k, AEStronglyMeasurable (fun X => f k X *
      Real.sqrt (rexp (-Ucentered W μ (Ns k) X) / K')) (Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d))))
    {Ψinf : (ℕ → ℝ) → ℝ} (hΨm : AEStronglyMeasurable Ψinf gammaRef)
    (hjoint : ∀ (J : ℕ) (g : ℝ × ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g (f k X * Real.sqrt (rexp (-Ucentered W μ (Ns k) X) / K'),
          Ucentered W μ (Ns k) X, fun n => fluct e (Ns k) n X)
          ∂Measure.pi (fun _ : Fin (Ns k) => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, g (Ψinf z, Uinf W μ Q z, fun n => z n) ∂gammaRef)))
    (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ) :
    Tendsto (fun k => ∫ X, rexp (-Ucentered W μ (Ns k) X) / K' * g (f k X, fun n => fluct e (Ns k) n X)
        ∂Measure.pi (fun _ : Fin (Ns k) => (μ : Measure (Torus d)))) atTop
      (𝓝 (∫ z, rexp (-Uinf W μ Q z) / K' *
        g (Ψinf z / Real.sqrt (wK K' (Uinf W μ Q z)), fun n => z n) ∂gammaRef)) := by
  set μm := (μ : Measure (Torus d))
  have key := tendsto_weighted_gen (E := ℝ × (Fin J → ℝ))
    (P := fun k => Measure.pi fun _ : Fin (Ns k) => μm)
    (A := fun k X => (f k X * Real.sqrt (rexp (-Ucentered W μ (Ns k) X) / K'),
      fun n => fluct e (Ns k) n X))
    (U := fun k X => Ucentered W μ (Ns k) X) (P' := gammaRef)
    (A' := fun z => (Ψinf z, fun n : Fin J => z n)) (U' := Uinf W μ Q)
    (fun G => hjoint J (rearr G)) (continuous_wK K') (fun u => (wK_pos hK' u).le) hq
    (fun k => ((hfm k).prodMk (aestronglyMeasurable_fluct_vec hyp hμ he _ J)).prodMk
      (measurable_Ucentered hyp μm _).aestronglyMeasurable)
    ((hΨm.prodMk (continuous_pi fun n => continuous_apply _).aestronglyMeasurable).prodMk
      (aestronglyMeasurable_Uinf hQ))
    (fun k => ?_) (fun k => ?_) (B := Bq / K' ^ q) (fun k => ?_) (hint.div_const K')
    (phiG hK' g)
  · have eL : ∀ k, ∫ X, wK K' (Ucentered W μ (Ns k) X) *
        phiG hK' g ((f k X * Real.sqrt (rexp (-Ucentered W μ (Ns k) X) / K'),
          fun n => fluct e (Ns k) n X), Ucentered W μ (Ns k) X) ∂Measure.pi (fun _ : Fin (Ns k) => μm) =
        ∫ X, rexp (-Ucentered W μ (Ns k) X) / K' * g (f k X, fun n => fluct e (Ns k) n X)
          ∂Measure.pi (fun _ : Fin (Ns k) => μm) := fun k => by
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      simp only [phiG_apply]
      rw [show rexp (-Ucentered W μ (Ns k) X) / K' = wK K' (Ucentered W μ (Ns k) X) from rfl,
        div_sqrt_wK hK']
    exact key.congr eL
  · obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm (Ns k)
    exact integrable_of_bdd ((continuous_wK K').measurable.comp (measurable_Ucentered hyp μm _))
      (C := rexp BU / K') fun X => by
        rw [abs_of_pos (wK_pos hK' _)]
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by
          have := hBU X; rw [abs_le] at this; linarith)) hK'.le
  · obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm (Ns k)
    exact integrable_of_bdd (((continuous_wK K').measurable.comp
      (measurable_Ucentered hyp μm _)).pow_const q) (C := (rexp BU / K') ^ q) fun X => by
        rw [abs_of_nonneg (Real.rpow_nonneg (wK_pos hK' _).le _)]
        refine Real.rpow_le_rpow (wK_pos hK' _).le ?_ (by linarith)
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by
          have := hBU X; rw [abs_le] at this; linarith)) hK'.le
  · have : ∀ X, wK K' (Ucentered W μ (Ns k) X) ^ q = rexp (-Ucentered W μ (Ns k) X) ^ q / K' ^ q :=
      fun X => Real.div_rpow (Real.exp_pos _).le hK'.le q
    simp_rw [this]
    rw [integral_div]
    exact div_le_div_of_nonneg_right (hBq _ (hN1 k)) (Real.rpow_nonneg hK'.le q)

end SharpLSI
