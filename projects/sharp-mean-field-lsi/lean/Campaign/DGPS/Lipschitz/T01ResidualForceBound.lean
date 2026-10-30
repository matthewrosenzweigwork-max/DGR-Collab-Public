import DGPS.Lipschitz.T01ResidualForce

/-! Boundedness retained for extracting particle thresholds from the real force limsup. -/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology KernelApproximation CenteredForceMoment
  CenteredForceExponential CenteredKernelMoments
open scoped ENNReal NNReal

/-- The changed-measure estimate also retains the boundedness needed for real limsup use. -/
private theorem t01_changed_measure_bound_and_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : ℕ → (N : ℕ) → (Fin N → Ω) → ℝ)
    (hFm : ∀ R N, Measurable (F R N)) (hF0 : ∀ R N x, 0 ≤ F R N x)
    {α K : ℝ} (hα : 0 < α) (hK0 : 0 ≤ K)
    (hK : ∀ R N, 1 ≤ N → ∫⁻ x, ENNReal.ofReal (Real.exp (α * F R N x))
      ∂(Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal K)
    {L : ℕ → ℝ} (hL : Tendsto L atTop (𝓝 0))
    (hlim : ∀ R, Tendsto (fun N : ℕ => ∫ x, F R N x ∂(Measure.pi fun _ : Fin N => μ)) atTop
      (𝓝 (L R)))
    (P : (N : ℕ) → Measure (Fin N → Ω)) (hP : ∀ N, 1 ≤ N → IsProbabilityMeasure (P N))
    (hPQ : ∀ N, 1 ≤ N → P N ≪ Measure.pi fun _ : Fin N => μ) {p : ℝ≥0∞} (hp : 1 < p)
    {Cp : ℝ≥0}
    (hCp : ∀ N, 1 ≤ N → eLpNorm (fun x => ((P N).rnDeriv
      (Measure.pi fun _ : Fin N => μ) x).toReal) p (Measure.pi fun _ : Fin N => μ) ≤ Cp) :
    (∀ R, IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => ∫ x, F R N x ∂P N)) ∧
    Tendsto (fun R => limsup (fun N : ℕ => ∫ x, F R N x ∂P N) atTop) atTop (𝓝 0) := by
  obtain ⟨mm, hmm, hmp⟩ := exists_nat_exponent hp
  let r : ℝ := 1 / (2 * ((mm : ℝ) + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  let Ccst : ℝ := ((Cp : ℝ) ^ (((mm : ℝ) + 1) / mm)) ^ ((mm : ℝ) / ((mm : ℝ) + 1)) *
    ((((2 * mm + 1).factorial : ℝ) / α ^ (2 * mm + 1) * K) ^ r)
  have hbound : ∀ R N, 1 ≤ N → ∫ x, F R N x ∂P N ≤
      Ccst * (∫ x, F R N x ∂(Measure.pi fun _ : Fin N => μ)) ^ r := by
    intro R N hN
    letI := hP N hN
    exact changed_measure_bound (hPQ N hN) (hFm R N) (hF0 R N) hmm
      (Real.rpow_nonneg Cp.coe_nonneg _) (rnDeriv_lintegral_le hmm hmp (hCp N hN))
      hα hK0 (hK R N hN)
  have hlimv : ∀ R, Tendsto
      (fun N : ℕ => Ccst * (∫ x, F R N x ∂(Measure.pi fun _ : Fin N => μ)) ^ r)
      atTop (𝓝 (Ccst * L R ^ r)) := fun R =>
    ((hlim R).rpow_const (Or.inr hr.le)).const_mul Ccst
  refine ⟨fun R => (hlimv R).isBoundedUnder_le.mono_le
    ((eventually_ge_atTop 1).mono fun N hN => hbound R N hN), ?_⟩
  exact limsup_changed_measure F hFm hF0 hα hK0 hK hL hlim P hP hPQ hp hCp

/-- Actual residual forces vanish after the particle limit under a uniform density moment. -/
theorem t01_residualForce_changed_measure_tendsto_with_bounds {d : ℕ}
    (S : Spec d) (aux : Aux S) (D : KData d)
    (hsym : ∀ x y, D.K x y = D.K y x) (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0)
    (gδ : Torus d → Tangent d) (hδm : Measurable gδ)
    {Mδ : ℝ} (hδb : ∀ x, ‖gδ x‖ ≤ Mδ)
    (hδ : IsWeakGradient (fun x => D.K x x) gδ)
    (t : ℕ → ℝ) (m : ℕ → ℕ) {C : ℝ}
    (h1 : ∀ R x y, ‖smoothG1 S aux D (t R) (m R) x y‖ ≤ C)
    (h2 : ∀ R x y, ‖smoothG2 S aux D (t R) (m R) x y‖ ≤ C)
    (hG1 : Tendsto (fun R => ∫ p,
      ‖D.G1 p.1 p.2 - smoothG1 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
      atTop (𝓝 0))
    (P : (N : ℕ) → Measure (Fin N → Torus d))
    (hP : ∀ N, 1 ≤ N → IsProbabilityMeasure (P N))
    (hPQ : ∀ N, 1 ≤ N → P N ≪ Measure.pi fun _ : Fin N => S.mu)
    {p : ℝ≥0∞} (hp : 1 < p) {Cp : ℝ≥0}
    (hCp : ∀ N, 1 ≤ N → eLpNorm (fun x => ((P N).rnDeriv
      (Measure.pi fun _ : Fin N => S.mu) x).toReal) p
      (Measure.pi fun _ : Fin N => S.mu) ≤ Cp) :
    (∀ R (N : ℕ+), IsParticleHaarWeakGradient N
      (fun x : ParticleSpace d N => ((2 : ℝ) * (N : ℝ))⁻¹ * ∑ i, ∑ j,
        (D.K (x i) (x j) - smoothK S D (t R) (m R) (x i) (x j)))
      (t01ResidualForce S aux D gδ t m R N)) ∧
    (∀ R, IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => ∫ x,
      ∑ i, ‖t01ResidualForce S aux D gδ t m R N x i‖ ^ 2 ∂P N)) ∧
    Tendsto (fun R => limsup (fun N : ℕ => ∫ x,
      ∑ i, ‖t01ResidualForce S aux D gδ t m R N x i‖ ^ 2 ∂P N) atTop)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hdiag : Measurable fun x : Torus d => (x, x) := measurable_id.prodMk measurable_id
  have hG1m : ∀ R, Measurable (Function.uncurry (smoothG1 S aux D (t R) (m R))) := fun R => by
    rw [smoothG1_eq]; exact G1fin_meas S aux D (t R) (m R + 1)
  have hG2m : ∀ R, Measurable (Function.uncurry (smoothG2 S aux D (t R) (m R))) := fun R => by
    rw [smoothG2_eq]; exact G2fin_meas S aux D (t R) (m R + 1)
  have hBm : ∀ R, Measurable (Function.uncurry fun x y =>
      D.G1 x y - smoothG1 S aux D (t R) (m R) x y) := fun R => D.G1m.sub (hG1m R)
  have hgm : ∀ R, Measurable fun x => gδ x - (smoothG1 S aux D (t R) (m R) x x +
      smoothG2 S aux D (t R) (m R) x x) := fun R =>
    hδm.sub (((hG1m R).comp hdiag).add ((hG2m R).comp hdiag))
  have hBb : ∀ R x y, ‖D.G1 x y - smoothG1 S aux D (t R) (m R) x y‖ ≤ D.B + C := fun R x y =>
    (norm_sub_le _ _).trans (add_le_add (D.G1b x y) (h1 R x y))
  have hgb : ∀ R x, ‖gδ x - (smoothG1 S aux D (t R) (m R) x x +
      smoothG2 S aux D (t R) (m R) x x)‖ ≤ Mδ + (C + C) := fun R x =>
    (norm_sub_le _ _).trans (add_le_add (hδb x)
      ((norm_add_le _ _).trans (add_le_add (h1 R x x) (h2 R x x))))
  have hsymR : ∀ R x y, D.K x y - smoothK S D (t R) (m R) x y =
      D.K y x - smoothK S D (t R) (m R) y x := fun R x y => by
    rw [hsym x y, smoothK_symm S D hsym _ _ x y]
  have hFc : ∀ R, Continuous (Function.uncurry fun x y =>
      D.K x y - smoothK S D (t R) (m R) x y) := fun R =>
    D.Kc.sub (smoothK_continuous S D _ _)
  have hwR : ∀ R y, IsWeakGradient (fun x => D.K x y - smoothK S D (t R) (m R) x y)
      (fun x => D.G1 x y - smoothG1 S aux D (t R) (m R) x y) := fun R y => by
    refine wg_sub (D.g1 y) ?_
    simpa only [smoothK_eq, smoothG1_eq] using Kfin_wg1 S aux D (t R) (m R + 1) y
  have hδR : ∀ R, IsWeakGradient (fun x => D.K x x - smoothK S D (t R) (m R) x x)
      (fun x => gδ x - (smoothG1 S aux D (t R) (m R) x x +
        smoothG2 S aux D (t R) (m R) x x)) := fun R =>
    wg_sub hδ (smoothK_diag_wg S aux D _ _)
  have h0R : ∀ R x, ∫ y, (D.K x y - smoothK S D (t R) (m R) x y) ∂S.mu = 0 := fun R x => by
    have hi1 : Integrable (fun y => D.K x y) S.mu :=
      S.int_cont (D.Kc.comp (continuous_const.prodMk continuous_id))
    have hi2 : Integrable (fun y => smoothK S D (t R) (m R) x y) S.mu :=
      S.int_cont ((smoothK_continuous S D (t R) (m R)).comp
        (continuous_const.prodMk continuous_id))
    rw [integral_sub hi1 hi2]
    have e1 : ∫ y, D.K x y ∂S.mu = 0 := by simp_rw [hsym x]; exact hc x
    have e2 : ∫ y, smoothK S D (t R) (m R) x y ∂S.mu = 0 := by
      simp_rw [smoothK_symm S D hsym _ _ x]
      exact smoothK_centered S D aux.v0 hc _ _ x
    rw [e1, e2, sub_zero]
  have key := fun R => force_package_centered (fun _ h => S.ae_mu h) (hsymR R) (hFc R) (hBm R)
    (hBb R) (hgm R) (hgb R) (hwR R) (hδR R) (h0R R)
  refine ⟨fun R N => (key R).1.1 N, ?_⟩
  let α : ℝ := (8 * (d : ℝ) * (1 + (D.B + C) ^ 2 + (Mδ + (C + C)) ^ 2))⁻¹
  have hα : 0 < α := by
    have hd : (0 : ℝ) < d := by exact_mod_cast aux.hd
    dsimp only [α]
    positivity
  have hM : 0 ≤ D.B + C :=
    (norm_nonneg _).trans (hBb 0 0 0)
  have hK : (0 : ℝ) ≤ 2 * Real.exp (1 / 16) := by positivity
  apply t01_changed_measure_bound_and_limit
    (fun R N x => ∑ i, ‖t01ResidualForce S aux D gδ t m R N x i‖ ^ 2)
    (fun R N => measurable_force_sq (hBm R) (hgm R) N)
    (fun R N x => Finset.sum_nonneg fun i _ => sq_nonneg _) hα hK
    (fun R N hN => ?_) hG1 (fun R => tendsto_of_identity (key R).1.2) P hP hPQ hp hCp
  exact (exp_moment_core aux.hd (hBm R) (hgm R) hM (hBb R) (hgb R) (key R).2 rfl hN).trans
    (le_of_eq (ENNReal.ofReal_mul (by norm_num)).symm)


end DGPS.Lipschitz
