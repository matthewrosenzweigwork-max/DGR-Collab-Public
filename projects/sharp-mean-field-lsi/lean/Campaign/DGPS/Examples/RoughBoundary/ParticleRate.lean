import DGPS.Examples.RoughBoundary.Particle
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.Foundations.NormalizationChecks
import DGPS.Analysis.BoundedPerturbation
import DGPS.Analysis.CircleLSI

/-!
# Every fixed particle rate of the rough model is positive and finite (RUF038)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 6, (6.3)-(6.5).  For the model data
`(0, W_{L,ε})` and every `N ≥ 1`:
`a0 exp(-11N/12) ≤ r_N^all ≤ r_N^sym < ∞`, and at `N = 1` both rates equal `a0`.

The lower bound is the Haar LSI on `𝕋^N` (DEF024, sharp rate `a0 = 4π²`) transferred to the Gibbs
law `P_N = Z⁻¹ exp(B_N) m^N` through the two-sided density bounds
`Z⁻¹ exp(inf B_N) ≤ dP_N/dm^N ≤ Z⁻¹ exp(sup B_N)`: the partition function cancels, so the loss is
the single factor `exp(-osc B_N)` (DEF025 pattern), and `osc B_N ≤ 11N/12` by RUF037.
-/

open MeasureTheory Set
open scoped ENNReal Real

namespace DGPS.Examples.RoughBoundary.Particle

open DGPS DGPS.FiniteN.PositiveRate
open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.Model

/-! ### Rates depend on the interaction only through the Gibbs law -/

lemma rate_congr_of_law_eq {d : ℕ} {A B : InteractionData d} {N : ℕ+}
    (h : particleLaw A N = particleLaw B N) :
    particleRateAll A N = particleRateAll B N ∧ particleRateSym A N = particleRateSym B N := by
  have hmem : ∀ f, MemParticleH1 A N f ↔ MemParticleH1 B N f := fun f => by
    rw [memParticleH1_iff, memParticleH1_iff]
  let e : ParticleH1 A N ≃ ParticleH1 B N :=
    { toFun := fun f => ⟨f.1, (hmem _).1 f.2⟩
      invFun := fun f => ⟨f.1, (hmem _).2 f.2⟩
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  have hent : ∀ f : ParticleH1 A N, particleEntropy A N f = particleEntropy B N (e f) := fun f => by
    unfold particleEntropy
    rw [h]
    rfl
  have hen : ∀ f : ParticleH1 A N, particleEnergy A N f = particleEnergy B N (e f) := fun f => by
    have hgA := isParticleWeakGradient_particleWeakGradient f
    have hgB : IsParticleWeakGradient B N (e f).1 (particleWeakGradient f) :=
      (isParticleWeakGradient_iff B N _ _).2 ((isParticleWeakGradient_iff A N _ _).1 hgA)
    rw [particleEnergy_eq_of_isParticleWeakGradient f hgA,
      particleEnergy_eq_of_isParticleWeakGradient (e f) hgB, h]
  have hq : ∀ f : ParticleH1 A N, particleQuotient A N f = particleQuotient B N (e f) :=
    fun f => by
      unfold particleQuotient
      rw [← hent f, ← hen f]
  have hs : ∀ f : ParticleH1 A N, IsSymmetricParticleTest f ↔ IsSymmetricParticleTest (e f) :=
    fun f => by
      unfold IsSymmetricParticleTest IsSymmetricParticleFun
      rw [h]
      rfl
  refine ⟨?_, ?_⟩
  · unfold particleRateAll
    exact Equiv.iInf_congr (e.subtypeEquiv fun f => by rw [hent f]) (fun f => (hq f.1).symm)
  · unfold particleRateSym
    let eS : SymmetricParticleH1 A N ≃ SymmetricParticleH1 B N := e.subtypeEquiv hs
    exact Equiv.iInf_congr (eS.subtypeEquiv fun f => by
      show 0 < particleEntropy A N f.1 ↔ 0 < particleEntropy B N (e f.1)
      rw [hent f.1]) (fun f => (hq f.1.1).symm)

/-! ### Transfer of the Haar LSI under explicit two-sided density bounds -/

lemma rateAll_ge_of_density_bounds {d : ℕ} (A : InteractionData d) (N : ℕ+) {c C : ℝ}
    (hc : 0 < c) (hb : ∀ x, c ≤ particleDensity A N x ∧ particleDensity A N x ≤ C) :
    ENNReal.ofReal (a0 * c / C) ≤ particleRateAll A N := by
  have hC : 0 < C := lt_of_lt_of_le hc ((hb (Classical.arbitrary _)).1.trans
    (hb (Classical.arbitrary _)).2)
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  have ha0 : a0 = 4 * Real.pi ^ 2 := rfl
  rw [ha0, ← particleRate_iff_lsi A N (by positivity)]
  intro f
  have hgP := isParticleWeakGradient_particleWeakGradient f
  have hg := (isParticleWeakGradient_iff A N _ _).1 hgP
  set g := particleWeakGradient f with hgdef
  have hPprob := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have h1 : particleLaw A N ≤ ENNReal.ofReal C • particleHaar d N :=
    particleLaw_le_smul A N fun x => (hb x).2
  have h2 : particleHaar d N ≤ ENNReal.ofReal c⁻¹ • particleLaw A N :=
    particleHaar_le_smul A N hc fun x => (hb x).1
  have hE : ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x)) ∂particleLaw A N =
      ENNReal.ofReal (particleEnergy A N f) := by
    unfold particleEnergy
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_particleTangentNormSq hgP.memLp_grad)
      (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc particleEntropy A N f
      = homogeneousEntropy (particleLaw A N) (fun x => f x ^ 2) := rfl
    _ ≤ ENNReal.ofReal C * homogeneousEntropy (particleHaar d N) (fun x => f x ^ 2) :=
        entropy_le_of_measure_le_smul h1 (fun x => sq_nonneg _) hg.memLp.integrable_sq
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x)) ∂particleHaar d N) :=
        by gcongr; exact particleHaar_lsi hg
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x))
            ∂(ENNReal.ofReal c⁻¹ • particleLaw A N)) :=
        by gcongr
    _ = ENNReal.ofReal (2 * particleEnergy A N f / (4 * Real.pi ^ 2 * c / C)) := by
        rw [lintegral_smul_measure, smul_eq_mul, hE, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-! ### The rough model -/

lemma roughB_continuous {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) :
    Continuous (roughB L ε N) := by
  have : roughB L ε N = fun x => kappa * (N : ℝ) / 2 - particleHamiltonian (modelData hL ε) N x := by
    funext x
    rw [hamiltonian_eq hL ε N x]
    ring
  rw [this]
  exact continuous_const.sub (DGPS.Particle.particleHamiltonian_continuous _ N)

lemma roughB_bddAbove (L ε : ℝ) (N : ℕ+) : BddAbove (Set.range (roughB L ε N)) :=
  ⟨11 * (N : ℝ) / 12, by rintro _ ⟨x, rfl⟩; exact roughB_le L ε N x⟩

lemma roughB_bddBelow (L ε : ℝ) (N : ℕ+) : BddBelow (Set.range (roughB L ε N)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact roughB_nonneg L ε N x⟩

/-- The oscillation `osc B_N = sup B_N - inf B_N`. -/
noncomputable def roughOsc (L ε : ℝ) (N : ℕ+) : ℝ :=
  sSup (Set.range (roughB L ε N)) - sInf (Set.range (roughB L ε N))

lemma roughOsc_le (L ε : ℝ) (N : ℕ+) : roughOsc L ε N ≤ 11 * (N : ℝ) / 12 := by
  obtain ⟨x0⟩ : Nonempty (ParticleSpace 1 N) := inferInstance
  have h1 : sSup (Set.range (roughB L ε N)) ≤ 11 * (N : ℝ) / 12 :=
    csSup_le ⟨_, x0, rfl⟩ (by rintro _ ⟨x, rfl⟩; exact roughB_le L ε N x)
  have h2 : 0 ≤ sInf (Set.range (roughB L ε N)) :=
    le_csInf ⟨_, x0, rfl⟩ (by rintro _ ⟨x, rfl⟩; exact roughB_nonneg L ε N x)
  unfold roughOsc
  linarith

lemma roughOsc_nonneg (L ε : ℝ) (N : ℕ+) : 0 ≤ roughOsc L ε N := by
  obtain ⟨x0⟩ : Nonempty (ParticleSpace 1 N) := inferInstance
  unfold roughOsc
  have := csInf_le (roughB_bddBelow L ε N) ⟨x0, rfl⟩
  have := le_csSup (roughB_bddAbove L ε N) ⟨x0, rfl⟩
  linarith

lemma roughOsc_one (L ε : ℝ) : roughOsc L ε 1 ≤ 0 := by
  obtain ⟨x0⟩ : Nonempty (ParticleSpace 1 1) := inferInstance
  have h1 : sSup (Set.range (roughB L ε 1)) ≤ kappa / 2 :=
    csSup_le ⟨_, x0, rfl⟩ (by rintro _ ⟨x, rfl⟩; exact (roughB_one L ε x).le)
  have h2 : kappa / 2 ≤ sInf (Set.range (roughB L ε 1)) :=
    le_csInf ⟨_, x0, rfl⟩ (by rintro _ ⟨x, rfl⟩; exact (roughB_one L ε x).ge)
  unfold roughOsc
  linarith

/-- The Haar LSI transferred to the rough Gibbs law, with the single oscillation factor
`exp(-osc B_N)`. -/
lemma rateAll_ge_oscillation {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) :
    ENNReal.ofReal (a0 * Real.exp (-roughOsc L ε N)) ≤ particleRateAll (modelData hL ε) N := by
  set Z : ℝ := ∫ y, Real.exp (roughB L ε N y) ∂particleHaar 1 N with hZdef
  have hcont : Continuous fun y => Real.exp (roughB L ε N y) :=
    Real.continuous_exp.comp (roughB_continuous hL ε N)
  have hint : Integrable (fun y => Real.exp (roughB L ε N y)) (particleHaar 1 N) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ1 : 1 ≤ Z := by
    have : ∫ _y, (1 : ℝ) ∂particleHaar 1 N ≤ Z :=
      integral_mono (integrable_const _) hint fun y => by
        simpa using Real.exp_le_exp.2 (roughB_nonneg L ε N y)
    simpa using this
  have hZ : 0 < Z := lt_of_lt_of_le one_pos hZ1
  set m := sInf (Set.range (roughB L ε N)) with hm
  set S := sSup (Set.range (roughB L ε N)) with hS
  have hb : ∀ x, Z⁻¹ * Real.exp m ≤ particleDensity (modelData hL ε) N x ∧
      particleDensity (modelData hL ε) N x ≤ Z⁻¹ * Real.exp S := fun x => by
    rw [density_eq hL ε N x]
    have hZi : 0 < Z⁻¹ := inv_pos.2 hZ
    exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (csInf_le (roughB_bddBelow L ε N) ⟨x, rfl⟩))
        hZi.le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_csSup (roughB_bddAbove L ε N) ⟨x, rfl⟩))
        hZi.le⟩
  have key := rateAll_ge_of_density_bounds (modelData hL ε) N
    (mul_pos (inv_pos.2 hZ) (Real.exp_pos m)) hb
  have heq : a0 * (Z⁻¹ * Real.exp m) / (Z⁻¹ * Real.exp S) = a0 * Real.exp (-roughOsc L ε N) := by
    unfold roughOsc
    rw [← hm, ← hS, neg_sub, Real.exp_sub]
    field_simp
  rwa [heq] at key

/-- RUF038: for every `N ≥ 1`, `a0 exp(-11N/12) ≤ r_N^all ≤ r_N^sym < ∞`; at `N = 1` both rates
equal `a0`.  The comparison uses the single oscillation factor `exp(-osc B_N)`, and
`osc B_N = 11N/12` for `N ≥ 2`. -/
theorem every_fixed_particle_rate_is_positive_and_finite {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) :
    ENNReal.ofReal (a0 * Real.exp (-(sSup (Set.range (roughB L ε N)) -
        sInf (Set.range (roughB L ε N))))) ≤ particleRateAll (modelData hL ε) N ∧
    ((2 : ℕ) ≤ (N : ℕ) → sSup (Set.range (roughB L ε N)) - sInf (Set.range (roughB L ε N)) =
        11 * (N : ℝ) / 12) ∧
    ENNReal.ofReal (a0 * Real.exp (-(11 * (N : ℝ) / 12))) ≤ particleRateAll (modelData hL ε) N ∧
    0 < ENNReal.ofReal (a0 * Real.exp (-(11 * (N : ℝ) / 12))) ∧
    particleRateAll (modelData hL ε) N ≤ particleRateSym (modelData hL ε) N ∧
    particleRateSym (modelData hL ε) N < ⊤ ∧
    ((N : ℕ) = 1 → particleRateAll (modelData hL ε) N = ENNReal.ofReal a0 ∧
      particleRateSym (modelData hL ε) N = ENNReal.ofReal a0) := by
  have hosc := rateAll_ge_oscillation hL ε N
  have hle : ENNReal.ofReal (a0 * Real.exp (-(11 * (N : ℝ) / 12))) ≤
      ENNReal.ofReal (a0 * Real.exp (-roughOsc L ε N)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by linarith [roughOsc_le L ε N])) a0_pos.le)
  refine ⟨hosc, fun hN => ?_, hle.trans hosc,
    ENNReal.ofReal_pos.2 (mul_pos a0_pos (Real.exp_pos _)), particleRateAll_le_sym _ N,
    (FiniteN.rates_pos_lt_top (modelData hL ε) N one_pos).2.1.2, fun hN => ?_⟩
  · obtain ⟨-, -, hsub⟩ := (rough_particle_hamiltonian_and_oscillation hL ε N).2.2.2.2.1 hN
    exact hsub
  · obtain rfl : N = 1 := PNat.coe_eq_one_iff.mp hN
    have hlaw : particleLaw (modelData hL ε) 1 = particleLaw (InteractionData.zero 1) 1 := by
      rw [particleLaw_one hL ε, DGPS.Particle.particleLaw_zero]
    obtain ⟨h1, h2⟩ := rate_congr_of_law_eq hlaw
    obtain ⟨-, h3, h4⟩ := circle_free_rates (AbsoluteDrift.zero 1)
    exact ⟨h1.trans h3, h2.trans h4⟩

end DGPS.Examples.RoughBoundary.Particle
