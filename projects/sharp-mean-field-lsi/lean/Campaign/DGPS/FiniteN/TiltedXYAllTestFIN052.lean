import DGPS.FiniteN.TiltedXYPosteriorFIN050
import DGPS.FiniteN.Tools.EntropyDefects
import DGPS.FiniteN.Tools.Rothaus
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.Particle.Rates

/-!
# FIN052: all-test inverse-N LSI lower bound for the tilted XY model

For a particle model `A` whose entropy defect has the form
`Ent(f²) ≤ (2/(4π²)) E(f) + D N ∫ f²` and whose unrestricted physical Poincaré rate is at least
`λ0 > 0`, the all-test rate satisfies `r_N^all ≥ c/N` with `c > 0` independent of `N`.

Proof chain (per test `f ∈ H¹(P_N)` with `Ent(f²) > 0`, `m = ∫ f`, `V = Var(f)`):

* Rothaus centering: `Ent(f²) ≤ Ent((f-m)²) + 2 Var(f)`;
* the energy is invariant under the constant shift `f ↦ f - m`, so the defect applies to `f - m`,
  and `∫ (f-m)² = Var(f)`;
* the Poincaré bound `λ0 Var(f) ≤ E(f)` gives `Ent(f²) ≤ (2/(4π²) + (DN+2)/λ0) E(f)`;
* `2E/Ent ≥ c/N` with `c = 2 / (2/(4π²) + (D+2)/λ0)`, using `N ≥ 1`.

The tilted instance is `TiltedXY.Fin051.tiltedXYData (1/2) 4`, with the defect constant
`D = |1/2| + 5·4/2` from FIN017 (the proved constant; the blueprint's `κ + h` is not used).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN

open DGPS

/-- Generic core of FIN052: an entropy defect of the form `(2/(4π²)) E + D N ∫ f²` together with
an unrestricted Poincaré rate `λ0 > 0` gives `r_N^all ≥ c/N` with `c > 0` independent of `N`. -/
theorem core_all_test_lsi_lower_FIN052 {d : ℕ} (A : InteractionData d) (D lam0 : ℝ)
    (hD : 0 ≤ D) (hlam : 0 < lam0)
    (hdef : ∀ (N : ℕ+) (f : ParticleH1 A N),
      homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy A N f +
          D * (N : ℝ) * ∫ y, f.1 y ^ 2 ∂particleLaw A N))
    (hpoin : ∀ N : ℕ+, ENNReal.ofReal lam0 ≤ particlePoincareRate A N) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+, ENNReal.ofReal (c / (N : ℝ)) ≤ particleRateAll A N := by
  have hK0 : 0 < 2 / (4 * Real.pi ^ 2) := by positivity
  have hMpos : 0 < 2 / (4 * Real.pi ^ 2) + (D + 2) / lam0 :=
    add_pos hK0 (div_pos (by linarith) hlam)
  have hc : 0 < 2 / (2 / (4 * Real.pi ^ 2) + (D + 2) / lam0) := div_pos two_pos hMpos
  -- Poincare inequality in multiplied form, valid also when the variance vanishes.
  have hpoinc : ∀ (N : ℕ+) (f : ParticleH1 A N),
      lam0 * variance f.1 (particleLaw A N) ≤ particleEnergy A N f := by
    intro N f
    by_cases hV : 0 < variance f.1 (particleLaw A N)
    · exact (le_particlePoincareRate_iff_forall A N lam0).1 (hpoin N) f hV
    · have h0 : variance f.1 (particleLaw A N) = 0 :=
        le_antisymm (not_lt.1 hV) (variance_nonneg _ _)
      rw [h0, mul_zero]
      exact particleEnergy_nonneg f
  -- Entropy bound after centering and the shift-invariance of the energy.
  have key : ∀ (N : ℕ+) (f : ParticleH1 A N),
      homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy A N f +
          (D * (N : ℝ) + 2) * variance f.1 (particleLaw A N)) := by
    intro N f
    have : IsProbabilityMeasure (particleLaw A N) :=
      DGPS.Particle.particleLaw_isProbabilityMeasure' A N
    have hmem : MemLp f.1 2 (particleLaw A N) :=
      (isParticleWeakGradient_particleWeakGradient f).memLp
    let g : ParticleH1 A N :=
      ⟨fun x => 1 * f.1 x + -(∫ y, f.1 y ∂particleLaw A N),
        MemParticleH1.affine f.2 1 (-(∫ y, f.1 y ∂particleLaw A N))⟩
    have hE : particleEnergy A N g = particleEnergy A N f := by
      rw [particleEnergy_affine f g 1 (-(∫ y, f.1 y ∂particleLaw A N)) rfl]
      ring
    have hfun : (fun y => g.1 y ^ 2) =
        fun y => (f.1 y - ∫ z, f.1 z ∂particleLaw A N) ^ 2 := by
      funext y
      show (1 * f.1 y + -(∫ z, f.1 z ∂particleLaw A N)) ^ 2 =
        (f.1 y - ∫ z, f.1 z ∂particleLaw A N) ^ 2
      ring
    have hV : ∫ y, (f.1 y - ∫ z, f.1 z ∂particleLaw A N) ^ 2 ∂particleLaw A N =
        variance f.1 (particleLaw A N) := by
      rw [variance_eq_integral hmem.aestronglyMeasurable.aemeasurable]
    have hD' := hdef N g
    rw [hfun, hE, hV] at hD'
    have hR := (DGPS.FiniteN.Tools.Rothaus.rothaus_with_quantitative_tightening
      (P := particleLaw A N)).1 f.1 hmem
    have h2 : (2 : ℝ≥0∞) * evariance f.1 (particleLaw A N) =
        ENNReal.ofReal (2 * variance f.1 (particleLaw A N)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        hmem.ofReal_variance_eq]
    have hEn := particleEnergy_nonneg f
    have hVn := variance_nonneg f.1 (particleLaw A N)
    have hsum : ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy A N f +
          D * (N : ℝ) * variance f.1 (particleLaw A N)) + ENNReal.ofReal (2 * variance f.1 (particleLaw A N)) =
        ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy A N f +
          (D * (N : ℝ) + 2) * variance f.1 (particleLaw A N)) := by
      rw [← ENNReal.ofReal_add (add_nonneg (mul_nonneg hK0.le hEn)
          (mul_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) hVn))
        (mul_nonneg two_pos.le hVn)]
      congr 1
      ring
    calc homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2)
        ≤ homogeneousEntropy (particleLaw A N)
            (fun x => (f.1 x - ∫ y, f.1 y ∂particleLaw A N) ^ 2) + 2 * evariance f.1 (particleLaw A N) := hR
      _ ≤ ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy A N f +
            D * (N : ℝ) * variance f.1 (particleLaw A N)) +
          ENNReal.ofReal (2 * variance f.1 (particleLaw A N)) := by
        rw [← h2]
        exact add_le_add hD' le_rfl
      _ = _ := hsum
  -- Entropy bounded by a multiple of the energy, using the Poincare inequality.
  have hbound : ∀ (N : ℕ+) (f : ParticleH1 A N),
      homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal ((2 / (4 * Real.pi ^ 2) + (D * (N : ℝ) + 2) / lam0) *
          particleEnergy A N f) := by
    intro N f
    refine (key N f).trans (ENNReal.ofReal_le_ofReal ?_)
    have hVle : variance f.1 (particleLaw A N) ≤ particleEnergy A N f / lam0 :=
      (le_div_iff₀ hlam).2 (by rw [mul_comm]; exact hpoinc N f)
    have hcoef : 0 ≤ D * (N : ℝ) + 2 :=
      add_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) (by norm_num)
    have h1 := mul_le_mul_of_nonneg_left hVle hcoef
    have e : (2 / (4 * Real.pi ^ 2) + (D * (N : ℝ) + 2) / lam0) * particleEnergy A N f =
        2 / (4 * Real.pi ^ 2) * particleEnergy A N f +
          (D * (N : ℝ) + 2) * (particleEnergy A N f / lam0) := by
      ring
    rw [e]
    linarith
  -- The constant.
  refine ⟨2 / (2 / (4 * Real.pi ^ 2) + (D + 2) / lam0), hc, fun N => ?_⟩
  unfold particleRateAll
  refine le_iInf fun g => ?_
  have hg : 0 < particleEntropy A N g.1 := g.2
  have hle : particleEntropy A N g.1 ≤
      ENNReal.ofReal ((2 / (4 * Real.pi ^ 2) + (D * (N : ℝ) + 2) / lam0) *
        particleEnergy A N g.1) := hbound N g.1
  have hne : particleEntropy A N g.1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  change ENNReal.ofReal (2 / (2 / (4 * Real.pi ^ 2) + (D + 2) / lam0) / (N : ℝ)) ≤
    ENNReal.ofReal (2 * particleEnergy A N g.1) / particleEntropy A N g.1
  rw [ENNReal.le_div_iff_mul_le (Or.inl hg.ne') (Or.inl hne)]
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hN1 : (1 : ℕ) ≤ (N : ℕ) := N.pos
    exact_mod_cast hN1
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  set K0 : ℝ := 2 / (4 * Real.pi ^ 2) with hK0def
  set M : ℝ := K0 + (D + 2) / lam0 with hMdef
  set n : ℝ := (N : ℝ) with hndef
  set E : ℝ := particleEnergy A N g.1 with hEdef
  have hEn : 0 ≤ E := particleEnergy_nonneg g.1
  have ht : 0 ≤ 1 / lam0 := (one_div_pos.2 hlam).le
  have hKM : K0 + (D * n + 2) / lam0 ≤ n * M := by
    have e1 : (D * n + 2) / lam0 = (D * n + 2) * (1 / lam0) := by ring
    have e2 : (D + 2) / lam0 = (D + 2) * (1 / lam0) := by ring
    rw [e1, hMdef, e2]
    nlinarith [mul_nonneg (sub_nonneg.2 hn1) hK0.le, mul_nonneg (sub_nonneg.2 hn1) ht]
  have hcM : (2 / M) * M = 2 := div_mul_cancel₀ 2 hMpos.ne'
  have hK2 : (2 / M) / n * (K0 + (D * n + 2) / lam0) ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    calc (2 / M) * (K0 + (D * n + 2) / lam0)
        ≤ (2 / M) * (n * M) := mul_le_mul_of_nonneg_left hKM hc.le
      _ = 2 * n := by linear_combination n * hcM
  calc ENNReal.ofReal ((2 / M) / n) * particleEntropy A N g.1
      ≤ ENNReal.ofReal ((2 / M) / n) *
          ENNReal.ofReal ((K0 + (D * n + 2) / lam0) * E) :=
        by gcongr
    _ = ENNReal.ofReal ((2 / M) / n * ((K0 + (D * n + 2) / lam0) * E)) :=
        (ENNReal.ofReal_mul (div_nonneg hc.le hn0.le)).symm
    _ ≤ ENNReal.ofReal (2 * E) := by
        apply ENNReal.ofReal_le_ofReal
        have : (2 / M) / n * ((K0 + (D * n + 2) / lam0) * E) =
            ((2 / M) / n * (K0 + (D * n + 2) / lam0)) * E := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hK2 hEn

/-- **FIN052.** For the fixed attractive tilted XY model `tiltedXYData (1/2) 4` (FIN050, FIN017):
the all-test particle rate satisfies `r_N^all ≥ c/N` for a constant `c > 0` independent of `N`,
on the full particle Sobolev domain `H¹(P_N)`. The second conjunct identifies this domain with the
Haar-Sobolev class (FIN026). -/
theorem tilted_all_test_inverse_n_lsi_lower :
    (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c / (N : ℝ)) ≤
        particleRateAll (DGPS.FiniteN.TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N) ∧
    ∀ (N : ℕ+) (f : ParticleSpace 1 N → ℝ),
      MemParticleH1 (DGPS.FiniteN.TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N f ↔
        MemParticleHaarH1 N f := by
  obtain ⟨lam0, hlam, hpoin⟩ :=
    (DGPS.FiniteN.posterior_averaged_conditional_constants_and_uniform_pi).2
  refine ⟨?_, fun N f => (DGPS.FiniteN.fixed_n_weighted_sobolev_extension
    (DGPS.FiniteN.TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).1 f⟩
  exact core_all_test_lsi_lower_FIN052 (DGPS.FiniteN.TiltedXY.Fin051.tiltedXYData (1 / 2) 4)
    (|(1 / 2 : ℝ)| + 5 * 4 / 2) lam0 (by positivity) hlam
    (fun N f => (DGPS.FiniteN.explicit_particle_entropy_defects).2.1 (1 / 2) 4 (by norm_num) N f)
    hpoin

end DGPS.FiniteN
