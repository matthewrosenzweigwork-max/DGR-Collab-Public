import DGPS.Lipschitz.T01PositiveBoundedComparison
import DGPS.Lipschitz.T01UniformParticleDefective
import DGPS.Lipschitz.T01ParticlePoincare
import DGPS.Lipschitz.T01ParticleTightening
import DGPS.Particle.RateEquivalences

/-! The actual unrestricted lower limit on the full canonical Sobolev domain. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

set_option backward.isDefEq.respectTransparency.types false in
/-- Every positive species subrate is eventually an unrestricted particle LSI rate. The
comparison, defective inequality, Poincare inequality and tightening are actual providers. -/
theorem t01_eventual_unrestricted_lsi {d : ℕ} (J : InteractionData d) (hJ : LipschitzData J)
    (hd : 0 < d) (drift : AbsoluteDrift J) (hrate : 0 < scalarRate J drift)
    {r : ℝ} (hr : 0 < r) (hrs : ENNReal.ofReal r < speciesRate J drift) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N,
      particleEntropy J N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy J N f) := by
  obtain ⟨a, ha, hsa, hcomp⟩ := t01_positive_rate_unrestricted_bounded_comparison J hJ hd drift hrate
  have hsfin : speciesRate J drift ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsa
  have hrs' : r < (speciesRate J drift).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr.le hsfin).mp hrs
  let R := (r + (speciesRate J drift).toReal) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  have hRs : R < (speciesRate J drift).toReal := by dsimp [R]; linarith
  have hRrate : ENNReal.ofReal R < speciesRate J drift :=
    (ENNReal.ofReal_lt_iff_lt_toReal hR.le hsfin).mpr hRs
  have hsa' : (speciesRate J drift).toReal ≤ a := by
    simpa only [ENNReal.toReal_ofReal ha.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hsa
  have hRa : R ≤ a := hRs.le.trans hsa'
  obtain ⟨C, hC0, hdef⟩ := t01_uniform_particle_defective J hJ hd drift hrate hR hRrate
  have hdefReal : ∀ N : ℕ+, ∀ f : ParticleH1 J N,
      particleEntropy J N f ≤ ENNReal.ofReal
        (2 * particleEnergy J N f / R + C * ∫ X, f X ^ 2 ∂particleLaw J N) := by
    intro N f
    have hmass : (∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw J N) =
        ENNReal.ofReal (∫ X, f X ^ 2 ∂particleLaw J N) :=
      (ofReal_integral_eq_lintegral_ofReal
        (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
        (Eventually.of_forall fun X => sq_nonneg _)).symm
    have h := hdef N f
    rw [hmass, ← ENNReal.ofReal_mul hC0,
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) (particleEnergy_nonneg f))
        (mul_nonneg hC0 (integral_nonneg fun X => sq_nonneg _))] at h
    convert h using 1 <;> congr 1 <;> ring
  have hpoin : ∀ ρ : ℝ, ρ < R → ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N,
      ρ * ((∫ X, f X ^ 2 ∂particleLaw J N) - (∫ X, f X ∂particleLaw J N) ^ 2) ≤
        particleEnergy J N f := by
    intro ρ hρ
    apply eventual_particle_poincare_of_bounded_comparison J ha hcomp
    · exact ⟨2 / R, C, fun N f => (hdefReal N f).trans_eq (by congr 1; ring)⟩
    · exact hρ.trans_le hRa
  exact eventual_particle_lsi_after_concrete_tightening J hR 1 C
    (fun N _ f => hdefReal N f) ⟨a, hRa, hcomp⟩ hpoin hr hrR

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual unrestricted particle rates have lower limit at least the species rate. -/
theorem t01_unrestricted_species_liminf_lower {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (hd : 0 < d) (drift : AbsoluteDrift J)
    (hrate : 0 < scalarRate J drift) :
    speciesRate J drift ≤ liminf (fun N : ℕ+ => particleRateAll J N) atTop := by
  apply (Filter.le_liminf_iff').2
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    exact Eventually.of_forall fun N => bot_le
  have hyfin : y ≠ ⊤ := ne_top_of_lt hy
  have hyr : 0 < y.toReal := ENNReal.toReal_pos hy0 hyfin
  have hys : ENNReal.ofReal y.toReal < speciesRate J drift := by
    simpa only [ENNReal.ofReal_toReal hyfin] using hy
  filter_upwards [t01_eventual_unrestricted_lsi J hJ hd drift hrate hyr hys] with N hN
  have hLSI : ∀ f : ParticleH1 J N,
      particleEntropy J N f ≤ ENNReal.ofReal (2 * particleEnergy J N f / y.toReal) := by
    intro f
    convert hN f using 1 <;> congr 1 <;> ring
  simpa only [ENNReal.ofReal_toReal hyfin] using (particleRate_iff_lsi J N hyr).mp hLSI

/-- The zero scalar-rate case is immediate from species inclusion, so no positive-rate
assumption is needed for the unrestricted lower-limit conclusion. -/
theorem t01_unrestricted_species_liminf_lower_all_rates {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (hd : 0 < d) (drift : AbsoluteDrift J) :
    speciesRate J drift ≤ liminf (fun N : ℕ+ => particleRateAll J N) atTop := by
  by_cases hrate : 0 < scalarRate J drift
  · exact t01_unrestricted_species_liminf_lower J hJ hd drift hrate
  · exact ((speciesRate_le_scalarRate J drift).trans (not_lt.mp hrate)).trans bot_le

end DGPS.Lipschitz
