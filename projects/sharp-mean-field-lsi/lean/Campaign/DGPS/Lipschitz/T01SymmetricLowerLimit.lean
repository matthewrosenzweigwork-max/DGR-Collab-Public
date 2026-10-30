import DGPS.Lipschitz.T01SymmetricBoundedComparison
import DGPS.Lipschitz.T01UniformParticleDefective
import DGPS.Lipschitz.T01SymmetricPoincare
import DGPS.Lipschitz.T01ParticleTightening
import DGPS.Particle.RateEquivalences

/-! The symmetric scalar lower limit on the full canonical a.e. symmetric Sobolev domain. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

set_option backward.isDefEq.respectTransparency.types false in
/-- Every positive scalar subrate is eventually a symmetric particle LSI rate. The
comparison, defective inequality, Poincare inequality and tightening are actual providers. -/
theorem t01_eventual_symmetric_lsi {d : ℕ} (J : InteractionData d) (hJ : LipschitzData J)
    (hd : 0 < d) (drift : AbsoluteDrift J) (hrate : 0 < scalarRate J drift)
    {r : ℝ} (hr : 0 < r) (hrs : ENNReal.ofReal r < scalarRate J drift) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N, IsSymmetricParticleTest f →
      particleEntropy J N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy J N f) := by
  obtain ⟨a, ha, hsa, hcomp⟩ := actual_positive_symmetric_bounded_comparison J hJ hd drift hrate
  have hsfin : scalarRate J drift ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsa
  have hrs' : r < (scalarRate J drift).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr.le hsfin).mp hrs
  let R := (r + (scalarRate J drift).toReal) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  have hRs : R < (scalarRate J drift).toReal := by dsimp [R]; linarith
  have hRrate : ENNReal.ofReal R < scalarRate J drift :=
    (ENNReal.ofReal_lt_iff_lt_toReal hR.le hsfin).mpr hRs
  have hsa' : (scalarRate J drift).toReal ≤ a := by
    simpa only [ENNReal.toReal_ofReal ha.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hsa
  have hRa : R ≤ a := hRs.le.trans hsa'
  obtain ⟨C, hC0, hdef⟩ := t01_uniform_symmetric_particle_defective J hJ hd drift hrate hR hRrate
  have hdefReal : ∀ N : ℕ+, ∀ f : ParticleH1 J N, IsSymmetricParticleTest f →
      particleEntropy J N f ≤ ENNReal.ofReal
        (2 * particleEnergy J N f / R + C * ∫ X, f X ^ 2 ∂particleLaw J N) := by
    intro N f hsym
    have hmass : (∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw J N) =
        ENNReal.ofReal (∫ X, f X ^ 2 ∂particleLaw J N) :=
      (ofReal_integral_eq_lintegral_ofReal
        (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
        (Eventually.of_forall fun X => sq_nonneg _)).symm
    have h := hdef N f hsym
    rw [hmass, ← ENNReal.ofReal_mul hC0,
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) (particleEnergy_nonneg f))
        (mul_nonneg hC0 (integral_nonneg fun X => sq_nonneg _))] at h
    convert h using 1 <;> congr 1 <;> ring
  have hpoin : ∀ ρ : ℝ, ρ < R → ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N, IsSymmetricParticleTest f →
      ρ * ((∫ X, f X ^ 2 ∂particleLaw J N) - (∫ X, f X ∂particleLaw J N) ^ 2) ≤
        particleEnergy J N f := by
    intro ρ hρ
    apply eventual_symmetric_particle_poincare_of_bounded_comparison J ha hcomp
    · exact ⟨2 / R, C, fun N f hsym => (hdefReal N f hsym).trans_eq (by congr 1; ring)⟩
    · exact hρ.trans_le hRa
  exact eventual_symmetric_particle_lsi_after_concrete_tightening J hR 1 C
    (fun N _ f hsym => hdefReal N f hsym) ⟨a, hRa, hcomp⟩ hpoin hr hrR

set_option backward.isDefEq.respectTransparency.types false in
/-- The original symmetric particle rates have lower limit at least the scalar rate. -/
theorem t01_symmetric_scalar_liminf_lower {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (hd : 0 < d) (drift : AbsoluteDrift J)
    (hrate : 0 < scalarRate J drift) :
    scalarRate J drift ≤ liminf (fun N : ℕ+ => particleRateSym J N) atTop := by
  apply (Filter.le_liminf_iff').2
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    exact Eventually.of_forall fun N => bot_le
  have hyfin : y ≠ ⊤ := ne_top_of_lt hy
  have hyr : 0 < y.toReal := ENNReal.toReal_pos hy0 hyfin
  have hys : ENNReal.ofReal y.toReal < scalarRate J drift := by
    simpa only [ENNReal.ofReal_toReal hyfin] using hy
  filter_upwards [t01_eventual_symmetric_lsi J hJ hd drift hrate hyr hys] with N hN
  have hLSI : ∀ f : ParticleH1 J N, IsSymmetricParticleTest f →
      particleEntropy J N f ≤ ENNReal.ofReal (2 * particleEnergy J N f / y.toReal) := by
    intro f hsym
    convert hN f hsym using 1 <;> congr 1 <;> ring
  simpa only [ENNReal.ofReal_toReal hyfin] using (particleRateSym_iff_lsi J N hyr).mp hLSI

/-- The zero scalar-rate case requires no comparison argument. -/
theorem t01_symmetric_scalar_liminf_lower_all_rates {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (hd : 0 < d) (drift : AbsoluteDrift J) :
    scalarRate J drift ≤ liminf (fun N : ℕ+ => particleRateSym J N) atTop := by
  by_cases hrate : 0 < scalarRate J drift
  · exact t01_symmetric_scalar_liminf_lower J hJ hd drift hrate
  · exact (not_lt.mp hrate).trans bot_le

end DGPS.Lipschitz
