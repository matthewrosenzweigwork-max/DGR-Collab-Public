import DGPS.FiniteN.AnisotropicQuarticEmpiricalCore
import DGPS.FiniteN.AnisotropicQuarticEmpiricalSupport
import DGPS.FiniteN.AnisotropicQuarticRareTestEnergy
import DGPS.FiniteN.Tools.RareCutoff

/-! Actual production upper rates from the concrete rare symmetric tests.
The longitudinal cutoff has a fixed width chosen before N. Its derivative cost
is bounded by the full support probability; the stronger canonical FIN074 shell
estimate is not asserted or used here. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.Tools.GaussianCoupling
open scoped ENNReal

namespace DGPS.FiniteN

private theorem quartic_empirical_box_preimage (N : ℕ+) (δ s : ℝ) :
    (posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
      quarticFieldBox δ s =
        {x | |quarticEmpiricalCos N x + 4| ≤ δ ∧ |quarticEmpiricalSin N x| ≤ s} := by
  ext x
  rw [mem_preimage, quartic_empirical_coordinates]
  rfl

/-- Actual ordinary Poincare and both LSI upper powers for the fixed quartic
zero-diagonal model, on the original production variational domains. -/
theorem quartic_particle_rates_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ+, N0 ≤ (N : ℕ) →
      particlePoincareRate anisotropicQuarticSaddle N ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      particleRateAll anisotropicQuarticSaddle N ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-(3 / 2 : ℝ))) ∧
      particleRateSym anisotropicQuarticSaddle N ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨t, δ, Cm, Ms, ht, hδ, hCm, hMs, hmin, huniq, hgap, hsupport⟩ :=
    quartic_empirical_support_rare_upper
  obtain ⟨tc, htc, hminc, huniqc, hgapc, hcore⟩ := quartic_empirical_core_rare_lower
  have htcEq : tc = t := by
    have hw := huniqc !₂[t, 0] (hmin !₂[tc, 0])
    have he := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) hw
    simpa using he.symm
  subst tc
  obtain ⟨c, Mc, hc, hMc, hcore⟩ := hcore δ hδ
  obtain ⟨f, hf, hsym, hEexact⟩ := quartic_rare_test_family δ
  obtain ⟨CE, hCE, henergy⟩ := quartic_rare_test_energy_support_bound δ hδ
  let Δ := quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]
  let Cs : (N : ℕ+) → Set (ParticleSpace 1 N) := fun N =>
    {x | |quarticEmpiricalCos N x + 4| ≤ δ / 2 ∧
      |quarticEmpiricalSin N x| ≤ (N : ℝ) ^ (-(1 / 4 : ℝ))}
  let Ss : (N : ℕ+) → Set (ParticleSpace 1 N) := quarticRareSupport δ
  let N0 : ℕ := Nat.ceil (max Ms Mc)
  have hthreshold (N : ℕ+) (hN : N0 ≤ (N : ℕ)) : max Ms Mc ≤ (N : ℝ) := by
    exact (Nat.le_ceil (max Ms Mc)).trans (by exact_mod_cast hN)
  have hCs (N : ℕ+) : MeasurableSet (Cs N) := by
    rw [show Cs N = (posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
      quarticFieldBox (δ / 2) ((N : ℝ) ^ (-(1 / 4 : ℝ))) from
        (quartic_empirical_box_preimage N _ _).symm]
    exact (quarticFieldBox_measurable _ _).preimage
      (measurable_posteriorCenter quartic_hubbard_hyp quarticHubbardD quarticHubbardField N)
  have hSs (N : ℕ+) : MeasurableSet (Ss N) := quarticRareSupport_measurable δ N
  have hf0 (N : ℕ+) (_ : N0 ≤ (N : ℕ)) (x) : 0 ≤ f N x := by
    rw [hf]
    exact (quarticRareTest_bounds δ N x).1
  have hf1 (N : ℕ+) (_ : N0 ≤ (N : ℕ)) (x) : f N x ≤ 1 := by
    rw [hf]
    exact (quarticRareTest_bounds δ N x).2
  have hfC (N : ℕ+) (_ : N0 ≤ (N : ℕ)) (x) (hx : x ∈ Cs N) : f N x = 1 := by
    rw [hf]
    exact quarticRareTest_one δ hδ N x hx.1 hx.2
  have hfS (N : ℕ+) (_ : N0 ≤ (N : ℕ)) (x) (hx : x ∉ Ss N) : f N x = 0 := by
    rw [hf]
    exact quarticRareTest_zero δ hδ N x hx
  have hCmass (N : ℕ+) (hN : N0 ≤ (N : ℕ)) :
      c * RareCutoff.rareMass (1 / 4) Δ N ≤ (particleLaw anisotropicQuarticSaddle N).real (Cs N) := by
    have h := hcore N ((le_max_right _ _).trans (hthreshold N hN))
    rw [quartic_empirical_box_preimage] at h
    simpa only [Cs, RareCutoff.rareMass, Δ, mul_assoc] using h
  have hSmass (N : ℕ+) (hN : N0 ≤ (N : ℕ)) :
      (particleLaw anisotropicQuarticSaddle N).real (Ss N) ≤ Cm * RareCutoff.rareMass (1 / 4) Δ N := by
    have h := hsupport N ((le_max_left _ _).trans (hthreshold N hN))
    rw [quartic_empirical_box_preimage] at h
    simpa only [Ss, quarticRareSupport, RareCutoff.rareMass, Δ, mul_assoc] using h
  have hEn (N : ℕ+) (hN : N0 ≤ (N : ℕ)) :
      particleEnergy anisotropicQuarticSaddle N (f N) ≤
        (CE * Cm / c) * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
          ∫ x, f N x ^ 2 ∂particleLaw anisotropicQuarticSaddle N := by
    have hm := (isParticleWeakGradient_particleWeakGradient (f N)).memLp
    have hn := (hCmass N hN).trans (RareCutoff.measureReal_le_integral_sq
      (hCs N) hm (hfC N hN))
    have hmass : RareCutoff.rareMass (1 / 4) Δ N ≤
        (∫ x, f N x ^ 2 ∂particleLaw anisotropicQuarticSaddle N) / c := by
      rw [le_div_iff₀ hc]
      simpa only [mul_comm] using hn
    calc
      _ ≤ CE * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (particleLaw anisotropicQuarticSaddle N).real (Ss N) :=
        henergy N (f N) (hf N)
      _ ≤ CE * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (Cm * RareCutoff.rareMass (1 / 4) Δ N) :=
        mul_le_mul_of_nonneg_left (hSmass N hN) (by positivity)
      _ ≤ CE * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Cm * ((∫ x, f N x ^ 2 ∂particleLaw anisotropicQuarticSaddle N) / c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hCm.le) (by positivity)
      _ = _ := by ring
  obtain ⟨_, hrate⟩ := rare_cutoff_variance_and_entropy_weights anisotropicQuarticSaddle
    f Cs Ss (1 / 4) Δ c Cm hgap hc N0 hCs hSs hf0 hf1 hfC hfS hCmass hSmass
  obtain ⟨C, hC, N1, hrate⟩ := hrate (1 / 2) (CE * Cm / c) (by positivity) hEn
  refine ⟨C, hC, N1, fun N hN => ?_⟩
  obtain ⟨hp, hs⟩ := hrate N hN
  have hs' := (hs (fun N _ => hsym N)).1
  norm_num only [show (-(1 / 2 + 1) : ℝ) = -(3 / 2 : ℝ) by norm_num] at hs'
  exact ⟨hp.1, (particleRateAll_le_sym anisotropicQuarticSaddle N).trans hs', hs'⟩

end DGPS.FiniteN
