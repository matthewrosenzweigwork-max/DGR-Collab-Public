import DGPS.FiniteN.AnisotropicQuarticAuxiliaryTransfer
import DGPS.FiniteN.AnisotropicQuarticConditionalPoincare
import DGPS.FiniteN.AnisotropicQuarticEntropyDefect
import DGPS.FiniteN.ScalarFoldFIN060I

/-! Actual full particle lower bounds for FIN070, without the rare-box upper cone. -/

open MeasureTheory ProbabilityTheory Matrix
open DGPS DGPS.Models DGPS.Particle
open DGPS.FiniteN.QuarticSaddleGlobalFIN066 DGPS.FiniteN.ScalarFoldFIN060
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open DGPS.FiniteN.Tools.AuxiliaryTransferTorus
open scoped ContDiff ENNReal

namespace DGPS.FiniteN

/-- Actual inverse Poincare bound on the full canonical weak particle H1 domain. -/
theorem quartic_particle_poincare_inverse :
    ∃ P : ℝ, 0 < P ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℕ+, N0 ≤ (N : ℝ) →
      ∀ f : ParticleH1 anisotropicQuarticSaddle N,
        variance f.1 (particleLaw anisotropicQuarticSaddle N) ≤
          P * Real.sqrt (N : ℝ) * particleEnergy anisotropicQuarticSaddle N f := by
  obtain ⟨a, ha, N0, hN0, haux⟩ := quartic_auxiliary_poincare
  obtain ⟨C, hC, hcond⟩ := quartic_conditional_uniform_poincare
  refine ⟨C * (1 + 1 / a), by positivity, N0, hN0, fun N hN f => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hlam : 0 < a * Real.sqrt (N : ℝ) := mul_pos ha hs
  have hK : ∀ x : ParticleSpace 1 N,
      ∫⁻ w, ENNReal.ofReal C ∂gaussLaw quarticHubbardD N
          (posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x) ≤
        ENNReal.ofReal C := by
    intro x
    haveI : IsProbabilityMeasure (gaussLaw quarticHubbardD N
        (posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x)) := by
      rw [← map_stdGaussian_affine quartic_hubbard_D_posDef]
      exact (Measure.isProbabilityMeasure_map_iff
        (measurable_affineMap quarticHubbardD N _).aemeasurable).mpr inferInstance
    simp
  have hmain := particle_poincare_torus_FIN060 (A := anisotropicQuarticSaddle) (N := N)
    quartic_hubbard_D_posDef quartic_hubbard_hyp (quartic_hubbard_particle_weight N)
    hlam (haux N hN) (C := fun _ => C) measurable_const (hcond N) hC.le hK
    (L := 1) (fun x => (quartic_hubbard_feature_length x).le) f
  simp only [one_pow, mul_one] at hmain
  have hq : (N : ℝ) / (a * Real.sqrt (N : ℝ)) = Real.sqrt (N : ℝ) / a := by
    rw [div_eq_div_iff (mul_pos ha hs).ne' ha.ne']
    rw [show Real.sqrt (N : ℝ) * (a * Real.sqrt (N : ℝ)) =
      a * Real.sqrt (N : ℝ) ^ 2 by ring, Real.sq_sqrt hNp.le]
    ring
  rw [hq] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (particleEnergy_nonneg f))
  have hcoeff : 1 + Real.sqrt (N : ℝ) / a ≤ (1 + 1 / a) * Real.sqrt (N : ℝ) := by
    rw [show (1 + 1 / a) * Real.sqrt (N : ℝ) =
      Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ) / a by ring]
    exact add_le_add (Real.one_le_sqrt.mpr hN1) le_rfl
  calc
    _ ≤ C * ((1 + 1 / a) * Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hcoeff hC.le
    _ = _ := by ring

/-- Production ordinary full Poincare rate lower bound for every positive particle number. -/
theorem quartic_particle_poincare_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤ particlePoincareRate anisotropicQuarticSaddle N := by
  obtain ⟨P, hP, N0, hN0, hbound⟩ := quartic_particle_poincare_inverse
  refine all_N_FIN060 (p := 1 / 2) (by norm_num)
    (fun N => particlePoincareRate anisotropicQuarticSaddle N) (fun N => ?_)
    (c := 1 / P) (N₀ := N0) (by positivity) (fun N hN => ?_)
  · obtain ⟨r, hr, h⟩ := PositiveRate.particlePoincare_pos_aux anisotropicQuarticSaddle N
    exact ⟨r, hr, (le_particlePoincareRate_iff_forall _ N r).mpr fun f _ => h f⟩
  · rw [le_particlePoincareRate_iff_forall]
    intro f hf
    have hNp : (0 : ℝ) < N := by positivity
    have hu : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNp _
    have hi : 1 / P * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (P * (N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg hNp.le, mul_inv, one_div]
    rw [hi, inv_mul_le_iff₀ (mul_pos hP hu)]
    simpa only [Real.sqrt_eq_rpow] using hbound N hN f

/-- Production unrestricted LSI lower bound, including the full weak H1 entropy closure. -/
theorem quartic_particle_lsi_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c * (N : ℝ) ^ (-(3 / 2 : ℝ))) ≤ particleRateAll anisotropicQuarticSaddle N := by
  obtain ⟨P, hP, N0, hN0, hbound⟩ := quartic_particle_poincare_inverse
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  let A : ℝ := 2 / (4 * Real.pi ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  let B : ℝ := 1 + quarticKappa + quarticKappa * quarticEta
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let M : ℝ := A + (B + 2) * P
  have hM : 0 < M := by dsimp [M]; positivity
  refine all_N_FIN060 (p := 3 / 2) (by norm_num) (fun N => particleRateAll anisotropicQuarticSaddle N)
    (fun N => PositiveRate.particleRateAll_pos_aux anisotropicQuarticSaddle N)
    (c := 2 / M) (N₀ := N0) (by positivity) (fun N hN => ?_)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hu : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hup : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := lt_of_lt_of_le zero_lt_one hu
  have hpow : (N : ℝ) ^ (3 / 2 : ℝ) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hNp, Real.rpow_one]
  have hmain := lsi_of_poincare_defect_FIN060 anisotropicQuarticSaddle N
    (P := P * (N : ℝ) ^ (1 / 2 : ℝ)) (a := A) (b := B * (N : ℝ))
    (mul_pos hP hup) hA.le (mul_nonneg hB hNp.le)
    (fun f => by simpa only [Real.sqrt_eq_rpow] using hbound N hN f)
    (quartic_particle_entropy_defect N)
  refine (ENNReal.ofReal_le_ofReal ?_).trans hmain
  have hden : A + (B * (N : ℝ) + 2) * (P * (N : ℝ) ^ (1 / 2 : ℝ)) ≤
      M * (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [hpow]
    dsimp [M]
    let u := (N : ℝ) ^ (1 / 2 : ℝ)
    let n : ℝ := N
    have h1 : 1 ≤ n * u := by dsimp [n, u]; nlinarith
    have h2 : u ≤ n * u := by dsimp [n, u]; nlinarith
    change A + (B * n + 2) * (P * u) ≤ (A + (B + 2) * P) * (n * u)
    nlinarith [mul_le_mul_of_nonneg_left h1 hA.le,
      mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * P by positivity)]
  have hpos : 0 < A + (B * (N : ℝ) + 2) * (P * (N : ℝ) ^ (1 / 2 : ℝ)) := by positivity
  rw [Real.rpow_neg hNp.le, ← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (by norm_num) hpos hden

/-- The same production lower power bound holds on symmetric weak particle tests. -/
theorem quartic_particle_symmetric_lsi_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c * (N : ℝ) ^ (-(3 / 2 : ℝ))) ≤ particleRateSym anisotropicQuarticSaddle N := by
  obtain ⟨c, hc, h⟩ := quartic_particle_lsi_lower
  exact ⟨c, hc, fun N => (h N).trans (particleRateAll_le_sym anisotropicQuarticSaddle N)⟩

end DGPS.FiniteN
