import DGPS.FiniteN.AnisotropicQuarticRareTestChain
import DGPS.FiniteN.Tools.EntropyDefects

/-! Actual pointwise shell-sensitive Dirichlet bound for the symmetric quartic test. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.ScalarFoldFIN064
open DGPS.FiniteN.QuarticSaddleGlobalFIN066 DGPS.Examples.AttractiveXY
open DGPS.FiniteN.Tools.AuxiliaryTransferTorus

namespace DGPS.FiniteN

def quarticRareSupport (δ : ℝ) (N : ℕ+) : Set (ParticleSpace 1 N) :=
  {x | |quarticEmpiricalCos N x + 4| ≤ δ ∧
    |quarticEmpiricalSin N x| ≤ 2 * (N : ℝ) ^ (-(1 / 4 : ℝ))}

def quarticRareDerivativeShell (δ : ℝ) (N : ℕ+) : Set (ParticleSpace 1 N) :=
  {x | δ / 2 ≤ |quarticEmpiricalCos N x + 4| ∧ x ∈ quarticRareSupport δ N}

theorem quarticRareSupport_measurable (δ : ℝ) (N : ℕ+) : MeasurableSet (quarticRareSupport δ N) := by
  have hc := (measurable_bounded_of_smooth (quartic_empirical_cos_smooth N)).1
  have hs := (measurable_bounded_of_smooth (quartic_empirical_sin_smooth N)).1
  exact (measurableSet_le (hc.add_const 4).abs measurable_const).inter
    (measurableSet_le hs.abs measurable_const)

theorem quarticRareDerivativeShell_measurable (δ : ℝ) (N : ℕ+) :
    MeasurableSet (quarticRareDerivativeShell δ N) := by
  have hc := (measurable_bounded_of_smooth (quartic_empirical_cos_smooth N)).1
  exact (measurableSet_le measurable_const (hc.add_const 4).abs).inter
    (quarticRareSupport_measurable δ N)

theorem quarticRareTest_partial_of_zero (δ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N)
    (hx : quarticRareTest δ N x = 0) (i : Fin N) :
    particlePartial i 0 (quarticRareTest δ N) x = 0 := by
  have hm : IsLocalMin (quarticRareTest δ N ∘ particleLift) (fun k => SharpLSI.secT (x k)) :=
    Filter.Eventually.of_forall fun y => by
      change quarticRareTest δ N (particleLift (fun k => SharpLSI.secT (x k))) ≤ _
      rw [PositiveRate.particleLift_secT, hx]
      exact (quarticRareTest_bounds δ N (particleLift y)).1
  unfold particlePartial
  rw [hm.fderiv_eq_zero]
  rfl

private theorem quartic_sin_sq_le_one (x : Torus 1) : scalarSin x ^ 2 ≤ 1 := by
  have h : |scalarSin x| ≤ 1 := by
    simpa only [scalarSin_eq_FIN066] using abs_xyMode_im_le x
  nlinarith [sq_abs (scalarSin x), abs_nonneg (scalarSin x)]

private theorem quartic_cos_sq_le_one (x : Torus 1) : scalarCos x ^ 2 ≤ 1 := by
  have h := scalarCos_bound x
  nlinarith [sq_abs (scalarCos x), abs_nonneg (scalarCos x)]

/-- The two genuine gradient contributions are localized separately: the fixed
longitudinal derivative shell and the full shrinking transverse support. -/
theorem quartic_rare_test_gradient_shell_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → ∀ N : ℕ+, ∀ x : ParticleSpace 1 N,
      (∑ i, particlePartial i 0 (quarticRareTest δ N) x ^ 2) ≤
        (2 * (N : ℝ) * K ^ 2 * (2 / δ) ^ 2 *
          (2 * Real.pi * quarticKappa / (N : ℝ)) ^ 2) *
            (quarticRareDerivativeShell δ N).indicator (fun _ => (1 : ℝ)) x +
        (2 * (N : ℝ) * K ^ 2 * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
          (2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)) ^ 2) *
            (quarticRareSupport δ N).indicator (fun _ => (1 : ℝ)) x := by
  obtain ⟨K, hK0, hK⟩ := deriv_chi_bound_FIN064
  refine ⟨K, hK0, fun δ hδ N x => ?_⟩
  by_cases hS : x ∈ quarticRareSupport δ N
  · let a := 2 / δ
    let q := (N : ℝ) ^ (1 / 4 : ℝ)
    let A := (2 / δ) * (quarticEmpiricalCos N x + 4)
    let B := (N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x
    let α := chiFIN064 B * deriv chiFIN064 A * a
    let β := chiFIN064 A * deriv chiFIN064 B * q
    let ρ := 2 * Real.pi * quarticKappa / (N : ℝ)
    let τ := 2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)
    let I := (quarticRareDerivativeShell δ N).indicator (fun _ => (1 : ℝ)) x
    have hI : 0 ≤ I := Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hχA : chiFIN064 A ^ 2 ≤ 1 := by
      nlinarith [chi_nonneg_FIN064 A, chi_le_one_FIN064 A]
    have hχB : chiFIN064 B ^ 2 ≤ 1 := by
      nlinarith [chi_nonneg_FIN064 B, chi_le_one_FIN064 B]
    have hdA : deriv chiFIN064 A ^ 2 ≤ K ^ 2 :=
      sq_le_sq' (abs_le.mp (hK A)).1 (abs_le.mp (hK A)).2
    have hdB : deriv chiFIN064 B ^ 2 ≤ K ^ 2 :=
      sq_le_sq' (abs_le.mp (hK B)).1 (abs_le.mp (hK B)).2
    have hα : α ^ 2 ≤ K ^ 2 * a ^ 2 * I := by
      by_cases hSh : x ∈ quarticRareDerivativeShell δ N
      · dsimp only [α, I]
        rw [Set.indicator_of_mem hSh, mul_one, mul_pow, mul_pow]
        calc
          _ ≤ 1 * K ^ 2 * a ^ 2 := by gcongr
          _ = _ := by ring
      · have hcore : |quarticEmpiricalCos N x + 4| ≤ δ / 2 := by
          have hn : ¬ δ / 2 ≤ |quarticEmpiricalCos N x + 4| := fun h => hSh ⟨h, hS⟩
          exact (lt_of_not_ge hn).le
        have hA : |A| ≤ 1 := by
          dsimp only [A]
          rw [abs_mul, abs_of_pos (div_pos (by norm_num) hδ)]
          calc
            _ ≤ (2 / δ) * (δ / 2) := mul_le_mul_of_nonneg_left hcore (by positivity)
            _ = 1 := by field_simp [hδ.ne']
        dsimp only [α, I]
        rw [quartic_cutoff_derivative_inner_zero A hA, mul_zero, zero_mul,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          Set.indicator_of_notMem hSh, mul_zero]
    have hβ : β ^ 2 ≤ K ^ 2 * q ^ 2 := by
      dsimp only [β]
      rw [mul_pow, mul_pow]
      calc
        _ ≤ 1 * K ^ 2 * q ^ 2 := by gcongr
        _ = _ := by ring
    have ht : ∀ i : Fin N, particlePartial i 0 (quarticRareTest δ N) x ^ 2 ≤
        2 * (K ^ 2 * a ^ 2 * I * ρ ^ 2) + 2 * (K ^ 2 * q ^ 2 * τ ^ 2) := by
      intro i
      have h1 : (α * (-ρ * scalarSin (x i))) ^ 2 ≤ K ^ 2 * a ^ 2 * I * ρ ^ 2 := by
        calc
          _ = α ^ 2 * ρ ^ 2 * scalarSin (x i) ^ 2 := by ring
          _ ≤ (K ^ 2 * a ^ 2 * I) * ρ ^ 2 * 1 := by gcongr; exact quartic_sin_sq_le_one _
          _ = _ := by ring
      have h2 : (β * (τ * scalarCos (x i))) ^ 2 ≤ K ^ 2 * q ^ 2 * τ ^ 2 := by
        calc
          _ = β ^ 2 * τ ^ 2 * scalarCos (x i) ^ 2 := by ring
          _ ≤ (K ^ 2 * q ^ 2) * τ ^ 2 * 1 := by gcongr; exact quartic_cos_sq_le_one _
          _ = _ := by ring
      rw [quarticRareTest_partial]
      change (α * (-ρ * scalarSin (x i)) + β * (τ * scalarCos (x i))) ^ 2 ≤ _
      nlinarith only [h1, h2, sq_nonneg (α * (-ρ * scalarSin (x i)) - β * (τ * scalarCos (x i)))]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => ht i)
    rw [Set.indicator_of_mem hS, mul_one]
    calc
      _ ≤ ∑ _i : Fin N, (2 * (K ^ 2 * a ^ 2 * I * ρ ^ 2) + 2 * (K ^ 2 * q ^ 2 * τ ^ 2)) := hsum
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp only [a, q, I, ρ, τ]; ring
  · have hzero := quarticRareTest_zero δ hδ N x hS
    have hSh : x ∉ quarticRareDerivativeShell δ N := fun h => hS h.2
    simp only [quarticRareTest_partial_of_zero δ N x hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
      Set.indicator_of_notMem hS, Set.indicator_of_notMem hSh, mul_zero, add_zero, le_refl]

/-- The actual native Dirichlet integral is bounded by the separate shell and
support probabilities. Membership and the energy identity are obtained from the
proved smooth native constructor, not assumed as additional regularity data. -/
theorem quartic_rare_test_energy_shell_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → ∀ N : ℕ+,
      ∀ f : ParticleH1 anisotropicQuarticSaddle N, (∀ x, f x = quarticRareTest δ N x) →
      particleEnergy anisotropicQuarticSaddle N f ≤
        (2 * (N : ℝ) * K ^ 2 * (2 / δ) ^ 2 *
          (2 * Real.pi * quarticKappa / (N : ℝ)) ^ 2) *
            (particleLaw anisotropicQuarticSaddle N).real (quarticRareDerivativeShell δ N) +
        (2 * (N : ℝ) * K ^ 2 * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
          (2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)) ^ 2) *
            (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) := by
  obtain ⟨K, hK, hgrad⟩ := quartic_rare_test_gradient_shell_bound
  refine ⟨K, hK, fun δ hδ N f hf => ?_⟩
  obtain ⟨g, hg, hE⟩ := smooth_h1_FIN064 anisotropicQuarticSaddle N (quarticRareTest_smooth δ N)
  have hfg : f = g := Subtype.ext (by funext x; rw [hf, hg])
  rw [hfg, hE]
  let A := 2 * (N : ℝ) * K ^ 2 * (2 / δ) ^ 2 * (2 * Real.pi * quarticKappa / (N : ℝ)) ^ 2
  let B := 2 * (N : ℝ) * K ^ 2 * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
    (2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)) ^ 2
  have hli : Integrable (fun x => ∑ i, particlePartial i 0 (quarticRareTest δ N) x ^ 2)
      (particleLaw anisotropicQuarticSaddle N) :=
    EntropyDefects.integrable_of_continuous (continuous_finsetSum _ fun i _ =>
      (EntropyDefects.continuous_particlePartial (quarticRareTest_smooth δ N) i 0).pow 2)
  have hAi : Integrable (fun x => A * (quarticRareDerivativeShell δ N).indicator (fun _ => (1 : ℝ)) x)
      (particleLaw anisotropicQuarticSaddle N) :=
    ((integrable_const (1 : ℝ)).indicator (quarticRareDerivativeShell_measurable δ N)).const_mul A
  have hBi : Integrable (fun x => B * (quarticRareSupport δ N).indicator (fun _ => (1 : ℝ)) x)
      (particleLaw anisotropicQuarticSaddle N) :=
    ((integrable_const (1 : ℝ)).indicator (quarticRareSupport_measurable δ N)).const_mul B
  have hm := integral_mono hli (hAi.add hBi) (fun x => hgrad δ hδ N x)
  simp only [Pi.add_apply] at hm
  have hInd (S : Set (ParticleSpace 1 N)) (hS : MeasurableSet S) :
      (∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂particleLaw anisotropicQuarticSaddle N) =
        (particleLaw anisotropicQuarticSaddle N).real S := by
    rw [integral_indicator hS]
    simp
  rw [integral_add hAi hBi, integral_const_mul, integral_const_mul,
    hInd _ (quarticRareDerivativeShell_measurable δ N),
    hInd _ (quarticRareSupport_measurable δ N)] at hm
  exact hm

/-- For the headline upper powers the fixed longitudinal cutoff costs less than
the transverse cutoff. Its shell is a subset of the support, so no stronger
canonical exponential shell estimate is needed in this actual energy bound. -/
theorem quartic_rare_test_energy_support_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ+, ∀ f : ParticleH1 anisotropicQuarticSaddle N,
      (∀ x, f x = quarticRareTest δ N x) →
      particleEnergy anisotropicQuarticSaddle N f ≤
        C * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
          (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) := by
  obtain ⟨K, hK, henergy⟩ := quartic_rare_test_energy_shell_bound
  let A := 2 * K ^ 2 * (2 / δ) ^ 2 * (2 * Real.pi * quarticKappa) ^ 2
  let B := 2 * K ^ 2 * (2 * Real.pi * (quarticKappa * quarticEta)) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨A + B + 1, by positivity, fun N f hf => ?_⟩
  have hNp : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast N.pos
  have hAx : 2 * (N : ℝ) * K ^ 2 * (2 / δ) ^ 2 *
      (2 * Real.pi * quarticKappa / (N : ℝ)) ^ 2 = A / (N : ℝ) := by
    dsimp only [A]
    field_simp [hNp.ne']
    <;> ring
  have hq2 : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    congr 1
    norm_num
  have hqr : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (N : ℝ) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hq2, ← Real.rpow_sub_one hNp.ne' (1 / 2 : ℝ)]
    norm_num
  have hBy : 2 * (N : ℝ) * K ^ 2 * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
      (2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)) ^ 2 =
        B * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = B * (((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (N : ℝ)) := by
        dsimp only [B]
        field_simp [hNp.ne']
        <;> ring
      _ = _ := by rw [hqr]
  have hE := henergy δ hδ N f hf
  rw [hAx, hBy] at hE
  have hm : (particleLaw anisotropicQuarticSaddle N).real (quarticRareDerivativeShell δ N) ≤
      (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) :=
    measureReal_mono (fun x hx => hx.2) (measure_ne_top _ _)
  have hp : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hcoef : A / (N : ℝ) ≤ A * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hp hA
  calc
    _ ≤ A / (N : ℝ) * (particleLaw anisotropicQuarticSaddle N).real (quarticRareDerivativeShell δ N) +
        B * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) := hE
    _ ≤ (A * (N : ℝ) ^ (-(1 / 2 : ℝ))) * (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) +
        B * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) :=
      add_le_add (mul_le_mul hcoef hm measureReal_nonneg (by positivity)) le_rfl
    _ = (A + B) * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
        (particleLaw anisotropicQuarticSaddle N).real (quarticRareSupport δ N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith : A + B ≤ A + B + 1) (Real.rpow_pos_of_pos hNp _).le) measureReal_nonneg

end DGPS.FiniteN
