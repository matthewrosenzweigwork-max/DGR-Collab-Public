import DGPS.Lipschitz.T01GroundStateSchrodinger
import DGPS.Lipschitz.T01SymmetricLower
import DGPS.Lipschitz.DualGenerator
import SharpSymmetricLSI.Paper.TestEnergy2
import SharpSymmetricLSI.Paper.TestEnergy6

/-!
# Actual Gibbs convergence of the empirical spectral mobility

The reference quartic moment and the uniform density moment are combined by Hölder. The
one-body eigen-equation is the actual frozen reference equation supplied by the caller.
-/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology
open SharpLSI SharpLSI.FL
open scoped ENNReal InnerProductSpace

variable {d : ℕ}

theorem t01_mobA_eq_ANmat (eC : ℕ → Torus d → ℝ) (N : ℕ)
    (X : SharpLSI.Config N d) (i j : ℕ) :
    SharpLSI.mobA eC N X i j = SharpLSI.FL.ANmat eC N X i j := rfl

/-- Native finite-cylinder mobility is the same empirical matrix in positive spectral modes. -/
theorem t01_dualA_eq_mobA (eC : ℕ → Torus d → ℝ) (N : ℕ+) {n : ℕ}
    (i j : Fin n) (X : ParticleSpace d N) :
    dualA N (fun k : Fin n => eC (k.val + 1)) i j X =
      SharpLSI.mobA eC N X i.val j.val := by
  simp only [dualA, dg_inner, smoothGrad_apply, coordPartial, SharpLSI.mobA,
    SharpLSI.cgrad, torusLift]

/-- An explicit particle-uniform rate bound from the actual reference and density moments. -/
theorem t01_mobility_error_rate_bound (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hac : (μ : Measure (Torus d)) ≪ haar d)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : SharpLSI.IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ SharpLSI.liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {p Bp : ℝ} (hp : 1 < p) (hBp : 0 ≤ Bp)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    (i j : ℕ) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ N : ℕ+,
      ∫ X, (SharpLSI.mobA eC N X i j - if i = j then lam (i + 1) else 0) ^ 2
        ∂particleLaw A N ≤
      Bp ^ (1 / p) * (M ^ (Real.conjExponent p - 1) *
        (C * ((N : ℝ)⁻¹) ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / Real.conjExponent p) := by
  obtain ⟨hSm, B, hB⟩ := schroC_S_facts hφ (i + 1) (j + 1)
  obtain ⟨C, hC, hCm⟩ := GroundState.ANmat_moment hac he hφ heC i j 2
  let c : ℝ := if i = j then lam (i + 1) else 0
  let D (N : ℕ) (X : SharpLSI.Config N d) := SharpLSI.FL.ANmat eC N X i j - c
  let L : ℝ := B + |c|
  let M : ℝ := L ^ 2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL : 0 ≤ L := add_nonneg hB0 (abs_nonneg _)
  have hM : 0 ≤ M := sq_nonneg _
  have hAN : ∀ (N : ℕ+) (X : SharpLSI.Config N d), |SharpLSI.FL.ANmat eC N X i j| ≤ B := by
    intro N X
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    unfold SharpLSI.FL.ANmat
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _l : Fin N, B :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun l _ => hB (X l))) (inv_nonneg.mpr hN.le)
      _ = B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  have hDb : ∀ (N : ℕ+) X, |D N X| ≤ L := fun N X =>
    (abs_sub _ _).trans (add_le_add (hAN N X) le_rfl)
  have hDm : ∀ N : ℕ, Measurable (D N) := fun N =>
    (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).1
  have hYb : ∀ (N : ℕ+) X, |D N X ^ 2| ≤ M := by
    intro N X
    simpa only [abs_sq, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hDb N X) 2
  have hfour : ∀ N : ℕ+, ∫ X, (D N X ^ 2) ^ 2
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C * ((N : ℝ)⁻¹) ^ 2 := by
    intro N
    simpa only [SharpLSI.FL.QN, D, c, ← pow_mul] using hCm N N.pos
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  refine ⟨C, M, hC, hM, fun N => ?_⟩
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn
    (centeredParticleDensity_continuous A μ N).continuousOn
  have hρK : ∀ X, centeredParticleDensity A μ N X ≤ K := fun X =>
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK X (Set.mem_univ X))
  have hweight := SharpLSI.integral_weight_abs_le
    (P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))
    (fun X => (centeredParticleDensity_pos A μ N X).le)
    (centeredParticleDensity_continuous A μ N).measurable hρK
    ((hDm N).pow_const 2) hM (hYb N) hpq
  simp only [abs_sq] at hweight
  rw [integral_particleLaw_eq_centered A μ hfix N]
  change (∫ X, centeredParticleDensity A μ N X * D N X ^ 2
    ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) ≤ _
  refine hweight.trans ?_
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < Real.conjExponent p := hpq.symm.pos
  have hw0 : 0 ≤ ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
    integral_nonneg fun X => Real.rpow_nonneg (centeredParticleDensity_pos A μ N X).le _
  have hy0 : 0 ≤ ∫ X, (D N X ^ 2) ^ 2
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
    integral_nonneg fun X => sq_nonneg (D N X ^ 2)
  have hw := Real.rpow_le_rpow hw0 (hρ N) (one_div_nonneg.mpr hp0.le)
  have hy := Real.rpow_le_rpow hy0 (hfour N) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hm0 : 0 ≤ M ^ (Real.conjExponent p - 1) := Real.rpow_nonneg hM _
  have hinner := mul_le_mul_of_nonneg_left hy hm0
  have hbase0 := mul_nonneg hm0 (Real.rpow_nonneg hy0 (1 / 2 : ℝ))
  have houter := Real.rpow_le_rpow hbase0 hinner (one_div_nonneg.mpr hq0.le)
  exact mul_le_mul hw houter (Real.rpow_nonneg hbase0 _) (Real.rpow_nonneg hBp _)

/-- The empirical mobility converges in L2 under the actual Gibbs law along every N→∞. -/
theorem t01_mobility_particleLaw_L2_tendsto (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hac : (μ : Measure (Torus d)) ≪ haar d)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : SharpLSI.IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ SharpLSI.liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {p Bp : ℝ} (hp : 1 < p) (hBp : 0 ≤ Bp)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    (Ns : ℕ → ℕ+) (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop) (i j : ℕ) :
    Tendsto (fun k => ∫ X,
      (SharpLSI.mobA eC (Ns k) X i j - if i = j then lam (i + 1) else 0) ^ 2
        ∂particleLaw A (Ns k)) atTop (𝓝 0) := by
  obtain ⟨C, M, hC, hM, hbound⟩ :=
    t01_mobility_error_rate_bound A μ hfix hac he hφ heC hp hBp hρ i j
  have hpq := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < Real.conjExponent p := hpq.symm.pos
  have hni : Tendsto (fun k => ((Ns k : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa only [Function.comp_def, one_div] using h.comp hNs
  have h0 : Tendsto (fun k => C * ((Ns k : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using (hni.pow 2).const_mul C
  have h1 := h0.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h1
  have h2 := h1.const_mul (M ^ (Real.conjExponent p - 1))
  rw [mul_zero] at h2
  have h3 := h2.rpow_const (Or.inr (one_div_nonneg.mpr hq0.le))
  rw [Real.zero_rpow (one_div_ne_zero hq0.ne')] at h3
  have hrate := h3.const_mul (Bp ^ (1 / p))
  rw [mul_zero] at hrate
  exact squeeze_zero (fun k => integral_nonneg fun X => sq_nonneg _) (fun k => hbound (Ns k)) hrate

end DGPS.Lipschitz
