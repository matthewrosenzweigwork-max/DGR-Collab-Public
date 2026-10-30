import DGPS.Lipschitz.T01SymmetricGibbsCompactness
import DGPS.Particle.Rates
import DGPS.Lipschitz.T01BoundedLawEntropy
import DGPS.Lipschitz.T01ActualGaussianEnergyLower
import DGPS.Lipschitz.T01GaussianLSI
import DGPS.Lipschitz.T01GaussianSpectralTests
import DGPS.Lipschitz.T01FrozenSpectralHessian
import DGPS.Lipschitz.T01ReferenceData
import DGPS.Lipschitz.T01ReferenceEigenbasis

/-!
# The actual symmetric bounded comparison

A hypothetical bounded violating sequence has an actual Gibbs joint limit and an
entropy limit. The centered native generator gives the Gaussian energy lower bound;
the Gaussian LSI contradicts the fixed positive error. Every spectral, force and
change-of-law input is supplied on one actual frozen reference witness.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal BoundedContinuousFunction InnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation DGPS.Analysis ParabolicChainRule

variable {d : ℕ}

/-- Actual same-reference data imply the symmetric bounded comparison at the Gaussian rate. -/
theorem actual_symmetric_bounded_comparison (A : InteractionData d) (hA : LipschitzData A)
    (S : Spec d) (aux : Aux S) (D : KData d) (hD : D.K = centeredKernel A S.mu)
    (hfix : (frozenGibbs A (specProbability_LIP016 S)).measure = S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hφ : ∀ j, IsC1Periodic (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1) (htop : Tendsto S.lam atTop atTop)
    (hcoerc : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    (H : ℕ → Fin d → Fin d → Torus d → ℝ)
    (hH : ∀ j, IsWeakHessian (S.v j) (smoothGrad (S.v j)) (H j))
    {gμ : Torus d → Tangent d} (hμ : IsWeakGradient (frozenPotential A S.mu) gμ)
    (hlap : ∀ j, IsWeakLaplacian (S.v j)
      (fun z => inner ℝ (gμ z) (smoothGrad (S.v j) z) - S.lam j * S.v j z))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hN : ∀ N : ℕ+, |Real.log (centeredParticleNormalizer A (specProbability_LIP016 S) N)| ≤ C ∧
      ∫ X, centeredParticleDensity A (specProbability_LIP016 S) N X ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu) ≤ C) :
    let a := (lamG (lamShift S.lam) (t01CovarianceMatrix S A)).toReal
    ∀ B E0 ε : ℝ, 0 < B → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
        IsSymmetricParticleTest f → (∀ X, |f X| ≤ B) → particleEnergy A N f ≤ E0 →
        ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε) := by
  classical
  dsimp only
  obtain ⟨σ, hσ, hbound⟩ := hcoerc
  have P := t01CovarianceMatrix_symPkg S aux A D hD hσ hbound
  have hlamBase : 0 < lamShift S.lam 0 := hlam1
  have hlamLower : ∀ i, lamShift S.lam 0 ≤ lamShift S.lam i :=
    fun i => he.mono (by omega)
  have hGpos := lamG_pos P.pos P.Csymm P.nn P.up (fun j => (P.inv j).1) hlamBase hlamLower
  have hGtop := lamG_lt_top P.Csymm P.nn P.inv (lamShift S.lam)
  let a := (lamG (lamShift S.lam) (t01CovarianceMatrix S A)).toReal
  have ha : 0 < a := ENNReal.toReal_pos hGpos.ne' hGtop.ne
  intro B E0 ε hB hE0 hε
  by_contra hfail
  have hfreq : ∃ᶠ N : ℕ+ in atTop, ∃ f : ParticleH1 A N,
      IsSymmetricParticleTest f ∧ (∀ X, |f X| ≤ B) ∧ particleEnergy A N f ≤ E0 ∧
        ¬(ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε)) := by
    refine (Filter.not_eventually.mp hfail).mono ?_
    intro N hbad
    simp only [not_forall] at hbad
    obtain ⟨f, hs, hb, he, hi⟩ := hbad
    exact ⟨f, hs, hb, he, hi⟩
  have hex : ∀ k : ℕ, ∃ N : ℕ+, Nat.succPNat k ≤ N ∧ ∃ f : ParticleH1 A N,
      IsSymmetricParticleTest f ∧ (∀ X, |f X| ≤ B) ∧ particleEnergy A N f ≤ E0 ∧
        ¬(ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε)) := fun k =>
    (Filter.frequently_atTop.mp hfreq) (Nat.succPNat k)
  choose Ns hNs f hs hfB hfE hfviol using hex
  have hNt : Tendsto (fun k => (Ns k : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by
      change k ≤ (Ns k : ℕ)
      have h := hNs k
      change k + 1 ≤ (Ns k : ℕ) at h
      omega) tendsto_id
  have hfL : ∀ k, MemLp (f k) 2 (particleLaw A (Ns k)) := fun k =>
    (isParticleWeakGradient_particleWeakGradient (f k)).memLp
  have hfFin : ∀ k, particleEntropy A (Ns k) (f k) ≠ ⊤ := by
    intro k
    exact (homogeneousEntropy_tendsto_of_bounded_law_and_mass
      (fun _ : ℕ => particleLaw A (Ns k)) (particleLaw A (Ns k))
      (fun _ : ℕ => (f k : ParticleSpace d (Ns k) → ℝ)) (fun _ => hfL k) (hfL k)
      hB.le (fun _ => hfB k) (fun _ => tendsto_const_nhds) tendsto_const_nhds).1
  have hviol : ∀ k, particleEnergy A (Ns k) (f k) + ε <
      a / 2 * (particleEntropy A (Ns k) (f k)).toReal := by
    intro k
    by_contra hn
    apply hfviol k
    rw [← ENNReal.ofReal_toReal (hfFin k),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ a / 2)]
    exact ENNReal.ofReal_le_ofReal (not_lt.mp hn)
  obtain ⟨φ, hφmono, Q, hQ, hγ, F, hF, hlaw, hmass⟩ :=
    t01_bounded_symmetric_gibbs_compactness A hA aux.hd S aux D hD hfix he hφ
      hlam0 hlam1 he.mono htop hσ hbound hp hC0 hN Ns hNt f hs B E0 hB.le hE0.le hfB hfE
  let γ := gammaInfOf A.W S.mu Q
  letI : IsProbabilityMeasure γ := hγ.1
  have hScalarLaw : ∀ g : ℝ →ᵇ ℝ,
      Tendsto (fun k => ∫ X, g (f (φ k) X) ∂particleLaw A (Ns (φ k))) atTop
        (𝓝 (∫ z, g (F z) ∂γ)) := fun g =>
    hlaw 0 (g.compContinuous ⟨Prod.fst, continuous_fst⟩)
  obtain ⟨hEntFin, hEnt⟩ := homogeneousEntropy_tendsto_of_bounded_law_and_mass
    (fun k => particleLaw A (Ns (φ k))) γ
    (fun k => (f (φ k) : ParticleSpace d (Ns (φ k)) → ℝ)) (fun k => hfL (φ k)) hF
    hB.le (fun k => hfB (φ k)) hScalarLaw hmass
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hF.integrable_sq] at hEntFin hEnt
  change Tendsto (fun k => (particleEntropy A (Ns (φ k)) (f (φ k))).toReal) atTop
    (𝓝 (ent γ (fun z => F z ^ 2)).toReal) at hEnt
  have hexY : ∀ i, ∃ Y, IsRowVariable (Tmat A.W S.mu S.v) γ i Y := fun i =>
    exists_rowVariable hγ P.pos P.nn P.up (P.hs.prod_factor i)
  choose Y hY using hexY
  have hLow := t01_actual_bounded_gaussian_energy_lower A hA S aux D hD hfix he hφ htop
    ⟨σ, hσ, hbound⟩ H hH hμ hlap hp hC0 (fun N => (hN N).2) hγ hY hF
    (fun k => Ns (φ k)) (hNt.comp hφmono.tendsto_atTop) (fun k => f (φ k)) hB.le
    (fun k => hfB (φ k)) hlaw
  let R := a / 2 * (ent γ (fun z => F z ^ 2)).toReal - ε
  have hRt : Tendsto (fun k => a / 2 * (particleEntropy A (Ns (φ k)) (f (φ k))).toReal - ε)
      atTop (𝓝 R) := (hEnt.const_mul (a / 2)).sub_const ε
  have hR0 : 0 ≤ R := ge_of_tendsto hRt (Eventually.of_forall fun k => by
    have ht := hviol (φ k)
    linarith [particleEnergy_nonneg (f (φ k))])
  have hUpper : liminf (fun k => ENNReal.ofReal (particleEnergy A (Ns (φ k)) (f (φ k)))) atTop ≤
      ENNReal.ofReal R := by
    calc
      _ ≤ liminf (fun k => ENNReal.ofReal
          (a / 2 * (particleEntropy A (Ns (φ k)) (f (φ k))).toReal - ε)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => ENNReal.ofReal_le_ofReal
          (by have ht := hviol (φ k); linarith))
      _ = _ := (ENNReal.tendsto_ofReal hRt).liminf_eq
  have hForm := hLow.trans hUpper
  have hFormFin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hForm
  have hFormReal : (gaussForm (lamShift S.lam) γ F).toReal ≤ R := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hForm
    rw [ENNReal.toReal_ofReal hR0] at ht
    exact ht
  have hLSI := ((t01_gaussian_lsi_poincare S aux A D hD hlam1 he.mono
    ⟨σ, hσ, hbound⟩ hγ).2.2 F hF).1
  have hLSIReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) hGpos.ne') hFormFin) hLSI
  rw [ENNReal.toReal_mul, ENNReal.toReal_div] at hLSIReal
  norm_num only [ENNReal.toReal_ofNat] at hLSIReal
  change (ent γ (fun z => F z ^ 2)).toReal ≤
    2 / a * (gaussForm (lamShift S.lam) γ F).toReal at hLSIReal
  have hmul := mul_le_mul_of_nonneg_left hLSIReal ha.le
  have heq : a * (2 / a * (gaussForm (lamShift S.lam) γ F).toReal) =
      2 * (gaussForm (lamShift S.lam) γ F).toReal := by field_simp [ha.ne']
  rw [heq] at hmul
  dsimp only [R] at hFormReal
  nlinarith

/-- Direct Lipschitz data and positive scalar rate give an actual symmetric bounded
comparison at a positive real rate at least the scalar rate. -/
theorem actual_positive_symmetric_bounded_comparison (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b) :
    ∃ a : ℝ, 0 < a ∧ scalarRate A b ≤ ENNReal.ofReal a ∧
      ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
        ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
          Measurable f.1 → IsSymmetricParticleTest f → (∀ X, |f X| ≤ M) →
            particleEnergy A N f ≤ E0 →
            ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
              ENNReal.ofReal (particleEnergy A N f + ε) := by
  obtain ⟨μ, hminval, -, hcoerc, hfix, c, C, p, -, -, hC, hp, -, hN⟩ :=
    t01_positive_rate_reference_data A hA b hrate
  have hmin : ∀ ν : ProbabilityMeasure (Torus d), DGPS.freeEnergy A μ ≤ DGPS.freeEnergy A ν := by
    intro ν
    rw [hminval]
    exact iInf_le (fun ν => DGPS.freeEnergy A ν) ν
  obtain ⟨S, aux, D, H, hS, hmono, hzero, hgap, hC1, heig, hD, hH, hlap, hgrad, hw⟩ :=
    exists_equilibrium_spectral_hessian_data A hA hd μ hmin
  have he := legacy_reference_eigenbasis S aux hmono heig
  have hμS : specProbability_LIP016 S = μ := ProbabilityMeasure.toMeasure_injective hS
  have hfixS : (frozenGibbs A (specProbability_LIP016 S)).measure = S.mu := by
    rw [hμS, hfix, hS]
  have hHS : IsCoerciveDensityHessian A (specProbability_LIP016 S) := by rw [hμS]; exact hcoerc
  have hNS : ∀ N : ℕ+,
      |Real.log (centeredParticleNormalizer A (specProbability_LIP016 S) N)| ≤ C ∧
      ∫ X, centeredParticleDensity A (specProbability_LIP016 S) N X ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu) ≤ C := by
    intro N
    simpa only [hμS, hS] using And.intro (hN N).1 (hN N).2.1
  have hpos1 : 0 < S.lam 1 := by simpa only [hzero] using hgap
  have htop : Tendsto S.lam atTop atTop := by
    have ht : Tendsto (fun n : ℕ => aux.a * (n : ℝ) ^ (2 / (d : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop aux.a_pos ((tendsto_rpow_atTop
        (by positivity : 0 < 2 / (d : ℝ))).comp tendsto_natCast_atTop_atTop)
    exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 1).mono fun n hn => aux.weyl n hn) ht
  have hgradS : IsWeakGradient (frozenPotential A S.mu) (smoothGrad (frozenPotential A S.mu)) := by
    simpa only [hS] using hgrad
  have hlapS : ∀ j, IsWeakLaplacian (S.v j) (fun z =>
      inner ℝ (smoothGrad (frozenPotential A S.mu) z) (smoothGrad (S.v j) z) - S.lam j * S.v j z) := by
    simpa only [hS] using hlap
  obtain ⟨σ, hσ, hbound⟩ := hHS
  have P := t01CovarianceMatrix_symPkg S aux A D hD hσ hbound
  have hlamBase : 0 < lamShift S.lam 0 := hpos1
  have hlamLower : ∀ i, lamShift S.lam 0 ≤ lamShift S.lam i :=
    fun i => hmono (by omega)
  have hGpos := lamG_pos P.pos P.Csymm P.nn P.up (fun j => (P.inv j).1) hlamBase hlamLower
  have hGtop := lamG_lt_top P.Csymm P.nn P.inv (lamShift S.lam)
  let a := (lamG (lamShift S.lam) (t01CovarianceMatrix S A)).toReal
  refine ⟨a, ENNReal.toReal_pos hGpos.ne' hGtop.ne, ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal hGtop.ne]
    exact t01_scalarRate_le_lamG S aux A hA b (by rw [hμS]; exact hmin)
      ⟨σ, hσ, hbound⟩ D hD
  · intro M E0 ε hM hE hε
    exact (actual_symmetric_bounded_comparison A hA S aux D hD hfixS he hC1 hzero hpos1 htop
      ⟨σ, hσ, hbound⟩ H hH hgradS hlapS hp hC.le hNS M E0 ε hM hE hε).mono
        fun N hN f _ hs hB hEf => hN f hs hB hEf

end DGPS.Lipschitz
