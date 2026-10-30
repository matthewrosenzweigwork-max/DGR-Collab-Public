import DGPS.Lipschitz.T01ParticlePoincare

/-!
# Eventual Poincare inequalities on the actual symmetric particle domain

The measurable representative, affine normalization, two-sided truncation, and affine
entropy test retain the genuine permutation-invariance predicate. The only analytic inputs
are bounded comparison on symmetric measurable tests and one uniform defective inequality.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Affine normalization retains actual a.e. permutation invariance. -/
theorem normalize_symmetric_particle_poincare_violator {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) (hm : Measurable f.1) (hsym : IsSymmetricParticleTest f) {ρ : ℝ} (hρ : 0 < ρ)
    (hviol : particleEnergy A N f < ρ *
      ((∫ x, f x ^ 2 ∂particleLaw A N) - (∫ x, f x ∂particleLaw A N) ^ 2)) :
    ∃ g : ParticleH1 A N, IsSymmetricParticleTest g ∧ Measurable g.1 ∧
      (∫ x, g x ∂particleLaw A N) = 0 ∧
      (∫ x, g x ^ 2 ∂particleLaw A N) = 1 ∧ particleEnergy A N g < ρ := by
  have hf := (isParticleWeakGradient_particleWeakGradient f).memLp
  let m : ℝ := ∫ x, f x ∂particleLaw A N
  let v : ℝ := ProbabilityTheory.variance f.1 (particleLaw A N)
  have hv : v = (∫ x, f x ^ 2 ∂particleLaw A N) - m ^ 2 :=
    ProbabilityTheory.variance_eq_sub hf
  have hv0 : 0 < v := by
    have hE := particleEnergy_nonneg f
    rw [← hv] at hviol
    nlinarith
  let a : ℝ := (Real.sqrt v)⁻¹
  have ha2 : a ^ 2 = v⁻¹ := by dsimp [a]; rw [inv_pow, Real.sq_sqrt hv0.le]
  let g : ParticleH1 A N := ⟨fun x => a * f x + (-a * m), f.2.affine a (-a * m)⟩
  refine ⟨g, hsym.comp_scalar (fun z => a * z + (-a * m)) rfl,
    (hm.const_mul a).add measurable_const, ?_, ?_, ?_⟩
  · change (∫ x, a * f x + (-a * m) ∂particleLaw A N) = 0
    rw [integral_add ((hf.integrable (by norm_num)).const_mul a) (integrable_const _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    dsimp [m]
    ring
  · have heq : (fun x => g x ^ 2) = fun x => a ^ 2 * (f x - m) ^ 2 := by
      funext x
      change (a * f x + (-a * m)) ^ 2 = _
      ring
    rw [heq, integral_const_mul]
    have hvint : v = ∫ x, (f x - m) ^ 2 ∂particleLaw A N :=
      ProbabilityTheory.variance_eq_integral hf.aemeasurable
    rw [← hvint, ha2, inv_mul_cancel₀ hv0.ne']
  · rw [particleEnergy_affine f g a (-a * m) rfl, ha2]
    calc v⁻¹ * particleEnergy A N f = particleEnergy A N f / v := by ring
      _ < ρ := (div_lt_iff₀ hv0).mpr (by simpa only [hv] using hviol)

/-- Bounded comparison below a rate and one uniform symmetric defect imply eventual
Poincare on the full symmetric Sobolev domain. No Poincare or particle-rate limit is assumed. -/
theorem eventual_symmetric_particle_poincare_of_bounded_comparison {d : ℕ} (A : InteractionData d)
    {b : ℝ} (hb : 0 < b)
    (hcomp : ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ g : ParticleH1 A N,
        Measurable g.1 → IsSymmetricParticleTest g → (∀ x, |g x| ≤ M) → particleEnergy A N g ≤ E0 →
        ENNReal.ofReal (b / 2) * particleEntropy A N g ≤
          ENNReal.ofReal (particleEnergy A N g + ε))
    (hdef : ∃ D C : ℝ, ∀ (N : ℕ+) (g : ParticleH1 A N),
      IsSymmetricParticleTest g → particleEntropy A N g ≤ ENNReal.ofReal
        (D * particleEnergy A N g + C * ∫ x, g x ^ 2 ∂particleLaw A N))
    {ρ : ℝ} (hρb : ρ < b) :
    ∀ᶠ N : ℕ+ in atTop, ∀ g : ParticleH1 A N,
      IsSymmetricParticleTest g → ρ * ((∫ x, g x ^ 2 ∂particleLaw A N) -
        (∫ x, g x ∂particleLaw A N) ^ 2) ≤ particleEnergy A N g := by
  by_cases hρ : 0 < ρ
  · by_contra hfail
    classical
    have hfreq : ∃ᶠ N : ℕ+ in atTop, ∃ f : ParticleH1 A N, IsSymmetricParticleTest f ∧
        particleEnergy A N f < ρ * ((∫ x, f x ^ 2 ∂particleLaw A N) -
          (∫ x, f x ∂particleLaw A N) ^ 2) := by
      refine (Filter.not_eventually.mp hfail).mono ?_
      intro N hN
      simp only [not_forall, not_le] at hN
      obtain ⟨f, hs, hv⟩ := hN
      exact ⟨f, hs, hv⟩
    have hex : ∀ n : ℕ, ∃ N : ℕ+, Nat.succPNat n ≤ N ∧ ∃ f : ParticleH1 A N, IsSymmetricParticleTest f ∧
        particleEnergy A N f < ρ * ((∫ x, f x ^ 2 ∂particleLaw A N) -
          (∫ x, f x ∂particleLaw A N) ^ 2) := fun n =>
      (Filter.frequently_atTop.mp hfreq) (Nat.succPNat n)
    choose Ns hNs f hfSym hf using hex
    have hNt : Tendsto Ns atTop atTop := by
      rw [tendsto_atTop]
      intro M
      filter_upwards [eventually_ge_atTop (M : ℕ)] with n hn
      exact le_trans (by change (M : ℕ) ≤ n + 1; omega) (hNs n)
    have hnorm : ∀ k, ∃ g : ParticleH1 A (Ns k), IsSymmetricParticleTest g ∧ Measurable g.1 ∧
        (∫ x, g x ∂particleLaw A (Ns k)) = 0 ∧
        (∫ x, g x ^ 2 ∂particleLaw A (Ns k)) = 1 ∧ particleEnergy A (Ns k) g < ρ := by
      intro k
      obtain ⟨u, huM, hfu, hEu, -, hsu⟩ := exists_measurable_particleH1_representative (f k)
      have hi : (∫ x, u x ∂particleLaw A (Ns k)) = ∫ x, f k x ∂particleLaw A (Ns k) :=
        integral_congr_ae hfu.symm
      have hi2 : (∫ x, u x ^ 2 ∂particleLaw A (Ns k)) = ∫ x, f k x ^ 2 ∂particleLaw A (Ns k) :=
        integral_congr_ae (hfu.symm.mono fun x hx => congrArg (fun t : ℝ => t ^ 2) hx)
      apply normalize_symmetric_particle_poincare_violator u huM (hsu.mp (hfSym k)) hρ
      rw [← hEu, hi, hi2]
      exact hf k
    choose g hsym hm hz hone hEg using hnorm
    obtain ⟨D, C, hDC⟩ := hdef
    let R : ℝ := |D| * ρ + |C|
    have hR : 0 ≤ R := by positivity
    have hUI : Analysis.UniformSquareIntegrable (fun k => particleLaw A (Ns k))
        (fun k => (g k).1) := by
      intro ε hε
      refine ⟨Real.exp (2 + R / ε), fun k => ?_⟩
      have hbound : particleEntropy A (Ns k) (g k) ≤ ENNReal.ofReal R := by
        refine (hDC (Ns k) (g k) (hsym k)).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hone k, mul_one]
        have h1 : D * particleEnergy A (Ns k) (g k) ≤ |D| * ρ :=
          (mul_le_mul_of_nonneg_right (le_abs_self D) (particleEnergy_nonneg (g k))).trans
            (mul_le_mul_of_nonneg_left (hEg k).le (abs_nonneg _))
        dsimp [R]
        linarith [le_abs_self C]
      have htail := Analysis.tail_integral_le_of_entropy_le
        (fun x => sq_nonneg (g k x)) ((hm k).pow_const 2)
        (isParticleWeakGradient_particleWeakGradient (g k)).memLp.integrable_sq
        (M' := 1) zero_lt_one (hone k).le hR hε hbound
      simpa only [one_mul] using htail
    apply poincare_sequence_contradiction_of_scalar_stable_class A
      (fun N f => Measurable f.1 ∧ IsSymmetricParticleTest f)
      (fun N f u ψ hψ hf hu => ?_) hb hρ.le hρb
      (fun M E0 ε hM hE0 hε => (hcomp M E0 ε hM hE0 hε).mono
        fun N hN u hu => hN u hu.1 hu.2)
      Ns hNt g (fun k => ⟨hm k, hsym k⟩) hz hone (fun k => (hEg k).le) hUI
    exact ⟨by rw [hu]; exact hψ.measurable.comp hf.1, hf.2.comp_scalar ψ hu⟩
  · refine Filter.Eventually.of_forall fun N g _ => ?_
    have hv := ProbabilityTheory.variance_nonneg g.1 (particleLaw A N)
    rw [ProbabilityTheory.variance_eq_sub
      (isParticleWeakGradient_particleWeakGradient g).memLp] at hv
    exact (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hρ) hv).trans (particleEnergy_nonneg g)

end DGPS.Lipschitz
