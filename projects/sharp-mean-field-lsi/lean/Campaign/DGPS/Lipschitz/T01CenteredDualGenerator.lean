import DGPS.Lipschitz.T01ParticleDensityGradient

/-!
# The dual generator at the actual frozen reference

The integration-by-parts identity only needs the canonical Hamiltonian gradient split.
This retains the original interaction and its particle law, while the eigen-equation uses
the frozen reference potential and the residual force is the actual centered force.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff InnerProductSpace RealInnerProductSpace

namespace DGPS.Lipschitz

open DGPS DGPS.Analysis DGPS.Particle DGPS.Lipschitz.ParabolicChainRule
  DGPS.Lipschitz.WeightedGenerator DGPS.Particle.ProductForceFisher

variable {d : ℕ} {N : ℕ+}

/-- The density-weighted cylinder derivative uses only the actual Hamiltonian gradient. -/
theorem t01_dg_psi_of_hamiltonian (A : InteractionData d) {n : ℕ} {v : Fin n → Torus d → ℝ}
    {H : Fin n → Fin d → Fin d → Torus d → ℝ}
    (hv : ∀ i, IsC1Periodic (v i)) (hH : ∀ i, IsWeakHessian (v i) (smoothGrad (v i)) (H i))
    {c : (Fin n → ℝ) → ℝ} (hc : ContDiff ℝ 2 c)
    {gV : Torus d → Tangent d} {gU : ParticleSpace d N → Fin N → Tangent d}
    (hHamiltonian : IsParticleHaarWeakGradient N (particleHamiltonian A N)
      (fun x l => gV (x l) + gU x l)) (l : Fin N) (j : Fin d) :
    ∃ g : ParticleSpace d N → Fin N → Tangent d,
      IsParticleHaarWeakGradient N (fun x => particleDensity A N x *
        ∑ i, (Real.sqrt (N : ℝ))⁻¹ * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) g ∧
      ∀ x, g x l j =
        (∑ i, (Real.sqrt (N : ℝ))⁻¹ * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          (-particleDensity A N x * (gV (x l) j + gU x l j)) +
        particleDensity A N x * ∑ i, (Real.sqrt (N : ℝ))⁻¹ *
          (smoothGrad (v i) (x l) j * ((Real.sqrt (N : ℝ))⁻¹ *
            ∑ p, dc2 c i p (dualZ N v x) * smoothGrad (v p) (x l) j) +
            dc c i (dualZ N v x) * H i j j (x l)) := by
  classical
  have hρ := dg_density A hHamiltonian
  have hρc : Continuous (particleDensity A N) := particleDensity_continuous A N
  have ha : ∀ i, IsParticleHaarWeakGradient N (fun x => dc c i (dualZ N v x)) _ :=
    fun i => dg_cyl hv (contDiff_dc hc i)
  have hq : ∀ i, IsParticleHaarWeakGradient N (fun x : ParticleSpace d N => smoothGrad (v i) (x l) j)
      _ := fun i => dg_slot l (hessian_col (hH i) j)
  have hac : ∀ i, Continuous (fun x : ParticleSpace d N => dc c i (dualZ N v x)) := fun i =>
    ((contDiff_dc hc i).continuous).comp (continuous_dualZ hv)
  have hqc : ∀ i, Continuous (fun x : ParticleSpace d N => smoothGrad (v i) (x l) j) := fun i => by
    simp only [smoothGrad_apply]
    exact ((hv i).continuous_coordPartial j).comp (continuous_apply l)
  have hprod := fun i => dg_mul (ha i) (hq i) (hac i) (hqc i)
  have hterm := fun i => dg_smul (hprod i) (Real.sqrt (N : ℝ))⁻¹
  have hsum := dg_sum (N := N) Finset.univ (fun i _ => hterm i)
  have hΨc : Continuous (fun x : ParticleSpace d N =>
      ∑ i, (Real.sqrt (N : ℝ))⁻¹ * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul ((hac i).mul (hqc i))
  have hfin := dg_mul hρ hsum hρc hΨc
  refine ⟨_, hfin, fun x => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sum, smoothGrad_apply]
  simp [vecOf, dc2]

theorem t01_weak_particle_dual_generator_of_hamiltonian (A : InteractionData d) {n : ℕ}
    (lam : Fin n → ℝ) (v : Fin n → Torus d → ℝ) (H : Fin n → Fin d → Fin d → Torus d → ℝ)
    (hv : ∀ i, IsC1Periodic (v i)) (hH : ∀ i, IsWeakHessian (v i) (smoothGrad (v i)) (H i))
    {gV : Torus d → Tangent d}
    (hlap : ∀ i, IsWeakLaplacian (v i) (fun z => ⟪gV z, smoothGrad (v i) z⟫_ℝ - lam i * v i z))
    {c : (Fin n → ℝ) → ℝ} (hc : ContDiff ℝ 2 c)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hHamiltonian : IsParticleHaarWeakGradient N (particleHamiltonian A N)
      (fun x l => gV (x l) + gU x l)) (f : ParticleH1 A N) :
    ∃ hmem : MemParticleH1 A N (fun x => c (dualZ N v x)),
      2 * ∫ x, f.1 x * dualGen N lam v c gU x ∂particleLaw A N -
        particleEnergy A N ⟨_, hmem⟩ ≤ particleEnergy A N f := by
  classical
  set s : ℝ := (Real.sqrt (N : ℝ))⁻¹ with hs
  have hss : s * s = (N : ℝ)⁻¹ := by
    rw [hs, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by norm_num)
  obtain ⟨gF, hF1, hgF⟩ : ∃ gF : ParticleSpace d N → Fin N → Tangent d,
      IsParticleHaarWeakGradient N (fun x => c (dualZ N v x)) gF ∧
      ∀ x l j, gF x l j = ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j) :=
    ⟨_, dg_cyl hv hc1, fun x l j => by
      simp [smoothGrad_apply, Finset.mul_sum, dc, hs]⟩
  have hFA := (isParticleWeakGradient_iff A N _ _).2 hF1
  refine ⟨⟨_, hFA⟩, ?_⟩
  have hfA := isParticleWeakGradient_particleWeakGradient f
  have hfH := (isParticleWeakGradient_iff A N _ _).1 hfA
  have hE := dg_energy A f ⟨_, ⟨_, hFA⟩⟩ hfA hFA
  suffices hB : ∫ x, ∑ i, ∑ j, particleWeakGradient f x i j * gF x i j ∂particleLaw A N =
      ∫ x, f.1 x * dualGen N lam v c gU x ∂particleLaw A N by linarith
  have hex := fun l j => t01_dg_psi_of_hamiltonian (N := N) A hv hH hc hHamiltonian l j
  choose g hg hgx using hex
  have hρ : Continuous (particleDensity A N) := particleDensity_continuous A N
  have hI1 : ∀ l j, Integrable (fun x => (particleDensity A N x *
      ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
        particleWeakGradient f x l j) (particleHaar d N) := fun l j =>
    (hg l j).memLp.integrable_mul (memLp_particleCoord hfH.memLp_grad l j)
  have hI2 : ∀ l j, Integrable (fun x => g l j x l j * f.1 x) (particleHaar d N) := fun l j =>
    (memLp_particleCoord (hg l j).memLp_grad l j).integrable_mul hfH.memLp
  have hterm : ∀ l j, ∫ x, (particleDensity A N x *
      ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
        particleWeakGradient f x l j ∂particleHaar d N =
      -∫ x, g l j x l j * f.1 x ∂particleHaar d N := fun l j =>
    dg_ibp (hg l j) hfH l j
  -- the a.e. Laplacian identity in every slot
  have hlapae : ∀ i, ∀ᵐ z ∂haar d, ∑ j, H i j j z =
      ⟪gV z, smoothGrad (v i) z⟫_ℝ - lam i * v i z := fun i =>
    dg_laplacian_ae (hH i) (hlap i)
  have hae : ∀ᵐ x ∂particleHaar d N, ∑ l, ∑ j, g l j x l j =
      -particleDensity A N x * dualGen N lam v c gU x := by
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun l => dg_slot_ae (hlapae i) l]
      with x hx
    have hl : ∀ i l, ∑ j, H i j j (x l) =
        ∑ j, gV (x l) j * smoothGrad (v i) (x l) j - lam i * v i (x l) := fun i l => by
      rw [hx i l, dg_inner]
    have e := dg_pointwise (N := N) s (particleDensity A N x) hss
      (fun i l j => smoothGrad (v i) (x l) j) (fun i l j => H i j j (x l))
      (fun l j => gV (x l) j) (fun l j => gU x l j) (fun i l => v i (x l))
      (fun i => dc c i (dualZ N v x)) lam (fun i p => dc2 c i p (dualZ N v x)) hl
    simp only [hgx]
    refine e.trans ?_
    simp only [dualGen, dualA, dualD, dualZ, dg_inner, hs]
  rw [integral_particleLaw, integral_particleLaw]
  have h1 : ∀ x, particleDensity A N x * ∑ i, ∑ j, particleWeakGradient f x i j * gF x i j =
      ∑ l, ∑ j, (particleDensity A N x *
        ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          particleWeakGradient f x l j := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgF]
    ring
  have h2 : ∑ l, ∑ j, ∫ x, g l j x l j * f.1 x ∂particleHaar d N =
      ∫ x, (∑ l, ∑ j, g l j x l j) * f.1 x ∂particleHaar d N := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun j _ => hI2 l j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ (fun j _ => hI2 l j)]
  calc ∫ x, particleDensity A N x * ∑ i, ∑ j, particleWeakGradient f x i j * gF x i j
        ∂particleHaar d N
      = ∫ x, ∑ l, ∑ j, (particleDensity A N x *
        ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          particleWeakGradient f x l j ∂particleHaar d N := integral_congr_ae
          (Filter.Eventually.of_forall h1)
    _ = ∑ l, ∑ j, ∫ x, (particleDensity A N x *
        ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          particleWeakGradient f x l j ∂particleHaar d N := by
      rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun j _ => hI1 l j)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_finsetSum _ (fun j _ => hI1 l j)]
    _ = ∑ l, ∑ j, -∫ x, g l j x l j * f.1 x ∂particleHaar d N :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => hterm l j
    _ = -∫ x, (∑ l, ∑ j, g l j x l j) * f.1 x ∂particleHaar d N := by
      rw [← h2]
      simp [Finset.sum_neg_distrib]
    _ = ∫ x, particleDensity A N x * (f.1 x * dualGen N lam v c gU x) ∂particleHaar d N := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
      ring


/-- The weak particle dual generator identity with the actual frozen eigen-equation
and actual centered interaction force. -/
theorem t01_centered_weak_particle_dual_generator_identity (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {n : ℕ}
    (lam : Fin n → ℝ) (v : Fin n → Torus d → ℝ)
    (H : Fin n → Fin d → Fin d → Torus d → ℝ)
    (hv : ∀ i, IsC1Periodic (v i))
    (hH : ∀ i, IsWeakHessian (v i) (smoothGrad (v i)) (H i))
    {gμ : Torus d → Tangent d}
    (hμ : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) gμ)
    (hlap : ∀ i, IsWeakLaplacian (v i)
      (fun z => ⟪gμ z, smoothGrad (v i) z⟫_ℝ - lam i * v i z))
    {c : (Fin n → ℝ) → ℝ} (hc : ContDiff ℝ 2 c)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU)
    (f : ParticleH1 A N) :
    ∃ hmem : MemParticleH1 A N (fun x => c (dualZ N v x)),
      2 * ∫ x, f.1 x * dualGen N lam v c gU x ∂particleLaw A N -
        particleEnergy A N ⟨_, hmem⟩ ≤ particleEnergy A N f :=
  t01_weak_particle_dual_generator_of_hamiltonian A lam v H hv hH hlap hc
    (particleHamiltonian_centered_weakGradient A μ N hμ hU) f

end DGPS.Lipschitz
