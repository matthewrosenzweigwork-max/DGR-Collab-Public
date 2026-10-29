import DGPS.FiniteN.Tools.AuxiliaryTransfer
import DGPS.FiniteN.Tools.UnitTorusNormalization
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.FiniteN.Tools.ConditionalMeanDerivative
import Mathlib

/-!
# FIN013b: the auxiliary-to-unrestricted Poincare transfer on the torus

Instantiation of the abstract transfer `DGPS.FiniteN.auxiliary_to_unrestricted_particle_poincare`
(FIN013) on the particle torus `(𝕋^d)^N` with the Gibbs law `particleLaw A N`:

* (a) under the finite-rank interaction hypothesis `V = U - h·φ`, `W(x,y) = -φ(x)ᵀ D φ(y)` the
  Gibbs law `particleLaw A N` is the Hubbard particle law (`hubbardParticleLaw_eq_particleLaw`);
* (b) smooth periodic tests are measurable and bounded, and so is their classical carre-du-champ
  (`smoothGamma`);
* (c) the smooth-test Poincare inequality extends to all of `ParticleH1 A N` by FIN026
  (`fixed_n_weighted_sobolev_extension`).

## Design choices (R5 notes)

* The finite-rank interaction hypothesis is stated pointwise on the data `A`, with `m = haar d`:
  `A.V x = U x - h ⬝ᵥ φ x` and `A.W x y = -(φ x ⬝ᵥ D *ᵥ φ y)`, so that
  `-H_N = -∑U + h·S + SᵀDS/(2N)`, plus `HubbardHyp (haar d) U φ`.
* The test class on the torus is `IsSmoothPeriodicParticle` with carre-du-champ `smoothGamma`
  `= ofReal (∑ᵢⱼ (∂ᵢⱼ f)²)`; the conditional inequality `hcond` is assumed in this form.
* The conclusion is `Var_{P_N} f ≤ K (1 + N L²/λ_aux) E_N(f)` for every `f : ParticleH1 A N`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.Tools.AuxiliaryTransferTorus

open DGPS DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.Tools.AuxiliaryTransfer
  DGPS.FiniteN.Tools.WeightedSobolev

variable {d : ℕ} {N : ℕ+}

/-! ### (a) The Hubbard particle law is the Gibbs law -/

section LawEq

variable {k : ℕ} (A : InteractionData d) (N : ℕ+) (U : Torus d → ℝ) (φ : Torus d → Fin k → ℝ)
  (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ)

theorem sum_sum_dot (x : Fin N → Torus d) :
    ∑ i, ∑ j, φ (x i) ⬝ᵥ D *ᵥ φ (x j) = fieldSum φ x ⬝ᵥ D *ᵥ fieldSum φ x := by
  unfold fieldSum
  simp [Matrix.mulVec_sum, dotProduct_sum, sum_dotProduct]
  exact Finset.sum_comm

variable {A N U φ D h}

theorem particleWeight_eq (hV : ∀ x, A.V x = U x - h ⬝ᵥ φ x)
    (hW : ∀ x y, A.W x y = -(φ x ⬝ᵥ D *ᵥ φ y)) (x : ParticleSpace d N) :
    particleWeight U φ D h N x = Real.exp (-particleHamiltonian A N x) := by
  unfold particleWeight particleHamiltonian
  congr 1
  have h1 : ∑ i, A.V (x i) = ∑ i, U (x i) - h ⬝ᵥ fieldSum φ x := by
    simp only [hV, Finset.sum_sub_distrib]
    unfold fieldSum
    rw [dotProduct_sum]
  have h2 : ∑ i, ∑ j, A.W (x i) (x j) = -(fieldSum φ x ⬝ᵥ D *ᵥ fieldSum φ x) := by
    simp only [hW, Finset.sum_neg_distrib]
    rw [sum_sum_dot]
  rw [h1, h2]
  ring

theorem particleMass_eq (hV : ∀ x, A.V x = U x - h ⬝ᵥ φ x)
    (hW : ∀ x y, A.W x y = -(φ x ⬝ᵥ D *ᵥ φ y)) :
    particleMass D h U φ (haar d) N = ENNReal.ofReal (particlePartition A N) := by
  unfold particleMass particlePartition
  simp_rw [particleWeight_eq hV hW]
  rw [ofReal_integral_eq_lintegral_ofReal (DGPS.Particle.exp_neg_hamiltonian_integrable A N)
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  rfl

/-- (a) Under the finite-rank interaction hypothesis the Hubbard particle law is `P_N`. -/
theorem hubbardParticleLaw_eq_particleLaw (hV : ∀ x, A.V x = U x - h ⬝ᵥ φ x)
    (hW : ∀ x y, A.W x y = -(φ x ⬝ᵥ D *ᵥ φ y)) :
    hubbardParticleLaw D h U φ (haar d) N = particleLaw A N := by
  have hZ := DGPS.Particle.particlePartition_pos A N
  rw [DGPS.Particle.particleLaw_eq_smul, hubbardParticleLaw, particleMass_eq hV hW,
    ENNReal.ofReal_inv_of_pos hZ]
  congr 2
  funext x
  rw [particleWeight_eq hV hW]

end LawEq

/-! ### (b) Smooth periodic tests are measurable and bounded -/

theorem measurable_sec :
    Measurable fun x : ParticleSpace d N => fun i => SharpLSI.secT (x i) :=
  Measurable.of_eval fun i => SharpLSI.measurable_secT.comp (measurable_pi_apply i)

theorem measurable_bounded_comp_sec {G : (Fin N → Fin d → ℝ) → ℝ} (hG : Continuous G) :
    Measurable (fun x : ParticleSpace d N => G (fun i => SharpLSI.secT (x i))) ∧
      ∃ B : ℝ, ∀ x : ParticleSpace d N, |G (fun i => SharpLSI.secT (x i))| ≤ B := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin N => Set.Icc (0 : Fin d → ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  exact ⟨hG.measurable.comp measurable_sec, C, fun x => by
    simpa using hC _ (Set.mem_univ_pi.2 fun i => secT_mem_Icc (x i))⟩

theorem measurable_bounded_of_smooth {f : ParticleSpace d N → ℝ}
    (hf : IsSmoothPeriodicParticle f) :
    Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B := by
  have h := measurable_bounded_comp_sec (d := d) (N := N) hf.continuous
  have e : ∀ x : ParticleSpace d N, particleLift (fun i => SharpLSI.secT (x i)) = x := fun x => by
    funext i; simp [particleLift, torusLift, SharpLSI.liftT_secT]
  simpa [Function.comp_def, e] using h

theorem measurable_bounded_partial_of_smooth {f : ParticleSpace d N → ℝ}
    (hf : IsSmoothPeriodicParticle f) (i : Fin N) (j : Fin d) :
    Measurable (particlePartial i j f) ∧ ∃ B : ℝ, ∀ x, |particlePartial i j f x| ≤ B :=
  measurable_bounded_comp_sec ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- The classical carre-du-champ `∑ᵢⱼ (∂ᵢⱼ f)²` of a smooth periodic test. -/
noncomputable def smoothGamma (f : ParticleSpace d N → ℝ) (x : ParticleSpace d N) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ i, ∑ j, particlePartial i j f x ^ 2)

theorem measurable_smoothGamma_of_smooth {f : ParticleSpace d N → ℝ}
    (hf : IsSmoothPeriodicParticle f) : Measurable (smoothGamma f) := by
  unfold smoothGamma
  refine ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ?_)
  exact (measurable_bounded_partial_of_smooth hf i j).1.pow_const 2

theorem lintegral_smoothGamma_of_smooth (A : InteractionData d)
    {f : ParticleSpace d N → ℝ} (hf : IsSmoothPeriodicParticle f) :
    ∫⁻ x, smoothGamma f x ∂particleLaw A N =
      ENNReal.ofReal (particleSmoothEnergy A f) := by
  unfold smoothGamma particleSmoothEnergy
  rw [ofReal_integral_eq_lintegral_ofReal]
  · refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (memLp_two_law_partial_of_smooth A hf i j).integrable_sq
  · exact Filter.Eventually.of_forall fun x =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### (c) Extension to `H¹(P_N)` -/

/-- A Poincare inequality for all smooth periodic tests, in the `PoincareAt` form for the Gibbs
law, is the classical one with the smooth energy. -/
theorem variance_le_of_poincareAt (A : InteractionData d)
    {C : ℝ} (hC : 0 ≤ C)
    (H : PoincareAt (particleLaw A N) IsSmoothPeriodicParticle smoothGamma C)
    {f : ParticleSpace d N → ℝ} (hf : IsSmoothPeriodicParticle f) :
    variance f (particleLaw A N) ≤ C * particleSmoothEnergy A f := by
  have h1 := H f hf
  rw [← (memLp_two_law_of_smooth A hf).ofReal_variance_eq, lintegral_smoothGamma_of_smooth A hf,
    ← ENNReal.ofReal_mul hC] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (integral_nonneg fun x =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))).1 h1

end DGPS.FiniteN.Tools.AuxiliaryTransferTorus

namespace DGPS.FiniteN

open MeasureTheory ProbabilityTheory Matrix
open DGPS DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.Tools.AuxiliaryTransfer
  DGPS.FiniteN.Tools.AuxiliaryTransferTorus

/-- **FIN013b.** Torus instantiation of FIN013.  Let the interaction be of finite rank,
`V = U - h·φ`, `W(x,y) = -φ(x)ᵀ D φ(y)` with `D` positive definite.  If `η_N` has Poincare rate
`lam` (bounded differentiable tests), the conditional one-site laws `q_w^{⊗N}` satisfy the smooth
test Poincare inequality with inverse constants `C(w)`, `E[C(w) | x] ≤ K` for every particle
configuration `x`, and `|φ| ≤ L`, then for every `f ∈ H¹(P_N)` (no symmetry)
`Var_{P_N} f ≤ K (1 + N L²/lam) E_N(f)`. -/
theorem auxiliary_to_unrestricted_particle_poincare_torus {d k : ℕ} (A : InteractionData d)
    (N : ℕ+) (U : Torus d → ℝ) (φ : Torus d → Fin k → ℝ) {D : Matrix (Fin k) (Fin k) ℝ}
    (hD : D.PosDef) (h : Fin k → ℝ) (hyp : HubbardHyp (haar d) U φ)
    (hV : ∀ x, A.V x = U x - h ⬝ᵥ φ x) (hW : ∀ x y, A.W x y = -(φ x ⬝ᵥ D *ᵥ φ y))
    {lam : ℝ} (hlam : 0 < lam)
    (haux : PoincareAt (auxLaw D h U φ (haar d) N) AuxTest auxGradSq lam⁻¹)
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ (haar d) N w) IsSmoothPeriodicParticle smoothGamma
      (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x))
      ≤ ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    ∀ f : ParticleH1 A N,
      variance f.1 (particleLaw A N) ≤ K * (1 + N * L ^ 2 / lam) * particleEnergy A N f := by
  have hmain := auxiliary_to_unrestricted_particle_poincare hyp hD h N hlam haux
    (Sm := IsSmoothPeriodicParticle) (Γ := smoothGamma)
    (fun f hf => measurable_bounded_of_smooth hf) (fun f hf => measurable_smoothGamma_of_smooth hf) hC hcond hK0 hK hL
  rw [hubbardParticleLaw_eq_particleLaw hV hW] at hmain
  have hC0 : 0 ≤ K * (1 + N * L ^ 2 / lam) := by positivity
  exact (fixed_n_weighted_sobolev_extension A N).2.2.1 _ fun f hf =>
    variance_le_of_poincareAt A hC0 hmain hf

end DGPS.FiniteN
