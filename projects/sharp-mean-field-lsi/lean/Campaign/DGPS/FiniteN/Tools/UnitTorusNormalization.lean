import DGPS.Circle.AngularNormalization
import DGPS.Particle.Rates

/-!
# Angular to unit-torus normalization for the finite-`N` Gibbs system (FIN002)

For `θ_i = 2π x_i` the `N`-particle unit-period torus `(𝕋¹)^N` (`ParticleSpace 1 N`) is identified
coordinatewise with the angular torus `(AddCircle (2π))^N` (`angEquivN`), a measure-preserving
measurable equivalence (EX001, `DGPS.Circle.AngularNormalization.angEquiv`, applied in each
coordinate).  We define the angular Gibbs law, the angular `H¹` tests (weak gradients against smooth
`2π`-periodic tests), the angular Dirichlet energy `E_θ(f) = ∫ ∑ᵢ |∂_{θᵢ} f|² dP_N^θ` (no factor
`1/N`), the angular entropy, quotient and the rates `r_N^all`, `r_N^sym`, and prove
`DGPS.FiniteN.angular_to_unit_torus_normalization`:

* `E_x(f) = a₀ E_θ(f)` with `a₀ = 4π²`, entropy unchanged, tests correspond bijectively;
* `r_N^all (unit period) = a₀ · r_N^all (angular)` and likewise for `r_N^sym`;
* the Poincaré rate on the unit torus is `a₀` times the angular Poincaré rate (EX001).
-/

open MeasureTheory Real
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.UnitTorusNormalization

open DGPS DGPS.Circle.AngularNormalization

/-! ### The angular particle torus -/

/-- The angular particle torus `(AddCircle (2π))^N`. -/
abbrev AngParticleSpace (N : ℕ+) := Fin N → AngCircle

/-- Product normalized angular Haar measure. -/
noncomputable def angParticleHaar (N : ℕ+) : Measure (AngParticleSpace N) :=
  Measure.pi fun _ => angHaar

/-- Coordinatewise `θ_i = 2π x_i`. -/
noncomputable def angEquivN (N : ℕ+) : ParticleSpace 1 N ≃ᵐ AngParticleSpace N :=
  MeasurableEquiv.piCongrRight fun _ => angEquiv

theorem angEquivN_apply {N : ℕ+} (x : ParticleSpace 1 N) (i : Fin N) :
    angEquivN N x i = angEquiv (x i) := rfl

theorem measurePreserving_angEquivN (N : ℕ+) :
    MeasurePreserving (angEquivN N) (particleHaar 1 N) (angParticleHaar N) :=
  measurePreserving_pi (fun _ => haar 1) (fun _ => angHaar) (fun _ => measurePreserving_angEquiv)

theorem integral_comp_angEquivN {N : ℕ+} (f : AngParticleSpace N → ℝ) :
    ∫ x, f (angEquivN N x) ∂particleHaar 1 N = ∫ θ, f θ ∂angParticleHaar N :=
  (measurePreserving_angEquivN N).integral_comp' f

/-- The angular Hamiltonian `∑ᵢ V(θᵢ) + (2N)⁻¹ ∑ᵢ∑ⱼ W(θᵢ, θⱼ)`. -/
noncomputable def angHamiltonian (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) (N : ℕ+)
    (θ : AngParticleSpace N) : ℝ :=
  ∑ i, V (θ i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, W (θ i) (θ j)

/-- The angular partition function. -/
noncomputable def angPartition (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) (N : ℕ+) : ℝ :=
  ∫ θ, Real.exp (-angHamiltonian V W N θ) ∂angParticleHaar N

/-- The angular Gibbs density with respect to `angParticleHaar`. -/
noncomputable def angDensity (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) (N : ℕ+)
    (θ : AngParticleSpace N) : ℝ :=
  (angPartition V W N)⁻¹ * Real.exp (-angHamiltonian V W N θ)

/-- The angular Gibbs law. -/
noncomputable def angParticleLaw (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) (N : ℕ+) :
    Measure (AngParticleSpace N) :=
  (angParticleHaar N).withDensity fun θ => ENNReal.ofReal (angDensity V W N θ)

theorem angHamiltonian_angEquivN (A : InteractionData 1) (N : ℕ+) (x : ParticleSpace 1 N) :
    angHamiltonian (angV A) (angW A) N (angEquivN N x) = particleHamiltonian A N x := by
  simp [angHamiltonian, particleHamiltonian, angEquivN_apply, angV, angW]

theorem angPartition_eq (A : InteractionData 1) (N : ℕ+) :
    angPartition (angV A) (angW A) N = particlePartition A N := by
  unfold angPartition particlePartition
  rw [← integral_comp_angEquivN]
  simp_rw [angHamiltonian_angEquivN]

theorem angDensity_angEquivN (A : InteractionData 1) (N : ℕ+) (x : ParticleSpace 1 N) :
    angDensity (angV A) (angW A) N (angEquivN N x) = particleDensity A N x := by
  unfold angDensity particleDensity
  rw [angPartition_eq, angHamiltonian_angEquivN]

theorem map_particleLaw (A : InteractionData 1) (N : ℕ+) :
    (particleLaw A N).map (angEquivN N) = angParticleLaw (angV A) (angW A) N := by
  ext s hs
  rw [Measure.map_apply (angEquivN N).measurable hs, angParticleLaw, particleLaw,
    withDensity_apply _ ((angEquivN N).measurable hs), withDensity_apply _ hs]
  simp_rw [← angDensity_angEquivN]
  exact (measurePreserving_angEquivN N).setLIntegral_comp_preimage_emb
    (angEquivN N).measurableEmbedding (fun θ => ENNReal.ofReal (angDensity (angV A) (angW A) N θ)) s

theorem measurePreserving_angEquivN_law (A : InteractionData 1) (N : ℕ+) :
    MeasurePreserving (angEquivN N) (particleLaw A N) (angParticleLaw (angV A) (angW A) N) :=
  ⟨(angEquivN N).measurable, map_particleLaw A N⟩

/-! ### Angular smooth tests, partial derivatives and weak gradients -/

/-- Smooth `2π`-periodic function on the angular particle torus. -/
def IsSmoothAngParticle {N : ℕ+} (φ : AngParticleSpace N → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun s : Fin N → ℝ => φ fun k => (s k : AngCircle))

/-- The angular partial derivative `∂_{θᵢ} φ`, evaluated at the representative in `(0, 2π]^N`. -/
noncomputable def angParticlePartial {N : ℕ+} (i : Fin N) (φ : AngParticleSpace N → ℝ)
    (θ : AngParticleSpace N) : ℝ :=
  fderiv ℝ (fun s : Fin N → ℝ => φ fun k => (s k : AngCircle)) (fun k => angSec (θ k))
    (Pi.single i 1)

/-- `g = (∂_{θ₁} u, …, ∂_{θ_N} u)` is the angular weak gradient of `u` in `H¹(P_N^θ)`. -/
structure IsAngParticleWeakGradient (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) (N : ℕ+)
    (u : AngParticleSpace N → ℝ) (g : AngParticleSpace N → Fin N → ℝ) : Prop where
  memLp : MemLp u 2 (angParticleLaw V W N)
  memLp_grad : MemLp g 2 (angParticleLaw V W N)
  ibp : ∀ φ : AngParticleSpace N → ℝ, IsSmoothAngParticle φ → ∀ i : Fin N,
    ∫ θ, u θ * angParticlePartial i φ θ ∂angParticleHaar N =
      -∫ θ, g θ i * φ θ ∂angParticleHaar N

/-- Angular `H¹(P_N^θ)` tests. -/
def AngParticleH1 (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) (N : ℕ+) : Type :=
  {u : AngParticleSpace N → ℝ // ∃ g, IsAngParticleWeakGradient V W N u g}

/-- A chosen angular weak gradient. -/
noncomputable def angParticleGrad {V : AngCircle → ℝ} {W : AngCircle → AngCircle → ℝ} {N : ℕ+}
    (u : AngParticleH1 V W N) : AngParticleSpace N → Fin N → ℝ :=
  u.2.choose

theorem isAngParticleWeakGradient_grad {V : AngCircle → ℝ} {W : AngCircle → AngCircle → ℝ}
    {N : ℕ+} (u : AngParticleH1 V W N) : IsAngParticleWeakGradient V W N u.1 (angParticleGrad u) :=
  u.2.choose_spec

/-- The angular Dirichlet energy `E_θ(f) = ∫ ∑ᵢ |∂_{θᵢ} f|² dP_N^θ` (no factor `1/N`). -/
noncomputable def angParticleEnergy {V : AngCircle → ℝ} {W : AngCircle → AngCircle → ℝ} {N : ℕ+}
    (u : AngParticleH1 V W N) : ℝ :=
  ∫ θ, ∑ i, angParticleGrad u θ i ^ 2 ∂angParticleLaw V W N

/-- The angular entropy `Ent_{P_N^θ}(u²)`. -/
noncomputable def angParticleEntropy {V : AngCircle → ℝ} {W : AngCircle → AngCircle → ℝ} {N : ℕ+}
    (u : AngParticleH1 V W N) : ℝ≥0∞ :=
  homogeneousEntropy (angParticleLaw V W N) fun θ => u.1 θ ^ 2

/-- The angular quotient `2 E_θ(u) / Ent(u²)`. -/
noncomputable def angParticleQuotient {V : AngCircle → ℝ} {W : AngCircle → AngCircle → ℝ} {N : ℕ+}
    (u : AngParticleH1 V W N) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * angParticleEnergy u) / angParticleEntropy u

/-- The angular label permutation action. -/
def angPermute {N : ℕ+} (σ : Equiv.Perm (Fin N)) (θ : AngParticleSpace N) : AngParticleSpace N :=
  fun i => θ (σ i)

/-- Angular symmetric tests: invariant under label permutations, a.e. for the angular Gibbs law. -/
def IsSymmetricAngTest {V : AngCircle → ℝ} {W : AngCircle → AngCircle → ℝ} {N : ℕ+}
    (u : AngParticleH1 V W N) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), (u.1 ∘ angPermute σ) =ᵐ[angParticleLaw V W N] u.1

/-- Angular `r_N^all`. -/
noncomputable def angParticleRateAll (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ)
    (N : ℕ+) : ℝ≥0∞ :=
  ⨅ u : {u : AngParticleH1 V W N // 0 < angParticleEntropy u}, angParticleQuotient u.1

/-- Angular `r_N^sym`. -/
noncomputable def angParticleRateSym (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ)
    (N : ℕ+) : ℝ≥0∞ :=
  ⨅ u : {u : {u : AngParticleH1 V W N // IsSymmetricAngTest u} // 0 < angParticleEntropy u.1},
    angParticleQuotient u.1.1

/-! ### Transfer of smooth tests and partial derivatives -/

theorem angEquivN_particleLift {N : ℕ+} (y : Fin N → Fin 1 → ℝ) :
    angEquivN N (particleLift y) = fun k => ((2 * π * y k 0 : ℝ) : AngCircle) := by
  funext k
  rw [angEquivN_apply, angEquiv_apply]
  exact angRescale_mk _

theorem isSmoothPeriodicParticle_comp_iff {N : ℕ+} (ψ : AngParticleSpace N → ℝ) :
    IsSmoothPeriodicParticle (ψ ∘ angEquivN N) ↔ IsSmoothAngParticle ψ := by
  unfold IsSmoothPeriodicParticle IsSmoothAngParticle
  have h1 : ((ψ ∘ angEquivN N) ∘ particleLift : (Fin N → Fin 1 → ℝ) → ℝ)
      = (fun s : Fin N → ℝ => ψ fun k => (s k : AngCircle)) ∘
        (fun y : Fin N → Fin 1 → ℝ => fun k => 2 * π * y k 0) := by
    funext y
    simp only [Function.comp_apply]
    rw [angEquivN_particleLift]
  have h2 : (fun s : Fin N → ℝ => ψ fun k => (s k : AngCircle))
      = ((ψ ∘ angEquivN N) ∘ particleLift : (Fin N → Fin 1 → ℝ) → ℝ) ∘
        (fun s : Fin N → ℝ => fun k _ => s k / (2 * π)) := by
    funext s
    rw [Function.comp_apply, h1]
    simp only [Function.comp_apply]
    congr 1
    funext k
    congr 1
    field_simp
  constructor
  · intro h
    rw [h2]
    exact h.comp (by fun_prop)
  · intro h
    rw [h1]
    exact h.comp (by fun_prop)

theorem particlePartial_comp_angEquivN {N : ℕ+} {ψ : AngParticleSpace N → ℝ}
    (hψ : IsSmoothAngParticle ψ) (i : Fin N) (x : ParticleSpace 1 N) :
    particlePartial i 0 (ψ ∘ angEquivN N) x
      = 2 * π * angParticlePartial i ψ (angEquivN N x) := by
  set F : (Fin N → ℝ) → ℝ := fun s => ψ fun k => (s k : AngCircle) with hF
  set L : (Fin N → Fin 1 → ℝ) → (Fin N → ℝ) := fun y k => 2 * π * y k 0 with hLdef
  have h1 : ((ψ ∘ angEquivN N) ∘ particleLift : (Fin N → Fin 1 → ℝ) → ℝ) = F ∘ L := by
    funext y
    simp only [Function.comp_apply, hF, hLdef]
    rw [angEquivN_particleLift]
  let Lcl : (Fin N → Fin 1 → ℝ) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun k => (2 * π) •
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin 1 → ℝ) k))
  have hL : HasFDerivAt L Lcl (fun k => SharpLSI.secT (x k)) := by
    have : L = Lcl := by
      funext y k
      simp [Lcl, hLdef]
    rw [this]
    exact Lcl.hasFDerivAt
  have hpt : L (fun k => SharpLSI.secT (x k)) = fun k => angSec (angEquivN N x k) := by
    funext k
    simp only [hLdef, angEquivN_apply, angSec_angEquiv]
  have hFd : DifferentiableAt ℝ F (L fun k => SharpLSI.secT (x k)) :=
    (hψ.differentiable (by simp)).differentiableAt
  have hcomp := (hFd.hasFDerivAt.comp _ hL).fderiv
  have hv : Lcl (Pi.single i (Pi.single 0 (1 : ℝ))) = (2 * π) • (Pi.single i (1 : ℝ) : Fin N → ℝ) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [Lcl]
    · simp [Lcl, hk]
  unfold particlePartial angParticlePartial
  rw [h1, hcomp, ContinuousLinearMap.comp_apply, hv, map_smul, hpt]
  simp only [smul_eq_mul]
  rfl

theorem integral_u_particlePartial {N : ℕ+} (u : AngParticleSpace N → ℝ) {ψ : AngParticleSpace N → ℝ}
    (hψ : IsSmoothAngParticle ψ) (i : Fin N) :
    ∫ x, (u ∘ angEquivN N) x * particlePartial i 0 (ψ ∘ angEquivN N) x ∂particleHaar 1 N
      = 2 * π * ∫ θ, u θ * angParticlePartial i ψ θ ∂angParticleHaar N := by
  have : ∀ x, (u ∘ angEquivN N) x * particlePartial i 0 (ψ ∘ angEquivN N) x
      = 2 * π * (fun θ => u θ * angParticlePartial i ψ θ) (angEquivN N x) := fun x => by
    rw [particlePartial_comp_angEquivN hψ]; simp only [Function.comp_apply]; ring
  simp_rw [this]
  rw [integral_const_mul, integral_comp_angEquivN (fun θ => u θ * angParticlePartial i ψ θ)]

/-! ### Physical gradient and transfer of weak gradients -/

/-- The unit-period gradient `2π ∂_θ`, as a tangent field on `(𝕋¹)^N`. -/
noncomputable def physGradN {N : ℕ+} (g : AngParticleSpace N → Fin N → ℝ) :
    ParticleSpace 1 N → Fin N → Tangent 1 :=
  fun x i => (2 * π * g (angEquivN N x) i) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

theorem physGradN_apply {N : ℕ+} (g : AngParticleSpace N → Fin N → ℝ) (x : ParticleSpace 1 N)
    (i : Fin N) (j : Fin 1) : physGradN g x i j = 2 * π * g (angEquivN N x) i := by
  have : j = 0 := Subsingleton.elim _ _
  subst this
  simp [physGradN]

theorem physGradN_surj {N : ℕ+} {G : ParticleSpace 1 N → Fin N → Tangent 1} :
    physGradN (fun θ i => G ((angEquivN N).symm θ) i 0 / (2 * π)) = G := by
  funext x i
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  unfold physGradN
  have : (2 * π * (G ((angEquivN N).symm (angEquivN N x)) i 0 / (2 * π))) = G x i 0 := by
    rw [MeasurableEquiv.symm_apply_apply]; field_simp
  rw [this]
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp

/-- `g ↦ 2π g` as a continuous linear map into tangent fields. -/
noncomputable def physCLM (N : ℕ+) : (Fin N → ℝ) →L[ℝ] (Fin N → Tangent 1) :=
  ContinuousLinearMap.pi fun i => (2 * π) •
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :
      ℝ →L[ℝ] Tangent 1).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i))

/-- Inverse of `physCLM`. -/
noncomputable def backCLM (N : ℕ+) : (Fin N → Tangent 1) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => (2 * π)⁻¹ •
    ((EuclideanSpace.proj (0 : Fin 1) : Tangent 1 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Tangent 1) i))

theorem physGradN_eq_physCLM {N : ℕ+} (g : AngParticleSpace N → Fin N → ℝ) (x : ParticleSpace 1 N) :
    physGradN g x = physCLM N (g (angEquivN N x)) := by
  funext i
  simp [physGradN, physCLM]
  rw [smul_smul]

theorem backCLM_physGradN {N : ℕ+} (g : AngParticleSpace N → Fin N → ℝ) (x : ParticleSpace 1 N) :
    backCLM N (physGradN g x) = g (angEquivN N x) := by
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  funext i
  simp [backCLM, physGradN]
  field_simp

theorem memLp_comp_angEquivN_iff {E : Type*} [NormedAddCommGroup E] {p : ENNReal}
    (A : InteractionData 1) (N : ℕ+) (f : AngParticleSpace N → E) :
    MemLp (f ∘ angEquivN N) p (particleLaw A N) ↔ MemLp f p (angParticleLaw (angV A) (angW A) N) := by
  rw [← MeasurableEquiv.memLp_map_measure_iff (angEquivN N), map_particleLaw]

theorem memLp_physGradN_iff (A : InteractionData 1) (N : ℕ+) (g : AngParticleSpace N → Fin N → ℝ) :
    MemLp (physGradN g) 2 (particleLaw A N) ↔
      MemLp g 2 (angParticleLaw (angV A) (angW A) N) := by
  rw [← memLp_comp_angEquivN_iff A N]
  constructor
  · intro h
    have := (backCLM N).comp_memLp' h
    refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
    exact backCLM_physGradN g x
  · intro h
    have := (physCLM N).comp_memLp' h
    refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
    exact (physGradN_eq_physCLM g x).symm

theorem integral_physGradN_mul {N : ℕ+} (g : AngParticleSpace N → Fin N → ℝ)
    (ψ : AngParticleSpace N → ℝ) (i : Fin N) :
    ∫ x, physGradN g x i 0 * (ψ ∘ angEquivN N) x ∂particleHaar 1 N
      = 2 * π * ∫ θ, g θ i * ψ θ ∂angParticleHaar N := by
  have : ∀ x, physGradN g x i 0 * (ψ ∘ angEquivN N) x
      = 2 * π * (fun θ => g θ i * ψ θ) (angEquivN N x) := fun x => by
    rw [physGradN_apply]; simp only [Function.comp_apply]; ring
  simp_rw [this]
  rw [integral_const_mul, integral_comp_angEquivN (fun θ => g θ i * ψ θ)]

theorem isParticleWeakGradient_iff (A : InteractionData 1) (N : ℕ+) (u : AngParticleSpace N → ℝ)
    (g : AngParticleSpace N → Fin N → ℝ) :
    IsParticleWeakGradient A N (u ∘ angEquivN N) (physGradN g) ↔
      IsAngParticleWeakGradient (angV A) (angW A) N u g := by
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  constructor
  · intro h
    refine ⟨(memLp_comp_angEquivN_iff A N u).1 h.memLp, (memLp_physGradN_iff A N g).1 h.memLp_grad,
      ?_⟩
    intro ψ hψ i
    have hφ : IsSmoothPeriodicParticle (ψ ∘ angEquivN N) :=
      (isSmoothPeriodicParticle_comp_iff ψ).2 hψ
    have := h.ibp (ψ ∘ angEquivN N) hφ i 0
    rw [integral_u_particlePartial u hψ i, integral_physGradN_mul] at this
    have h2 : 2 * π * (∫ θ, u θ * angParticlePartial i ψ θ ∂angParticleHaar N
        + ∫ θ, g θ i * ψ θ ∂angParticleHaar N) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hpi
    · linarith
  · intro h
    refine ⟨(memLp_comp_angEquivN_iff A N u).2 h.memLp, (memLp_physGradN_iff A N g).2 h.memLp_grad,
      ?_⟩
    intro φ hφ i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    set ψ : AngParticleSpace N → ℝ := φ ∘ (angEquivN N).symm with hψdef
    have hφψ : φ = ψ ∘ angEquivN N := by
      funext x; simp [hψdef]
    have hψ : IsSmoothAngParticle ψ := by
      rw [← isSmoothPeriodicParticle_comp_iff, ← hφψ]; exact hφ
    rw [hφψ, integral_u_particlePartial u hψ i, integral_physGradN_mul, h.ibp ψ hψ i]
    ring

/-! ### Bijection of the `H¹` domains -/

/-- The angular and unit-period `H¹(P_N)` domains correspond bijectively under `θ = 2π x`. -/
noncomputable def angParticleH1Equiv (A : InteractionData 1) (N : ℕ+) :
    AngParticleH1 (angV A) (angW A) N ≃ ParticleH1 A N where
  toFun u := ⟨u.1 ∘ angEquivN N, by
    obtain ⟨g, hg⟩ := u.2
    exact ⟨physGradN g, (isParticleWeakGradient_iff A N u.1 g).2 hg⟩⟩
  invFun f := ⟨f.1 ∘ (angEquivN N).symm, by
    obtain ⟨G, hG⟩ := f.2
    refine ⟨fun θ i => G ((angEquivN N).symm θ) i 0 / (2 * π), ?_⟩
    rw [← isParticleWeakGradient_iff A N]
    have e1 : (f.1 ∘ (angEquivN N).symm) ∘ angEquivN N = f.1 := by funext x; simp
    rw [e1, physGradN_surj]
    exact hG⟩
  left_inv u := Subtype.ext (by funext θ; simp)
  right_inv f := Subtype.ext (by funext x; simp)

theorem angParticleH1Equiv_val (A : InteractionData 1) (N : ℕ+)
    (u : AngParticleH1 (angV A) (angW A) N) : (angParticleH1Equiv A N u).1 = u.1 ∘ angEquivN N :=
  rfl

/-! ### Energy, entropy and quotient -/

theorem particleEnergy_angParticleH1Equiv (A : InteractionData 1) (N : ℕ+)
    (u : AngParticleH1 (angV A) (angW A) N) :
    particleEnergy A N (angParticleH1Equiv A N u) = a0 * angParticleEnergy u := by
  have hg : IsParticleWeakGradient A N (angParticleH1Equiv A N u).1
      (physGradN (angParticleGrad u)) :=
    (isParticleWeakGradient_iff A N u.1 _).2 (isAngParticleWeakGradient_grad u)
  rw [particleEnergy_eq_of_isParticleWeakGradient _ hg]
  unfold angParticleEnergy
  have hn : ∀ x, particleTangentNormSq (physGradN (angParticleGrad u) x)
      = a0 * (fun θ => ∑ i, angParticleGrad u θ i ^ 2) (angEquivN N x) := by
    intro x
    rw [particleTangentNormSq_eq]
    simp only [physGradN_apply, a0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_one]
    ring
  simp_rw [hn]
  rw [integral_const_mul, ← map_particleLaw A N,
    integral_map_equiv (angEquivN N) (fun θ => ∑ i, angParticleGrad u θ i ^ 2)]

theorem homogeneousEntropy_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (P : Measure α) (v : β → ℝ) :
    homogeneousEntropy P (v ∘ e) = homogeneousEntropy (P.map e) v := by
  unfold homogeneousEntropy
  have h1 : ∫ x, (v ∘ e) x ∂P = ∫ y, v y ∂P.map e := (integral_map_equiv e v).symm
  rw [h1]
  split_ifs
  · rfl
  · rw [lintegral_map_equiv (fun y => ENNReal.ofReal (entropyIntegrand (∫ z, v z ∂P.map e) (v y))) e]
    rfl

theorem particleEntropy_angParticleH1Equiv (A : InteractionData 1) (N : ℕ+)
    (u : AngParticleH1 (angV A) (angW A) N) :
    particleEntropy A N (angParticleH1Equiv A N u) = angParticleEntropy u := by
  unfold particleEntropy angParticleEntropy
  rw [← map_particleLaw A N]
  exact homogeneousEntropy_map_equiv (angEquivN N) (particleLaw A N) fun θ => u.1 θ ^ 2

theorem particleQuotient_angParticleH1Equiv (A : InteractionData 1) (N : ℕ+)
    (u : AngParticleH1 (angV A) (angW A) N) :
    particleQuotient A N (angParticleH1Equiv A N u) = ENNReal.ofReal a0 * angParticleQuotient u := by
  unfold particleQuotient angParticleQuotient
  rw [particleEnergy_angParticleH1Equiv, particleEntropy_angParticleH1Equiv,
    show 2 * (a0 * angParticleEnergy u) = a0 * (2 * angParticleEnergy u) by ring,
    ENNReal.ofReal_mul a0_pos.le, mul_div_assoc]

/-! ### Symmetric tests -/

theorem angEquivN_permute {N : ℕ+} (σ : Equiv.Perm (Fin N)) (x : ParticleSpace 1 N) :
    angEquivN N (permuteParticles σ x) = angPermute σ (angEquivN N x) := rfl

theorem ae_comp_angEquivN_iff (A : InteractionData 1) (N : ℕ+) (f h : AngParticleSpace N → ℝ) :
    (f ∘ angEquivN N) =ᵐ[particleLaw A N] (h ∘ angEquivN N) ↔
      f =ᵐ[angParticleLaw (angV A) (angW A) N] h := by
  rw [← map_particleLaw A N]
  exact ((angEquivN N).measurableEmbedding.ae_map_iff (p := fun y => f y = h y)).symm

theorem isSymmetricParticleTest_angEquiv_iff (A : InteractionData 1) (N : ℕ+)
    (u : AngParticleH1 (angV A) (angW A) N) :
    IsSymmetricParticleTest (angParticleH1Equiv A N u) ↔ IsSymmetricAngTest u := by
  unfold IsSymmetricParticleTest IsSymmetricParticleFun IsSymmetricAngTest
  refine forall_congr' fun σ => ?_
  exact ae_comp_angEquivN_iff A N (u.1 ∘ angPermute σ) u.1

/-- The `ℝ≥0∞`-valued infimum scales: reindex along an equivalence of the domains. -/
theorem particleRateAll_eq (A : InteractionData 1) (N : ℕ+) :
    particleRateAll A N = ENNReal.ofReal a0 * angParticleRateAll (angV A) (angW A) N := by
  have ha0 : ENNReal.ofReal a0 ≠ 0 := (ENNReal.ofReal_pos.2 a0_pos).ne'
  unfold particleRateAll angParticleRateAll
  rw [ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top]
  let E : {u : AngParticleH1 (angV A) (angW A) N // 0 < angParticleEntropy u} ≃
      {f : ParticleH1 A N // 0 < particleEntropy A N f} :=
    (angParticleH1Equiv A N).subtypeEquiv fun u => by
      rw [particleEntropy_angParticleH1Equiv]
  rw [← E.iInf_comp]
  refine iInf_congr fun u => ?_
  exact particleQuotient_angParticleH1Equiv A N u.1

theorem particleRateSym_eq (A : InteractionData 1) (N : ℕ+) :
    particleRateSym A N = ENNReal.ofReal a0 * angParticleRateSym (angV A) (angW A) N := by
  have ha0 : ENNReal.ofReal a0 ≠ 0 := (ENNReal.ofReal_pos.2 a0_pos).ne'
  unfold particleRateSym angParticleRateSym
  rw [ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top]
  let E1 : {u : AngParticleH1 (angV A) (angW A) N // IsSymmetricAngTest u} ≃
      SymmetricParticleH1 A N :=
    (angParticleH1Equiv A N).subtypeEquiv fun u => (isSymmetricParticleTest_angEquiv_iff A N u).symm
  let E : {u : {u : AngParticleH1 (angV A) (angW A) N // IsSymmetricAngTest u} //
        0 < angParticleEntropy u.1} ≃
      {f : SymmetricParticleH1 A N // 0 < particleEntropy A N f.1} :=
    E1.subtypeEquiv fun u => by
      show _ ↔ 0 < particleEntropy A N (angParticleH1Equiv A N u.1)
      rw [particleEntropy_angParticleH1Equiv]
  rw [← E.iInf_comp]
  refine iInf_congr fun u => ?_
  exact particleQuotient_angParticleH1Equiv A N u.1.1

end DGPS.FiniteN.UnitTorusNormalization

namespace DGPS.FiniteN

open DGPS DGPS.Circle.AngularNormalization DGPS.FiniteN.UnitTorusNormalization
open MeasureTheory
open scoped ENNReal

/-- FIN002: under `θ_i = 2π x_i`, the unit-period `N`-particle torus `(𝕋¹)^N` is identified with the
angular torus by the measure-preserving `angEquivN`, the Gibbs law is the pushforward of the
angular Gibbs law, the `H¹` domains correspond bijectively, the Dirichlet energy (no factor `1/N`)
is `E_x = a₀ E_θ` with `a₀ = 4π²`, entropy is unchanged, so the quotients and both LSI rates
`r_N^all`, `r_N^sym` are `a₀` times the angular ones; the Poincaré rate on the unit torus is
`a₀` times the angular Poincaré rate. -/
theorem angular_to_unit_torus_normalization :
    a0 = 4 * Real.pi ^ 2 ∧
    (∀ N : ℕ+, MeasurePreserving (angEquivN N) (particleHaar 1 N) (angParticleHaar N)) ∧
    (∀ (A : InteractionData 1) (N : ℕ+),
      (angEquivN N : ParticleSpace 1 N → AngParticleSpace N) '' Set.univ = Set.univ ∧
      (particleLaw A N).map (angEquivN N) = angParticleLaw (angV A) (angW A) N) ∧
    (∀ (A : InteractionData 1) (N : ℕ+) (u : AngParticleH1 (angV A) (angW A) N),
      (angParticleH1Equiv A N u).1 = u.1 ∘ angEquivN N ∧
      particleEnergy A N (angParticleH1Equiv A N u) = a0 * angParticleEnergy u ∧
      particleEntropy A N (angParticleH1Equiv A N u) = angParticleEntropy u ∧
      particleQuotient A N (angParticleH1Equiv A N u) =
        ENNReal.ofReal a0 * angParticleQuotient u ∧
      (IsSymmetricParticleTest (angParticleH1Equiv A N u) ↔ IsSymmetricAngTest u)) ∧
    (∀ (A : InteractionData 1) (N : ℕ+),
      particleRateAll A N = ENNReal.ofReal a0 * angParticleRateAll (angV A) (angW A) N ∧
      particleRateSym A N = ENNReal.ofReal a0 * angParticleRateSym (angV A) (angW A) N) ∧
    (∀ μ : ProbabilityMeasure (Torus 1),
      poincareRate μ = ENNReal.ofReal a0 * angPoincareRate (angMap μ)) :=
  ⟨rfl, measurePreserving_angEquivN,
    fun A N => ⟨Set.image_univ_of_surjective (angEquivN N).surjective, map_particleLaw A N⟩,
    fun A N u => ⟨angParticleH1Equiv_val A N u, particleEnergy_angParticleH1Equiv A N u,
      particleEntropy_angParticleH1Equiv A N u, particleQuotient_angParticleH1Equiv A N u,
      isSymmetricParticleTest_angEquiv_iff A N u⟩,
    fun A N => ⟨particleRateAll_eq A N, particleRateSym_eq A N⟩,
    poincareRate_eq⟩

end DGPS.FiniteN
