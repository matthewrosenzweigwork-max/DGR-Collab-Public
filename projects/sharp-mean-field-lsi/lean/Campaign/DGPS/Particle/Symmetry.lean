import DGPS.Particle.Gibbs
import DGPS.Particle.Sobolev

/-!
# Permutation-invariant particle subspace (DEF018)

INTERFACES/definitions.md §4, common_lemmas.md DEF018. The label permutation `σ ∈ S_N` acts on
`(𝕋^d)^N` by `x ↦ x ∘ σ` (`permuteParticles`).

* `permuteParticles_*`, `measurePreserving_permuteParticles`: the action is a measurable equivalence
  preserving the product Haar probability;
* `particleHamiltonian_permute`, `particleDensity_permute`,
  `measurePreserving_permuteParticles_law`: `H_N`, the Gibbs density and `P_N` are invariant;
* `IsParticleWeakGradient.permute`, `ParticleH1.permute`: `f ∈ H¹(P_N) ⇒ f ∘ σ ∈ H¹(P_N)` with
  weak gradient `(∇ᵢ (f ∘ σ))(x) = (∇_{σ⁻¹ i} f)(x ∘ σ)` (`permuteGradient`);
* `permutation_preserves_gibbs_energy`: `P_N` and `E_N` are preserved by every permutation;
* `IsSymmetricParticleTest f`: `f ∘ σ = f` `P_N`-a.e. for every `σ`; independent of the
  representative (`IsSymmetricParticleFun.congr`, `isSymmetricParticleTest_congr`), equivalently
  `m^N`-a.e. (`isSymmetricParticleFun_iff_haar`); `SymmetricParticleH1` is the subtype.
-/

open MeasureTheory

namespace DGPS

/-- The label permutation action `x ↦ x ∘ σ` on `(𝕋^d)^N`. -/
def permuteParticles {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N)) (x : ParticleSpace d N) :
    ParticleSpace d N := fun i => x (σ i)

theorem permuteParticles_one {d : ℕ} {N : ℕ+} (x : ParticleSpace d N) :
    permuteParticles (1 : Equiv.Perm (Fin N)) x = x := rfl

theorem permuteParticles_mul {d : ℕ} {N : ℕ+} (σ τ : Equiv.Perm (Fin N)) (x : ParticleSpace d N) :
    permuteParticles σ (permuteParticles τ x) = permuteParticles (τ * σ) x := rfl

theorem permuteParticles_symm_apply {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (x : ParticleSpace d N) : permuteParticles σ (permuteParticles σ.symm x) = x := by
  funext i; simp [permuteParticles]

theorem permuteParticles_apply_symm {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (x : ParticleSpace d N) : permuteParticles σ.symm (permuteParticles σ x) = x := by
  funext i; simp [permuteParticles]

theorem continuous_permuteParticles {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N)) :
    Continuous (permuteParticles (d := d) σ) :=
  continuous_pi fun i => continuous_apply (σ i)

theorem measurable_permuteParticles {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N)) :
    Measurable (permuteParticles (d := d) σ) :=
  Measurable.of_eval fun i => measurable_pi_apply (σ i)

/-- The label permutation as a measurable equivalence. -/
def permuteEquiv {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N)) :
    ParticleSpace d N ≃ᵐ ParticleSpace d N where
  toFun := permuteParticles σ
  invFun := permuteParticles σ.symm
  left_inv := permuteParticles_apply_symm σ
  right_inv := permuteParticles_symm_apply σ
  measurable_toFun := measurable_permuteParticles σ
  measurable_invFun := measurable_permuteParticles σ.symm

theorem permuteEquiv_apply {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N)) (x : ParticleSpace d N) :
    permuteEquiv σ x = permuteParticles σ x := rfl

theorem measurePreserving_permuteParticles (d : ℕ) {N : ℕ+} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permuteParticles (d := d) σ) (particleHaar d N) (particleHaar d N) := by
  refine ⟨measurable_permuteParticles σ, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_permuteParticles σ) (MeasurableSet.univ_pi hs)]
  have : permuteParticles (d := d) σ ⁻¹' (Set.univ.pi s) = Set.univ.pi fun k => s (σ.symm k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, permuteParticles]
    exact ⟨fun h k => by simpa using h (σ.symm k), fun h i => by simpa using h (σ i)⟩
  rw [this, particleHaar, Measure.pi_pi]
  exact σ.symm.prod_comp (fun i => haar d (s i))


/-! ### Invariance of the Hamiltonian and of the Gibbs law -/

theorem particleHamiltonian_permute {d : ℕ} (A : InteractionData d) {N : ℕ+}
    (σ : Equiv.Perm (Fin N)) (x : ParticleSpace d N) :
    particleHamiltonian A N (permuteParticles σ x) = particleHamiltonian A N x := by
  unfold particleHamiltonian permuteParticles
  congr 1
  · exact Equiv.sum_comp σ (fun i => A.V (x i))
  · congr 1
    rw [← Equiv.sum_comp σ (fun i => ∑ j, A.W (x i) (x j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp σ (fun j => A.W (x (σ i)) (x j))

theorem particleDensity_permute {d : ℕ} (A : InteractionData d) {N : ℕ+}
    (σ : Equiv.Perm (Fin N)) (x : ParticleSpace d N) :
    particleDensity A N (permuteParticles σ x) = particleDensity A N x := by
  simp [particleDensity, particleHamiltonian_permute]

theorem measurePreserving_permuteParticles_law {d : ℕ} (A : InteractionData d) {N : ℕ+}
    (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permuteParticles (d := d) σ) (particleLaw A N) (particleLaw A N) := by
  refine ⟨measurable_permuteParticles σ, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_permuteParticles σ) hs, particleLaw,
    withDensity_apply _ (measurable_permuteParticles σ hs), withDensity_apply _ hs]
  have hρ : Measurable fun x => ENNReal.ofReal (particleDensity A N x) :=
    (DGPS.Particle.particleDensity_measurable A N).ennreal_ofReal
  rw [← lintegral_indicator (measurable_permuteParticles σ hs), ← lintegral_indicator hs]
  have : (fun x => (permuteParticles (d := d) σ ⁻¹' s).indicator
      (fun x => ENNReal.ofReal (particleDensity A N x)) x) =
      fun x => s.indicator (fun x => ENNReal.ofReal (particleDensity A N x)) (permuteParticles σ x) := by
    funext x
    by_cases h : permuteParticles σ x ∈ s <;>
      simp [Set.indicator, h, particleDensity_permute]
  rw [this]
  exact (measurePreserving_permuteParticles d σ).lintegral_comp_emb
    (permuteEquiv σ).measurableEmbedding _

/-! ### Permuting smooth tests and their partial derivatives -/

/-- `y ↦ y ∘ σ` as a continuous linear equivalence of `Fin N → M`. -/
noncomputable def permCLE {N : ℕ+} (σ : Equiv.Perm (Fin N)) (M : Type*) [NormedAddCommGroup M]
    [NormedSpace ℝ M] [FiniteDimensional ℝ M] : (Fin N → M) ≃L[ℝ] (Fin N → M) :=
  (LinearEquiv.funCongrLeft ℝ M σ).toContinuousLinearEquiv

theorem permCLE_apply {N : ℕ+} (σ : Equiv.Perm (Fin N)) (M : Type*) [NormedAddCommGroup M]
    [NormedSpace ℝ M] [FiniteDimensional ℝ M] (y : Fin N → M) (i : Fin N) :
    permCLE σ M y i = y (σ i) := rfl

theorem isSmoothPeriodicParticle_comp_permute {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    IsSmoothPeriodicParticle (φ ∘ permuteParticles σ) := by
  unfold IsSmoothPeriodicParticle at *
  have h : (φ ∘ permuteParticles σ) ∘ particleLift =
      (φ ∘ particleLift) ∘ (permCLE σ (Fin d → ℝ)) := rfl
  rw [h]
  exact hφ.comp (permCLE σ (Fin d → ℝ)).contDiff

theorem particlePartial_permute {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N)) (φ : ParticleSpace d N → ℝ)
    (i : Fin N) (j : Fin d) (x : ParticleSpace d N) :
    particlePartial i j (φ ∘ permuteParticles σ) x =
      particlePartial (σ.symm i) j φ (permuteParticles σ x) := by
  unfold particlePartial
  have h : (φ ∘ permuteParticles σ) ∘ particleLift =
      (φ ∘ particleLift) ∘ (permCLE σ (Fin d → ℝ)) := rfl
  rw [h, ContinuousLinearEquiv.comp_right_fderiv]
  have e1 : (permCLE σ (Fin d → ℝ)) (fun k => SharpLSI.secT (x k)) =
      fun k => SharpLSI.secT (permuteParticles σ x k) := rfl
  have e2 : (permCLE σ (Fin d → ℝ) : (Fin N → Fin d → ℝ) →L[ℝ] (Fin N → Fin d → ℝ))
      (Pi.single i (Pi.single j (1 : ℝ))) = Pi.single (σ.symm i) (Pi.single j (1 : ℝ)) := by
    funext k
    simp only [ContinuousLinearEquiv.coe_coe, permCLE_apply, Pi.single_apply]
    by_cases h : k = σ.symm i
    · subst h; simp
    · have : σ k ≠ i := fun h' => h (by rw [← h']; simp)
      simp [h, this]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [e1]
  congr 1

theorem integral_comp_permuteParticles_haar {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (h : ParticleSpace d N → ℝ) :
    ∫ x, h (permuteParticles σ x) ∂particleHaar d N = ∫ x, h x ∂particleHaar d N :=
  (measurePreserving_permuteParticles d σ).integral_comp' (f := permuteEquiv σ) h

theorem integral_comp_permuteParticles_law {d : ℕ} (A : InteractionData d) {N : ℕ+}
    (σ : Equiv.Perm (Fin N)) (h : ParticleSpace d N → ℝ) :
    ∫ x, h (permuteParticles σ x) ∂particleLaw A N = ∫ x, h x ∂particleLaw A N :=
  (measurePreserving_permuteParticles_law A σ).integral_comp' (f := permuteEquiv σ) h

/-! ### Permuting weak gradients -/

/-- The gradient of `f ∘ π_σ` in terms of the gradient `g` of `f`:
`(∇ᵢ (f ∘ π_σ))(x) = (∇_{σ⁻¹ i} f)(x ∘ σ)`. -/
def permuteGradient {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (g : ParticleSpace d N → Fin N → Tangent d) : ParticleSpace d N → Fin N → Tangent d :=
  fun x i => g (permuteParticles σ x) (σ.symm i)

theorem IsParticleWeakGradient.permute {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleWeakGradient A N f g) (σ : Equiv.Perm (Fin N)) :
    IsParticleWeakGradient A N (f ∘ permuteParticles σ) (permuteGradient σ g) := by
  refine ⟨hg.memLp.comp_measurePreserving (measurePreserving_permuteParticles_law A σ), ?_, ?_⟩
  · have h1 := hg.memLp_grad.comp_measurePreserving (measurePreserving_permuteParticles_law A σ)
    have h2 := ((permCLE σ.symm (Tangent d) : (Fin N → Tangent d) ≃L[ℝ] (Fin N → Tangent d)) :
      (Fin N → Tangent d) →L[ℝ] (Fin N → Tangent d)).comp_memLp' h1
    exact h2
  · intro φ hφ i j
    have hψ := isSmoothPeriodicParticle_comp_permute σ.symm hφ
    have key := hg.ibp _ hψ (σ.symm i) j
    have hp : ∀ y, particlePartial (σ.symm i) j (φ ∘ permuteParticles σ.symm) y =
        particlePartial i j φ (permuteParticles σ.symm y) := fun y => by
      rw [particlePartial_permute]; simp
    simp_rw [hp] at key
    have lhs : ∫ x, (f ∘ permuteParticles σ) x * particlePartial i j φ x ∂particleHaar d N =
        ∫ y, f y * particlePartial i j φ (permuteParticles σ.symm y) ∂particleHaar d N := by
      rw [← integral_comp_permuteParticles_haar σ (fun y => f y *
        particlePartial i j φ (permuteParticles σ.symm y))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [permuteParticles_apply_symm]
    have rhs : ∫ x, permuteGradient σ g x i j * φ x ∂particleHaar d N =
        ∫ y, g y (σ.symm i) j * (φ ∘ permuteParticles σ.symm) y ∂particleHaar d N := by
      rw [← integral_comp_permuteParticles_haar σ (fun y => g y (σ.symm i) j *
        (φ ∘ permuteParticles σ.symm) y)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [permuteGradient, permuteParticles_apply_symm]
    rw [lhs, rhs]
    exact key

theorem particleTangentNormSq_permuteGradient {d : ℕ} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (g : ParticleSpace d N → Fin N → Tangent d) (x : ParticleSpace d N) :
    particleTangentNormSq (permuteGradient σ g x) =
      particleTangentNormSq (g (permuteParticles σ x)) := by
  unfold particleTangentNormSq permuteGradient
  exact Equiv.sum_comp σ.symm (fun i => ‖g (permuteParticles σ x) i‖ ^ 2)

/-- `f ∘ π_σ` stays in `H¹(P_N)`. -/
theorem memParticleH1_permute {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (σ : Equiv.Perm (Fin N)) :
    MemParticleH1 A N (f ∘ permuteParticles σ) :=
  let ⟨g, hg⟩ := hf
  ⟨permuteGradient σ g, hg.permute σ⟩

/-- The label-permutation action on `H¹(P_N)`: `f ↦ f ∘ π_σ`. -/
def ParticleH1.permute {d : ℕ} {A : InteractionData d} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (f : ParticleH1 A N) : ParticleH1 A N :=
  ⟨f.1 ∘ permuteParticles σ, memParticleH1_permute f.2 σ⟩

theorem ParticleH1.permute_apply {d : ℕ} {A : InteractionData d} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (f : ParticleH1 A N) (x : ParticleSpace d N) :
    f.permute σ x = f (permuteParticles σ x) := rfl

/-! ### Permutation invariance of the Gibbs energy -/

theorem particleEnergy_permute {d : ℕ} {A : InteractionData d} {N : ℕ+} (σ : Equiv.Perm (Fin N))
    (f : ParticleH1 A N) : particleEnergy A N (f.permute σ) = particleEnergy A N f := by
  rw [particleEnergy_eq_of_isParticleWeakGradient (f.permute σ)
    ((isParticleWeakGradient_particleWeakGradient f).permute σ)]
  simp_rw [particleTangentNormSq_permuteGradient]
  rw [integral_comp_permuteParticles_law A σ (fun x => particleTangentNormSq (particleWeakGradient f x))]
  rfl

/-- DEF018: every label permutation preserves the Gibbs law `P_N` (pushforward) and the Gibbs
energy `E_N`. -/
theorem permutation_preserves_gibbs_energy {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (σ : Equiv.Perm (Fin N)) :
    (particleLaw A N).map (permuteParticles σ) = particleLaw A N ∧
      ∀ f : ParticleH1 A N, particleEnergy A N (f.permute σ) = particleEnergy A N f :=
  ⟨(measurePreserving_permuteParticles_law A σ).map_eq, fun f => particleEnergy_permute σ f⟩

/-! ### Symmetric tests -/

/-- A function `u` on `(𝕋^d)^N` is permutation invariant: `u ∘ π_σ = u` `P_N`-a.e., for every
`σ ∈ S_N`. -/
def IsSymmetricParticleFun {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (u : ParticleSpace d N → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), (u ∘ permuteParticles σ) =ᵐ[particleLaw A N] u

/-- DEF018: a test `f ∈ H¹(P_N)` is symmetric if `f ∘ σ = f` `P_N`-a.e. for every permutation
`σ ∈ S_N`. -/
def IsSymmetricParticleTest {d : ℕ} {A : InteractionData d} {N : ℕ+} (f : ParticleH1 A N) : Prop :=
  IsSymmetricParticleFun A N f.1

theorem isSymmetricParticleTest_iff {d : ℕ} {A : InteractionData d} {N : ℕ+} (f : ParticleH1 A N) :
    IsSymmetricParticleTest f ↔ ∀ σ : Equiv.Perm (Fin N), (f.permute σ).1 =ᵐ[particleLaw A N] f.1 :=
  Iff.rfl

/-- Independence of the representative. -/
theorem IsSymmetricParticleFun.congr {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {u v : ParticleSpace d N → ℝ} (h : u =ᵐ[particleLaw A N] v) :
    IsSymmetricParticleFun A N u ↔ IsSymmetricParticleFun A N v := by
  have key : ∀ {u v : ParticleSpace d N → ℝ}, u =ᵐ[particleLaw A N] v →
      IsSymmetricParticleFun A N u → IsSymmetricParticleFun A N v := by
    intro u v h hu σ
    have h2 : (u ∘ permuteParticles σ) =ᵐ[particleLaw A N] (v ∘ permuteParticles σ) :=
      (measurePreserving_permuteParticles_law A σ).quasiMeasurePreserving.ae_eq_comp h
    exact h2.symm.trans ((hu σ).trans h)
  exact ⟨key h, key h.symm⟩

theorem isSymmetricParticleTest_congr {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f f' : ParticleH1 A N} (h : f.1 =ᵐ[particleLaw A N] f'.1) :
    IsSymmetricParticleTest f ↔ IsSymmetricParticleTest f' :=
  IsSymmetricParticleFun.congr h

/-- Symmetry may equivalently be tested a.e. for `m^N`. -/
theorem isSymmetricParticleFun_iff_haar {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (u : ParticleSpace d N → ℝ) :
    IsSymmetricParticleFun A N u ↔
      ∀ σ : Equiv.Perm (Fin N), (u ∘ permuteParticles σ) =ᵐ[particleHaar d N] u :=
  forall_congr' fun _ => ⟨fun h => (DGPS.Particle.particleHaar_absolutelyContinuous A N).ae_le h,
    fun h => (DGPS.Particle.particleLaw_absolutelyContinuous A N).ae_le h⟩

/-- Everywhere permutation-invariant functions are symmetric. -/
theorem IsSymmetricParticleFun.of_forall {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {u : ParticleSpace d N → ℝ} (h : ∀ σ x, u (permuteParticles σ x) = u x) :
    IsSymmetricParticleFun A N u :=
  fun σ => Filter.Eventually.of_forall fun x => h σ x

/-- The symmetric subspace is stable under the permutation action. -/
theorem IsSymmetricParticleTest.permute {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f : ParticleH1 A N} (hf : IsSymmetricParticleTest f) (σ : Equiv.Perm (Fin N)) :
    IsSymmetricParticleTest (f.permute σ) :=
  (IsSymmetricParticleFun.congr (A := A) (N := N) (u := f.1 ∘ permuteParticles σ) (v := f.1)
    (hf σ)).2 hf

theorem particleH1_permute_one {d : ℕ} {A : InteractionData d} {N : ℕ+} (f : ParticleH1 A N) :
    f.permute 1 = f := rfl

/-- The symmetric Sobolev subspace `H¹_sym(P_N)`. -/
def SymmetricParticleH1 {d : ℕ} (A : InteractionData d) (N : ℕ+) : Type :=
  {f : ParticleH1 A N // IsSymmetricParticleTest f}

/-- A symmetric test is fixed by every permutation up to `P_N`-null sets, with the same energy. -/
theorem IsSymmetricParticleTest.energy_permute {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f : ParticleH1 A N} (_hf : IsSymmetricParticleTest f) (σ : Equiv.Perm (Fin N)) :
    particleEnergy A N (f.permute σ) = particleEnergy A N f :=
  particleEnergy_permute σ f

end DGPS
