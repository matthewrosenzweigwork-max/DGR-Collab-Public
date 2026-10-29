import DGPS.Foundations.WeakContractions
import DGPS.Foundations.Entropy
import DGPS.Particle.Sobolev
import DGPS.Particle.Symmetry

/-!
# Particle contraction closure (FOU011)

For a fixed Gibbs law `P_N` on `(𝕋^d)^N`, the test class `H¹(P_N)` is stable under `|·|`, level
truncations `max (·, c)`, `min (·, c)`, affine maps `a · + b` and products with `W^{1,∞}` cutoffs; the
contractions do not increase the Dirichlet energy and `a · + b` scales it by `a²`; scalar
transformations preserve permutation invariance; homogeneous entropy is positively homogeneous.

The weak-gradient statements are reduced to the torus results of `DGPS.Foundations.WeakContractions`
through the measure-preserving equivalence `(𝕋^d)^N ≃ᵐ 𝕋^{N d}` (`particleTorusEquiv`), which is
compatible with periodic lifts, smooth periodic tests and partial derivatives.
-/

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace DGPS

variable {d : ℕ} {N : ℕ+}

/-- Index equivalence `Fin N × Fin d ≃ Fin (N d)`. -/
def particleIdx (d : ℕ) (N : ℕ+) : Fin N × Fin d ≃ Fin ((N : ℕ) * d) := finProdFinEquiv

/-- Particle torus `(𝕋^d)^N` as the torus `𝕋^{Nd}`. -/
def particleTorusEquiv (d : ℕ) (N : ℕ+) : ParticleSpace d N ≃ᵐ Torus ((N : ℕ) * d) :=
  (particleUncurry d N).trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin ((N : ℕ) * d) => UnitAddCircle) (particleIdx d N))

theorem particleTorusEquiv_apply (x : ParticleSpace d N) (k : Fin ((N : ℕ) * d)) :
    particleTorusEquiv d N x k =
      x ((particleIdx d N).symm k).1 ((particleIdx d N).symm k).2 := by
  simp only [particleTorusEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply]
  exact eq_rec_constant _ _

theorem measurePreserving_particleTorusEquiv (d : ℕ) (N : ℕ+) :
    MeasurePreserving (particleTorusEquiv d N) (particleHaar d N) (haar ((N : ℕ) * d)) := by
  rw [haar_eq_pi_haarAddCircle]
  exact (measurePreserving_piCongrLeft (fun _ : Fin ((N : ℕ) * d) =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)) (particleIdx d N)).comp
    (measurePreserving_particleUncurry d N)

/-- Linear identification of the lifts `(ℝ^d)^N ≃ ℝ^{Nd}`. -/
def particleLinEquiv (d : ℕ) (N : ℕ+) :
    (Fin N → Fin d → ℝ) ≃L[ℝ] (Fin ((N : ℕ) * d) → ℝ) where
  toFun y k := y ((particleIdx d N).symm k).1 ((particleIdx d N).symm k).2
  invFun z i j := z (particleIdx d N (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by funext i j; simp
  right_inv z := by funext k; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem particleLinEquiv_apply (y : Fin N → Fin d → ℝ) (k : Fin ((N : ℕ) * d)) :
    particleLinEquiv d N y k = y ((particleIdx d N).symm k).1 ((particleIdx d N).symm k).2 := rfl

theorem particleLinEquiv_symm_apply (z : Fin ((N : ℕ) * d) → ℝ) (i : Fin N) (j : Fin d) :
    (particleLinEquiv d N).symm z i j = z (particleIdx d N (i, j)) := rfl

theorem particleTorusEquiv_lift (y : Fin N → Fin d → ℝ) :
    particleTorusEquiv d N (particleLift y) = torusLift (particleLinEquiv d N y) := by
  funext k
  rw [particleTorusEquiv_apply]
  rfl

theorem particleTorusEquiv_symm_lift (z : Fin ((N : ℕ) * d) → ℝ) :
    (particleTorusEquiv d N).symm (torusLift z) = particleLift ((particleLinEquiv d N).symm z) := by
  apply (particleTorusEquiv d N).injective
  rw [MeasurableEquiv.apply_symm_apply, particleTorusEquiv_lift]
  simp

theorem isSmoothPeriodic_comp_particleTorusEquiv_symm {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) :
    IsSmoothPeriodic (φ ∘ (particleTorusEquiv d N).symm) := by
  have : (φ ∘ (particleTorusEquiv d N).symm) ∘ torusLift =
      (φ ∘ particleLift) ∘ (particleLinEquiv d N).symm := by
    funext z
    simp [particleTorusEquiv_symm_lift]
  unfold IsSmoothPeriodic
  rw [this]
  exact hφ.comp (particleLinEquiv d N).symm.contDiff

theorem isSmoothPeriodicParticle_comp_particleTorusEquiv {ψ : Torus ((N : ℕ) * d) → ℝ}
    (hψ : IsSmoothPeriodic ψ) : IsSmoothPeriodicParticle (ψ ∘ particleTorusEquiv d N) := by
  have : (ψ ∘ particleTorusEquiv d N) ∘ particleLift = (ψ ∘ torusLift) ∘ particleLinEquiv d N := by
    funext y
    simp [particleTorusEquiv_lift]
  unfold IsSmoothPeriodicParticle
  rw [this]
  exact hψ.comp (particleLinEquiv d N).contDiff

theorem particlePartial_eq_coordPartial (φ : ParticleSpace d N → ℝ) (i : Fin N) (j : Fin d)
    (x : ParticleSpace d N) :
    particlePartial i j φ x =
      coordPartial (particleIdx d N (i, j)) (φ ∘ (particleTorusEquiv d N).symm)
        (particleTorusEquiv d N x) := by
  have h1 : (φ ∘ (particleTorusEquiv d N).symm) ∘ torusLift =
      (φ ∘ particleLift) ∘ (particleLinEquiv d N).symm := by
    funext z
    simp [particleTorusEquiv_symm_lift]
  unfold coordPartial particlePartial
  rw [h1]
  have h2 : ((φ ∘ particleLift) ∘ (particleLinEquiv d N).symm) = (φ ∘ particleLift) ∘
      ((particleLinEquiv d N).symm : (Fin ((N : ℕ) * d) → ℝ) → (Fin N → Fin d → ℝ)) := rfl
  rw [h2, (particleLinEquiv d N).symm.comp_right_fderiv]
  have h3 : (particleLinEquiv d N).symm (SharpLSI.secT (particleTorusEquiv d N x)) =
      fun i => SharpLSI.secT (x i) := by
    funext i j
    rw [particleLinEquiv_symm_apply]
    simp [SharpLSI.secT, particleTorusEquiv_apply]
  have h4 : (particleLinEquiv d N).symm (Pi.single (particleIdx d N (i, j)) (1 : ℝ)) =
      Pi.single i (Pi.single j (1 : ℝ)) := by
    funext i' j'
    rw [particleLinEquiv_symm_apply]
    by_cases hi : i' = i
    · subst hi
      by_cases hj : j' = j
      · subst hj; simp
      · have : particleIdx d N (i', j') ≠ particleIdx d N (i', j) := fun h => hj (by
          simpa using (particleIdx d N).injective h)
        simp [this, hj]
    · have : particleIdx d N (i', j') ≠ particleIdx d N (i, j) := fun h => hi (by
        simpa using congrArg Prod.fst ((particleIdx d N).injective h))
      simp [this, hi]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [h3, h4]

/-- Weak gradient in `Lᵖ(m^N)` on the particle torus (`p = 2` is `IsParticleHaarWeakGradient`). -/
structure IsParticleHaarWeakGradientLp {d : ℕ} (p : ℝ≥0∞) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d) : Prop where
  memLp : MemLp f p (particleHaar d N)
  memLp_grad : MemLp g p (particleHaar d N)
  ibp : ∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ → ∀ (i : Fin N) (j : Fin d),
    ∫ x, f x * particlePartial i j φ x ∂particleHaar d N =
      -∫ x, g x i j * φ x ∂particleHaar d N

theorem isParticleHaarWeakGradient_iff_lp {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} :
    IsParticleHaarWeakGradient N f g ↔ IsParticleHaarWeakGradientLp 2 N f g :=
  ⟨fun h => ⟨h.memLp, h.memLp_grad, h.ibp⟩, fun h => ⟨h.memLp, h.memLp_grad, h.ibp⟩⟩

/-- The gradient of a function on `(𝕋^d)^N`, read as a function on `𝕋^{Nd}`. -/
noncomputable def particleGradT (g : ParticleSpace d N → Fin N → Tangent d) :
    Torus ((N : ℕ) * d) → Tangent ((N : ℕ) * d) :=
  fun z => WithLp.toLp 2 fun k =>
    g ((particleTorusEquiv d N).symm z) ((particleIdx d N).symm k).1 ((particleIdx d N).symm k).2

theorem particleGradT_apply (g : ParticleSpace d N → Fin N → Tangent d) (z : Torus ((N : ℕ) * d))
    (k : Fin ((N : ℕ) * d)) :
    particleGradT g z k =
      g ((particleTorusEquiv d N).symm z) ((particleIdx d N).symm k).1
        ((particleIdx d N).symm k).2 := rfl

theorem memLp_comp_particleTorusEquiv_symm {F : ParticleSpace d N → ℝ} {p : ℝ≥0∞} :
    MemLp (F ∘ (particleTorusEquiv d N).symm) p (haar ((N : ℕ) * d)) ↔
      MemLp F p (particleHaar d N) := by
  rw [← (measurePreserving_particleTorusEquiv d N).map_eq,
    (particleTorusEquiv d N).measurableEmbedding.memLp_map_measure_iff]
  simp [Function.comp_def]

theorem memLp_particleGradT_iff {g : ParticleSpace d N → Fin N → Tangent d} {p : ℝ≥0∞} :
    MemLp (particleGradT g) p (haar ((N : ℕ) * d)) ↔ MemLp g p (particleHaar d N) := by
  rw [memLp_piLp_iff, memLp_pi_iff]
  constructor
  · intro h i
    rw [memLp_piLp_iff]
    intro j
    have := (memLp_comp_particleTorusEquiv_symm (F := fun x => g x i j) (p := p)).1
      (by simpa [Function.comp_def, particleGradT_apply] using h (particleIdx d N (i, j)))
    exact this
  · intro h k
    have h1 := (memLp_piLp_iff.1 (h ((particleIdx d N).symm k).1)) ((particleIdx d N).symm k).2
    exact (memLp_comp_particleTorusEquiv_symm
      (F := fun x => g x ((particleIdx d N).symm k).1 ((particleIdx d N).symm k).2)).2 h1

theorem isWeakGradientLp_iff_particle {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} {p : ℝ≥0∞} :
    IsParticleHaarWeakGradientLp p N f g ↔
      IsWeakGradientLp p (f ∘ (particleTorusEquiv d N).symm) (particleGradT g) := by
  have hint : ∀ (F : Torus ((N : ℕ) * d) → ℝ),
      ∫ x, F (particleTorusEquiv d N x) ∂particleHaar d N = ∫ z, F z ∂haar ((N : ℕ) * d) :=
    fun F => (measurePreserving_particleTorusEquiv d N).integral_comp' F
  constructor
  · intro h
    refine ⟨memLp_comp_particleTorusEquiv_symm.2 h.memLp, (memLp_particleGradT_iff).2 h.memLp_grad,
      fun ψ hψ k => ?_⟩
    have hs := isSmoothPeriodicParticle_comp_particleTorusEquiv hψ
    have := h.ibp _ hs ((particleIdx d N).symm k).1 ((particleIdx d N).symm k).2
    rw [← hint, ← hint]
    simp only [particlePartial_eq_coordPartial, Function.comp_def,
      MeasurableEquiv.symm_apply_apply] at this ⊢
    simpa [particleGradT_apply] using this
  · intro h
    refine ⟨memLp_comp_particleTorusEquiv_symm.1 h.memLp, (memLp_particleGradT_iff).1 h.memLp_grad,
      fun φ hφ i j => ?_⟩
    have hs := isSmoothPeriodic_comp_particleTorusEquiv_symm hφ
    have := h.ibp _ hs (particleIdx d N (i, j))
    rw [← hint, ← hint] at this
    simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply] at this
    simp only [particlePartial_eq_coordPartial, Function.comp_def]
    simpa [particleGradT_apply] using this

/-! ### Transport of the `L²` weak gradient -/

theorem isParticleHaarWeakGradient_iff_weakGradient {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} :
    IsParticleHaarWeakGradient N f g ↔
      IsWeakGradient (f ∘ (particleTorusEquiv d N).symm) (particleGradT g) :=
  isParticleHaarWeakGradient_iff_lp.trans
    (isWeakGradientLp_iff_particle.trans isWeakGradient_iff_isWeakGradientLp.symm)

theorem particleGradT_ite (P : ParticleSpace d N → Prop) [DecidablePred P]
    (g h : ParticleSpace d N → Fin N → Tangent d) :
    particleGradT (fun x => if P x then g x else h x) =
      fun z => if P ((particleTorusEquiv d N).symm z) then particleGradT g z
        else particleGradT h z := by
  funext z
  by_cases hp : P ((particleTorusEquiv d N).symm z) <;> simp [particleGradT, hp]

theorem particleGradT_neg (g : ParticleSpace d N → Fin N → Tangent d) :
    particleGradT (fun x => -g x) = fun z => -particleGradT g z := by
  funext z
  simp [particleGradT]
  rfl

theorem particleGradT_zero :
    particleGradT (fun _ : ParticleSpace d N => (0 : Fin N → Tangent d)) = fun _ => 0 := by
  funext z
  simp [particleGradT]
  rfl

theorem particleGradT_smul (c : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d) :
    particleGradT (fun x => c x • g x) =
      fun z => c ((particleTorusEquiv d N).symm z) • particleGradT g z := by
  funext z
  simp [particleGradT]
  rfl

theorem particleGradT_add (g h : ParticleSpace d N → Fin N → Tangent d) :
    particleGradT (fun x => g x + h x) = fun z => particleGradT g z + particleGradT h z := by
  funext z
  simp [particleGradT]
  rfl

/-! ### Contractions, truncations and affine maps on `H¹(m^N)` -/

theorem IsParticleHaarWeakGradient.abs {u : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hu : IsParticleHaarWeakGradient N u g) :
    IsParticleHaarWeakGradient N (fun x => |u x|)
      (fun x => if 0 < u x then g x else if u x < 0 then -g x else 0) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu ⊢
  have h := hu.abs
  rw [particleGradT_ite, show (fun x => if u x < 0 then -g x else 0) =
    fun x => if u x < 0 then -g x else (fun _ => (0 : Fin N → Tangent d)) x from rfl,
    particleGradT_ite, particleGradT_neg, particleGradT_zero]
  exact h

theorem IsParticleHaarWeakGradient.max_const {u : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hu : IsParticleHaarWeakGradient N u g) (c : ℝ) :
    IsParticleHaarWeakGradient N (fun x => max (u x) c) (fun x => if c < u x then g x else 0) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu ⊢
  have h := hu.max_const c
  rw [particleGradT_ite, particleGradT_zero]
  exact h

theorem IsParticleHaarWeakGradient.min_const {u : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hu : IsParticleHaarWeakGradient N u g) (c : ℝ) :
    IsParticleHaarWeakGradient N (fun x => min (u x) c) (fun x => if u x < c then g x else 0) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu ⊢
  have h := hu.min_const c
  rw [particleGradT_ite, particleGradT_zero]
  exact h

theorem IsParticleHaarWeakGradient.affine {u : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hu : IsParticleHaarWeakGradient N u g)
    (a b : ℝ) :
    IsParticleHaarWeakGradient N (fun x => a * u x + b) (fun x => a • g x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu ⊢
  have h := hu.affine a b
  rw [show (fun x => a • g x) = fun x => (fun _ => a) x • g x from rfl, particleGradT_smul]
  exact h

theorem IsParticleHaarWeakGradient.mul_W1infty {u w : ParticleSpace d N → ℝ}
    {g h : ParticleSpace d N → Fin N → Tangent d} (hu : IsParticleHaarWeakGradient N u g)
    (hw : IsParticleHaarWeakGradientLp ∞ N w h) :
    IsParticleHaarWeakGradient N (fun x => u x * w x) (fun x => w x • g x + u x • h x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu ⊢
  have h' := hu.mul_W1infty (isWeakGradientLp_iff_particle.1 hw)
  rw [particleGradT_add, particleGradT_smul, particleGradT_smul]
  exact h'

/-! ### The Gibbs-weighted versions -/

section Gibbs

variable {A : InteractionData d} {u : ParticleSpace d N → ℝ}
  {g : ParticleSpace d N → Fin N → Tangent d}

theorem IsParticleWeakGradient.abs (hu : IsParticleWeakGradient A N u g) :
    IsParticleWeakGradient A N (fun x => |u x|)
      (fun x => if 0 < u x then g x else if u x < 0 then -g x else 0) :=
  (isParticleWeakGradient_iff A N _ _).2 (((isParticleWeakGradient_iff A N _ _).1 hu).abs)

theorem IsParticleWeakGradient.max_const (hu : IsParticleWeakGradient A N u g) (c : ℝ) :
    IsParticleWeakGradient A N (fun x => max (u x) c) (fun x => if c < u x then g x else 0) :=
  (isParticleWeakGradient_iff A N _ _).2 (((isParticleWeakGradient_iff A N _ _).1 hu).max_const c)

theorem IsParticleWeakGradient.min_const (hu : IsParticleWeakGradient A N u g) (c : ℝ) :
    IsParticleWeakGradient A N (fun x => min (u x) c) (fun x => if u x < c then g x else 0) :=
  (isParticleWeakGradient_iff A N _ _).2 (((isParticleWeakGradient_iff A N _ _).1 hu).min_const c)

theorem IsParticleWeakGradient.affine (hu : IsParticleWeakGradient A N u g) (a b : ℝ) :
    IsParticleWeakGradient A N (fun x => a * u x + b) (fun x => a • g x) :=
  (isParticleWeakGradient_iff A N _ _).2 (((isParticleWeakGradient_iff A N _ _).1 hu).affine a b)

theorem IsParticleWeakGradient.mul_W1infty {w : ParticleSpace d N → ℝ}
    {h : ParticleSpace d N → Fin N → Tangent d} (hu : IsParticleWeakGradient A N u g)
    (hw : IsParticleHaarWeakGradientLp ∞ N w h) :
    IsParticleWeakGradient A N (fun x => u x * w x) (fun x => w x • g x + u x • h x) :=
  (isParticleWeakGradient_iff A N _ _).2
    (((isParticleWeakGradient_iff A N _ _).1 hu).mul_W1infty hw)

end Gibbs

/-! ### Energy -/

theorem particleTangentNormSq_nonneg' (v : Fin N → Tangent d) : 0 ≤ particleTangentNormSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem particleTangentNormSq_neg' (v : Fin N → Tangent d) :
    particleTangentNormSq (-v) = particleTangentNormSq v := by
  simp [particleTangentNormSq]

theorem particleTangentNormSq_smul' (a : ℝ) (v : Fin N → Tangent d) :
    particleTangentNormSq (a • v) = a ^ 2 * particleTangentNormSq v := by
  simp [particleTangentNormSq, norm_smul, mul_pow, Finset.mul_sum]

theorem particleEnergy_le_of_pointwise {A : InteractionData d} (f f' : ParticleH1 A N)
    {G : ParticleSpace d N → Fin N → Tangent d} (hG : IsParticleWeakGradient A N f'.1 G)
    (hpt : ∀ x, particleTangentNormSq (G x) ≤ particleTangentNormSq (particleWeakGradient f x)) :
    particleEnergy A N f' ≤ particleEnergy A N f := by
  rw [particleEnergy_eq_of_isParticleWeakGradient f' hG]
  exact integral_mono (integrable_particleTangentNormSq hG.memLp_grad)
    (integrable_particleTangentNormSq (isParticleWeakGradient_particleWeakGradient f).memLp_grad)
    hpt

theorem particleEnergy_abs_le {A : InteractionData d} (f f' : ParticleH1 A N)
    (hf' : f'.1 = fun x => |f.1 x|) : particleEnergy A N f' ≤ particleEnergy A N f := by
  have hG := (isParticleWeakGradient_particleWeakGradient f).abs
  rw [← hf'] at hG
  refine particleEnergy_le_of_pointwise f f' hG fun x => ?_
  split_ifs
  · exact le_rfl
  · exact (particleTangentNormSq_neg' _).le
  · simpa [particleTangentNormSq] using particleTangentNormSq_nonneg' (particleWeakGradient f x)

theorem particleEnergy_max_const_le {A : InteractionData d} (f f' : ParticleH1 A N) (c : ℝ)
    (hf' : f'.1 = fun x => max (f.1 x) c) : particleEnergy A N f' ≤ particleEnergy A N f := by
  have hG := (isParticleWeakGradient_particleWeakGradient f).max_const c
  rw [← hf'] at hG
  refine particleEnergy_le_of_pointwise f f' hG fun x => ?_
  split_ifs
  · exact le_rfl
  · simpa [particleTangentNormSq] using particleTangentNormSq_nonneg' (particleWeakGradient f x)

theorem particleEnergy_min_const_le {A : InteractionData d} (f f' : ParticleH1 A N) (c : ℝ)
    (hf' : f'.1 = fun x => min (f.1 x) c) : particleEnergy A N f' ≤ particleEnergy A N f := by
  have hG := (isParticleWeakGradient_particleWeakGradient f).min_const c
  rw [← hf'] at hG
  refine particleEnergy_le_of_pointwise f f' hG fun x => ?_
  split_ifs
  · exact le_rfl
  · simpa [particleTangentNormSq] using particleTangentNormSq_nonneg' (particleWeakGradient f x)

theorem particleEnergy_affine {A : InteractionData d} (f f' : ParticleH1 A N) (a b : ℝ)
    (hf' : f'.1 = fun x => a * f.1 x + b) :
    particleEnergy A N f' = a ^ 2 * particleEnergy A N f := by
  have hG := (isParticleWeakGradient_particleWeakGradient f).affine a b
  rw [← hf'] at hG
  rw [particleEnergy_eq_of_isParticleWeakGradient f' hG]
  simp_rw [particleTangentNormSq_smul']
  exact integral_const_mul _ _

/-! ### Stability of the test class -/

section Stability

variable {A : InteractionData d}

theorem MemParticleH1.abs {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) :
    MemParticleH1 A N (fun x => |f x|) :=
  hf.elim fun _ hg => ⟨_, hg.abs⟩

theorem MemParticleH1.max_const {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (c : ℝ) :
    MemParticleH1 A N (fun x => max (f x) c) :=
  hf.elim fun _ hg => ⟨_, hg.max_const c⟩

theorem MemParticleH1.min_const {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (c : ℝ) :
    MemParticleH1 A N (fun x => min (f x) c) :=
  hf.elim fun _ hg => ⟨_, hg.min_const c⟩

theorem MemParticleH1.affine {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (a b : ℝ) :
    MemParticleH1 A N (fun x => a * f x + b) :=
  hf.elim fun _ hg => ⟨_, hg.affine a b⟩

theorem MemParticleH1.mul_W1infty {f w : ParticleSpace d N → ℝ}
    {h : ParticleSpace d N → Fin N → Tangent d} (hf : MemParticleH1 A N f)
    (hw : IsParticleHaarWeakGradientLp ∞ N w h) :
    MemParticleH1 A N (fun x => f x * w x) :=
  hf.elim fun _ hg => ⟨_, hg.mul_W1infty hw⟩

end Stability

/-! ### Symmetry -/

theorem IsSymmetricParticleFun.comp_scalar {A : InteractionData d} {u : ParticleSpace d N → ℝ}
    (hu : IsSymmetricParticleFun A N u) (ψ : ℝ → ℝ) :
    IsSymmetricParticleFun A N (fun x => ψ (u x)) := fun σ => by
  filter_upwards [hu σ] with x hx
  simpa [Function.comp_def] using congrArg ψ hx

theorem IsSymmetricParticleTest.comp_scalar {A : InteractionData d} {f f' : ParticleH1 A N}
    (hf : IsSymmetricParticleTest f) (ψ : ℝ → ℝ) (hf' : f'.1 = fun x => ψ (f.1 x)) :
    IsSymmetricParticleTest f' := by
  unfold IsSymmetricParticleTest at hf ⊢
  rw [hf']
  exact IsSymmetricParticleFun.comp_scalar hf ψ

/-! ### Entropy homogeneity -/

theorem entropyIntegrand_mul {a t c : ℝ} (hc : 0 < c) :
    entropyIntegrand (c * a) (c * t) = c * entropyIntegrand a t := by
  unfold entropyIntegrand
  rw [mul_div_mul_left _ _ hc.ne']
  ring

theorem homogeneousEntropy_const_mul {α : Type*} [MeasurableSpace α] (P : Measure α) (v : α → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    homogeneousEntropy P (fun x => c * v x) = ENNReal.ofReal c * homogeneousEntropy P v := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [homogeneousEntropy]
  have hI : ∫ x, c * v x ∂P = c * ∫ x, v x ∂P := integral_const_mul _ _
  by_cases h0 : ∫ x, v x ∂P = 0
  · rw [homogeneousEntropy_of_integral_eq_zero h0,
      homogeneousEntropy_of_integral_eq_zero (by rw [hI, h0, mul_zero]), mul_zero]
  · have h1 : ∫ x, c * v x ∂P ≠ 0 := by rw [hI]; exact mul_ne_zero hc.ne' h0
    rw [homogeneousEntropy_of_integral_ne_zero h1, homogeneousEntropy_of_integral_ne_zero h0,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [hI, entropyIntegrand_mul hc, ENNReal.ofReal_mul hc.le]

theorem homogeneousEntropy_sq_const_mul {α : Type*} [MeasurableSpace α] (P : Measure α)
    (f : α → ℝ) (a : ℝ) :
    homogeneousEntropy P (fun x => (a * f x) ^ 2) =
      ENNReal.ofReal (a ^ 2) * homogeneousEntropy P (fun x => f x ^ 2) := by
  have := homogeneousEntropy_const_mul P (fun x => f x ^ 2) (sq_nonneg a)
  simpa only [mul_pow] using this

end DGPS

namespace DGPS.Analysis

open DGPS MeasureTheory

/-- FOU011 canonical bundle: particle contraction closure for a fixed Gibbs law `P_N`.

1. weak-gradient chain formulas for `|u|`, `max (u, c)`, `min (u, c)`, `a u + b` and the product with
   a `W^{1,∞}` cutoff, in `H¹(P_N)`;
2. stability of the test class `MemParticleH1` under these operations;
3. energy: the three contractions do not increase `E_N`, and `f ↦ a f + b` multiplies it by `a²`;
4. every scalar transformation of a permutation-invariant function / test stays invariant;
5. homogeneous entropy scales linearly under `v ↦ c v` (`c ≥ 0`), hence by `a²` for `f ↦ a f`. -/
theorem particle_contraction_closure (d : ℕ) (A : InteractionData d) (N : ℕ+) :
    (∀ (u : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d),
      IsParticleWeakGradient A N u g →
        IsParticleWeakGradient A N (fun x => |u x|)
          (fun x => if 0 < u x then g x else if u x < 0 then -g x else 0) ∧
        (∀ c : ℝ,
          IsParticleWeakGradient A N (fun x => max (u x) c) (fun x => if c < u x then g x else 0) ∧
          IsParticleWeakGradient A N (fun x => min (u x) c) (fun x => if u x < c then g x else 0)) ∧
        (∀ a b : ℝ, IsParticleWeakGradient A N (fun x => a * u x + b) (fun x => a • g x)) ∧
        (∀ (w : ParticleSpace d N → ℝ) (h : ParticleSpace d N → Fin N → Tangent d),
          IsParticleHaarWeakGradientLp ∞ N w h →
            IsParticleWeakGradient A N (fun x => u x * w x) (fun x => w x • g x + u x • h x))) ∧
    (∀ f : ParticleH1 A N,
      MemParticleH1 A N (fun x => |f.1 x|) ∧
      (∀ c : ℝ, MemParticleH1 A N (fun x => max (f.1 x) c) ∧
        MemParticleH1 A N (fun x => min (f.1 x) c)) ∧
      (∀ a b : ℝ, MemParticleH1 A N (fun x => a * f.1 x + b)) ∧
      (∀ (w : ParticleSpace d N → ℝ) (h : ParticleSpace d N → Fin N → Tangent d),
        IsParticleHaarWeakGradientLp ∞ N w h → MemParticleH1 A N (fun x => f.1 x * w x))) ∧
    (∀ f f' : ParticleH1 A N,
      (f'.1 = (fun x => |f.1 x|) → particleEnergy A N f' ≤ particleEnergy A N f) ∧
      (∀ c : ℝ, (f'.1 = (fun x => max (f.1 x) c) → particleEnergy A N f' ≤ particleEnergy A N f) ∧
        (f'.1 = (fun x => min (f.1 x) c) → particleEnergy A N f' ≤ particleEnergy A N f)) ∧
      (∀ a b : ℝ, f'.1 = (fun x => a * f.1 x + b) →
        particleEnergy A N f' = a ^ 2 * particleEnergy A N f)) ∧
    (∀ ψ : ℝ → ℝ,
      (∀ u : ParticleSpace d N → ℝ, IsSymmetricParticleFun A N u →
        IsSymmetricParticleFun A N (fun x => ψ (u x))) ∧
      (∀ f f' : ParticleH1 A N, IsSymmetricParticleTest f → f'.1 = (fun x => ψ (f.1 x)) →
        IsSymmetricParticleTest f')) ∧
    (∀ (v : ParticleSpace d N → ℝ) (c : ℝ), 0 ≤ c →
      homogeneousEntropy (particleLaw A N) (fun x => c * v x) =
        ENNReal.ofReal c * homogeneousEntropy (particleLaw A N) v) ∧
    (∀ (f : ParticleSpace d N → ℝ) (a : ℝ),
      homogeneousEntropy (particleLaw A N) (fun x => (a * f x) ^ 2) =
        ENNReal.ofReal (a ^ 2) * homogeneousEntropy (particleLaw A N) (fun x => f x ^ 2)) :=
  ⟨fun _ _ hg => ⟨hg.abs, fun c => ⟨hg.max_const c, hg.min_const c⟩, fun a b => hg.affine a b,
      fun _ _ hw => hg.mul_W1infty hw⟩,
   fun f => ⟨f.2.abs, fun c => ⟨f.2.max_const c, f.2.min_const c⟩, fun a b => f.2.affine a b,
      fun _ _ hw => f.2.mul_W1infty hw⟩,
   fun f f' => ⟨particleEnergy_abs_le f f',
      fun c => ⟨particleEnergy_max_const_le f f' c, particleEnergy_min_const_le f f' c⟩,
      fun a b => particleEnergy_affine f f' a b⟩,
   fun ψ => ⟨fun _ hu => hu.comp_scalar ψ, fun _ _ hf hf' => hf.comp_scalar ψ hf'⟩,
   fun v _ hc => homogeneousEntropy_const_mul _ v hc,
   fun f a => homogeneousEntropy_sq_const_mul _ f a⟩

end DGPS.Analysis
