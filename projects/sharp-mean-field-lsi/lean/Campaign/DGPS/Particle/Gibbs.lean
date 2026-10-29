import DGPS.Foundations.Torus
import DGPS.Model.Data

/-!
# Gibbs particle law and unscaled form (DEF016)

INTERFACES/definitions.md §4, common_lemmas.md DEF016. For `N : ℕ+` the particle space is
`(𝕋^d)^N` (`ParticleSpace d N`, functions `Fin N → Torus d`) with product Haar probability
`particleHaar d N = m^{⊗N}`. For continuous interaction data `A`:

* `particleHamiltonian A N x = ∑ᵢ V(xᵢ) + (1/(2N)) ∑ᵢ ∑ⱼ W(xᵢ, xⱼ)` (the double sum includes the
  pointwise zero diagonal; the factor is the reciprocal `(2N)⁻¹`);
* `particlePartition A N = ∫ exp(-H_N) dm^N`, `particleDensity A N = Z_N⁻¹ exp(-H_N)`,
  `particleLaw A N = particleDensity · m^N` as a measure (`withDensity`);
* `ParticleH1 A N` is the real weighted weak `H¹(P_N)` space, with `L²(P_N)` function and gradient
  and the distributional integration-by-parts identity against smooth periodic tests on
  `(𝕋^d)^N` (integrals against `m^N`; by the fixed-`N` density bounds `L²(P_N) = L²(m^N)`,
  `memLp_particleLaw_iff`);
* `particleEnergy A N f = ∫ ∑ᵢ |∇ᵢ f|² dP_N` — no factor `1/N`, Euclidean sum of squares over
  labels and coordinates (`particleTangentNormSq`).

Well-posedness: `0 < Z_N < ∞`, explicit two-sided bounds on the density, `P_N` is a probability
measure equivalent to `m^N`, and the scaled/unscaled forms agree (`particleLaw_eq_smul`).
-/

open MeasureTheory
open scoped ContDiff ENNReal

namespace DGPS

/-- The particle space `(𝕋^d)^N`. -/
abbrev ParticleSpace (d : ℕ) (N : ℕ+) := Fin N → Torus d

/-- Product Haar probability `m^{⊗N}` on `(𝕋^d)^N`. -/
noncomputable def particleHaar (d : ℕ) (N : ℕ+) : Measure (ParticleSpace d N) :=
  Measure.pi fun _ => haar d

instance (d : ℕ) (N : ℕ+) : IsProbabilityMeasure (particleHaar d N) := by
  unfold particleHaar; infer_instance

/-- The Hamiltonian `H_N(x) = ∑ᵢ V(xᵢ) + (2N)⁻¹ ∑ᵢ ∑ⱼ W(xᵢ, xⱼ)`; the double sum runs over all
pairs including the (zero) diagonal. -/
noncomputable def particleHamiltonian {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (x : ParticleSpace d N) : ℝ :=
  ∑ i, A.V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, A.W (x i) (x j)

/-- The partition function `Z_N = ∫ exp(-H_N) dm^N`. -/
noncomputable def particlePartition {d : ℕ} (A : InteractionData d) (N : ℕ+) : ℝ :=
  ∫ x, Real.exp (-particleHamiltonian A N x) ∂particleHaar d N

/-- The Gibbs density `Z_N⁻¹ exp(-H_N)` with respect to `m^N`. -/
noncomputable def particleDensity {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (x : ParticleSpace d N) : ℝ :=
  (particlePartition A N)⁻¹ * Real.exp (-particleHamiltonian A N x)

/-- The Gibbs particle law `P_N = Z_N⁻¹ exp(-H_N) m^N`. -/
noncomputable def particleLaw {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    Measure (ParticleSpace d N) :=
  (particleHaar d N).withDensity fun x => ENNReal.ofReal (particleDensity A N x)

/-! ### Weak gradients on the particle torus -/

/-- Periodic lift `(ℝ^d)^N → (𝕋^d)^N`. -/
def particleLift {d : ℕ} {N : ℕ+} (y : Fin N → Fin d → ℝ) : ParticleSpace d N :=
  fun i => torusLift (y i)

/-- Smooth periodic function on `(𝕋^d)^N`: its periodic lift is `C^∞`. -/
def IsSmoothPeriodicParticle {d : ℕ} {N : ℕ+} (φ : ParticleSpace d N → ℝ) : Prop :=
  ContDiff ℝ ∞ (φ ∘ particleLift)

/-- The partial derivative `∂_{(i,j)} φ` (label `i`, coordinate `j`) computed on the lift at the
representative in `(0,1]^{dN}`. -/
noncomputable def particlePartial {d : ℕ} {N : ℕ+} (i : Fin N) (j : Fin d)
    (φ : ParticleSpace d N → ℝ) (x : ParticleSpace d N) : ℝ :=
  fderiv ℝ (φ ∘ particleLift) (fun k => SharpLSI.secT (x k))
    (Pi.single i (Pi.single j (1 : ℝ)))

/-- `g = (∇₁f, …, ∇_N f)` is the weak gradient of `f` in the weighted space `H¹(P_N)`: `f` and `g`
are in `L²(P_N)` and `∫ f ∂_{ij}φ dm^N = -∫ gᵢⱼ φ dm^N` for all smooth periodic `φ`, all labels
`i` and coordinates `j`. -/
structure IsParticleWeakGradient {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d) : Prop where
  memLp : MemLp f 2 (particleLaw A N)
  memLp_grad : MemLp g 2 (particleLaw A N)
  ibp : ∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ → ∀ (i : Fin N) (j : Fin d),
    ∫ x, f x * particlePartial i j φ x ∂particleHaar d N =
      -∫ x, g x i j * φ x ∂particleHaar d N

/-- `f ∈ H¹(P_N)`: `f` has an `L²(P_N)` weak gradient. -/
def MemParticleH1 {d : ℕ} (A : InteractionData d) (N : ℕ+) (f : ParticleSpace d N → ℝ) : Prop :=
  ∃ g, IsParticleWeakGradient A N f g

/-- The real weighted Sobolev space `H¹(P_N)` of tests, as a subtype of functions. -/
def ParticleH1 {d : ℕ} (A : InteractionData d) (N : ℕ+) : Type :=
  {f : ParticleSpace d N → ℝ // MemParticleH1 A N f}

instance {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    CoeFun (ParticleH1 A N) fun _ => ParticleSpace d N → ℝ := ⟨Subtype.val⟩

/-- The weak gradient of a test `f ∈ H¹(P_N)` (a chosen representative, unique a.e.). -/
noncomputable def particleWeakGradient {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) : ParticleSpace d N → Fin N → Tangent d :=
  f.2.choose

/-- The Gibbs Dirichlet energy `E_N(f) = ∫ ∑ᵢ |∇ᵢ f|² dP_N` (no factor `1/N`). -/
noncomputable def particleEnergy {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) : ℝ :=
  ∫ x, particleTangentNormSq (particleWeakGradient f x) ∂particleLaw A N

theorem isParticleWeakGradient_particleWeakGradient {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) : IsParticleWeakGradient A N f.1 (particleWeakGradient f) :=
  f.2.choose_spec

theorem particleEnergy_eq {d : ℕ} {A : InteractionData d} {N : ℕ+} (f : ParticleH1 A N) :
    particleEnergy A N f =
      ∫ x, ∑ i, ∑ j, particleWeakGradient f x i j ^ 2 ∂particleLaw A N := by
  simp [particleEnergy, particleTangentNormSq_eq]

theorem particleEnergy_nonneg {d : ℕ} {A : InteractionData d} {N : ℕ+} (f : ParticleH1 A N) :
    0 ≤ particleEnergy A N f :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

end DGPS

namespace DGPS.Particle

open DGPS

variable {d : ℕ} (A : InteractionData d) (N : ℕ+)

theorem particleHamiltonian_continuous : Continuous (particleHamiltonian A N) := by
  unfold particleHamiltonian
  refine (continuous_finsetSum _ fun i _ => A.V_continuous.comp (continuous_apply i)).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_))
  have h : Continuous fun x : ParticleSpace d N => (x i, x j) := by fun_prop
  exact A.W_continuous.comp h

theorem particleHamiltonian_measurable : Measurable (particleHamiltonian A N) :=
  (particleHamiltonian_continuous A N).measurable

/-- Zero diagonal: the double sum equals the off-diagonal sum. -/
theorem particleHamiltonian_offDiag (x : ParticleSpace d N) :
    particleHamiltonian A N x =
      ∑ i, A.V (x i) + (1 / (2 * (N : ℝ))) *
        ∑ i, ∑ j ∈ Finset.univ.erase i, A.W (x i) (x j) := by
  unfold particleHamiltonian
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), A.W_diag, zero_add]

/-- `H_N` is bounded: the torus power is compact. -/
theorem particleHamiltonian_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |particleHamiltonian A N x| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (particleHamiltonian_continuous A N).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x =>
    le_max_of_le_left (by simpa using hC x (Set.mem_univ x))⟩

theorem exp_neg_hamiltonian_integrable : Integrable (fun x => Real.exp (-particleHamiltonian A N x))
    (particleHaar d N) := by
  have hc : Continuous fun x => Real.exp (-particleHamiltonian A N x) :=
    Real.continuous_exp.comp (particleHamiltonian_continuous A N).neg
  obtain ⟨M, -, hM⟩ := particleHamiltonian_bounded A N
  refine Integrable.of_bound hc.aestronglyMeasurable (Real.exp M) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM x)).1])

/-- Two-sided bound on `Z_N`: `e^{-M} ≤ Z_N ≤ e^{M}` whenever `|H_N| ≤ M`. -/
theorem particlePartition_bounds {M : ℝ} (hM : ∀ x, |particleHamiltonian A N x| ≤ M) :
    Real.exp (-M) ≤ particlePartition A N ∧ particlePartition A N ≤ Real.exp M := by
  have hi := exp_neg_hamiltonian_integrable A N
  constructor
  · have : ∫ _x, Real.exp (-M) ∂particleHaar d N ≤ particlePartition A N :=
      integral_mono (integrable_const _) hi fun x =>
        Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM x)).2])
    simpa using this
  · have : particlePartition A N ≤ ∫ _x, Real.exp M ∂particleHaar d N :=
      integral_mono hi (integrable_const _) fun x =>
        Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM x)).1])
    simpa using this

/-- `0 < Z_N`. -/
theorem particlePartition_pos : 0 < particlePartition A N := by
  obtain ⟨M, -, hM⟩ := particleHamiltonian_bounded A N
  exact lt_of_lt_of_le (Real.exp_pos _) (particlePartition_bounds A N hM).1

/-- `Z_N < ∞` (as a real number it is finite; the integrand is bounded and integrable). -/
theorem particlePartition_normalizable :
    0 < particlePartition A N ∧ ∃ C : ℝ, particlePartition A N ≤ C :=
  ⟨particlePartition_pos A N, by
    obtain ⟨M, -, hM⟩ := particleHamiltonian_bounded A N
    exact ⟨_, (particlePartition_bounds A N hM).2⟩⟩

theorem particleDensity_pos (x : ParticleSpace d N) : 0 < particleDensity A N x :=
  mul_pos (inv_pos.2 (particlePartition_pos A N)) (Real.exp_pos _)

theorem particleDensity_continuous : Continuous (particleDensity A N) :=
  continuous_const.mul (Real.continuous_exp.comp (particleHamiltonian_continuous A N).neg)

theorem particleDensity_measurable : Measurable (particleDensity A N) :=
  (particleDensity_continuous A N).measurable

/-- Fixed-`N` two-sided density bounds `e^{-2M} ≤ dP_N/dm^N ≤ e^{2M}`. -/
theorem particleDensity_bounds {M : ℝ} (hM : ∀ x, |particleHamiltonian A N x| ≤ M) (x : ParticleSpace d N) :
    Real.exp (-(2 * M)) ≤ particleDensity A N x ∧ particleDensity A N x ≤ Real.exp (2 * M) := by
  obtain ⟨hZ1, hZ2⟩ := particlePartition_bounds A N hM
  have hZ := particlePartition_pos A N
  have hx1 : Real.exp (-M) ≤ Real.exp (-particleHamiltonian A N x) :=
    Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM x)).2])
  have hx2 : Real.exp (-particleHamiltonian A N x) ≤ Real.exp M :=
    Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM x)).1])
  unfold particleDensity
  have e1 : Real.exp (-(2 * M)) = Real.exp (-M) / Real.exp M := by
    rw [← Real.exp_sub]; ring_nf
  have e2 : Real.exp (2 * M) = Real.exp M / Real.exp (-M) := by
    rw [← Real.exp_sub]; ring_nf
  rw [inv_mul_eq_div]
  constructor
  · rw [e1]; exact div_le_div₀ (Real.exp_pos _).le hx1 hZ hZ2
  · rw [e2]; exact div_le_div₀ (Real.exp_pos _).le hx2 (Real.exp_pos _) hZ1

/-- Positive lower and finite upper bounds on the Gibbs density (the shape of DEF017's
`particle_weight_bounds`). -/
theorem particleDensity_bounded :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x, c ≤ particleDensity A N x ∧ particleDensity A N x ≤ C := by
  obtain ⟨M, hM0, hM⟩ := particleHamiltonian_bounded A N
  refine ⟨Real.exp (-(2 * M)), Real.exp (2 * M), Real.exp_pos _, Real.exp_le_exp.2 (by linarith),
    fun x => particleDensity_bounds A N hM x⟩

/-- Normalization: `∫ density dm^N = 1`. -/
theorem integral_particleDensity : ∫ x, particleDensity A N x ∂particleHaar d N = 1 := by
  unfold particleDensity
  rw [integral_const_mul]
  change (particlePartition A N)⁻¹ * particlePartition A N = 1
  exact inv_mul_cancel₀ (particlePartition_pos A N).ne'

theorem particleDensity_integrable : Integrable (particleDensity A N) (particleHaar d N) :=
  (exp_neg_hamiltonian_integrable A N).const_mul _

/-- `P_N` is a probability measure. -/
instance particleLaw_isProbabilityMeasure : IsProbabilityMeasure (particleLaw A N) := by
  refine ⟨?_⟩
  unfold particleLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (particleDensity_integrable A N)
      (Filter.Eventually.of_forall fun x => (particleDensity_pos A N x).le),
    integral_particleDensity]
  simp

theorem particleLaw_isProbabilityMeasure' : IsProbabilityMeasure (particleLaw A N) :=
  inferInstance

/-- Scaled/unscaled equivalence: `P_N = Z_N⁻¹ · (exp(-H_N) m^N)` as measures. -/
theorem particleLaw_eq_smul :
    particleLaw A N = ENNReal.ofReal (particlePartition A N)⁻¹ •
      (particleHaar d N).withDensity fun x => ENNReal.ofReal (Real.exp (-particleHamiltonian A N x)) := by
  unfold particleLaw
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  · congr 1
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, particleDensity]
    rw [ENNReal.ofReal_mul (inv_pos.2 (particlePartition_pos A N)).le, ENNReal.ofReal_inv_of_pos
      (particlePartition_pos A N)]

/-- Integration against `P_N` is integration against `density · m^N`. -/
theorem integral_particleLaw (g : ParticleSpace d N → ℝ) :
    ∫ x, g x ∂particleLaw A N = ∫ x, particleDensity A N x * g x ∂particleHaar d N := by
  unfold particleLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (particleDensity_measurable A N).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (particleDensity_pos A N x).le]

/-- Mutual absolute continuity. -/
theorem particleLaw_absolutelyContinuous : particleLaw A N ≪ particleHaar d N :=
  withDensity_absolutelyContinuous _ _

theorem particleHaar_absolutelyContinuous : particleHaar d N ≪ particleLaw A N :=
  withDensity_absolutelyContinuous' (particleDensity_measurable A N).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa using (particleDensity_pos A N x))

/-- Fixed-`N` equivalence of `L²` classes: `L²(P_N) = L²(m^N)`. -/
theorem memLp_particleLaw_iff {E : Type*} [NormedAddCommGroup E] {f : ParticleSpace d N → E}
    {p : ℝ≥0∞} :
    MemLp f p (particleLaw A N) ↔ MemLp f p (particleHaar d N) := by
  obtain ⟨c, C, hc, hcC, hb⟩ := particleDensity_bounded A N
  have h1 : particleLaw A N ≤ ENNReal.ofReal C • particleHaar d N := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [particleLaw, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ x in s, ENNReal.ofReal (particleDensity A N x) ∂particleHaar d N
        ≤ ∫⁻ _ in s, ENNReal.ofReal C ∂particleHaar d N :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hb x).2
      _ = _ := by rw [setLIntegral_const]
  have h2 : particleHaar d N ≤ ENNReal.ofReal c⁻¹ • particleLaw A N := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, particleLaw, withDensity_apply _ hs]
    calc particleHaar d N s = ∫⁻ _ in s, 1 ∂particleHaar d N := by simp
      _ ≤ ∫⁻ x in s, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (particleDensity A N x) ∂particleHaar d N :=
          lintegral_mono fun x => by
            rw [← ENNReal.ofReal_mul (inv_pos.2 hc).le]
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (by
              rw [inv_mul_eq_div, le_div_iff₀ hc]; simpa using (hb x).1)
      _ = _ := by rw [lintegral_const_mul _ (particleDensity_measurable A N).ennreal_ofReal]
  constructor
  · intro h
    exact h.of_measure_le_smul ENNReal.ofReal_ne_top h2
  · intro h
    exact h.of_measure_le_smul ENNReal.ofReal_ne_top h1

/-- Sanity: for the trivial data the Hamiltonian vanishes, `Z_N = 1` and `P_N = m^N`. -/
theorem particleLaw_zero (d : ℕ) (N : ℕ+) :
    particleLaw (InteractionData.zero d) N = particleHaar d N := by
  have hH : particleHamiltonian (InteractionData.zero d) N = fun _ => 0 := by
    funext x; simp [particleHamiltonian, InteractionData.zero]
  have hZ : particlePartition (InteractionData.zero d) N = 1 := by
    simp [particlePartition, hH]
  unfold particleLaw
  have : (fun x => ENNReal.ofReal (particleDensity (InteractionData.zero d) N x)) = fun _ => 1 := by
    funext x; simp [particleDensity, hZ, hH]
  rw [this]; exact withDensity_one

end DGPS.Particle
