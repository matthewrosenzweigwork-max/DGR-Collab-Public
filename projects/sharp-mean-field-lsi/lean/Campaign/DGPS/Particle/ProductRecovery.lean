import DGPS.Particle.PartitionLimit
import DGPS.Foundations.SobolevEntropy
import DGPS.Model.SpeciesRate

/-!
# Rounded finite species product entropy (LIP021)

For a fixed finite species family `F` and a labelling `σ_N : Fin N → Fin q` of the `N` particles
by species (with `n_s = #σ_N⁻¹(s)` labels of species `s`, `p_s = n_s / N`), the product law
`ν_N = ⨂ᵢ ρ_{σ_N i} m` satisfies the exact identity
`N⁻¹ H(ν_N | P_N) = ∑ₛ pₛ [H(ρₛ|m) + ∫ V ρₛ] + ½ ∑ₛₜ pₛ pₜ Uₛₜ - (2N)⁻¹ ∑ₛ pₛ Uₛₛ + N⁻¹ log Z_N`,
and whenever `pₛ → θₛ` its limit is the species gap `G_θ`. Rounded labellings with `pₛ → θₛ`
exist (floor allocations, remainder to the last species).
-/

open MeasureTheory InformationTheory ProbabilityTheory Filter Topology
open DGPS.Lipschitz
open scoped ENNReal

namespace DGPS.Particle.ProductRecovery

theorem klDiv_pi_sum {α : Type*} [MeasurableSpace α] (n : ℕ) (μ ν : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
    have : (Measure.pi μ) = Measure.pi ν := by
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    rw [this, klDiv_self]; simp
  | succ n ih =>
    have e := measurePreserving_piFinSuccAbove μ 0
    have e' := measurePreserving_piFinSuccAbove ν 0
    rw [← klDiv_map_equiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0),
      e.map_eq, e'.map_eq, klDiv_prod_eq_add, ih, Fin.sum_univ_succ]
    simp

/-- Pair marginal of a product law with distinct factors. -/
theorem pi_map_pair' {α : Type*} [MeasurableSpace α] (n : ℕ) (μ : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi μ).map (fun x => (x i, x j)) = (μ i).prod (μ j) := by
  have hind := iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := hind.indepFun hij
  have hm := (indepFun_iff_map_prod_eq_prod_map_map
    (μ := Measure.pi μ) (f := fun ω : Fin n → α => id (ω i))
    (g := fun ω : Fin n → α => id (ω j)) (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 h
  have hi := (measurePreserving_eval μ i).map_eq
  have hj := (measurePreserving_eval μ j).map_eq
  simp only [id] at hm
  rw [hm]
  have e1 : Measure.map (fun ω : Fin n → α => ω i) (Measure.pi μ) = μ i := hi
  have e2 : Measure.map (fun ω : Fin n → α => ω j) (Measure.pi μ) = μ j := hj
  rw [e1, e2]

theorem integral_pi_pair' {α : Type*} [MeasurableSpace α] (n : ℕ) (μ : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] {i j : Fin n} (hij : i ≠ j) (g : α × α → ℝ)
    (hg : Measurable g) :
    ∫ x, g (x i, x j) ∂(Measure.pi μ) = ∫ p, g p ∂((μ i).prod (μ j)) := by
  rw [← pi_map_pair' n μ hij, integral_map]
  · exact ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
  · exact hg.aestronglyMeasurable

theorem integral_pi_single' {α : Type*} [MeasurableSpace α] (n : ℕ) (μ : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) (g : α → ℝ) (hg : Measurable g) :
    ∫ x, g (x i) ∂(Measure.pi μ) = ∫ a, g a ∂(μ i) := by
  have hi : Measure.map (fun ω : Fin n → α => ω i) (Measure.pi μ) = μ i :=
    (measurePreserving_eval μ i).map_eq
  conv_rhs => rw [← hi]
  rw [integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]


variable {d : ℕ}

/-- The law `ρ_s m` of species `s`. -/
noncomputable def speciesLaw (F : SpeciesFamily d) (s : Fin F.count) : Measure (Torus d) :=
  (densityMeasure (F.density s) : Measure (Torus d))

instance (F : SpeciesFamily d) (s : Fin F.count) : IsProbabilityMeasure (speciesLaw F s) :=
  (densityMeasure (F.density s)).prop

/-- The product law `ν_N = ⨂ᵢ ρ_{σ i} m` for a species labelling `σ`. -/
noncomputable def productLaw (F : SpeciesFamily d) {N : ℕ+} (σ : Fin N → Fin F.count) :
    Measure (ParticleSpace d N) :=
  Measure.pi fun i => speciesLaw F (σ i)

instance (F : SpeciesFamily d) {N : ℕ+} (σ : Fin N → Fin F.count) :
    IsProbabilityMeasure (productLaw F σ) := by
  unfold productLaw; infer_instance

/-- The cross interaction `U_{st} = ∬ W dμ ⊗ dν`. -/
noncomputable def crossEnergy (A : InteractionData d) (μ ν : Measure (Torus d)) : ℝ :=
  ∫ p, A.W p.1 p.2 ∂(μ.prod ν)

theorem crossEnergy_self (A : InteractionData d) (μ : Measure (Torus d)) :
    crossEnergy A μ μ = interactionEnergy A μ := rfl

theorem particleLaw_eq_tilted (A : InteractionData d) (N : ℕ+) :
    particleLaw A N = (particleHaar d N).tilted fun x => -particleHamiltonian A N x := by
  unfold particleLaw
  rw [Measure.tilted]
  congr 1
  funext x
  congr 1
  simp only [particleDensity, particlePartition]
  rw [div_eq_inv_mul]

theorem integral_hamiltonian_productLaw (A : InteractionData d) (F : SpeciesFamily d) {N : ℕ+}
    (σ : Fin N → Fin F.count) :
    ∫ x, particleHamiltonian A N x ∂productLaw F σ =
      ∑ i, potentialEnergy A (speciesLaw F (σ i)) +
        (1 / (2 * (N : ℝ))) * ∑ i, ∑ j,
          (if i = j then 0 else crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ j))) := by
  set P : Measure (ParticleSpace d N) := productLaw F σ with hP
  have hV : ∀ i : Fin N, Integrable (fun x : ParticleSpace d N => A.V (x i)) P := fun i =>
    (A.V_continuous.comp (continuous_apply i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : ∀ i j : Fin N, Integrable (fun x : ParticleSpace d N => A.W (x i) (x j)) P := by
    intro i j
    have h : Continuous fun x : ParticleSpace d N => (x i, x j) := by fun_prop
    exact Continuous.integrable_of_hasCompactSupport (A.W_continuous.comp h)
      (HasCompactSupport.of_compactSpace _)
  unfold particleHamiltonian
  rw [integral_add (integrable_finsetSum _ fun i _ => hV i)
    ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hW i j).const_mul _),
    integral_finsetSum _ fun i _ => hV i, integral_const_mul,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hW i j]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_pi_single' N (fun i => speciesLaw F (σ i)) i A.V A.V_continuous.measurable
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hW i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp [A.W_diag]
    · simp only [hij, ↓reduceIte]
      exact integral_pi_pair' N (fun i => speciesLaw F (σ i)) hij (fun p => A.W p.1 p.2)
        A.W_continuous.measurable


/-- The entropy `H(ρ_s | m)` as a real number. -/
noncomputable def speciesEntropy (F : SpeciesFamily d) (s : Fin F.count) : ℝ :=
  (relativeEntropy (speciesLaw F s) (haar d)).toReal

theorem relativeEntropy_speciesLaw_ne_top (F : SpeciesFamily d) (s : Fin F.count) :
    relativeEntropy (speciesLaw F s) (haar d) ≠ ⊤ :=
  (absoluteDensity_entropy_finite (F.density s)).2.2.1

theorem relativeEntropy_productLaw_toReal (A : InteractionData d) (F : SpeciesFamily d) {N : ℕ+}
    (σ : Fin N → Fin F.count) :
    (relativeEntropy (productLaw F σ) (particleLaw A N)).toReal =
      ∑ i, speciesEntropy F (σ i) + ∑ i, potentialEnergy A (speciesLaw F (σ i)) +
        (1 / (2 * (N : ℝ))) * ∑ i, ∑ j,
          (if i = j then 0 else crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ j))) +
        Real.log (particlePartition A N) := by
  have hk : ∀ s, klDiv (speciesLaw F s) (haar d) ≠ ⊤ := fun s => by
    rw [← DGPS.Analysis.relativeEntropy_eq_klDiv]; exact relativeEntropy_speciesLaw_ne_top F s
  have hKL : klDiv (productLaw F σ) (particleHaar d N) =
      ∑ i, klDiv (speciesLaw F (σ i)) (haar d) :=
    klDiv_pi_sum N (fun i => speciesLaw F (σ i)) (fun _ => haar d)
  have hKLne : klDiv (productLaw F σ) (particleHaar d N) ≠ ⊤ := by
    rw [hKL]; exact (ENNReal.sum_lt_top.2 fun i _ => (hk _).lt_top).ne
  obtain ⟨M, -, hM⟩ := particleHamiltonian_bounded A N
  have key := DGPS.Lipschitz.klDiv_tilted_forward (ρ := productLaw F σ) (ν := particleHaar d N)
    (f := fun x => -particleHamiltonian A N x) (B := M)
    (particleHamiltonian_measurable A N).neg (fun x => by simpa using hM x) hKLne
  have := particleLaw_isProbabilityMeasure' A N
  rw [DGPS.Analysis.relativeEntropy_eq_klDiv, particleLaw_eq_tilted, key.2, hKL,
    ENNReal.toReal_sum fun i _ => hk _, integral_neg, integral_hamiltonian_productLaw]
  have : ∀ i, speciesEntropy F (σ i) = (klDiv (speciesLaw F (σ i)) (haar d)).toReal := fun i => by
    unfold speciesEntropy; rw [DGPS.Analysis.relativeEntropy_eq_klDiv]
  simp only [this]
  unfold particlePartition
  ring


/-- The proportion `p_s = n_s / N` of labels of species `s`. -/
noncomputable def proportion {N : ℕ+} {q : ℕ} (σ : Fin N → Fin q) (s : Fin q) : ℝ :=
  (typeCount σ s : ℝ) / (N : ℝ)

theorem product_entropy_identity (A : InteractionData d) (F : SpeciesFamily d) {N : ℕ+}
    (σ : Fin N → Fin F.count) :
    (1 / (N : ℝ)) * (relativeEntropy (productLaw F σ) (particleLaw A N)).toReal =
      ∑ s, proportion σ s * (speciesEntropy F s + potentialEnergy A (speciesLaw F s)) +
        (1 / 2 : ℝ) * ∑ s, ∑ t, proportion σ s * proportion σ t *
          crossEnergy A (speciesLaw F s) (speciesLaw F t) -
        (1 / (2 * (N : ℝ))) * ∑ s, proportion σ s * crossEnergy A (speciesLaw F s) (speciesLaw F s) +
        (1 / (N : ℝ)) * Real.log (particlePartition A N) := by
  have hN : (N : ℝ) ≠ 0 := by positivity
  rw [relativeEntropy_productLaw_toReal]
  have hdiag : ∀ i j : Fin N, (if i = j then (0 : ℝ) else
      crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ j))) =
      crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ j)) -
        (if i = j then crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ i)) else 0) := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hD : ∑ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else
      crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ j))) =
      ∑ i, ∑ j, crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ j)) -
        ∑ i, crossEnergy A (speciesLaw F (σ i)) (speciesLaw F (σ i)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hdiag, Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq]
  rw [hD, sum_comp_typeCount σ (fun s => speciesEntropy F s),
    sum_comp_typeCount σ (fun s => potentialEnergy A (speciesLaw F s)),
    sum_comp_typeCount₂ σ (fun s t => crossEnergy A (speciesLaw F s) (speciesLaw F t)),
    sum_comp_typeCount σ (fun s => crossEnergy A (speciesLaw F s) (speciesLaw F s))]
  have e1 : ∑ s, proportion σ s * (speciesEntropy F s + potentialEnergy A (speciesLaw F s)) =
      (1 / (N : ℝ)) * (∑ s, (typeCount σ s : ℝ) * speciesEntropy F s +
        ∑ s, (typeCount σ s : ℝ) * potentialEnergy A (speciesLaw F s)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold proportion; ring
  have e2 : ∑ s, ∑ t, proportion σ s * proportion σ t *
        crossEnergy A (speciesLaw F s) (speciesLaw F t) =
      (1 / (N : ℝ) ^ 2) * ∑ s, ∑ t, (typeCount σ s : ℝ) * (typeCount σ t : ℝ) *
        crossEnergy A (speciesLaw F s) (speciesLaw F t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold proportion; field_simp
  have e3 : ∑ s, proportion σ s * crossEnergy A (speciesLaw F s) (speciesLaw F s) =
      (1 / (N : ℝ)) * ∑ s, (typeCount σ s : ℝ) *
        crossEnergy A (speciesLaw F s) (speciesLaw F s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold proportion; ring
  rw [e1, e2, e3]
  field_simp
  ring


/-! ### The barycenter energies -/

theorem aemeasurable_density' (ρ : AbsoluteDensity d) : AEMeasurable ρ.density (haar d) :=
  ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2

theorem integral_densityMeasure_eq (ρ : AbsoluteDensity d) (g : Torus d → ℝ) :
    ∫ x, g x ∂(densityMeasure ρ : Measure (Torus d)) = ∫ x, ρ.density x * g x ∂haar d := by
  have h1 : AEMeasurable (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density' ρ)
  rw [densityMeasure_coe, integral_withDensity_eq_integral_toReal_smul₀ h1
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem crossEnergy_densityMeasure (A : InteractionData d) (ρ σ : AbsoluteDensity d) :
    crossEnergy A (densityMeasure ρ : Measure (Torus d)) (densityMeasure σ : Measure (Torus d)) =
      ∫ p, ρ.density p.1 * σ.density p.2 * A.W p.1 p.2 ∂((haar d).prod (haar d)) := by
  unfold crossEnergy
  rw [densityMeasure_coe, densityMeasure_coe]
  have h1 : AEMeasurable (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density' ρ)
  have h2 : AEMeasurable (fun x => ENNReal.ofReal (σ.sqrt x ^ 2)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density' σ)
  rw [prod_withDensity₀ h1 h2]
  have h3 : AEMeasurable (fun z : Torus d × Torus d =>
      ENNReal.ofReal (ρ.sqrt z.1 ^ 2) * ENNReal.ofReal (σ.sqrt z.2 ^ 2))
      ((haar d).prod (haar d)) :=
    (h1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (h2.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  rw [integral_withDensity_eq_integral_toReal_smul₀ h3
    (Filter.Eventually.of_forall fun x =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _)]
  simp [AbsoluteDensity.density]


theorem potentialEnergy_barycenter (A : InteractionData d) (F : SpeciesFamily d) :
    potentialEnergy A (densityMeasure (barycenter F) : Measure (Torus d)) =
      ∑ s, F.weight s * potentialEnergy A (speciesLaw F s) := by
  obtain ⟨C, hC⟩ := A.V_bounded
  have hint : ∀ s : Fin F.count, Integrable (fun x => (F.density s).density x * A.V x) (haar d) :=
    fun s => (F.density s).integrable_density.mul_bdd A.V_continuous.aestronglyMeasurable
      (c := C) (Filter.Eventually.of_forall fun x => by simpa using hC x)
  unfold potentialEnergy
  rw [integral_densityMeasure_eq]
  have e : ∀ x, (barycenter F).density x * A.V x =
      ∑ s, F.weight s * ((F.density s).density x * A.V x) := fun x => by
    rw [SpeciesFamily.barycenter_density_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by simp [AbsoluteDensity.density]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun s _ => (hint s).const_mul _]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]
  congr 1
  exact (integral_densityMeasure_eq (F.density s) A.V).symm

theorem interactionEnergy_barycenter (A : InteractionData d) (F : SpeciesFamily d) :
    interactionEnergy A (densityMeasure (barycenter F) : Measure (Torus d)) =
      ∑ s, ∑ t, F.weight s * F.weight t * crossEnergy A (speciesLaw F s) (speciesLaw F t) := by
  obtain ⟨C, hC⟩ := A.W_bounded
  have hint : ∀ s t : Fin F.count, Integrable (fun p : Torus d × Torus d =>
      (F.density s).density p.1 * (F.density t).density p.2 * A.W p.1 p.2)
      ((haar d).prod (haar d)) := fun s t =>
    ((F.density s).integrable_density.mul_prod (F.density t).integrable_density).mul_bdd
      A.W_continuous.aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun x => by simpa using hC x.1 x.2)
  rw [← crossEnergy_self, crossEnergy_densityMeasure]
  have e : ∀ p : Torus d × Torus d, (barycenter F).density p.1 *
      (barycenter F).density p.2 * A.W p.1 p.2 =
      ∑ s, ∑ t, F.weight s * F.weight t * ((F.density s).density p.1 *
        (F.density t).density p.2 * A.W p.1 p.2) := fun p => by
    rw [SpeciesFamily.barycenter_density_apply, SpeciesFamily.barycenter_density_apply,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [AbsoluteDensity.density]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun t _ => (hint s t).const_mul _]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun t _ => (hint s t).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul]
  congr 1
  exact (crossEnergy_densityMeasure A (F.density s) (F.density t)).symm


/-! ### The limit -/

theorem tendsto_product_entropy (A : InteractionData d) (F : SpeciesFamily d)
    (σ : (N : ℕ+) → Fin N → Fin F.count)
    (hp : ∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (F.weight s))) :
    Tendsto (fun N : ℕ+ =>
      (1 / (N : ℝ)) * (relativeEntropy (productLaw F (σ N)) (particleLaw A N)).toReal) atTop
      (𝓝 (speciesGap A F : ℝ)) := by
  simp_rw [product_entropy_identity]
  have hlog := (partition_function_limit_by_finite_empirical_types A).1
  have hinv : Tendsto (fun N : ℕ+ => (1 / (2 * (N : ℝ)))) atTop (𝓝 0) := by
    have := (tendsto_nat_inv).const_mul (1 / 2 : ℝ)
    simpa [one_div, mul_comm] using this
  have h1 : Tendsto (fun N : ℕ+ => ∑ s, proportion (σ N) s *
      (speciesEntropy F s + potentialEnergy A (speciesLaw F s))) atTop
      (𝓝 (∑ s, F.weight s * (speciesEntropy F s + potentialEnergy A (speciesLaw F s)))) :=
    tendsto_finsetSum _ fun s _ => (hp s).mul_const _
  have h2 : Tendsto (fun N : ℕ+ => ∑ s, ∑ t, proportion (σ N) s * proportion (σ N) t *
      crossEnergy A (speciesLaw F s) (speciesLaw F t)) atTop
      (𝓝 (∑ s, ∑ t, F.weight s * F.weight t *
        crossEnergy A (speciesLaw F s) (speciesLaw F t))) :=
    tendsto_finsetSum _ fun s _ => tendsto_finsetSum _ fun t _ =>
      ((hp s).mul (hp t)).mul_const _
  have h3 : Tendsto (fun N : ℕ+ => ∑ s, proportion (σ N) s *
      crossEnergy A (speciesLaw F s) (speciesLaw F s)) atTop
      (𝓝 (∑ s, F.weight s * crossEnergy A (speciesLaw F s) (speciesLaw F s))) :=
    tendsto_finsetSum _ fun s _ => (hp s).mul_const _
  have h := ((h1.add (h2.const_mul (1 / 2 : ℝ))).sub (hinv.mul h3)).add hlog
  have hval : (speciesGap A F : ℝ) =
      ((∑ s, F.weight s * (speciesEntropy F s + potentialEnergy A (speciesLaw F s))) +
        (1 / 2 : ℝ) * ∑ s, ∑ t, F.weight s * F.weight t *
          crossEnergy A (speciesLaw F s) (speciesLaw F t) -
        0 * ∑ s, F.weight s * crossEnergy A (speciesLaw F s) (speciesLaw F s)) +
        -freeEnergyMinimumReal A := by
    rw [coe_speciesGap, speciesRawGap, potentialEnergy_barycenter, interactionEnergy_barycenter]
    simp only [mul_add, Finset.sum_add_distrib, zero_mul, sub_zero, speciesEntropy, speciesLaw]
    ring
  rw [hval]
  exact h

/-! ### Rounded allocations -/

/-- Any count vector with total `N` is realised by a labelling of `Fin N`. -/
theorem exists_labelling {q N : ℕ} (n : Fin q → ℕ) (h : ∑ s, n s = N) :
    ∃ σ : Fin N → Fin q, ∀ s, typeCount σ s = n s := by
  have hc : Fintype.card (Fin N) = Fintype.card (Σ s : Fin q, Fin (n s)) := by simp [h]
  let e := Fintype.equivOfCardEq hc
  refine ⟨fun i => (e i).1, fun s => ?_⟩
  unfold typeCount
  have h1 : (Finset.univ.filter fun i => (e i).1 = s).card =
      (Finset.univ.filter fun x : (Σ s : Fin q, Fin (n s)) => x.1 = s).card :=
    Finset.card_bij (fun i _ => e i) (fun i hi => by simpa using hi)
      (fun a _ b _ hab => e.injective hab)
      (fun x hx => ⟨e.symm x, by simpa using hx, by simp⟩)
  rw [h1]
  have h2 : (Finset.univ.filter fun x : (Σ s : Fin q, Fin (n s)) => x.1 = s) =
      (Finset.univ : Finset (Fin (n s))).map
        ⟨fun j => (⟨s, j⟩ : Σ s : Fin q, Fin (n s)), fun a b hab => by simpa using hab⟩ := by
    ext ⟨t, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro rfl
      exact ⟨j, rfl⟩
    · rintro ⟨i, hi⟩
      exact (Sigma.mk.inj hi).1.symm
  rw [h2, Finset.card_map]
  simp

theorem tendsto_floor_div (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ+ => (⌊(N : ℝ) * c⌋₊ : ℝ) / (N : ℝ)) atTop (𝓝 c) := by
  have hlow := (tendsto_const_nhds (x := c)).sub tendsto_nat_inv
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_) (fun N => ?_)
  · have hN : (0 : ℝ) < (N : ℝ) := by positivity
    rw [le_div_iff₀ hN]
    have := Nat.lt_floor_add_one ((N : ℝ) * c)
    have e : (c - ((N : ℕ) : ℝ)⁻¹) * (N : ℝ) = (N : ℝ) * c - 1 := by field_simp
    rw [e]
    linarith
  · have hN : (0 : ℝ) < (N : ℝ) := by positivity
    rw [div_le_iff₀ hN]
    have := Nat.floor_le (mul_nonneg hN.le hc)
    linarith

/-- The species receiving the remainder of the rounded allocation. -/
def firstSpecies (F : SpeciesFamily d) : Fin F.count := ⟨0, F.count.pos⟩

/-- The rounded allocation: floors for all species but the first, the remainder to the first. -/
noncomputable def roundCount (F : SpeciesFamily d) (N : ℕ+) (s : Fin F.count) : ℕ :=
  if s = (firstSpecies F) then
    (N : ℕ) - ∑ t ∈ Finset.univ.erase (firstSpecies F),
      ⌊(N : ℝ) * F.weight t⌋₊
  else ⌊(N : ℝ) * F.weight s⌋₊

theorem roundCount_first (F : SpeciesFamily d) (N : ℕ+) :
    roundCount F N (firstSpecies F) =
      (N : ℕ) - ∑ t ∈ Finset.univ.erase (firstSpecies F), ⌊(N : ℝ) * F.weight t⌋₊ := by
  simp [roundCount]

theorem sum_floor_le (F : SpeciesFamily d) (N : ℕ+) :
    ∑ t ∈ Finset.univ.erase (firstSpecies F), ⌊(N : ℝ) * F.weight t⌋₊ ≤ N := by
  have h1 : ((∑ t ∈ Finset.univ.erase (firstSpecies F), ⌊(N : ℝ) * F.weight t⌋₊ : ℕ) : ℝ) ≤ N := by
    push_cast
    calc ∑ t ∈ Finset.univ.erase (firstSpecies F), (⌊(N : ℝ) * F.weight t⌋₊ : ℝ)
        ≤ ∑ t ∈ Finset.univ.erase (firstSpecies F), (N : ℝ) * F.weight t :=
          Finset.sum_le_sum fun t _ =>
            Nat.floor_le (mul_nonneg (by positivity) (F.weight_nonneg t))
      _ = (N : ℝ) * ∑ t ∈ Finset.univ.erase (firstSpecies F), F.weight t := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← F.weight_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun t _ _ => F.weight_nonneg t
      _ = N := mul_one _
  exact_mod_cast h1

theorem sum_roundCount (F : SpeciesFamily d) (N : ℕ+) : ∑ s, roundCount F N s = N := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (firstSpecies F))]
  have h : ∑ t ∈ Finset.univ.erase (firstSpecies F), roundCount F N t =
      ∑ t ∈ Finset.univ.erase (firstSpecies F), ⌊(N : ℝ) * F.weight t⌋₊ :=
    Finset.sum_congr rfl fun t ht => by
      simp [roundCount, Finset.ne_of_mem_erase ht]
  rw [h]
  have := sum_floor_le F N
  rw [roundCount_first]
  omega

theorem tendsto_roundCount (F : SpeciesFamily d) (s : Fin F.count) :
    Tendsto (fun N : ℕ+ => (roundCount F N s : ℝ) / (N : ℝ)) atTop (𝓝 (F.weight s)) := by
  by_cases hs : s = (firstSpecies F)
  · rw [hs]
    have hsum : Tendsto (fun N : ℕ+ => ∑ t ∈ Finset.univ.erase (firstSpecies F),
        (⌊(N : ℝ) * F.weight t⌋₊ : ℝ) / (N : ℝ)) atTop
        (𝓝 (∑ t ∈ Finset.univ.erase (firstSpecies F), F.weight t)) :=
      tendsto_finsetSum _ fun t _ => tendsto_floor_div _ (F.weight_nonneg t)
    have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hsum
    have hw : 1 - ∑ t ∈ Finset.univ.erase (firstSpecies F), F.weight t = F.weight (firstSpecies F) := by
      rw [← F.weight_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (firstSpecies F))]
      ring
    rw [hw] at hlim
    refine hlim.congr fun N => ?_
    have hN : (N : ℝ) ≠ 0 := by positivity
    have hle := sum_floor_le F N
    rw [roundCount_first, Nat.cast_sub hle, ← Finset.sum_div]
    push_cast
    field_simp
  · refine (tendsto_floor_div _ (F.weight_nonneg s)).congr fun N => ?_
    simp [roundCount, hs]

theorem exists_rounded_labelling (F : SpeciesFamily d) :
    ∃ σ : (N : ℕ+) → Fin N → Fin F.count,
      ∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (F.weight s)) := by
  choose σ hσ using fun N : ℕ+ => exists_labelling (N := (N : ℕ)) (roundCount F N)
    (sum_roundCount F N)
  refine ⟨σ, fun s => ?_⟩
  refine (tendsto_roundCount F s).congr fun N => ?_
  simp [proportion, hσ]

end DGPS.Particle.ProductRecovery

namespace DGPS.Lipschitz

open DGPS.Particle.ProductRecovery

variable {d : ℕ}

/-- LIP021. For a fixed finite species family there are rounded labellings `σ_N` with species
proportions `p_s → θ_s`; for them the product law `ν_N = ⨂ᵢ ρ_{σ_N i} m` satisfies the exact
entropy identity
`N⁻¹ H(ν_N | P_N) = ∑ₛ pₛ [H(ρₛ|m) + ∫ V ρₛ] + ½ ∑ₛₜ pₛ pₜ Uₛₜ - (2N)⁻¹ ∑ₛ pₛ Uₛₛ
  + N⁻¹ log Z_N`
with `Uₛₜ = ∫ W ρₛ ⊗ ρₜ`, and `N⁻¹ H(ν_N | P_N)` converges to the species gap `G_θ`. -/
theorem rounded_finite_species_product_entropy (A : InteractionData d) (F : SpeciesFamily d) :
    ∃ σ : (N : ℕ+) → Fin N → Fin F.count,
      (∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (F.weight s))) ∧
      (∀ N : ℕ+,
        (1 / (N : ℝ)) * (relativeEntropy (productLaw F (σ N)) (particleLaw A N)).toReal =
          ∑ s, proportion (σ N) s * (speciesEntropy F s + potentialEnergy A (speciesLaw F s)) +
            (1 / 2 : ℝ) * ∑ s, ∑ t, proportion (σ N) s * proportion (σ N) t *
              crossEnergy A (speciesLaw F s) (speciesLaw F t) -
            (1 / (2 * (N : ℝ))) * ∑ s, proportion (σ N) s *
              crossEnergy A (speciesLaw F s) (speciesLaw F s) +
            (1 / (N : ℝ)) * Real.log (particlePartition A N)) ∧
      Tendsto (fun N : ℕ+ =>
        (1 / (N : ℝ)) * (relativeEntropy (productLaw F (σ N)) (particleLaw A N)).toReal) atTop
        (𝓝 (speciesGap A F : ℝ)) := by
  obtain ⟨σ, hσ⟩ := exists_rounded_labelling F
  exact ⟨σ, hσ, fun N => product_entropy_identity A F (σ N), tendsto_product_entropy A F σ hσ⟩

end DGPS.Lipschitz
