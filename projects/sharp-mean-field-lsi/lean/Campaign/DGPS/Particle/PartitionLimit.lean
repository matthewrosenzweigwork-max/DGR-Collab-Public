import DGPS.Particle.Gibbs
import DGPS.Variational.EquilibriumGibbs
import DGPS.Measure.EntropyChain

/-!
# Partition function limit by finite empirical types (LIP018)

`N⁻¹ log Z_N → -F_*`, with the quantitative upper bound via equal-volume cell partitions and
type counting, and the product-trial lower bound.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal
namespace DGPS.Particle

theorem klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have : IsFiniteMeasure (μ.map e) := Measure.isFiniteMeasure_map _ _
  have : IsFiniteMeasure (ν.map e) := Measure.isFiniteMeasure_map _ _
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at this

theorem klDiv_prod_eq_add {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {μ' ν' : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
    klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + klDiv μ' ν' := by
  have h := klDiv_compProd_eq_add μ ν (ProbabilityTheory.Kernel.const α μ')
    (ProbabilityTheory.Kernel.const α ν')
  rw [Measure.compProd_const, Measure.compProd_const, Measure.compProd_const] at h
  rw [h]
  congr 1
  have h2 : klDiv (μ'.prod μ) (ν'.prod μ) = klDiv μ' ν' := by
    have := klDiv_compProd_left μ' ν' (ProbabilityTheory.Kernel.const β μ)
    rwa [Measure.compProd_const, Measure.compProd_const] at this
  rw [← h2, ← klDiv_map_equiv (MeasurableEquiv.prodComm (α := α) (β := β))]
  have hs : ∀ (m : Measure α) (n : Measure β) [IsProbabilityMeasure m] [IsProbabilityMeasure n],
      (m.prod n).map (MeasurableEquiv.prodComm (α := α) (β := β)) = n.prod m := fun m n _ _ =>
    Measure.prod_swap
  rw [hs, hs]

theorem klDiv_pi_const {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (n : ℕ) :
    klDiv (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν) = n * klDiv μ ν := by
  induction n with
  | zero =>
    have : (Measure.pi fun _ : Fin 0 => μ) = Measure.pi fun _ : Fin 0 => ν := by
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    rw [this, klDiv_self]; simp
  | succ n ih =>
    have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have e' := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    rw [← klDiv_map_equiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0),
      e.map_eq, e'.map_eq, klDiv_prod_eq_add]
    rw [ih]; push_cast; ring


/-- Pair marginal of a product law. -/
theorem pi_map_pair {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin n => ν).map (fun x => (x i, x j)) = ν.prod ν := by
  have hind := iIndepFun_pi (μ := fun _ : Fin n => ν) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have h := hind.indepFun hij
  have hm := (indepFun_iff_map_prod_eq_prod_map_map
    (μ := Measure.pi fun _ : Fin n => ν) (f := fun ω : Fin n → α => id (ω i))
    (g := fun ω : Fin n → α => id (ω j)) (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 h
  have hi := (measurePreserving_eval (fun _ : Fin n => ν) i).map_eq
  have hj := (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq
  simp only [id] at hm
  rw [hm]
  have e1 : Measure.map (fun ω : Fin n → α => ω i) (Measure.pi fun _ : Fin n => ν) = ν := hi
  have e2 : Measure.map (fun ω : Fin n → α => ω j) (Measure.pi fun _ : Fin n => ν) = ν := hj
  rw [e1, e2]

theorem integral_pi_pair {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) (g : α × α → ℝ) (hg : Measurable g) :
    ∫ x, g (x i, x j) ∂(Measure.pi fun _ : Fin n => ν) = ∫ p, g p ∂(ν.prod ν) := by
  rw [← pi_map_pair ν n hij, integral_map]
  · exact ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
  · exact hg.aestronglyMeasurable

theorem integral_pi_single {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) (i : Fin n) (g : α → ℝ) (hg : Measurable g) :
    ∫ x, g (x i) ∂(Measure.pi fun _ : Fin n => ν) = ∫ a, g a ∂ν := by
  have hi : Measure.map (fun ω : Fin n → α => ω i) (Measure.pi fun _ : Fin n => ν) = ν :=
    (measurePreserving_eval (fun _ : Fin n => ν) i).map_eq
  conv_rhs => rw [← hi]
  rw [integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]

end DGPS.Particle

namespace DGPS.Particle

open DGPS

theorem freeEnergy_toReal {d : ℕ} (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (h : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    (freeEnergy A ν).toReal = (klDiv (ν : Measure (Torus d)) (haar d)).toReal +
      (potentialEnergy A ν + (1 / 2 : ℝ) * interactionEnergy A ν) := by
  rw [freeEnergy_eq_klDiv]
  have hk : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [← DGPS.Analysis.relativeEntropy_eq_klDiv]; exact h
  rw [← EReal.coe_ennreal_toReal hk, ← EReal.coe_add, EReal.toReal_coe]

theorem integral_hamiltonian_pi {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (ν : ProbabilityMeasure (Torus d)) :
    ∫ x, particleHamiltonian A N x ∂(Measure.pi fun _ : Fin N => (ν : Measure (Torus d))) =
      N * potentialEnergy A ν +
        (1 / (2 * (N : ℝ))) * ((N : ℝ) * ((N : ℝ) - 1)) * interactionEnergy A ν := by
  set P : Measure (ParticleSpace d N) := Measure.pi fun _ : Fin N => (ν : Measure (Torus d)) with hP
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
  have h1 : ∀ i : Fin N, ∫ x : ParticleSpace d N, A.V (x i) ∂P = potentialEnergy A ν := fun i =>
    integral_pi_single (ν : Measure (Torus d)) N i A.V A.V_continuous.measurable
  have h2 : ∀ i j : Fin N, ∫ x : ParticleSpace d N, A.W (x i) (x j) ∂P =
      if i = j then 0 else interactionEnergy A ν := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [A.W_diag]
    · simp only [hij, ↓reduceIte]
      exact integral_pi_pair (ν : Measure (Torus d)) N hij (fun p => A.W p.1 p.2)
        A.W_continuous.measurable
  have h3 : ∀ i : Fin N, ∑ j : Fin N, ∫ x : ParticleSpace d N, A.W (x i) (x j) ∂P =
      ((N : ℝ) - 1) * interactionEnergy A ν := by
    intro i
    simp_rw [h2]
    rw [Finset.sum_ite]
    simp [Finset.filter_ne, Finset.card_erase_of_mem]
  have h4 : ∀ i : Fin N, ∫ x : ParticleSpace d N, ∑ j : Fin N, A.W (x i) (x j) ∂P =
      ∑ j : Fin N, ∫ x : ParticleSpace d N, A.W (x i) (x j) ∂P := fun i =>
    integral_finsetSum _ fun j _ => hW i j
  simp only [h1, h4, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- Product-trial lower bound for the partition function. -/
theorem partition_lower_bound {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (ν : ProbabilityMeasure (Torus d))
    (hν : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    -(freeEnergy A ν).toReal + (1 / (2 * (N : ℝ))) * interactionEnergy A ν ≤
      (1 / (N : ℝ)) * Real.log (particlePartition A N) := by
  have hk : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [← DGPS.Analysis.relativeEntropy_eq_klDiv]; exact hν
  set P : Measure (ParticleSpace d N) := Measure.pi fun _ : Fin N => (ν : Measure (Torus d)) with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hKL : klDiv P (particleHaar d N) = (N : ℝ≥0∞) * klDiv (ν : Measure (Torus d)) (haar d) :=
    klDiv_pi_const _ _ N
  have hKLne : klDiv P (particleHaar d N) ≠ ⊤ := by
    rw [hKL]; exact ENNReal.mul_ne_top (by simp) hk
  obtain ⟨M, -, hM⟩ := particleHamiltonian_bounded A N
  have key := DGPS.Lipschitz.klDiv_tilted_forward (ρ := P) (ν := particleHaar d N)
    (f := fun x => -particleHamiltonian A N x) (B := M)
    (particleHamiltonian_measurable A N).neg (fun x => by simpa using hM x) hKLne
  have hnn : 0 ≤ (klDiv P ((particleHaar d N).tilted fun x => -particleHamiltonian A N x)).toReal :=
    ENNReal.toReal_nonneg
  rw [key.2] at hnn
  have hint : ∫ x, -particleHamiltonian A N x ∂P =
      -(N * potentialEnergy A ν +
        (1 / (2 * (N : ℝ))) * ((N : ℝ) * ((N : ℝ) - 1)) * interactionEnergy A ν) := by
    rw [integral_neg, integral_hamiltonian_pi]
  rw [hint, hKL, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hnn
  have hlog : Real.log (particlePartition A N) =
      Real.log (∫ x, Real.exp (-particleHamiltonian A N x) ∂particleHaar d N) := rfl
  rw [← hlog] at hnn
  rw [freeEnergy_toReal A ν hν]
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [show (1 / (N : ℝ)) * Real.log (particlePartition A N) =
    (Real.log (particlePartition A N)) / N by ring, le_div_iff₀ hN]
  have e : (2 * (N : ℝ))⁻¹ * ((N : ℝ) * ((N : ℝ) - 1)) = ((N : ℝ) - 1) / 2 := by
    field_simp
  have e2 : (1 / (2 * (N : ℝ))) * ((N : ℝ) * ((N : ℝ) - 1)) = ((N : ℝ) - 1) / 2 := by
    rw [one_div]; exact e
  rw [e2] at hnn
  have e3 : (1 / (2 * (N : ℝ))) * interactionEnergy A ν * N = interactionEnergy A ν / 2 := by
    field_simp
  nlinarith [e3]

end DGPS.Particle

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Modulus of continuity of `V` for the Euclidean quotient distance. -/
noncomputable def potentialModulus (A : InteractionData d) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x y : Torus d, torusDist x y ≤ δ ∧ r = |A.V x - A.V y|}

/-- Modulus of continuity of `W`, for the sum of the two quotient distances. -/
noncomputable def interactionModulus (A : InteractionData d) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x y x' y' : Torus d, torusDist x x' + torusDist y y' ≤ δ ∧
    r = |A.W x y - A.W x' y'|}

theorem potentialModulus_bddAbove (A : InteractionData d) (δ : ℝ) :
    BddAbove {r : ℝ | ∃ x y : Torus d, torusDist x y ≤ δ ∧ r = |A.V x - A.V y|} := by
  obtain ⟨C, hC⟩ := A.V_bounded
  refine ⟨2 * C, ?_⟩
  rintro r ⟨x, y, -, rfl⟩
  rw [abs_le]; constructor <;> linarith [abs_le.1 (hC x), abs_le.1 (hC y)]

theorem interactionModulus_bddAbove (A : InteractionData d) (δ : ℝ) :
    BddAbove {r : ℝ | ∃ x y x' y' : Torus d, torusDist x x' + torusDist y y' ≤ δ ∧
      r = |A.W x y - A.W x' y'|} := by
  obtain ⟨C, hC⟩ := A.W_bounded
  refine ⟨2 * C, ?_⟩
  rintro r ⟨x, y, x', y', -, rfl⟩
  rw [abs_le]; constructor <;> linarith [abs_le.1 (hC x y), abs_le.1 (hC x' y')]

theorem abs_sub_le_potentialModulus (A : InteractionData d) {δ : ℝ} {x y : Torus d}
    (h : torusDist x y ≤ δ) : |A.V x - A.V y| ≤ potentialModulus A δ :=
  le_csSup (potentialModulus_bddAbove A δ) ⟨x, y, h, rfl⟩

theorem abs_sub_le_interactionModulus (A : InteractionData d) {δ : ℝ} {x y x' y' : Torus d}
    (h : torusDist x x' + torusDist y y' ≤ δ) :
    |A.W x y - A.W x' y'| ≤ interactionModulus A δ :=
  le_csSup (interactionModulus_bddAbove A δ) ⟨x, y, x', y', h, rfl⟩

theorem potentialModulus_nonneg (A : InteractionData d) (δ : ℝ) : 0 ≤ potentialModulus A δ :=
  Real.sSup_nonneg (by rintro r ⟨x, y, -, rfl⟩; exact abs_nonneg _)

theorem interactionModulus_nonneg (A : InteractionData d) (δ : ℝ) : 0 ≤ interactionModulus A δ :=
  Real.sSup_nonneg (by rintro r ⟨x, y, x', y', -, rfl⟩; exact abs_nonneg _)

theorem exists_potentialModulus_le (A : InteractionData d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ potentialModulus A δ ≤ ε := by
  have huc := CompactSpace.uniformContinuous_of_continuous A.V_continuous
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  refine ⟨η / 2, by positivity, Real.sSup_le ?_ hε.le⟩
  rintro r ⟨x, y, hxy, rfl⟩
  have hd : dist x y < η := lt_of_le_of_lt ((torusDist_comparison x y).1.trans hxy) (by linarith)
  have := h hd
  rw [Real.dist_eq] at this
  exact this.le

theorem exists_interactionModulus_le (A : InteractionData d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ interactionModulus A (2 * δ) ≤ ε := by
  have huc := CompactSpace.uniformContinuous_of_continuous A.W_continuous
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  refine ⟨η / 4, by positivity, Real.sSup_le ?_ hε.le⟩
  rintro r ⟨x, y, x', y', hxy, rfl⟩
  have h1 := (torusDist_comparison x x').1
  have h2 := (torusDist_comparison y y').1
  have h3 : 0 ≤ dist x x' := dist_nonneg
  have h4 : 0 ≤ dist y y' := dist_nonneg
  have hd : dist (x, y) (x', y') < η := by
    rw [Prod.dist_eq]
    show max (dist x x') (dist y y') < η
    refine max_lt ?_ ?_ <;> linarith
  have := h hd
  rw [Real.dist_eq] at this
  exact this.le


/-- A partition of the torus into `L` measurable cells of equal Haar volume `1/L`, each of
`torusDist`-diameter at most `δ`, presented by its cell-index map. -/
structure CellPartition (d L : ℕ) (δ : ℝ) where
  cell : Torus d → Fin L
  measurable_cell : Measurable cell
  volume_cell : ∀ l, haar d (cell ⁻¹' {l}) = (L : ℝ≥0∞)⁻¹
  diam_cell : ∀ x y, cell x = cell y → torusDist x y ≤ δ

/-- Grid index of a point `t ∈ (0,1]` among `n+1` equal subintervals. -/
noncomputable def gridIdx (n : ℕ) (t : ℝ) : Fin (n + 1) :=
  ⟨min (⌈((n : ℝ) + 1) * t⌉₊ - 1) n, by omega⟩

theorem measurable_gridIdx (n : ℕ) : Measurable (gridIdx n) := by
  have : gridIdx n = (fun m : ℕ => (⟨min (m - 1) n, by omega⟩ : Fin (n + 1))) ∘
      (fun t : ℝ => ⌈((n : ℝ) + 1) * t⌉₊) := rfl
  rw [this]
  exact (Measurable.of_discrete).comp (Nat.measurable_ceil.comp (measurable_const.mul measurable_id))

theorem gridIdx_eq_iff (n : ℕ) (k : Fin (n + 1)) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    gridIdx n t = k ↔ t ∈ Set.Ioc ((k : ℝ) / ((n : ℝ) + 1)) (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs0 : 0 < ((n : ℝ) + 1) * t := mul_pos hn ht.1
  have hs1 : ((n : ℝ) + 1) * t ≤ (n : ℝ) + 1 := by nlinarith [ht.2]
  have hc1 : 1 ≤ ⌈((n : ℝ) + 1) * t⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hs0).ne'
  have hc2 : ⌈((n : ℝ) + 1) * t⌉₊ ≤ n + 1 := by
    rw [Nat.ceil_le]; exact_mod_cast hs1
  have hmin : min (⌈((n : ℝ) + 1) * t⌉₊ - 1) n = ⌈((n : ℝ) + 1) * t⌉₊ - 1 := min_eq_left (by omega)
  have e1 : gridIdx n t = k ↔ ⌈((n : ℝ) + 1) * t⌉₊ = (k : ℕ) + 1 := by
    rw [Fin.ext_iff]
    show min (⌈((n : ℝ) + 1) * t⌉₊ - 1) n = (k : ℕ) ↔ _
    rw [hmin]; omega
  rw [e1, Nat.ceil_eq_iff (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Set.mem_Ioc]
  rw [div_lt_iff₀ hn, le_div_iff₀ hn]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem secT_mem_Ioc {d : ℕ} (x : Torus d) (i : Fin d) :
    SharpLSI.secT x i ∈ Set.Ioc (0 : ℝ) 1 := by
  have := ((AddCircle.measurableEquivIoc 1 0) (x i)).2
  simpa [SharpLSI.secT] using this

/-- The grid cell index. -/
noncomputable def gridCell (d n : ℕ) (x : Torus d) : Fin d → Fin (n + 1) :=
  fun i => gridIdx n (SharpLSI.secT x i)

theorem measurable_gridCell (d n : ℕ) : Measurable (gridCell d n) :=
  measurable_pi_iff.2 fun i => (measurable_gridIdx n).comp
    ((measurable_pi_apply i).comp SharpLSI.measurable_secT)

theorem haar_gridCell (d n : ℕ) (k : Fin d → Fin (n + 1)) :
    haar d (gridCell d n ⁻¹' {k}) = (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ d := by
  have hmeas : MeasurableSet (gridCell d n ⁻¹' {k}) :=
    (measurable_gridCell d n) (measurableSet_singleton k)
  rw [haar_eq_map_unitBox, Measure.map_apply SharpLSI.measurable_liftT hmeas,
    Measure.restrict_apply (SharpLSI.measurable_liftT hmeas)]
  have hset : SharpLSI.liftT ⁻¹' (gridCell d n ⁻¹' {k}) ∩ SharpLSI.unitBox (Fin d) =
      Set.univ.pi fun i => Set.Ioc ((k i : ℝ) / ((n : ℝ) + 1)) (((k i : ℝ) + 1) / ((n : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ i
      have hx : x ∈ SharpLSI.unitBox (Fin d) := h2
      have hxi : x i ∈ Set.Ioc (0 : ℝ) 1 := h2 i (Set.mem_univ i)
      have := congrFun h1 i
      simp only [gridCell, SharpLSI.secT_liftT hx] at this
      exact (gridIdx_eq_iff n (k i) hxi).1 this
    · intro h
      have hx : x ∈ SharpLSI.unitBox (Fin d) := by
        intro i _
        have hi := h i
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hk : (k i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have := (k i).2; have : (k i : ℕ) ≤ n := by omega
          exact_mod_cast Nat.succ_le_succ this
        refine ⟨lt_of_le_of_lt (by positivity) hi.1, hi.2.trans ?_⟩
        rw [div_le_one hn]; exact hk
      refine ⟨?_, hx⟩
      funext i
      simp only [gridCell, SharpLSI.secT_liftT hx]
      exact (gridIdx_eq_iff n (k i) (hx i (Set.mem_univ i))).2 (h i)
  rw [hset, Real.volume_pi_Ioc]
  have : ∀ i : Fin d, ENNReal.ofReal (((k i : ℝ) + 1) / ((n : ℝ) + 1) - (k i : ℝ) / ((n : ℝ) + 1)) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro i
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show ((k i : ℝ) + 1) / ((n : ℝ) + 1) - (k i : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) by ring,
      one_div, ENNReal.ofReal_inv_of_pos hn]
    congr 1
    rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem torusDist_gridCell_le (d n : ℕ) {x y : Torus d} (h : gridCell d n x = gridCell d n y) :
    torusDist x y ≤ Real.sqrt d / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcoord : ∀ i : Fin d, ‖x i - y i‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro i
    have hi := congrFun h i
    simp only [gridCell] at hi
    have hxa : x i = ((SharpLSI.secT x i : ℝ) : AddCircle (1 : ℝ)) := by
      have := congrFun (SharpLSI.liftT_secT x) i
      simpa [SharpLSI.liftT] using this.symm
    have hyb : y i = ((SharpLSI.secT y i : ℝ) : AddCircle (1 : ℝ)) := by
      have := congrFun (SharpLSI.liftT_secT y) i
      simpa [SharpLSI.liftT] using this.symm
    have ha' := (gridIdx_eq_iff n (gridIdx n (SharpLSI.secT x i)) (secT_mem_Ioc x i)).1 rfl
    have hb' := (gridIdx_eq_iff n (gridIdx n (SharpLSI.secT x i)) (secT_mem_Ioc y i)).1 hi.symm
    have e : (((gridIdx n (SharpLSI.secT x i) : ℕ) : ℝ) + 1) / ((n : ℝ) + 1) -
        ((gridIdx n (SharpLSI.secT x i) : ℕ) : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by ring
    have hab : |SharpLSI.secT x i - SharpLSI.secT y i| ≤ 1 / ((n : ℝ) + 1) := by
      rw [abs_le]
      constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
    rw [hxa, hyb, ← QuotientAddGroup.mk_sub]
    refine le_trans ?_ hab
    rw [AddCircle.norm_eq]
    simpa using round_le (SharpLSI.secT x i - SharpLSI.secT y i) 0
  unfold torusDist SharpLSI.flatDist
  rw [show Real.sqrt d / ((n : ℝ) + 1) = Real.sqrt (∑ _i : Fin d, (1 / ((n : ℝ) + 1)) ^ 2) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
    ring]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2)


/-- Equal-volume partitions of arbitrarily small diameter exist. -/
theorem exists_cellPartition (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℕ, Nonempty (CellPartition d L δ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.sqrt d / δ)
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsmall : Real.sqrt d / ((n : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ hn0]
    have := (div_lt_iff₀ hδ).1 hn
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  let e : (Fin d → Fin (n + 1)) ≃ Fin ((n + 1) ^ d) :=
    Fintype.equivFinOfCardEq (by simp)
  refine ⟨(n + 1) ^ d, ⟨{
    cell := fun x => e (gridCell d n x)
    measurable_cell := Measurable.of_discrete.comp (measurable_gridCell d n)
    volume_cell := ?_
    diam_cell := ?_ }⟩⟩
  · intro l
    have : (fun x => e (gridCell d n x)) ⁻¹' {l} = gridCell d n ⁻¹' {e.symm l} := by
      ext x; simp [Equiv.eq_symm_apply]
    rw [this, haar_gridCell, ← ENNReal.inv_pow]
    push_cast
    rfl
  · intro x y hxy
    exact (torusDist_gridCell_le d n (e.injective hxy)).trans hsmall


open Finset

theorem abs_hamiltonian_sub_le {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (x x' : ParticleSpace d N) {a b : ℝ}
    (hV : ∀ i, |A.V (x i) - A.V (x' i)| ≤ a)
    (hW : ∀ i j, |A.W (x i) (x j) - A.W (x' i) (x' j)| ≤ b) :
    |particleHamiltonian A N x - particleHamiltonian A N x'| ≤ N * a + N * b / 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast N.pos
  have e : particleHamiltonian A N x - particleHamiltonian A N x' =
      ∑ i, (A.V (x i) - A.V (x' i)) +
        (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, (A.W (x i) (x j) - A.W (x' i) (x' j)) := by
    unfold particleHamiltonian
    simp only [Finset.sum_sub_distrib]
    ring
  have h1 : |∑ i, (A.V (x i) - A.V (x' i))| ≤ N * a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hV i).trans ?_
    simp
  have h2 : |∑ i, ∑ j, (A.W (x i) (x j) - A.W (x' i) (x' j))| ≤ N * N * b := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => hW i j)).trans ?_
    simp [mul_assoc]
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (N : ℝ)))]
  have : (1 / (2 * (N : ℝ))) * (N * N * b) = N * b / 2 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * (N : ℝ)))]

variable {d L : ℕ} {δ : ℝ}

theorem hamiltonian_cell_comparison (A : InteractionData d) (P : CellPartition d L δ)
    (r : Fin L → Torus d) (hr : ∀ l, P.cell (r l) = l) (N : ℕ+) (x : ParticleSpace d N) :
    |particleHamiltonian A N x - particleHamiltonian A N (fun i => r (P.cell (x i)))| ≤
      N * potentialModulus A δ + N * interactionModulus A (2 * δ) / 2 := by
  have hd : ∀ i, torusDist (x i) (r (P.cell (x i))) ≤ δ := fun i =>
    P.diam_cell _ _ (hr _).symm
  refine abs_hamiltonian_sub_le A N _ _ (fun i => abs_sub_le_potentialModulus A (hd i)) ?_
  intro i j
  exact abs_sub_le_interactionModulus A (by linarith [hd i, hd j])

/-- The cell-index map on particle configurations. -/
def cellConfig (P : CellPartition d L δ) {N : ℕ} (x : Fin N → Torus d) : Fin N → Fin L :=
  fun i => P.cell (x i)

theorem measurable_cellConfig (P : CellPartition d L δ) (N : ℕ) :
    Measurable (cellConfig P (N := N)) :=
  measurable_pi_iff.2 fun i => P.measurable_cell.comp (measurable_pi_apply i)

theorem map_cellConfig_real (P : CellPartition d L δ) (N : ℕ) (k : Fin N → Fin L) :
    ((Measure.pi fun _ : Fin N => haar d).map (cellConfig P)).real {k} = ((L : ℝ) ^ N)⁻¹ := by
  rw [measureReal_def, Measure.map_apply (measurable_cellConfig P N) (measurableSet_singleton k)]
  have : cellConfig P ⁻¹' {k} = Set.univ.pi fun i => P.cell ⁻¹' {k i} := by
    ext x; simp [cellConfig, funext_iff, Set.mem_pi]
  rw [this, Measure.pi_pi]
  simp only [P.volume_cell, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_pow]

theorem integral_cellConfig (P : CellPartition d L δ) (N : ℕ) (F : (Fin N → Fin L) → ℝ) :
    ∫ x, F (cellConfig P x) ∂(Measure.pi fun _ : Fin N => haar d) =
      ∑ k, ((L : ℝ) ^ N)⁻¹ * F k := by
  have hint : Integrable F ((Measure.pi fun _ : Fin N => haar d).map (cellConfig P)) :=
    Integrable.of_finite
  rw [← integral_map (measurable_cellConfig P N).aemeasurable
    (Measurable.of_discrete).aestronglyMeasurable, integral_fintype hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_cellConfig_real, smul_eq_mul]

theorem particlePartition_le (A : InteractionData d) (P : CellPartition d L δ)
    (r : Fin L → Torus d) (hr : ∀ l, P.cell (r l) = l) (N : ℕ+) :
    particlePartition A N ≤ Real.exp (N * (potentialModulus A δ + interactionModulus A (2 * δ) / 2)) *
      ∑ k : Fin N → Fin L, ((L : ℝ) ^ (N : ℕ))⁻¹ *
        Real.exp (-(particleHamiltonian A N (fun i => r (k i)))) := by
  set ω : ℝ := N * potentialModulus A δ + N * interactionModulus A (2 * δ) / 2 with hω
  have hint : Integrable (fun x : ParticleSpace d N =>
      Real.exp ω * Real.exp (-(particleHamiltonian A N (fun i => r (cellConfig P x i)))))
      (particleHaar d N) := by
    have : Integrable (fun k : Fin N → Fin L => Real.exp ω * Real.exp (-(particleHamiltonian A N (fun i => r (k i)))))
        ((particleHaar d N).map (cellConfig P)) := Integrable.of_finite
    exact this.comp_measurable (measurable_cellConfig P N)
  have h1 : particlePartition A N ≤ ∫ x : ParticleSpace d N,
      Real.exp ω * Real.exp (-(particleHamiltonian A N (fun i => r (cellConfig P x i)))) ∂(particleHaar d N) := by
    unfold particlePartition
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hint
      (Filter.Eventually.of_forall fun x => ?_)
    have := hamiltonian_cell_comparison A P r hr N x
    show Real.exp (-particleHamiltonian A N x) ≤ Real.exp ω * Real.exp _
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 this).1
    simp only [cellConfig]
    linarith
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul]
  have := integral_cellConfig P N (fun k => Real.exp (-(particleHamiltonian A N (fun i => r (k i)))))
  have hωe : ω = N * (potentialModulus A δ + interactionModulus A (2 * δ) / 2) := by rw [hω]; ring
  rw [hωe]
  congr 1



section TypeCounting

open Finset

variable {L N : ℕ}

/-- Number of labels sitting in cell `l`. -/
def typeCount (k : Fin N → Fin L) (l : Fin L) : ℕ := (univ.filter fun i => k i = l).card

theorem sum_typeCount (k : Fin N → Fin L) : ∑ l, typeCount k l = N := by
  have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin N)))
    (t := (univ : Finset (Fin L))) (f := k) (fun _ _ => mem_univ _)
  simpa [typeCount] using this.symm

theorem typeCount_le (k : Fin N → Fin L) (l : Fin L) : typeCount k l ≤ N := by
  unfold typeCount
  calc (univ.filter fun i => k i = l).card ≤ (univ : Finset (Fin N)).card := card_filter_le _ _
    _ = N := by simp

theorem typeCount_pos (k : Fin N → Fin L) (i : Fin N) : 0 < typeCount k (k i) :=
  Finset.card_pos.2 ⟨i, by simp⟩

theorem sum_comp_typeCount (k : Fin N → Fin L) (f : Fin L → ℝ) :
    ∑ i, f (k i) = ∑ l, (typeCount k l : ℝ) * f l := by
  rw [← Finset.sum_fiberwise (s := (univ : Finset (Fin N))) (g := k) (fun i => f (k i))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f l) (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
  simp [typeCount, mul_comm]

theorem sum_comp_typeCount₂ (k : Fin N → Fin L) (g : Fin L → Fin L → ℝ) :
    ∑ i, ∑ j, g (k i) (k j) = ∑ l, ∑ l', (typeCount k l : ℝ) * (typeCount k l' : ℝ) * g l l' := by
  have h1 : ∀ i, ∑ j, g (k i) (k j) = ∑ l', (typeCount k l' : ℝ) * g (k i) l' :=
    fun i => sum_comp_typeCount k (g (k i))
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ l', ∑ i, (typeCount k l' : ℝ) * g (k i) l' =
      ∑ l, (typeCount k l : ℝ) * (typeCount k l' : ℝ) * g l l' := by
    intro l'
    rw [← Finset.mul_sum, sum_comp_typeCount k (fun l => g l l'), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [h2]
  exact Finset.sum_comm

theorem sum_prod_eq_one (q : Fin L → ℝ) (hs : ∑ l, q l = 1) :
    ∑ k : Fin N → Fin L, ∏ i, q (k i) = 1 := by
  have := Finset.prod_univ_sum (fun _ : Fin N => (univ : Finset (Fin L))) (fun _ l => q l)
  simpa [hs, Fintype.piFinset_univ] using this.symm

theorem sum_typeProb_le (hN : 0 < N) :
    ∑ k : Fin N → Fin L, ∏ i, ((typeCount k (k i) : ℝ) / N) ≤ ((N : ℝ) + 1) ^ L := by
  classical
  have hmaps : ∀ k ∈ (univ : Finset (Fin N → Fin L)), (fun k => fun l => typeCount k l) k ∈
      (Fintype.piFinset fun _ : Fin L => Finset.range (N + 1)) := by
    intro k _
    simp only [Fintype.mem_piFinset, mem_range]
    intro l; exact Nat.lt_succ_of_le (typeCount_le k l)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : Fin L => Finset.range (N + 1)), (1 : ℝ) := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases hne : ∃ k0 : Fin N → Fin L, (fun l => typeCount k0 l) = t
        · obtain ⟨k0, hk0⟩ := hne
          have hsum : ∑ l, (t l : ℝ) / N = 1 := by
            rw [← Finset.sum_div, ← hk0]
            have : (∑ l, (typeCount k0 l : ℝ)) = N := by exact_mod_cast sum_typeCount k0
            rw [this, div_self (by exact_mod_cast hN.ne')]
          have hle : ∑ k ∈ univ.filter (fun k : Fin N → Fin L => (fun l => typeCount k l) = t),
              ∏ i, ((typeCount k (k i) : ℝ) / N) ≤
              ∑ k : Fin N → Fin L, ∏ i, ((t (k i) : ℝ) / N) := by
            calc _ = ∑ k ∈ univ.filter (fun k : Fin N → Fin L => (fun l => typeCount k l) = t),
                    ∏ i, ((t (k i) : ℝ) / N) := by
                  refine Finset.sum_congr rfl fun k hk => ?_
                  have := (Finset.mem_filter.1 hk).2
                  refine Finset.prod_congr rfl fun i _ => ?_
                  rw [← this]
              _ ≤ _ := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
                  intro k _ _
                  exact Finset.prod_nonneg fun i _ => by positivity
          exact hle.trans (sum_prod_eq_one (fun l => (t l : ℝ) / N) hsum).le
        · have hne := not_exists.1 hne
          rw [Finset.sum_eq_zero]
          · exact zero_le_one
          · intro k hk
            exact absurd (Finset.mem_filter.1 hk).2 (hne k)
    _ = ((N : ℝ) + 1) ^ L := by
        rw [Finset.sum_const, Fintype.card_piFinset]
        simp [Finset.prod_const]

theorem sum_exp_le (hN : 0 < N) (hL : 0 < L) (G : (Fin N → Fin L) → ℝ) (β : ℝ)
    (h : ∀ k, (N : ℝ) * β ≤ G k + ∑ i, Real.log ((L : ℝ) * ((typeCount k (k i) : ℝ) / N))) :
    ∑ k, ((L : ℝ) ^ N)⁻¹ * Real.exp (-G k) ≤ ((N : ℝ) + 1) ^ L * Real.exp (-((N : ℝ) * β)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hterm : ∀ k : Fin N → Fin L, ((L : ℝ) ^ N)⁻¹ * Real.exp (-G k) ≤
      (∏ i, ((typeCount k (k i) : ℝ) / N)) * Real.exp (-((N : ℝ) * β)) := by
    intro k
    have hq : ∀ i, 0 < (typeCount k (k i) : ℝ) / N := fun i => by
      have := typeCount_pos k i
      positivity
    have hlogsum : ∑ i, Real.log ((L : ℝ) * ((typeCount k (k i) : ℝ) / N)) =
        N * Real.log L + ∑ i, Real.log ((typeCount k (k i) : ℝ) / N) := by
      rw [Finset.sum_congr rfl fun i _ => Real.log_mul hLp.ne' (hq i).ne', Finset.sum_add_distrib]
      simp
    have hk := h k
    rw [hlogsum] at hk
    have hprod : ∏ i, ((typeCount k (k i) : ℝ) / N) =
        Real.exp (∑ i, Real.log ((typeCount k (k i) : ℝ) / N)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hq i)).symm
    have hLN : ((L : ℝ) ^ N)⁻¹ = Real.exp (-((N : ℝ) * Real.log L)) := by
      rw [← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos hLp N)]
    rw [hprod, hLN, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc _ ≤ ∑ k : Fin N → Fin L, (∏ i, ((typeCount k (k i) : ℝ) / N)) * Real.exp (-((N : ℝ) * β)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (∑ k : Fin N → Fin L, ∏ i, ((typeCount k (k i) : ℝ) / N)) * Real.exp (-((N : ℝ) * β)) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_typeProb_le hN) (Real.exp_pos _).le

end TypeCounting

end DGPS.Lipschitz

namespace DGPS.Lipschitz

variable {d L : ℕ} {δ : ℝ}

theorem cell_L_pos (P : CellPartition d L δ) : 0 < L := Fin.pos (P.cell 0)

theorem integral_comp_cell (P : CellPartition d L δ) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (ψ : Fin L → ℝ) :
    ∫ x, ψ (P.cell x) ∂μ = ∑ l, (μ (P.cell ⁻¹' {l})).toReal * ψ l := by
  have hint : Integrable ψ (μ.map P.cell) := Integrable.of_finite
  rw [← integral_map P.measurable_cell.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    integral_fintype hint]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [measureReal_def, Measure.map_apply P.measurable_cell (measurableSet_singleton l), smul_eq_mul]

theorem integrable_comp_cell (P : CellPartition d L δ) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (ψ : Fin L → ℝ) : Integrable (fun x => ψ (P.cell x)) μ :=
  (Integrable.of_finite (μ := μ.map P.cell) (f := ψ)).comp_measurable P.measurable_cell

/-- Density of the trial law with prescribed cell masses `p`. -/
noncomputable def trialDensity (P : CellPartition d L δ) (p : Fin L → ℝ) (x : Torus d) : ℝ≥0∞ :=
  ENNReal.ofReal (L * p (P.cell x))

theorem measurable_trialDensity (P : CellPartition d L δ) (p : Fin L → ℝ) :
    Measurable (trialDensity P p) :=
  ENNReal.measurable_ofReal.comp
    ((Measurable.of_discrete (f := fun l : Fin L => (L : ℝ) * p l)).comp P.measurable_cell)

/-- The trial law `(L p_{c(x)}) dx`. -/
noncomputable def trialMeasure (P : CellPartition d L δ) (p : Fin L → ℝ) : Measure (Torus d) :=
  (haar d).withDensity (trialDensity P p)

theorem trial_cell (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l) (l : Fin L) :
    trialMeasure P p (P.cell ⁻¹' {l}) = ENNReal.ofReal (p l) := by
  have hL := cell_L_pos P
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hm : MeasurableSet (P.cell ⁻¹' {l}) := P.measurable_cell (measurableSet_singleton l)
  rw [trialMeasure, withDensity_apply _ hm]
  rw [setLIntegral_congr_fun hm (g := fun _ => ENNReal.ofReal (L * p l)) (fun x hx => ?_)]
  · rw [setLIntegral_const, P.volume_cell]
    have : ((L : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((L : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_natCast]
    rw [this, ← ENNReal.ofReal_mul (by have := hp l; positivity)]
    congr 1
    field_simp
  · have : P.cell x = l := hx
    simp only [trialDensity, this]

theorem trial_univ (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) : trialMeasure P p Set.univ = 1 := by
  have h := sum_measure_singleton (μ := (trialMeasure P p).map P.cell) (s := Finset.univ)
  rw [Finset.coe_univ, Measure.map_apply P.measurable_cell MeasurableSet.univ,
    Set.preimage_univ] at h
  rw [← h]
  have : ∀ l ∈ (Finset.univ : Finset (Fin L)), ((trialMeasure P p).map P.cell) {l} =
      ENNReal.ofReal (p l) := by
    intro l _
    rw [Measure.map_apply P.measurable_cell (measurableSet_singleton l), trial_cell P p hp]
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg (fun l _ => hp l), h1,
    ENNReal.ofReal_one]

/-- The trial law as a probability measure. -/
noncomputable def trialProb (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) : ProbabilityMeasure (Torus d) :=
  ⟨trialMeasure P p, ⟨trial_univ P p hp h1⟩⟩

theorem coe_trialProb (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) : (trialProb P p hp h1 : Measure (Torus d)) = trialMeasure P p := rfl

theorem trial_real (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) (l : Fin L) :
    ((trialProb P p hp h1 : Measure (Torus d)) (P.cell ⁻¹' {l})).toReal = p l := by
  rw [coe_trialProb, trial_cell P p hp, ENNReal.toReal_ofReal (hp l)]

theorem integral_trial_comp (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) (ψ : Fin L → ℝ) :
    ∫ x, ψ (P.cell x) ∂(trialProb P p hp h1 : Measure (Torus d)) = ∑ l, p l * ψ l := by
  rw [integral_comp_cell]
  exact Finset.sum_congr rfl fun l _ => by rw [trial_real]

theorem sum_klFun (hL : 0 < L) (p : Fin L → ℝ) (h1 : ∑ l, p l = 1) :
    ∑ l, (L : ℝ)⁻¹ * klFun (L * p l) = ∑ l, p l * Real.log (L * p l) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have : ∀ l, (L : ℝ)⁻¹ * klFun (L * p l) = p l * Real.log (L * p l) - p l + (L : ℝ)⁻¹ := by
    intro l; unfold klFun; field_simp; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀ hLr.ne']
  ring

theorem relEntropy_trial (P : CellPartition d L δ) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) :
    relativeEntropy (trialProb P p hp h1 : Measure (Torus d)) (haar d) =
      ENNReal.ofReal (∑ l, (L : ℝ)⁻¹ * klFun (L * p l)) := by
  have hinst : IsProbabilityMeasure ((haar d).withDensity (trialDensity P p)) :=
    (trialProb P p hp h1).prop
  have key := DGPS.Analysis.relativeEntropy_withDensity_eq_lintegral (ρ := haar d)
    (measurable_trialDensity P p)
  change relativeEntropy ((haar d).withDensity (trialDensity P p)) (haar d) = _
  rw [key]
  have e : ∀ x, ENNReal.ofReal (klFun ((trialDensity P p x).toReal)) =
      ENNReal.ofReal (klFun (L * p (P.cell x))) := by
    intro x; unfold trialDensity
    rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (hp _))]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_comp_cell P (haar d) (fun l => klFun (L * p l)))
    (Filter.Eventually.of_forall fun x => klFun_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp _)))]
  have hI : ∫ x, klFun (L * p (P.cell x)) ∂haar d =
      ∑ l, ((haar d) (P.cell ⁻¹' {l})).toReal * klFun (L * p l) :=
    integral_comp_cell P (haar d) (fun l => klFun (L * p l))
  rw [hI]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [P.volume_cell, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem abs_integral_sub_le_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {C : ℝ}
    (h : ∀ x, |f x - g x| ≤ C) : |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ C := by
  rw [← integral_sub hf hg]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x - g x) (C := C)
    (Filter.Eventually.of_forall fun x => by simpa using h x)
  simpa using this

theorem potentialEnergy_trial (A : InteractionData d) (P : CellPartition d L δ)
    (r : Fin L → Torus d) (hr : ∀ l, P.cell (r l) = l) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) :
    |potentialEnergy A (trialProb P p hp h1 : Measure (Torus d)) - ∑ l, p l * A.V (r l)| ≤
      potentialModulus A δ := by
  rw [← integral_trial_comp P p hp h1 (fun l => A.V (r l))]
  refine abs_integral_sub_le_of_le
    (A.V_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_comp_cell P _ (fun l => A.V (r l))) fun x => ?_
  exact abs_sub_le_potentialModulus A (P.diam_cell _ _ (hr _).symm)

theorem interactionEnergy_trial (A : InteractionData d) (P : CellPartition d L δ)
    (r : Fin L → Torus d) (hr : ∀ l, P.cell (r l) = l) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) :
    |interactionEnergy A (trialProb P p hp h1 : Measure (Torus d)) -
        ∑ l, ∑ l', p l * p l' * A.W (r l) (r l')| ≤ interactionModulus A (2 * δ) := by
  set ν : Measure (Torus d) := (trialProb P p hp h1 : Measure (Torus d)) with hν
  have hc : Measurable (Prod.map P.cell P.cell) := P.measurable_cell.prodMap P.measurable_cell
  set Ψ : Fin L × Fin L → ℝ := fun z => A.W (r z.1) (r z.2) with hΨ
  have e1 : ∫ z, Ψ (Prod.map P.cell P.cell z) ∂(ν.prod ν) =
      ∑ l, ∑ l', p l * p l' * A.W (r l) (r l') := by
    rw [← integral_map hc.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
      ← Measure.map_prod_map ν ν P.measurable_cell P.measurable_cell,
      integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [measureReal_def, show ({(l, l')} : Set (Fin L × Fin L)) = {l} ×ˢ {l'} from
      (Set.singleton_prod_singleton).symm, Measure.prod_prod, ENNReal.toReal_mul,
      Measure.map_apply P.measurable_cell (measurableSet_singleton l),
      Measure.map_apply P.measurable_cell (measurableSet_singleton l'), hν, trial_real,
      trial_real, smul_eq_mul]
  rw [← e1]
  refine abs_integral_sub_le_of_le (integrable_W_prod A (trialProb P p hp h1)) ?_ fun z => ?_
  · exact (Integrable.of_finite (μ := (ν.prod ν).map (Prod.map P.cell P.cell)) (f := Ψ)).comp_measurable hc
  · have h1' := P.diam_cell z.1 (r (P.cell z.1)) (hr _).symm
    have h2' := P.diam_cell z.2 (r (P.cell z.2)) (hr _).symm
    exact abs_sub_le_interactionModulus A (x := z.1) (y := z.2) (x' := r (P.cell z.1))
      (y' := r (P.cell z.2)) (by linarith)

end DGPS.Lipschitz

namespace DGPS.Lipschitz

variable {d L : ℕ} {δ : ℝ}

theorem exists_reps (P : CellPartition d L δ) : ∃ r : Fin L → Torus d, ∀ l, P.cell (r l) = l := by
  have : ∀ l : Fin L, ∃ x, P.cell x = l := by
    intro l
    by_contra hne
    have hne := not_exists.1 hne
    have h0 : haar d (P.cell ⁻¹' {l}) = 0 := by
      have : P.cell ⁻¹' {l} = ∅ := by ext x; simpa using hne x
      rw [this, measure_empty]
    rw [P.volume_cell] at h0
    exact (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top L)) h0
  choose r hr using this
  exact ⟨r, hr⟩

theorem freeEnergyMinimumReal_le_real (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (h : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    freeEnergyMinimumReal A ≤
      (relativeEntropy (ν : Measure (Torus d)) (haar d)).toReal + potentialEnergy A ν +
        (1 / 2 : ℝ) * interactionEnergy A ν := by
  have h1 : freeEnergyMinimum A ≤ freeEnergy A ν := iInf_le _ ν
  have e : freeEnergy A ν =
      (((relativeEntropy (ν : Measure (Torus d)) (haar d)).toReal + potentialEnergy A ν +
        (1 / 2 : ℝ) * interactionEnergy A ν : ℝ) : EReal) := by
    unfold freeEnergy
    rw [← EReal.coe_ennreal_toReal h, EReal.coe_add, EReal.coe_add]
  rw [← coe_freeEnergyMinimumReal, e, EReal.coe_le_coe_iff] at h1
  exact h1

theorem variational_lower (A : InteractionData d) (P : CellPartition d L δ)
    (r : Fin L → Torus d) (hr : ∀ l, P.cell (r l) = l) (p : Fin L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h1 : ∑ l, p l = 1) :
    freeEnergyMinimumReal A - potentialModulus A δ - interactionModulus A (2 * δ) / 2 ≤
      ∑ l, p l * Real.log (L * p l) +
        (∑ l, p l * A.V (r l) + (1 / 2) * ∑ l, ∑ l', p l * p l' * A.W (r l) (r l')) := by
  have hne : relativeEntropy (trialProb P p hp h1 : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [relEntropy_trial]; exact ENNReal.ofReal_ne_top
  have h := freeEnergyMinimumReal_le_real A (trialProb P p hp h1) hne
  have hk : (relativeEntropy (trialProb P p hp h1 : Measure (Torus d)) (haar d)).toReal =
      ∑ l, p l * Real.log (L * p l) := by
    rw [relEntropy_trial, ENNReal.toReal_ofReal, sum_klFun (cell_L_pos P) p h1]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (klFun_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp _)))
  have hV := abs_le.1 (potentialEnergy_trial A P r hr p hp h1)
  have hW := abs_le.1 (interactionEnergy_trial A P r hr p hp h1)
  rw [hk] at h
  linarith [hV.1, hV.2, hW.1, hW.2]

section Discrete

variable {N : ℕ+}

theorem hamiltonian_type (A : InteractionData d) (r : Fin L → Torus d) (k : Fin (N : ℕ) → Fin L) :
    particleHamiltonian A N (fun i => r (k i)) =
      N * (∑ l, ((typeCount k l : ℝ) / N) * A.V (r l) +
        (1 / 2) * ∑ l, ∑ l', ((typeCount k l : ℝ) / N) * ((typeCount k l' : ℝ) / N) *
          A.W (r l) (r l')) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold particleHamiltonian
  rw [sum_comp_typeCount k (fun l => A.V (r l)),
    sum_comp_typeCount₂ k (fun l l' => A.W (r l) (r l')), mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    field_simp

theorem entropy_type (k : Fin (N : ℕ) → Fin L) :
    ∑ i, Real.log ((L : ℝ) * ((typeCount k (k i) : ℝ) / N)) =
      N * ∑ l, ((typeCount k l : ℝ) / N) * Real.log (L * ((typeCount k l : ℝ) / N)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [sum_comp_typeCount k (fun l => Real.log ((L : ℝ) * ((typeCount k l : ℝ) / N))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  field_simp

theorem type_prob_sum (k : Fin (N : ℕ) → Fin L) : ∑ l, ((typeCount k l : ℝ) / N) = 1 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_typeCount, div_self hN]

theorem partition_upper_bound (A : InteractionData d) (P : CellPartition d L δ) (N : ℕ+) :
    (1 / (N : ℝ)) * Real.log (particlePartition A N) ≤
      -freeEnergyMinimumReal A + 2 * potentialModulus A δ + interactionModulus A (2 * δ) +
        L * Real.log ((N : ℝ) + 1) / N := by
  obtain ⟨r, hr⟩ := exists_reps P
  have hLpos := cell_L_pos P
  have hNp : (0 : ℝ) < N := by exact_mod_cast N.pos
  set ωV := potentialModulus A δ with hωV
  set ωW := interactionModulus A (2 * δ) with hωW
  set β := freeEnergyMinimumReal A - ωV - ωW / 2 with hβ
  have hsum := sum_exp_le (N := (N : ℕ)) (L := L) N.pos hLpos
    (fun k => particleHamiltonian A N (fun i => r (k i))) β (fun k => by
      rw [hamiltonian_type A r k, entropy_type k]
      have hp0 : ∀ l, 0 ≤ (typeCount k l : ℝ) / N := fun l => by positivity
      have := variational_lower A P r hr (fun l => (typeCount k l : ℝ) / N) hp0
        (type_prob_sum k)
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [this, hβ]) hNp.le)
  have hle := particlePartition_le A P r hr N
  have hZ := DGPS.Particle.particlePartition_pos (A := A) (N := N)
  have hB : particlePartition A N ≤ Real.exp (N * (ωV + ωW / 2)) *
      (((N : ℝ) + 1) ^ L * Real.exp (-((N : ℝ) * β))) :=
    hle.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le)
  have hlog := Real.log_le_log hZ hB
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at hlog
  have : (1 / (N : ℝ)) * Real.log (particlePartition A N) ≤
      (1 / (N : ℝ)) * (N * (ωV + ωW / 2) + (L * Real.log ((N : ℝ) + 1) + -((N : ℝ) * β))) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  refine this.trans (le_of_eq ?_)
  rw [hβ]
  field_simp
  ring

end Discrete

end DGPS.Lipschitz

namespace DGPS.Lipschitz

open Filter Topology

variable {d : ℕ}

theorem potentialModulus_mono (A : InteractionData d) {a b : ℝ} (h : a ≤ b) :
    potentialModulus A a ≤ potentialModulus A b :=
  Real.sSup_le (by
    rintro r ⟨x, y, hxy, rfl⟩
    exact abs_sub_le_potentialModulus A (hxy.trans h)) (potentialModulus_nonneg A b)

theorem interactionModulus_mono (A : InteractionData d) {a b : ℝ} (h : a ≤ b) :
    interactionModulus A a ≤ interactionModulus A b :=
  Real.sSup_le (by
    rintro r ⟨x, y, x', y', hxy, rfl⟩
    exact abs_sub_le_interactionModulus A (hxy.trans h)) (interactionModulus_nonneg A b)

theorem abs_interactionEnergy_le (A : InteractionData d) :
    ∃ C : ℝ, ∀ ν : ProbabilityMeasure (Torus d), |interactionEnergy A ν| ≤ C := by
  obtain ⟨C, hC⟩ := A.W_bounded
  refine ⟨C, fun ν => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Torus d)).prod ν)
    (f := fun p : Torus d × Torus d => A.W p.1 p.2) (C := C)
    (Filter.Eventually.of_forall fun z => by simpa using hC z.1 z.2)
  simpa [interactionEnergy] using this

theorem tendsto_nat_inv : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)

theorem tendsto_log_div_succ (c : ℝ) :
    Tendsto (fun N : ℕ+ => c * Real.log (((N : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hN : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
  have h1 := (h0.comp hN).const_mul (2 * |c|)
  rw [mul_zero] at h1
  refine squeeze_zero_norm (fun N => ?_) h1
  have hNp : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hl : 0 ≤ Real.log (((N : ℕ) : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ |c| * Real.log (((N : ℕ) : ℝ) + 1) := mul_nonneg (abs_nonneg _) hl
  have e1 : ‖c * Real.log (((N : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ)‖ =
      |c| * Real.log (((N : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hl,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((N : ℕ) : ℝ))]
  rw [e1]
  simp only [Function.comp]
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hq (sub_nonneg.2 hNp)]

/-- LIP018: the partition function limit `N⁻¹ log Z_N → -F_*`, the quantitative upper bound for
equal-volume cell partitions (via finite empirical types), and the product-trial lower bound. -/
theorem partition_function_limit_by_finite_empirical_types (A : InteractionData d) :
    Tendsto (fun N : ℕ+ => (1 / (N : ℝ)) * Real.log (particlePartition A N)) atTop
        (𝓝 (-freeEnergyMinimumReal A)) ∧
      (∀ (L : ℕ) (δ : ℝ) (_ : CellPartition d L δ) (N : ℕ+),
        (1 / (N : ℝ)) * Real.log (particlePartition A N) ≤
          -freeEnergyMinimumReal A + 2 * potentialModulus A δ + interactionModulus A (2 * δ) +
            L * Real.log ((N : ℝ) + 1) / N) ∧
      (∀ (ν : ProbabilityMeasure (Torus d)),
        relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤ → ∀ N : ℕ+,
          -(freeEnergy A ν).toReal + (1 / (2 * (N : ℝ))) * interactionEnergy A ν ≤
            (1 / (N : ℝ)) * Real.log (particlePartition A N)) := by
  refine ⟨?_, fun L δ P N => partition_upper_bound A P N, fun ν hν N =>
    DGPS.Particle.partition_lower_bound A N ν hν⟩
  obtain ⟨C, hC⟩ := abs_interactionEnergy_le A
  obtain ⟨μ, hμ⟩ := freeEnergy_minimum_exists A
  have hfin : FiniteFreeEnergy A μ :=
    ⟨freeEnergyMinimumReal A, by rw [hμ, coe_freeEnergyMinimumReal]⟩
  have hent := (finiteFreeEnergy_iff A μ).1 hfin
  have hμF : (freeEnergy A μ).toReal = freeEnergyMinimumReal A := by
    rw [hμ, ← coe_freeEnergyMinimumReal, EReal.toReal_coe]
  have hlow : ∀ N : ℕ+, -freeEnergyMinimumReal A - C / 2 * ((N : ℕ) : ℝ)⁻¹ ≤
      (1 / (N : ℝ)) * Real.log (particlePartition A N) := by
    intro N
    have hNp : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    have h1 := DGPS.Particle.partition_lower_bound A N μ hent
    have h2 := (abs_le.1 (hC μ)).1
    have h3 : (1 / (2 * (N : ℝ))) * (-C) ≤ (1 / (2 * (N : ℝ))) * interactionEnergy A μ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (1 / (2 * (N : ℝ))) * (-C) = -(C / 2 * ((N : ℕ) : ℝ)⁻¹) := by
      field_simp
    rw [hμF] at h1
    linarith
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · have hT : Tendsto (fun N : ℕ+ => -freeEnergyMinimumReal A - C / 2 * ((N : ℕ) : ℝ)⁻¹) atTop
        (𝓝 (-freeEnergyMinimumReal A)) := by
      have := (tendsto_const_nhds (x := -freeEnergyMinimumReal A)).sub
        (tendsto_nat_inv.const_mul (C / 2))
      simpa using this
    filter_upwards [hT.eventually (lt_mem_nhds ha')] with N hN
    exact hN.trans_le (hlow N)
  · set ε := a' + freeEnergyMinimumReal A with hε
    have hεp : 0 < ε := by rw [hε]; linarith
    obtain ⟨δ1, hδ1, h1⟩ := exists_potentialModulus_le A (show 0 < ε / 8 by positivity)
    obtain ⟨δ2, hδ2, h2⟩ := exists_interactionModulus_le A (show 0 < ε / 8 by positivity)
    have hδ : 0 < min δ1 δ2 := lt_min hδ1 hδ2
    obtain ⟨L, ⟨P⟩⟩ := exists_cellPartition d hδ
    have h1' : potentialModulus A (min δ1 δ2) ≤ ε / 8 :=
      (potentialModulus_mono A (min_le_left _ _)).trans h1
    have h2' : interactionModulus A (2 * min δ1 δ2) ≤ ε / 8 :=
      (interactionModulus_mono A (by linarith [min_le_right δ1 δ2])).trans h2
    have hT : Tendsto (fun N : ℕ+ => -freeEnergyMinimumReal A + 2 * potentialModulus A (min δ1 δ2) +
        interactionModulus A (2 * min δ1 δ2) + (L : ℝ) * Real.log (((N : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ))
        atTop (𝓝 (-freeEnergyMinimumReal A + 2 * potentialModulus A (min δ1 δ2) +
          interactionModulus A (2 * min δ1 δ2) + 0)) :=
      tendsto_const_nhds.add (tendsto_log_div_succ (L : ℝ))
    have hlt : -freeEnergyMinimumReal A + 2 * potentialModulus A (min δ1 δ2) +
        interactionModulus A (2 * min δ1 δ2) + 0 < a' := by
      rw [hε] at h1' h2'
      linarith
    filter_upwards [hT.eventually (gt_mem_nhds hlt)] with N hN
    exact (partition_upper_bound A P N).trans_lt hN

end DGPS.Lipschitz
