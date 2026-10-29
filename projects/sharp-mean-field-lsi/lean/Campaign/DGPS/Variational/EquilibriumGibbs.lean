import DGPS.Model.FreeEnergy
import DGPS.Analysis.WeakConvolution
import DGPS.Lipschitz.Representatives
import DGPS.Foundations.WeakContractions

/-!
# Free energy minimizers are Gibbs measures (LIP017)

Let `A = (V, W)` be continuous interaction data on the torus and `F` the free energy of DEF008.
The main result `free_energy_minimum_and_gibbs_identity` states:

* `F` attains a finite minimum;
* every minimizer `μ` equals `q m` with `q = exp (-(V + W * μ)) / ∫ exp (-(V + W * μ)) dm`
  (the Gibbs fixed-point equation), proved by comparing `μ` with the mixtures
  `(1 - s) μ + s (q m)` and the Gibbs variational identity;
* for every probability `ν` with finite entropy,
  `F(ν) - F(μ) = H(ν | μ) + (1/2) ∫ K dν⊗ν` with `K` the kernel `W` centered at `μ`;
* under `LipschitzData A`, `q` is Lipschitz and bounded above and below by positive constants
  independent of the minimizer, and `∇ log q = - ∇ (V + W * μ)` as weak `L^∞` gradients.
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}


theorem klDiv_tilted_forward {α : Type*} [MeasurableSpace α] {ρ ν : Measure α}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] {f : α → ℝ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) (h : klDiv ρ ν ≠ ⊤) :
    klDiv ρ (ν.tilted f) ≠ ⊤ ∧
      (klDiv ρ (ν.tilted f)).toReal =
        (klDiv ρ ν).toReal - ∫ x, f x ∂ρ + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp h
  have hfρ : Integrable f ρ := Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hexp : ∀ x, ‖Real.exp (f x)‖ ≤ Real.exp B := fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hfν : Integrable (fun x => Real.exp (f x)) ν :=
    Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable _
      (Filter.Eventually.of_forall hexp)
  have := isProbabilityMeasure_tilted hfν
  have hac' : ρ ≪ ν.tilted f := hac.trans (absolutelyContinuous_tilted hfν)
  have hint' := integrable_llr_tilted_right hac hfρ hint hfν
  refine ⟨klDiv_ne_top hac' hint', ?_⟩
  rw [toReal_klDiv_of_measure_eq hac' (by simp), toReal_klDiv_of_measure_eq hac (by simp)]
  exact integral_llr_tilted_right hac hfρ hfν hint



/-- Mixture `(1-s) μ + s g`. -/
noncomputable def mixMeasure {α : Type*} [MeasurableSpace α] (s : ℝ≥0) (μ g : Measure α) :
    Measure α := (1 - s) • μ + s • g

theorem isProbabilityMeasure_mix {α : Type*} [MeasurableSpace α] {s : ℝ≥0} (hs : s ≤ 1)
    {μ g : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure g] :
    IsProbabilityMeasure (mixMeasure s μ g) := by
  constructor
  have h : ((1 - s : ℝ≥0) : ℝ≥0∞) + (s : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_add, tsub_add_cancel_of_le hs]; simp
  simp only [mixMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def,
    smul_eq_mul, mul_one]
  exact h

theorem klDiv_mix_le {α : Type*} [MeasurableSpace α] {s : ℝ≥0} (hs : s ≤ 1)
    {μ g : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure g] (hμg : μ ≪ g) :
    klDiv (mixMeasure s μ g) g ≤ ((1 - s : ℝ≥0) : ℝ≥0∞) * klDiv μ g := by
  have := isProbabilityMeasure_mix hs (μ := μ) (g := g)
  have hac : mixMeasure s μ g ≪ g := by
    intro t ht
    simp [mixMeasure, hμg ht, ht]
  rw [klDiv_eq_lintegral_klFun_of_ac hac, klDiv_eq_lintegral_klFun_of_ac hμg,
    ← lintegral_const_mul' ((1 - s : ℝ≥0) : ℝ≥0∞) _ ENNReal.coe_ne_top]
  have hd : (mixMeasure s μ g).rnDeriv g =ᵐ[g] fun x => (1 - s) • μ.rnDeriv g x + s • (1 : ℝ≥0∞) := by
    have h1 := Measure.rnDeriv_add ((1 - s) • μ) (s • g) g
    have h2 := Measure.rnDeriv_smul_left μ g (1 - s)
    have h3 := Measure.rnDeriv_smul_left g g s
    have h4 := Measure.rnDeriv_self g
    filter_upwards [h1, h2, h3, h4] with x a b c e
    simp only [mixMeasure]
    simp only [Pi.add_apply, Pi.smul_apply] at a b c
    rw [a, b, c, e]
  refine lintegral_mono_ae ?_
  filter_upwards [hd, Measure.rnDeriv_ne_top μ g] with x hx hx2
  rw [hx]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hr : 0 ≤ (μ.rnDeriv g x).toReal := ENNReal.toReal_nonneg
  have := convexOn_klFun.2 (Set.mem_Ici.mpr hr) (Set.mem_Ici.mpr (zero_le_one' ℝ))
    (NNReal.coe_nonneg (1 - s)) (NNReal.coe_nonneg s)
    (by rw [NNReal.coe_sub hs]; simp)
  simp only [smul_eq_mul, klFun_one, mul_zero, add_zero] at this
  convert this using 2
  rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hx2) ENNReal.coe_ne_top,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]




/-- `(W * μ)(x) = ∫ W(x,y) dμ(y)`. -/
noncomputable def interactionConvolution (A : InteractionData d) (μ : Measure (Torus d))
    (x : Torus d) : ℝ :=
  ∫ y, A.W x y ∂μ

/-- The equilibrium potential `Φ = V + W * μ`. -/
noncomputable def equilibriumPotential (A : InteractionData d) (μ : Measure (Torus d))
    (x : Torus d) : ℝ :=
  A.V x + interactionConvolution A μ x

/-- The partition function `Z = ∫ e^{-Φ} dm`. -/
noncomputable def gibbsPartition (A : InteractionData d) (μ : Measure (Torus d)) : ℝ :=
  ∫ x, Real.exp (-equilibriumPotential A μ x) ∂(haar d)

/-- The Gibbs density `q = e^{-Φ} / Z` (with respect to Haar measure). -/
noncomputable def gibbsDensity (A : InteractionData d) (μ : Measure (Torus d))
    (x : Torus d) : ℝ :=
  Real.exp (-equilibriumPotential A μ x) / gibbsPartition A μ

/-- The centered kernel `K_μ(x,y) = W(x,y) - (W*μ)(x) - (W*μ)(y) + ∬ W dμ²`. -/
noncomputable def centeredKernel (A : InteractionData d) (μ : Measure (Torus d))
    (x y : Torus d) : ℝ :=
  A.W x y - interactionConvolution A μ x - interactionConvolution A μ y + interactionEnergy A μ

theorem continuous_interactionConvolution (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Continuous (interactionConvolution A μ) := by
  have h := continuous_parametric_integral_of_continuous (μ := μ) (f := A.W)
    A.W_continuous (isCompact_univ : IsCompact (Set.univ : Set (Torus d)))
  simp only [Measure.restrict_univ] at h
  exact h

theorem abs_interactionConvolution_le (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {C : ℝ} (hC : ∀ x y, |A.W x y| ≤ C) (x : Torus d) :
    |interactionConvolution A μ x| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => A.W x y)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC x y)
  simpa [interactionConvolution, Real.norm_eq_abs] using this

theorem continuous_equilibriumPotential (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Continuous (equilibriumPotential A μ) :=
  A.V_continuous.add (continuous_interactionConvolution A μ)

/-- Uniform bound `|Φ| ≤ B` with `B` independent of `μ`. -/
theorem exists_potential_bound (A : InteractionData d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (x : Torus d),
      |equilibriumPotential A μ x| ≤ B := by
  obtain ⟨BV, hBV⟩ := A.V_bounded
  obtain ⟨BW, hBW⟩ := A.W_bounded
  refine ⟨|BV| + |BW|, by positivity, fun μ _ x => ?_⟩
  unfold equilibriumPotential
  refine (abs_add_le _ _).trans (add_le_add ((hBV x).trans (le_abs_self _)) ?_)
  exact (abs_interactionConvolution_le A μ hBW x).trans (le_abs_self _)

theorem integrable_exp_neg_potential (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    Integrable (fun x => Real.exp (-equilibriumPotential A μ x)) (haar d) :=
  SharpLSI.integrable_exp_neg_of_continuous (haar d) (continuous_equilibriumPotential A μ)

theorem gibbsPartition_pos (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : 0 < gibbsPartition A μ :=
  integral_exp_pos (integrable_exp_neg_potential A μ)

theorem gibbsPartition_bounds (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {B : ℝ} (hB : ∀ x, |equilibriumPotential A μ x| ≤ B) :
    Real.exp (-B) ≤ gibbsPartition A μ ∧ gibbsPartition A μ ≤ Real.exp B := by
  have hb : ∀ x, Real.exp (-B) ≤ Real.exp (-equilibriumPotential A μ x) ∧
      Real.exp (-equilibriumPotential A μ x) ≤ Real.exp B := fun x => by
    have := abs_le.mp (hB x)
    exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩
  constructor
  · have := integral_mono (integrable_const (Real.exp (-B))) (integrable_exp_neg_potential A μ)
      (fun x => (hb x).1)
    simpa [gibbsPartition] using this
  · have := integral_mono (integrable_exp_neg_potential A μ) (integrable_const (Real.exp B))
      (fun x => (hb x).2)
    simpa [gibbsPartition] using this

theorem gibbsDensity_bounds (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {B : ℝ} (hB : ∀ x, |equilibriumPotential A μ x| ≤ B) (x : Torus d) :
    Real.exp (-(2 * B)) ≤ gibbsDensity A μ x ∧ gibbsDensity A μ x ≤ Real.exp (2 * B) := by
  obtain ⟨hZ1, hZ2⟩ := gibbsPartition_bounds A μ hB
  have hx := abs_le.mp (hB x)
  have hZ := gibbsPartition_pos A μ
  unfold gibbsDensity
  constructor
  · rw [le_div_iff₀ hZ]
    calc Real.exp (-(2 * B)) * gibbsPartition A μ ≤ Real.exp (-(2 * B)) * Real.exp B :=
          mul_le_mul_of_nonneg_left hZ2 (Real.exp_pos _).le
      _ = Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · rw [div_le_iff₀ hZ]
    calc Real.exp (-equilibriumPotential A μ x) ≤ Real.exp B := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (2 * B) * Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ1 (Real.exp_pos _).le






/-- The bilinear pairing `∬ W(x,y) da(x) db(y)`. -/
noncomputable def interactionPairing (A : InteractionData d) (a b : Measure (Torus d)) : ℝ :=
  ∫ p, A.W p.1 p.2 ∂(a.prod b)

theorem interactionPairing_self (A : InteractionData d) (ν : Measure (Torus d)) :
    interactionPairing A ν ν = interactionEnergy A ν := rfl

theorem integrable_W_pair (A : InteractionData d) (a b : Measure (Torus d)) [IsFiniteMeasure a]
    [IsFiniteMeasure b] : Integrable (fun p : Torus d × Torus d => A.W p.1 p.2) (a.prod b) :=
  A.W_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem interactionPairing_symm (A : InteractionData d) (a b : Measure (Torus d))
    [IsFiniteMeasure a] [IsFiniteMeasure b] :
    interactionPairing A a b = interactionPairing A b a := by
  unfold interactionPairing
  rw [← integral_prod_swap (μ := a) (ν := b) (fun p : Torus d × Torus d => A.W p.1 p.2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact A.W_symm _ _

theorem interactionPairing_eq_integral (A : InteractionData d) (a b : Measure (Torus d))
    [IsFiniteMeasure a] [IsFiniteMeasure b] :
    interactionPairing A a b = ∫ x, interactionConvolution A b x ∂a :=
  integral_prod _ (integrable_W_pair A a b)

theorem interactionPairing_mix_left (A : InteractionData d) (s : ℝ≥0) (a₁ a₂ b : Measure (Torus d))
    [IsFiniteMeasure a₁] [IsFiniteMeasure a₂] [IsFiniteMeasure b] (hs : s ≤ 1) :
    interactionPairing A (mixMeasure s a₁ a₂) b =
      (1 - (s : ℝ)) * interactionPairing A a₁ b + (s : ℝ) * interactionPairing A a₂ b := by
  unfold interactionPairing mixMeasure
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    integral_add_measure ((integrable_W_pair A a₁ b).smul_measure_nnreal)
      ((integrable_W_pair A a₂ b).smul_measure_nnreal),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def,
    NNReal.smul_def, NNReal.coe_sub hs, NNReal.coe_one, smul_eq_mul, smul_eq_mul]

theorem interactionPairing_mix_right (A : InteractionData d) (s : ℝ≥0) (a b₁ b₂ : Measure (Torus d))
    [IsFiniteMeasure a] [IsFiniteMeasure b₁] [IsFiniteMeasure b₂] (hs : s ≤ 1) :
    interactionPairing A a (mixMeasure s b₁ b₂) =
      (1 - (s : ℝ)) * interactionPairing A a b₁ + (s : ℝ) * interactionPairing A a b₂ := by
  unfold interactionPairing mixMeasure
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    integral_add_measure ((integrable_W_pair A a b₁).smul_measure_nnreal)
      ((integrable_W_pair A a b₂).smul_measure_nnreal),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def,
    NNReal.smul_def, NNReal.coe_sub hs, NNReal.coe_one, smul_eq_mul, smul_eq_mul]



theorem integrable_exp_of_bound {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ} {B : ℝ} (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) :
    Integrable (fun x => Real.exp (f x)) ν := by
  refine Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp B)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))

theorem klDiv_tilted_ne_top_iff {α : Type*} [MeasurableSpace α] {ρ ν : Measure α}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] {f : α → ℝ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) :
    klDiv ρ (ν.tilted f) ≠ ⊤ ↔ klDiv ρ ν ≠ ⊤ := by
  refine ⟨fun h => ?_, fun h => (klDiv_tilted_forward hf hB h).1⟩
  have hfν := integrable_exp_of_bound (ν := ν) hf hB
  have := isProbabilityMeasure_tilted hfν
  have h2 := (klDiv_tilted_forward (ρ := ρ) (ν := ν.tilted f) (f := -f) (B := B) hf.neg
    (fun x => by simpa using hB x) h).1
  rwa [tilted_tilted hfν, add_neg_cancel, show (0 : α → ℝ) = fun _ => 0 from rfl,
    ← Pi.zero_def, tilted_zero] at h2

/-- The Gibbs measure `m.tilted(-Φ)`. -/
noncomputable def gibbsMeasure (A : InteractionData d) (μ : Measure (Torus d)) :
    Measure (Torus d) :=
  (haar d).tilted fun x => -equilibriumPotential A μ x

theorem gibbsMeasure_eq_withDensity (A : InteractionData d) (μ : Measure (Torus d)) :
    gibbsMeasure A μ = (haar d).withDensity fun x => ENNReal.ofReal (gibbsDensity A μ x) := rfl

theorem isProbabilityMeasure_gibbsMeasure (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (gibbsMeasure A μ) :=
  isProbabilityMeasure_tilted (integrable_exp_neg_potential A μ)

theorem integrable_of_continuous_torus {f : Torus d → ℝ} (hf : Continuous f)
    (ν : Measure (Torus d)) [IsFiniteMeasure ν] : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem freeEnergy_eq_coe (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (h : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    freeEnergy A ν = (((klDiv (ν : Measure (Torus d)) (haar d)).toReal +
      (potentialEnergy A ν + (1 / 2 : ℝ) * interactionEnergy A ν) : ℝ) : EReal) := by
  rw [freeEnergy_eq_klDiv]
  simp only [EReal.coe_add, EReal.coe_ennreal_toReal h]

/-- Real form of the Gibbs identity: `F(ν) + log Z = H(ν|g) + ½⟪ν,ν⟫ - ⟪ν,μ⟫`. -/
theorem free_energy_gibbs_identity (A : InteractionData d) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hν : klDiv ν (haar d) ≠ ⊤) :
    klDiv ν (gibbsMeasure A μ) ≠ ⊤ ∧
      (klDiv ν (haar d)).toReal + (potentialEnergy A ν + (1 / 2 : ℝ) * interactionEnergy A ν) +
          Real.log (gibbsPartition A μ) =
        (klDiv ν (gibbsMeasure A μ)).toReal + (1 / 2 : ℝ) * interactionPairing A ν ν -
          interactionPairing A ν μ := by
  obtain ⟨B, -, hB⟩ := exists_potential_bound A
  have hmeas : Measurable fun x => -equilibriumPotential A μ x :=
    (continuous_equilibriumPotential A μ).neg.measurable
  have hb : ∀ x, |-equilibriumPotential A μ x| ≤ B := fun x => by simpa using hB μ x
  obtain ⟨h1, h2⟩ := klDiv_tilted_forward (ρ := ν) (ν := haar d) hmeas hb hν
  refine ⟨h1, ?_⟩
  have hV : Integrable A.V ν := integrable_of_continuous_torus A.V_continuous ν
  have hC : Integrable (interactionConvolution A μ) ν :=
    integrable_of_continuous_torus (continuous_interactionConvolution A μ) ν
  have e1 : ∫ x, -equilibriumPotential A μ x ∂ν =
      -(potentialEnergy A ν + interactionPairing A ν μ) := by
    rw [integral_neg, interactionPairing_eq_integral]
    congr 1
    exact integral_add hV hC
  rw [e1] at h2
  have hZ : ∫ x, Real.exp (-equilibriumPotential A μ x) ∂(haar d) = gibbsPartition A μ := rfl
  rw [hZ] at h2
  unfold gibbsMeasure
  rw [h2]
  rw [← interactionPairing_self]
  ring


theorem nonpos_of_forall_small {h D : ℝ}
    (H : ∀ s : ℝ≥0, 0 < s → s ≤ 1 → h ≤ (s : ℝ) * D / 2) : h ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hD : 0 < |D| + 1 := by positivity
  set t : ℝ := min 1 (h / (|D| + 1)) with ht
  have htpos : 0 < t := lt_min one_pos (div_pos hpos hD)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ h / (|D| + 1) := min_le_right _ _
  have := H t.toNNReal (by simpa using htpos) (by simpa using ht1)
  rw [Real.coe_toNNReal _ htpos.le] at this
  have h3 : t * (|D| + 1) ≤ h := by rwa [le_div_iff₀ hD] at ht2
  have h4 : t * D ≤ t * |D| := mul_le_mul_of_nonneg_left (le_abs_self D) htpos.le
  nlinarith [abs_nonneg D]

theorem klDiv_gibbs_ne_top_iff (A : InteractionData d) (μ ρ : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] :
    klDiv ρ (gibbsMeasure A μ) ≠ ⊤ ↔ klDiv ρ (haar d) ≠ ⊤ := by
  obtain ⟨B, -, hB⟩ := exists_potential_bound A
  exact klDiv_tilted_ne_top_iff (f := fun x => -equilibriumPotential A μ x)
    (continuous_equilibriumPotential A μ).neg.measurable (fun x => by rw [abs_neg]; exact hB μ x)

theorem minimizer_eq_gibbs (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (hμ : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    (μ : Measure (Torus d)) = gibbsMeasure A (μ : Measure (Torus d)) := by
  have hfin : klDiv (μ : Measure (Torus d)) (haar d) ≠ ⊤ := by
    by_contra hT
    have h := hμ (haarProbability d)
    obtain ⟨r, hr⟩ := finiteFreeEnergy_haar A
    rw [freeEnergy_eq_klDiv A μ, hT, EReal.coe_ennreal_top, EReal.top_add_coe, hr] at h
    exact absurd (top_le_iff.mp h) (EReal.coe_ne_top r)
  have hgp := isProbabilityMeasure_gibbsMeasure A (μ : Measure (Torus d))
  obtain ⟨hMg, hid⟩ := free_energy_gibbs_identity A (μ : Measure (Torus d)) (μ : Measure (Torus d)) hfin
  set g := gibbsMeasure A (μ : Measure (Torus d)) with hg
  set L := Real.log (gibbsPartition A (μ : Measure (Torus d))) with hL
  set h := (klDiv (μ : Measure (Torus d)) g).toReal with hh
  set a := interactionPairing A (μ : Measure (Torus d)) (μ : Measure (Torus d)) with ha
  set b := interactionPairing A g (μ : Measure (Torus d)) with hb
  set c := interactionPairing A g g with hc
  have hbb : interactionPairing A (μ : Measure (Torus d)) g = b := interactionPairing_symm A _ _
  have key : ∀ s : ℝ≥0, 0 < s → s ≤ 1 → h ≤ (s : ℝ) * (a - 2 * b + c) / 2 := by
    intro s hs0 hs1
    have hmp := isProbabilityMeasure_mix hs1 (μ := (μ : Measure (Torus d))) (g := g)
    obtain ⟨ν, hνc⟩ : ∃ ν : ProbabilityMeasure (Torus d),
        (ν : Measure (Torus d)) = mixMeasure s (μ : Measure (Torus d)) g := ⟨⟨_, hmp⟩, rfl⟩
    have hacμ : (μ : Measure (Torus d)) ≪ g := (klDiv_ne_top_iff.mp hMg).1
    have hmixle := klDiv_mix_le hs1 hacμ
    have hmixne : klDiv (mixMeasure s (μ : Measure (Torus d)) g) g ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hMg) hmixle
    have hνm : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
      rw [hνc]
      exact (klDiv_gibbs_ne_top_iff A (μ : Measure (Torus d)) _).mp hmixne
    obtain ⟨-, hidν⟩ := free_energy_gibbs_identity A (μ : Measure (Torus d)) (ν : Measure (Torus d)) hνm
    have hle := hμ ν
    rw [freeEnergy_eq_coe A μ hfin, freeEnergy_eq_coe A ν hνm, EReal.coe_le_coe_iff] at hle
    have hreal : (klDiv (mixMeasure s (μ : Measure (Torus d)) g) g).toReal ≤ (1 - (s : ℝ)) * h := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hMg) hmixle
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_sub hs1, NNReal.coe_one] at this
    have e : (1 / 2 : ℝ) * interactionPairing A (ν : Measure (Torus d)) (ν : Measure (Torus d)) -
        interactionPairing A (ν : Measure (Torus d)) (μ : Measure (Torus d)) =
        -(1 / 2) * a + (s : ℝ) ^ 2 / 2 * (a - 2 * b + c) := by
      have := isProbabilityMeasure_mix hs1 (μ := (μ : Measure (Torus d))) (g := g)
      rw [hνc, interactionPairing_mix_left A s _ _ _ hs1, interactionPairing_mix_left A s _ _ _ hs1,
        interactionPairing_mix_right A s _ _ _ hs1, interactionPairing_mix_right A s _ _ _ hs1,
        hbb]
      have hb' : interactionPairing A g (μ : Measure (Torus d)) = b := rfl
      rw [hb']
      ring
    have hE : interactionEnergy A (μ : Measure (Torus d)) = a := rfl
    rw [hνc] at hidν hle
    rw [hνc] at e
    have hs : (0 : ℝ) < s := by exact_mod_cast hs0
    have : (s : ℝ) * h ≤ (s : ℝ) * ((s : ℝ) * (a - 2 * b + c) / 2) := by
      nlinarith
    exact le_of_mul_le_mul_left this hs
  have hh0 : h ≤ 0 := nonpos_of_forall_small key
  have hh1 : (klDiv (μ : Measure (Torus d)) g).toReal = 0 :=
    le_antisymm hh0 ENNReal.toReal_nonneg
  have hz : klDiv (μ : Measure (Torus d)) g = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hh1 with h0 | h0
    · exact h0
    · exact absurd h0 hMg
  exact (klDiv_eq_zero_iff.mp hz)


theorem integral_centeredKernel (A : InteractionData d) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ p, centeredKernel A μ p.1 p.2 ∂(ν.prod ν) =
      interactionPairing A ν ν - 2 * interactionPairing A ν μ + interactionPairing A μ μ := by
  have hc := continuous_interactionConvolution A μ
  have hW : Integrable (fun p : Torus d × Torus d => A.W p.1 p.2) (ν.prod ν) :=
    integrable_W_pair A ν ν
  have hc1 : Integrable (fun p : Torus d × Torus d => interactionConvolution A μ p.1)
      (ν.prod ν) :=
    (hc.comp continuous_fst).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc2 : Integrable (fun p : Torus d × Torus d => interactionConvolution A μ p.2)
      (ν.prod ν) :=
    (hc.comp continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hk : Integrable (fun _ : Torus d × Torus d => interactionEnergy A μ) (ν.prod ν) :=
    integrable_const _
  have e1 : ∫ p : Torus d × Torus d, interactionConvolution A μ p.1 ∂(ν.prod ν) =
      interactionPairing A ν μ := by
    rw [integral_fun_fst, interactionPairing_eq_integral]; simp
  have e2 : ∫ p : Torus d × Torus d, interactionConvolution A μ p.2 ∂(ν.prod ν) =
      interactionPairing A ν μ := by
    rw [integral_fun_snd, interactionPairing_eq_integral]; simp
  have i2 : Integrable (fun p : Torus d × Torus d =>
      A.W p.1 p.2 - interactionConvolution A μ p.1) (ν.prod ν) := hW.sub hc1
  have i1 : Integrable (fun p : Torus d × Torus d =>
      A.W p.1 p.2 - interactionConvolution A μ p.1 - interactionConvolution A μ p.2)
      (ν.prod ν) := i2.sub hc2
  unfold centeredKernel
  rw [integral_add i1 hk, integral_sub i2 hc2, integral_sub hW hc1, e1, e2, integral_const]
  simp only [probReal_univ, one_smul]
  rw [← interactionPairing_self]
  unfold interactionPairing
  ring

theorem free_energy_sub_eq (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (hμ : (μ : Measure (Torus d)) = gibbsMeasure A (μ : Measure (Torus d)))
    (ν : ProbabilityMeasure (Torus d))
    (hν : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    freeEnergy A ν - freeEnergy A μ =
      ((relativeEntropy (ν : Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) +
        (((1 / 2 : ℝ) * ∫ p, centeredKernel A (μ : Measure (Torus d)) p.1 p.2
          ∂((ν : Measure (Torus d)).prod (ν : Measure (Torus d))) : ℝ) : EReal) := by
  have hνk : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rwa [Analysis.relativeEntropy_eq_klDiv] at hν
  have hμk : klDiv (μ : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [← klDiv_gibbs_ne_top_iff A (μ : Measure (Torus d)) (μ : Measure (Torus d)), ← hμ]
    simp
  obtain ⟨hνg, hid⟩ := free_energy_gibbs_identity A (μ : Measure (Torus d)) (ν : Measure (Torus d)) hνk
  obtain ⟨-, hidμ⟩ := free_energy_gibbs_identity A (μ : Measure (Torus d)) (μ : Measure (Torus d)) hμk
  rw [← hμ] at hνg hid hidμ
  rw [klDiv_self, ENNReal.toReal_zero] at hidμ
  have hνμ : relativeEntropy (ν : Measure (Torus d)) (μ : Measure (Torus d)) =
      klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d)) := Analysis.relativeEntropy_eq_klDiv
  rw [freeEnergy_eq_coe A ν hνk, freeEnergy_eq_coe A μ hμk, hνμ,
    ← EReal.coe_ennreal_toReal hνg, ← EReal.coe_sub, ← EReal.coe_add]
  congr 1
  rw [integral_centeredKernel]
  have hE : interactionEnergy A (μ : Measure (Torus d)) =
      interactionPairing A (μ : Measure (Torus d)) (μ : Measure (Torus d)) := rfl
  linarith


theorem isWeakGradientLp_top_neg_sub_const {Φ : Torus d → ℝ} {G : Torus d → Tangent d} (c : ℝ)
    (h : IsWeakGradientLp ∞ Φ G) :
    IsWeakGradientLp ∞ (fun x => -Φ x - c) (fun x => -G x) where
  memLp := h.memLp.neg.sub (memLp_const c)
  memLp_grad := h.memLp_grad.neg
  ibp φ hφ j := by
    have h1 := h.ibp φ hφ j
    have h0 := (isWeakGradient_const (d := d) 1).ibp φ hφ j
    simp only [one_mul, PiLp.zero_apply, zero_mul, integral_zero, neg_zero] at h0
    have iΦ : Integrable (fun x => Φ x * coordPartial j φ x) (haar d) :=
      integrable_mul_top h.memLp (hφ.memLp_top_coordPartial j)
    have ic : Integrable (fun x => c * coordPartial j φ x) (haar d) :=
      ((hφ.memLp_top_coordPartial j).integrable le_top).const_mul c
    have e : ∫ x, (-Φ x - c) * coordPartial j φ x ∂haar d =
        -∫ x, Φ x * coordPartial j φ x ∂haar d - c * ∫ x, coordPartial j φ x ∂haar d := by
      have i3 : Integrable (fun x => -(Φ x * coordPartial j φ x)) (haar d) := iΦ.neg
      rw [← integral_const_mul, ← integral_neg, ← integral_sub i3 ic]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [e, h0, h1]
    simp only [PiLp.neg_apply, neg_mul, integral_neg, mul_zero, sub_zero, neg_neg]

theorem exp_sub_exp_le {a b : ℝ} (_h : b ≤ a) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have h1 := Real.add_one_le_exp (b - a)
  have e : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  have hp := Real.exp_pos a
  rw [e]
  nlinarith

theorem abs_exp_sub_exp_le {a b B : ℝ} (ha : a ≤ B) (hb : b ≤ B) :
    |Real.exp a - Real.exp b| ≤ Real.exp B * |a - b| := by
  have key : ∀ {a b : ℝ}, b ≤ a → a ≤ B →
      |Real.exp a - Real.exp b| ≤ Real.exp B * |a - b| := by
    intro a b hba haB
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    calc Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := exp_sub_exp_le hba
      _ ≤ Real.exp B * (a - b) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr haB) (sub_nonneg.mpr hba)
  rcases le_total b a with h | h
  · exact key h ha
  · rw [abs_sub_comm, abs_sub_comm a b]; exact key h hb

theorem lipschitz_equilibriumPotential (A : InteractionData d) (hA : LipschitzData A) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ],
      TorusLipschitzWith L (equilibriumPotential A μ) := by
  obtain ⟨LV, hLV⟩ := hA.V_lipschitz
  obtain ⟨LW, hLW⟩ := hA.W_lipschitz
  have hx : ∀ y, TorusLipschitzWith LW fun x => A.W x y := by
    intro y x x'
    have := hLW x y x' y
    have h0 : 0 ≤ torusDist x x' := Real.sqrt_nonneg _
    simpa [torusDist_metric.1 y, Real.sqrt_sq h0] using this
  refine ⟨|LV| + |LW|, by positivity, fun μ _ x x' => ?_⟩
  have hc := lipschitz_integral_of_lipschitz A.W_continuous hx μ x x'
  have h0 : 0 ≤ torusDist x x' := Real.sqrt_nonneg _
  have e : equilibriumPotential A μ x - equilibriumPotential A μ x' =
      (A.V x - A.V x') + (interactionConvolution A μ x - interactionConvolution A μ x') := by
    unfold equilibriumPotential; ring
  rw [e]
  calc _ ≤ |A.V x - A.V x'| + |interactionConvolution A μ x - interactionConvolution A μ x'| :=
        abs_add_le _ _
    _ ≤ |LV| * torusDist x x' + |LW| * torusDist x x' :=
        add_le_add ((hLV x x').trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0))
          (hc.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0))
    _ = _ := by ring

theorem lipschitz_gibbsDensity (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {B L : ℝ} (hB : ∀ x, |equilibriumPotential A μ x| ≤ B)
    (hL : TorusLipschitzWith L (equilibriumPotential A μ)) :
    TorusLipschitzWith (Real.exp (2 * B) * L) (gibbsDensity A μ) := by
  intro x x'
  obtain ⟨hZ1, -⟩ := gibbsPartition_bounds A μ hB
  have hZ : 0 < gibbsPartition A μ := (Real.exp_pos _).trans_le hZ1
  have hinv : 1 / gibbsPartition A μ ≤ Real.exp B := by
    rw [div_le_iff₀ hZ]
    calc (1 : ℝ) = Real.exp B * Real.exp (-B) := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp B * gibbsPartition A μ := mul_le_mul_of_nonneg_left hZ1 (Real.exp_pos _).le
  have h1 := abs_exp_sub_exp_le (a := -equilibriumPotential A μ x)
    (b := -equilibriumPotential A μ x') (B := B)
    (by linarith [(abs_le.mp (hB x)).1]) (by linarith [(abs_le.mp (hB x')).1])
  have h2 : |-equilibriumPotential A μ x - -equilibriumPotential A μ x'| ≤ L * torusDist x x' := by
    rw [show -equilibriumPotential A μ x - -equilibriumPotential A μ x' =
      -(equilibriumPotential A μ x - equilibriumPotential A μ x') by ring, abs_neg]
    exact hL x x'
  have e : gibbsDensity A μ x - gibbsDensity A μ x' =
      (Real.exp (-equilibriumPotential A μ x) - Real.exp (-equilibriumPotential A μ x')) *
        (1 / gibbsPartition A μ) := by
    unfold gibbsDensity; ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 1 / gibbsPartition A μ)]
  have h3 : |Real.exp (-equilibriumPotential A μ x) - Real.exp (-equilibriumPotential A μ x')| ≤
      Real.exp B * (L * torusDist x x') := h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  calc _ ≤ (Real.exp B * (L * torusDist x x')) * Real.exp B :=
        mul_le_mul h3 hinv (by positivity) ((abs_nonneg _).trans h3)
    _ = Real.exp (2 * B) * L * torusDist x x' := by
        have : Real.exp (2 * B) = Real.exp B * Real.exp B := by rw [← Real.exp_add]; ring_nf
        rw [this]; ring

theorem weak_gradient_log_gibbsDensity (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {G : Torus d → Tangent d}
    (h : IsWeakGradientLp ∞ (equilibriumPotential A μ) G) :
    IsWeakGradientLp ∞ (fun x => Real.log (gibbsDensity A μ x)) (fun x => -G x) := by
  have hZ := gibbsPartition_pos A μ
  have e : (fun x => Real.log (gibbsDensity A μ x)) =
      fun x => -equilibriumPotential A μ x - Real.log (gibbsPartition A μ) := by
    funext x
    unfold gibbsDensity
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  rw [e]
  exact isWeakGradientLp_top_neg_sub_const _ h


/-- **LIP017.** Free energy minimum and Gibbs identity. -/
theorem free_energy_minimum_and_gibbs_identity (A : InteractionData d) :
    (∃ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A) ∧
    (∃ r : ℝ, freeEnergyMinimum A = (r : EReal)) ∧
    (∀ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A →
      (μ : Measure (Torus d)) =
        (haar d).withDensity (fun x => ENNReal.ofReal (gibbsDensity A (μ : Measure (Torus d)) x)) ∧
      ∀ ν : ProbabilityMeasure (Torus d),
        relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤ →
          freeEnergy A ν - freeEnergy A μ =
            ((relativeEntropy (ν : Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) +
              (((1 / 2 : ℝ) * ∫ p, centeredKernel A (μ : Measure (Torus d)) p.1 p.2
                ∂((ν : Measure (Torus d)).prod (ν : Measure (Torus d))) : ℝ) : EReal)) ∧
    (LipschitzData A → ∃ c C L K : ℝ, 0 < c ∧ 0 ≤ K ∧
      ∀ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A →
        (∀ x, c ≤ gibbsDensity A (μ : Measure (Torus d)) x ∧
          gibbsDensity A (μ : Measure (Torus d)) x ≤ C) ∧
        TorusLipschitzWith L (gibbsDensity A (μ : Measure (Torus d))) ∧
        TorusLipschitzWith K (equilibriumPotential A (μ : Measure (Torus d))) ∧
        (∃ G : Torus d → Tangent d,
          IsWeakGradientLp ∞ (equilibriumPotential A (μ : Measure (Torus d))) G ∧
            ∀ᵐ x ∂haar d, ‖G x‖ ≤ K) ∧
        ∀ G : Torus d → Tangent d,
          IsWeakGradientLp ∞ (equilibriumPotential A (μ : Measure (Torus d))) G →
            IsWeakGradientLp ∞ (fun x => Real.log (gibbsDensity A (μ : Measure (Torus d)) x))
              (fun x => -G x)) := by
  have hmin : ∀ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A →
      ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν := fun μ hμ ν => by
    rw [hμ]; exact iInf_le _ ν
  refine ⟨freeEnergy_minimum_exists A, (freeEnergyMinimum_finite A).1, fun μ hμ => ?_, fun hA => ?_⟩
  · have hg := minimizer_eq_gibbs A μ (hmin μ hμ)
    exact ⟨hg, fun ν hν => free_energy_sub_eq A μ hg ν hν⟩
  · obtain ⟨B, hB0, hB⟩ := exists_potential_bound A
    obtain ⟨K0, hK0, hK⟩ := lipschitz_equilibriumPotential A hA
    refine ⟨Real.exp (-(2 * B)), Real.exp (2 * B), Real.exp (2 * B) * K0, K0,
      Real.exp_pos _, hK0, fun μ hμ => ?_⟩
    have hMp : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
    have hKμ := hK (μ : Measure (Torus d))
    refine ⟨fun x => gibbsDensity_bounds A (μ : Measure (Torus d)) (hB _) x,
      lipschitz_gibbsDensity A (μ : Measure (Torus d)) (hB _) hKμ, hKμ, ?_,
      fun G hG => weak_gradient_log_gibbsDensity A (μ : Measure (Torus d)) hG⟩
    obtain ⟨hG, hbd⟩ := exists_weak_gradient hK0 hKμ
    exact ⟨_, hG, hbd⟩

end DGPS.Lipschitz
