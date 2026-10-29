import LeanResearch.PeriodicAttractiveLogGas.MovingPoleIntegrability
import LeanResearch.PeriodicAttractiveLogGas.GreenRegularizationL1
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Actual moving-pole limits for the local Green exponential.

The capped theorem below proves joint L1 convergence from the earlier
three-halves bounds and the actual mollifier convergence. The weak identity
is obtained by passing the ordinary smooth integration-by-parts identity to
that limit. Local chart geometry remains explicit; no weak derivative or
common pointwise dominating function is assumed.

This is a partial development result. Full chart assembly and normalized
weak calculus for manuscript Lemma 3.5 remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.MovingPoleWeakLimit

open MovingPoleIntegrability GreenPointWeights MeshCells MeshAdjacentCells
open LabelOccupations ConditionalParameters

variable {ι : Type*} [Fintype ι]

/-- The literal proposed source gradient, including its negative sign. The
value on collisions uses the already fixed totalized Green representative. -/
def sourceGradient (y : ι → Torus) (w : ι → ℝ) (j : ι) (z : Torus) : PlanarSpace :=
  (-w j * torusWeight y w z) • greenGradient (z - y j)

theorem sourceGradient_eq_zero_of_coefficient_zero (y : ι → Torus) (w : ι → ℝ)
    (j : ι) (hj : w j = 0) (z : Torus) : sourceGradient y w j z = 0 := by
  simp [sourceGradient, hj]

theorem tendsto_weight {κ : Type*} {l : Filter κ} {ε : κ → ℝ}
    (hε : ∀ t, 0 < ε t) (hs : ∀ t, ε t ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) (y : ι → Torus) (w : ι → ℝ) (z : Torus)
    (hz : ∀ i, z - y i ≠ 0) :
    Tendsto (fun t ↦ regularizedTorusWeight y w (ε t) (hε t) z) l
      (𝓝 (torusWeight y w z)) := by
  apply Real.continuous_exp.continuousAt.tendsto.comp
  exact tendsto_finsetSum _ fun i _ ↦
    (tendsto_regularizedGreen hε hs ht (hz i)).const_mul (w i)

theorem tendsto_sourceGradient {κ : Type*} {l : Filter κ} {ε : κ → ℝ}
    (hε : ∀ t, 0 < ε t) (hs : ∀ t, ε t ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) (y : ι → Torus) (w : ι → ℝ) (j : ι) (z : Torus)
    (hz : ∀ i, z - y i ≠ 0) :
    Tendsto (fun t ↦ regularizedSourceGradient y w (ε t) (hε t) j z) l
      (𝓝 (sourceGradient y w j z)) := by
  have hg : Tendsto (fun t ↦ regularizedGreenGradient (ε t) (hε t) (z - y j)) l
      (𝓝 (greenGradient (z - y j))) :=
    tendsto_const_nhds.congr'
      (Filter.EventuallyEq.symm (eventually_regularizedGreenGradient_eq hε hs ht (hz j)))
  exact ((tendsto_weight hε hs ht y w z hz).const_mul (-w j)).smul hg

theorem measurable_joint_weight {A : Type*} [MeasurableSpace A]
    (X : A → ι → Torus) (hX : ∀ i, Measurable (fun a ↦ X a i)) (w : ι → ℝ) :
    Measurable (fun x : A × Torus ↦ torusWeight (X x.1) w x.2) := by
  apply Real.measurable_exp.comp
  apply Finset.measurable_sum
  intro i _
  exact (regularGreenRepresentative_measurable.comp
    (measurable_snd.sub ((hX i).comp measurable_fst))).const_mul (w i)

theorem measurable_joint_sourceGradient {A : Type*} [MeasurableSpace A]
    (X : A → ι → Torus) (hX : ∀ i, Measurable (fun a ↦ X a i)) (w : ι → ℝ) (j : ι) :
    Measurable (fun x : A × Torus ↦ sourceGradient (X x.1) w j x.2) :=
  ((measurable_joint_weight X hX w).const_mul (-w j)).smul
    (measurable_greenGradient.comp (measurable_snd.sub ((hX j).comp measurable_fst)))

/-- No separation of source poles from one another is required. Absolute
continuity of the integration-variable law removes every moving collision
diagonal in the actual product measure. -/
theorem ae_joint_sub_ne_zero {A : Type*} [MeasurableSpace A]
    {σ : Measure A} {μ : Measure Torus} [SFinite μ]
    (hμ : μ ≪ torusMeasure) (X : A → ι → Torus)
    (hX : ∀ i, Measurable (fun a ↦ X a i)) :
    ∀ᵐ x ∂σ.prod μ, ∀ i, x.2 - X x.1 i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have hm : MeasurableSet {x : A × Torus | x.2 ≠ X x.1 i} :=
    (measurableSet_eq_fun measurable_snd ((hX i).comp measurable_fst)).compl
  have hn : ∀ᵐ x ∂σ.prod μ, x.2 ≠ X x.1 i :=
    (Measure.ae_prod_iff_ae_ae hm).2 (ae_of_all _ fun a ↦
      (torusMeasure.ae_ne (X a i)).filter_mono hμ.ae_le)
  exact hn.mono fun x hx ↦ sub_ne_zero.mpr hx

theorem patchMeasure_absolutelyContinuous {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) : patchMeasure J hJ a b ≪ torusMeasure := by
  cases b with
  | cell => exact meshCellMeasure_absolutelyContinuous J hJ a
  | edge j => exact edgeCellMeasure_absolutelyContinuous J hJ hJ₂ a j

theorem uniformIntegrable_comp {T U A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] {μ : Measure A} {p : ℝ≥0∞} {f : T → A → E}
    (hf : UniformIntegrable f p μ) (k : U → T) : UniformIntegrable (f ∘ k) p μ := by
  refine ⟨hf.1.comp k, ?_⟩
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨C, fun u ↦ hC (k u)⟩

/-- The actual Vitali implication includes integrability of the limit, so
subsequent Bochner integrals do not rely on their totalized default value. -/
theorem integrable_and_tendsto_L1_of_uniformIntegrable
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} [IsFiniteMeasure μ] {f : ℕ → A → E} {g : A → E}
    (hf : UniformIntegrable f 1 μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  have hg := hf.integrable_of_ae_tendsto ht
  exact ⟨hg, tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp)
    (fun n ↦ hf.aestronglyMeasurable n) (memLp_one_iff_integrable.mpr hg) hf.1 ht⟩

/-- A reusable joint limit interface. Its uniform-integrability inputs are
discharged, with the actual exponent `51/32`, in `capped_joint_L1` below. -/
theorem joint_L1_of_uniformIntegrable {A : Type*} [MeasurableSpace A]
    {σ : Measure A} {μ : Measure Torus} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hμ : μ ≪ torusMeasure) (X : A → ι → Torus)
    (hX : ∀ i, Measurable (fun a ↦ X a i)) (w : ι → ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε atTop (𝓝 0))
    (hW : UniformIntegrable (fun n (x : A × Torus) ↦
      regularizedTorusWeight (X x.1) w (ε n) (hε n) x.2) 1 (σ.prod μ))
    (hG : UniformIntegrable (fun t : ℕ × ι ↦ fun x : A × Torus ↦
      regularizedSourceGradient (X x.1) w (ε t.1) (hε t.1) t.2 x.2) 1 (σ.prod μ)) :
    (Integrable (fun x : A × Torus ↦ torusWeight (X x.1) w x.2) (σ.prod μ) ∧
      Tendsto (fun n ↦ eLpNorm (fun x : A × Torus ↦
        regularizedTorusWeight (X x.1) w (ε n) (hε n) x.2 -
          torusWeight (X x.1) w x.2) 1 (σ.prod μ)) atTop (𝓝 0)) ∧
    ∀ j, Integrable (fun x : A × Torus ↦ sourceGradient (X x.1) w j x.2) (σ.prod μ) ∧
      Tendsto (fun n ↦ eLpNorm (fun x : A × Torus ↦
        regularizedSourceGradient (X x.1) w (ε n) (hε n) j x.2 -
          sourceGradient (X x.1) w j x.2) 1 (σ.prod μ)) atTop (𝓝 0) := by
  have hn := ae_joint_sub_ne_zero (σ := σ) hμ X hX
  constructor
  · apply integrable_and_tendsto_L1_of_uniformIntegrable hW
    exact hn.mono fun x hx ↦ tendsto_weight hε hs ht (X x.1) w x.2 hx
  · intro j
    apply integrable_and_tendsto_L1_of_uniformIntegrable
      (uniformIntegrable_comp hG (fun n ↦ (n, j)))
    exact hn.mono fun x hx ↦ tendsto_sourceGradient hε hs ht (X x.1) w j x.2 hx

/-- Actual joint L1 convergence on a capped product chart. The premises are
coefficient, occupation and closed-cell placement conditions, together with
measurability of the actual source placement. No integrability, L1 convergence,
derivative or dominating-function premise is included. This covers both
edge orientations, wrap-around cells, coincident sources and zero or deleted
coefficients. -/
theorem capped_joint_L1 {A : Type*} [MeasurableSpace A]
    {σ : Measure A} [IsProbabilityMeasure σ] (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : A → LabelVector J N)
    (hη : ∀ᵐ x ∂σ, OccupationCap (fixedDelta β₀ C₀ C₁) (η x))
    (I : Finset (Fin N)) (X : A → Configuration N)
    (hXm : ∀ i, Measurable (fun x ↦ X x i))
    (hX : ∀ᵐ x ∂σ, ∀ i ∈ I, X x i ∈ closure (meshCell J hJ (η x i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hs : ∀ n, ε n ≤ (1 / 16 : ℝ)) (ht : Tendsto ε atTop (𝓝 0)) :
    (Integrable (fun x : A × Torus ↦ torusWeight
      (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) x.2) (σ.prod (patchMeasure J hJ a b)) ∧
      Tendsto (fun n ↦ eLpNorm (fun x : A × Torus ↦ regularizedTorusWeight
        (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) (ε n) (hε n) x.2 -
          torusWeight (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) x.2)
        1 (σ.prod (patchMeasure J hJ a b))) atTop (𝓝 0)) ∧
    ∀ j : I, Integrable (fun x : A × Torus ↦ sourceGradient
      (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) j x.2) (σ.prod (patchMeasure J hJ a b)) ∧
      Tendsto (fun n ↦ eLpNorm (fun x : A × Torus ↦ regularizedSourceGradient
        (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) (ε n) (hε n) j x.2 -
          sourceGradient (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) j x.2)
        1 (σ.prod (patchMeasure J hJ a b))) atTop (𝓝 0) := by
  let := patchMeasure_probability J hJ a b
  have hJ₂ : 2 ≤ J := by omega
  obtain ⟨hW, hG⟩ := capped_joint_uniformIntegrable K hJ hN hβ hβ₀ hC₀ hmesh
    η hη I X hXm hX w hw₀ hw a b ε hε hs
  exact joint_L1_of_uniformIntegrable (patchMeasure_absolutelyContinuous hJ hJ₂ a b)
    (fun x (i : I) ↦ X x i) (fun i ↦ hXm i) (fun i : I ↦ w i) ε hε hs ht hW hG

/-- Bounded measurable tests preserve L1 convergence. This is proved from
the actual pointwise norm inequality and the Bochner integral continuity
theorem, rather than a distributional-convergence assumption. -/
theorem tendsto_integral_mul_of_L1 {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : ℕ → A → ℝ} {g : A → ℝ} (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (ht : Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0))
    (ψ : A → ℝ) (hψ : AEStronglyMeasurable ψ μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C) :
    Tendsto (fun n ↦ ∫ x, f n x * ψ x ∂μ) atTop (𝓝 (∫ x, g x * ψ x ∂μ)) := by
  have hm (n : ℕ) : Integrable (fun x ↦ f n x * ψ x) μ := (hf n).mul_bdd hψ hb
  have hmg : Integrable (fun x ↦ g x * ψ x) μ := hg.mul_bdd hψ hb
  apply tendsto_integral_of_L1' _ (Eventually.of_forall hm)
  have hbound (n : ℕ) : eLpNorm (fun x ↦ f n x * ψ x - g x * ψ x) 1 μ ≤
      ENNReal.ofReal C * eLpNorm (f n - g) 1 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm n |>.sub hmg |>.aestronglyMeasurable)
    filter_upwards [hb] with x hx
    change ‖f n x * ψ x - g x * ψ x‖ ≤ C * ‖f n x - g x‖
    rw [← sub_mul, norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) ht (Or.inr ENNReal.ofReal_ne_top)))
    (fun _ ↦ bot_le) hbound

theorem integrable_inner_const {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {G : A → PlanarSpace} (hG : Integrable G μ) (v : PlanarSpace) :
    Integrable (fun x ↦ inner ℝ (G x) v) μ := by
  refine (hG.norm.mul_const ‖v‖).mono'
    (hG.aestronglyMeasurable.inner aestronglyMeasurable_const) ?_
  exact ae_of_all _ fun x ↦ norm_inner_le_norm (G x) v

theorem tendsto_integral_inner_mul_of_L1 {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {F : ℕ → A → PlanarSpace} {G : A → PlanarSpace}
    (hF : ∀ n, Integrable (F n) μ) (hG : Integrable G μ)
    (ht : Tendsto (fun n ↦ eLpNorm (F n - G) 1 μ) atTop (𝓝 0))
    (v : PlanarSpace) (ψ : A → ℝ) (hψ : AEStronglyMeasurable ψ μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C) :
    Tendsto (fun n ↦ ∫ x, inner ℝ (F n x) v * ψ x ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (G x) v * ψ x ∂μ)) := by
  have hi (n : ℕ) := integrable_inner_const (hF n) v
  have hig := integrable_inner_const hG v
  apply tendsto_integral_mul_of_L1 hi hig ?_ ψ hψ hb
  have hbound (n : ℕ) : eLpNorm (fun x ↦ inner ℝ (F n x) v - inner ℝ (G x) v) 1 μ ≤
      ENNReal.ofReal ‖v‖ * eLpNorm (F n - G) 1 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hi n).sub hig).aestronglyMeasurable
    filter_upwards with x
    change ‖inner ℝ (F n x) v - inner ℝ (G x) v‖ ≤ ‖v‖ * ‖F n x - G x‖
    rw [← inner_sub_left, mul_comm ‖v‖]
    exact norm_inner_le_norm _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖v‖) ht
        (Or.inr ENNReal.ofReal_ne_top)))
    (fun _ ↦ bot_le) hbound

section MovingOneSource

variable [DecidableEq ι]

def movingSources (y : ι → Torus) (j : ι) (x : PlanarSpace) : ι → Torus :=
  Function.update y j (torusQuotient x)

def movingWeight (y : ι → Torus) (w : ι → ℝ) (j : ι) (p : PlanarSpace × Torus) : ℝ :=
  torusWeight (movingSources y j p.1) w p.2

def movingGradient (y : ι → Torus) (w : ι → ℝ) (j : ι) (p : PlanarSpace × Torus) :
    PlanarSpace := sourceGradient (movingSources y j p.1) w j p.2

def movingRegularizedWeight (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (p : PlanarSpace × Torus) : ℝ :=
  regularizedTorusWeight (movingSources y j p.1) w ε hε p.2

def movingRegularizedGradient (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (p : PlanarSpace × Torus) : PlanarSpace :=
  regularizedSourceGradient (movingSources y j p.1) w ε hε j p.2

omit [Fintype ι] in
theorem measurable_movingSources (y : ι → Torus) (j i : ι) :
    Measurable (fun x ↦ movingSources y j x i) := by
  by_cases hi : i = j
  · subst i
    simpa [movingSources] using isOpenQuotientMap_torusQuotient.continuous.measurable
  · simp [movingSources, Function.update_of_ne hi]

theorem continuous_movingRegularizedWeight (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    Continuous (fun x ↦ movingRegularizedWeight y w j ε hε (x, z)) := by
  have hq : Continuous torusQuotient := isOpenQuotientMap_torusQuotient.continuous
  have hg : Continuous (fun x : PlanarSpace ↦ regularizedGreen ε hε (z - torusQuotient x)) :=
    (continuous_regularizedGreen ε hε).comp (continuous_const.sub hq)
  have h : Continuous (fun x : PlanarSpace ↦ Real.exp
      ((∑ i ∈ Finset.univ.erase j, w i * regularizedGreen ε hε (z - y i)) +
        w j * regularizedGreen ε hε (z - torusQuotient x))) :=
    Real.continuous_exp.comp (continuous_const.add (continuous_const.mul hg))
  simpa only [movingRegularizedWeight, movingSources, regularizedTorusWeight_update] using h

theorem continuous_movingRegularizedGradient (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    Continuous (fun x ↦ movingRegularizedGradient y w j ε hε (x, z)) := by
  have hq : Continuous torusQuotient := isOpenQuotientMap_torusQuotient.continuous
  have h : Continuous (fun x : PlanarSpace ↦
      (-w j * movingRegularizedWeight y w j ε hε (x, z)) •
        regularizedGreenGradient ε hε (z - torusQuotient x)) :=
    (continuous_const.mul (continuous_movingRegularizedWeight y w j ε hε z)).smul
      ((continuous_regularizedGreenGradient ε hε hs).comp (continuous_const.sub hq))
  simpa only [movingRegularizedGradient, movingRegularizedWeight,
    regularizedSourceGradient, movingSources, Function.update_self] using h

theorem hasFDerivAt_movingRegularizedWeight (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus) (x : PlanarSpace) :
    HasFDerivAt (fun X ↦ movingRegularizedWeight y w j ε hε (X, z))
      ((-w j * movingRegularizedWeight y w j ε hε (x, z)) •
        regularizedGreenDifferential ε hε (z - torusQuotient x)) x := by
  simpa only [movingRegularizedWeight, movingSources, regularizedTorusWeight_update] using
    hasFDerivAt_single_source ε hε hs z
      (∑ i ∈ Finset.univ.erase j, w i * regularizedGreen ε hε (z - y i)) (w j) x

theorem fderiv_movingRegularizedWeight_apply (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus) (x v : PlanarSpace) :
    fderiv ℝ (fun X ↦ movingRegularizedWeight y w j ε hε (X, z)) x v =
      inner ℝ (movingRegularizedGradient y w j ε hε (x, z)) v := by
  rw [(hasFDerivAt_movingRegularizedWeight y w j ε hε hs z x).fderiv]
  simp only [movingRegularizedGradient, regularizedSourceGradient, movingRegularizedWeight,
    movingSources, Function.update_self, smul_apply,
    real_inner_smul_left, regularizedGreenGradient_inner, smul_eq_mul]

/-- Ordinary Euclidean integration by parts for the actual smooth Green
weight, before any singular limit. The test may cross every source pole. -/
theorem smooth_source_integral_identity (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus)
    {φ : PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (v : PlanarSpace) :
    (∫ x, movingRegularizedWeight y w j ε hε (x, z) * fderiv ℝ φ x v) =
      -(∫ x, inner ℝ (movingRegularizedGradient y w j ε hε (x, z)) v * φ x) := by
  have hW := continuous_movingRegularizedWeight y w j ε hε z
  have hG : Continuous (fun x ↦ inner ℝ (movingRegularizedGradient y w j ε hε (x, z)) v) :=
    (continuous_movingRegularizedGradient y w j ε hε hs z).inner continuous_const
  have hD : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc := hc.fderiv_apply ℝ v
  have hWG : Integrable (fun x ↦
      fderiv ℝ (fun X ↦ movingRegularizedWeight y w j ε hε (X, z)) x v * φ x) volume := by
    simpa only [fderiv_movingRegularizedWeight_apply y w j ε hε hs] using!
      (hG.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hWD : Integrable (fun x ↦ movingRegularizedWeight y w j ε hε (x, z) *
      fderiv ℝ φ x v) volume :=
    (hW.mul hD).integrable_of_hasCompactSupport hDc.mul_left
  have hWφ : Integrable (fun x ↦ movingRegularizedWeight y w j ε hε (x, z) * φ x) volume :=
    (hW.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  simpa only [fderiv_movingRegularizedWeight_apply y w j ε hε hs] using
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hWG hWD hWφ
      (fun x _ ↦ (hasFDerivAt_movingRegularizedWeight y w j ε hε hs z x).differentiableAt)
      (fun x _ ↦ hφ.differentiable one_ne_zero x)

/-- Restriction to a physical chart introduces no boundary term for tests
supported in that chart. The coefficient is the literal measure multiplier. -/
theorem smooth_source_setIntegral_identity (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus)
    (S : Set PlanarSpace) (c : ℝ≥0∞)
    {φ : PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hS : tsupport φ ⊆ S) (v : PlanarSpace) :
    (∫ x, movingRegularizedWeight y w j ε hε (x, z) * fderiv ℝ φ x v
      ∂c • volume.restrict S) =
      -(∫ x, inner ℝ (movingRegularizedGradient y w j ε hε (x, z)) v * φ x
        ∂c • volume.restrict S) := by
  have hL : (∫ x in S, movingRegularizedWeight y w j ε hε (x, z) * fderiv ℝ φ x v) =
      ∫ x, movingRegularizedWeight y w j ε hε (x, z) * fderiv ℝ φ x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport (fun x ↦ fderiv ℝ φ x v) :=
      fun ht ↦ hx (hS (tsupport_fderiv_apply_subset ℝ v ht))
    simp [image_eq_zero_of_notMem_tsupport hn]
  have hR : (∫ x in S, inner ℝ (movingRegularizedGradient y w j ε hε (x, z)) v * φ x) =
      ∫ x, inner ℝ (movingRegularizedGradient y w j ε hε (x, z)) v * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hS ht))]
  rw [integral_smul_measure, integral_smul_measure, hL, hR,
    smooth_source_integral_identity y w j ε hε hs z hφ hc v, smul_neg]

theorem exists_test_bound {φ : PlanarSpace → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖φ x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (hc.isCompact_range hφ).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun x ↦ hb (φ x) (mem_range_self x)⟩

/-- Fubini applied to the ordinary regularized identity. Integrability of
the two actual fields is the only analytic input here; all derivative and
test-support statements are proved above. -/
theorem smooth_source_joint_identity (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (S : Set PlanarSpace) (c : ℝ≥0∞) {μ : Measure Torus} [IsFiniteMeasure μ]
    [IsFiniteMeasure (c • (volume : Measure PlanarSpace).restrict S)]
    (hW : Integrable (movingRegularizedWeight y w j ε hε)
      ((c • volume.restrict S).prod μ))
    (hG : Integrable (movingRegularizedGradient y w j ε hε)
      ((c • volume.restrict S).prod μ))
    {φ : PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hS : tsupport φ ⊆ S) (v : PlanarSpace)
    (ψ : Torus → ℝ) (hψ : Measurable ψ) {H : ℝ} (hH : ∀ z, ‖ψ z‖ ≤ H) :
    (∫ p, movingRegularizedWeight y w j ε hε p * (fderiv ℝ φ p.1 v * ψ p.2)
      ∂(c • volume.restrict S).prod μ) =
      -(∫ p, inner ℝ (movingRegularizedGradient y w j ε hε p) v * (φ p.1 * ψ p.2)
        ∂(c • volume.restrict S).prod μ) := by
  obtain ⟨C, hC, hCφ⟩ := exists_test_bound hφ.continuous hc
  have hD : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨D, hDpos, hDφ⟩ := exists_test_bound hD (hc.fderiv_apply ℝ v)
  have hL : Integrable (fun p ↦ movingRegularizedWeight y w j ε hε p *
      (fderiv ℝ φ p.1 v * ψ p.2)) ((c • volume.restrict S).prod μ) := hW.mul_bdd
    ((hD.measurable.comp measurable_fst).mul (hψ.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ show ‖fderiv ℝ φ p.1 v * ψ p.2‖ ≤ D * H from
      (norm_mul _ _).trans_le (mul_le_mul (hDφ p.1) (hH p.2) (norm_nonneg _) hDpos.le))
  have hR : Integrable (fun p ↦ inner ℝ (movingRegularizedGradient y w j ε hε p) v *
      (φ p.1 * ψ p.2)) ((c • volume.restrict S).prod μ) := (integrable_inner_const hG v).mul_bdd
    ((hφ.continuous.measurable.comp measurable_fst).mul
      (hψ.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ show ‖φ p.1 * ψ p.2‖ ≤ C * H from
      (norm_mul _ _).trans_le (mul_le_mul (hCφ p.1) (hH p.2) (norm_nonneg _) hC.le))
  rw [integral_prod_symm _ hL, integral_prod_symm _ hR, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with z
  simpa only [← mul_assoc, integral_mul_const, neg_mul] using
    congrArg (fun r : ℝ ↦ r * ψ z)
      (smooth_source_setIntegral_identity y w j ε hε hs z S c hφ hc hS v)

/-- The limit passage for the actual one-source Green exponential. The L1
premises are an explicit interface to `capped_joint_L1`, not a presumed weak
derivative. The following capped wrapper discharges that interface. -/
theorem source_joint_identity_of_L1 (y : ι → Torus) (w : ι → ℝ) (j : ι)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ (1 / 16 : ℝ))
    (S : Set PlanarSpace) (c : ℝ≥0∞) {μ : Measure Torus} [IsFiniteMeasure μ]
    [IsFiniteMeasure (c • (volume : Measure PlanarSpace).restrict S)]
    (hW : ∀ n, Integrable (movingRegularizedWeight y w j (ε n) (hε n))
      ((c • volume.restrict S).prod μ))
    (hG : ∀ n, Integrable (movingRegularizedGradient y w j (ε n) (hε n))
      ((c • volume.restrict S).prod μ))
    (hW₀ : Integrable (movingWeight y w j) ((c • volume.restrict S).prod μ))
    (hG₀ : Integrable (movingGradient y w j) ((c • volume.restrict S).prod μ))
    (htW : Tendsto (fun n ↦ eLpNorm
      (movingRegularizedWeight y w j (ε n) (hε n) - movingWeight y w j)
        1 ((c • volume.restrict S).prod μ)) atTop (𝓝 0))
    (htG : Tendsto (fun n ↦ eLpNorm
      (movingRegularizedGradient y w j (ε n) (hε n) - movingGradient y w j)
        1 ((c • volume.restrict S).prod μ)) atTop (𝓝 0))
    {φ : PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hS : tsupport φ ⊆ S) (v : PlanarSpace)
    (ψ : Torus → ℝ) (hψ : Measurable ψ) {H : ℝ} (hH : ∀ z, ‖ψ z‖ ≤ H) :
    (∫ p, movingWeight y w j p * (fderiv ℝ φ p.1 v * ψ p.2)
      ∂(c • volume.restrict S).prod μ) =
      -(∫ p, inner ℝ (movingGradient y w j p) v * (φ p.1 * ψ p.2)
        ∂(c • volume.restrict S).prod μ) := by
  obtain ⟨C, hC, hCφ⟩ := exists_test_bound hφ.continuous hc
  have hD : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨D, hDpos, hDφ⟩ := exists_test_bound hD (hc.fderiv_apply ℝ v)
  have hL := tendsto_integral_mul_of_L1 hW hW₀ htW (fun p ↦ fderiv ℝ φ p.1 v * ψ p.2)
    ((hD.measurable.comp measurable_fst).mul (hψ.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ show ‖fderiv ℝ φ p.1 v * ψ p.2‖ ≤ D * H from
      (norm_mul _ _).trans_le (mul_le_mul (hDφ p.1) (hH p.2) (norm_nonneg _) hDpos.le))
  have hR := tendsto_integral_inner_mul_of_L1 hG hG₀ htG v (fun p ↦ φ p.1 * ψ p.2)
    ((hφ.continuous.measurable.comp measurable_fst).mul
      (hψ.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ show ‖φ p.1 * ψ p.2‖ ≤ C * H from
      (norm_mul _ _).trans_le (mul_le_mul (hCφ p.1) (hH p.2) (norm_nonneg _) hC.le))
  have he : ∀ᶠ n in atTop,
      (∫ p, movingRegularizedWeight y w j (ε n) (hε n) p * (fderiv ℝ φ p.1 v * ψ p.2)
        ∂(c • volume.restrict S).prod μ) =
      -(∫ p, inner ℝ (movingRegularizedGradient y w j (ε n) (hε n) p) v * (φ p.1 * ψ p.2)
        ∂(c • volume.restrict S).prod μ) :=
    Eventually.of_forall fun n ↦ smooth_source_joint_identity y w j (ε n) (hε n) (hs n)
      S c (hW n) (hG n) hφ hc hS v ψ hψ hH
  exact tendsto_nhds_unique (hL.congr' he) hR.neg

omit [Fintype ι] in
theorem movingSources_subtype (I : Finset ι) (y : ι → Torus) (j : I) (x : PlanarSpace) :
    (fun i : I ↦ movingSources y (j : ι) x i) =
      movingSources (fun i : I ↦ y i) j x := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [movingSources]
  · have hv : (i : ι) ≠ (j : ι) := fun h ↦ hij (Subtype.ext h)
    simp [movingSources, Function.update_of_ne hij, Function.update_of_ne hv]

end MovingOneSource

/-- A complete capped one-source weak identity on a literal finite-volume
physical source chart. The source chart measure is exactly
`c • volume.restrict S`, assumed normalized to mass one. The test is compactly
supported inside `S`; the integration-variable law is exactly the normalized
mesh-cell or adjacent-union law. Both the L1 and smooth derivative premises
of the intermediate lemmas are discharged here.

The arbitrary bounded measurable `ψ` permits tensor tests in the joint
variables and, in particular, unnormalized conditional numerators. No source
separation, positive individual coefficient, or test vanishing at a collision
is imposed. Full multi-source chart assembly and weak log/quotient calculus
for normalized conditionals are separate obligations. -/
theorem capped_single_source_joint_identity
    (K : KernelBounds) {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (S : Set PlanarSpace) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure PlanarSpace).restrict S)]
    (η : PlanarSpace → LabelVector J N)
    (hη : ∀ᵐ x ∂c • volume.restrict S, OccupationCap (fixedDelta β₀ C₀ C₁) (η x))
    (I : Finset (Fin N)) (y : Configuration N) (j : I)
    (hX : ∀ᵐ x ∂c • volume.restrict S, ∀ i ∈ I,
      movingSources y (j : Fin N) x i ∈ closure (meshCell J hJ (η x i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hs : ∀ n, ε n ≤ (1 / 16 : ℝ)) (ht : Tendsto ε atTop (𝓝 0))
    {φ : PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hS : tsupport φ ⊆ S) (v : PlanarSpace)
    (ψ : Torus → ℝ) (hψ : Measurable ψ) {H : ℝ} (hH : ∀ z, ‖ψ z‖ ≤ H) :
    (∫ p, movingWeight (fun i : I ↦ y i) (fun i : I ↦ w i) j p *
      (fderiv ℝ φ p.1 v * ψ p.2) ∂(c • volume.restrict S).prod (patchMeasure J hJ a b)) =
      -(∫ p, inner ℝ (movingGradient (fun i : I ↦ y i) (fun i : I ↦ w i) j p) v *
        (φ p.1 * ψ p.2) ∂(c • volume.restrict S).prod (patchMeasure J hJ a b)) := by
  classical
  let := patchMeasure_probability J hJ a b
  have hJ₂ : 2 ≤ J := by omega
  obtain ⟨hW, hG⟩ := capped_joint_uniformIntegrable K hJ hN hβ hβ₀ hC₀ hmesh
    η hη I (movingSources y (j : Fin N)) (measurable_movingSources y (j : Fin N))
    hX w hw₀ hw a b ε hε hs
  have hW' : UniformIntegrable
      (fun n ↦ movingRegularizedWeight (fun i : I ↦ y i) (fun i : I ↦ w i) j (ε n) (hε n))
      1 ((c • volume.restrict S).prod (patchMeasure J hJ a b)) := by
    change UniformIntegrable (fun n (p : PlanarSpace × Torus) ↦ regularizedTorusWeight
      (movingSources (fun i : I ↦ y i) j p.1) (fun i : I ↦ w i) (ε n) (hε n) p.2)
      1 ((c • volume.restrict S).prod (patchMeasure J hJ a b))
    simpa only [movingSources_subtype] using hW
  have hG' : UniformIntegrable
      (fun t : ℕ × I ↦ fun p : PlanarSpace × Torus ↦ regularizedSourceGradient
        (movingSources (fun i : I ↦ y i) j p.1) (fun i : I ↦ w i)
          (ε t.1) (hε t.1) t.2 p.2)
      1 ((c • volume.restrict S).prod (patchMeasure J hJ a b)) := by
    simpa only [movingSources_subtype] using hG
  obtain ⟨hWL, hGL⟩ := joint_L1_of_uniformIntegrable
    (patchMeasure_absolutelyContinuous hJ hJ₂ a b)
    (movingSources (fun i : I ↦ y i) j) (measurable_movingSources (fun i : I ↦ y i) j)
    (fun i : I ↦ w i) ε hε hs ht hW' hG'
  exact source_joint_identity_of_L1 (fun i : I ↦ y i) (fun i : I ↦ w i) j ε hε hs S c
    (fun n ↦ memLp_one_iff_integrable.mp (hW'.memLp n))
    (fun n ↦ memLp_one_iff_integrable.mp (hG'.memLp (n, j)))
    hWL.1 (hGL j).1 hWL.2 (hGL j).2 hφ hc hS v ψ hψ hH

end PeriodicAttractiveLogGas.MovingPoleWeakLimit
