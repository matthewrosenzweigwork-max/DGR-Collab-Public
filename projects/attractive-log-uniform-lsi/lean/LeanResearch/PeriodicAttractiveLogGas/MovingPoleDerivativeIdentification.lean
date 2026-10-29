import LeanResearch.PeriodicAttractiveLogGas.MovingPoleNormalized
import LeanResearch.PeriodicAttractiveLogGas.WeakChartDerivative

/-! Source-only candidate for the physical source-block formulas and their
ordinary and weighted almost-everywhere interpretation in Lemma 3.5.

The full gradients use the genuine Euclidean source coordinates. Their
blocks are proved to be the corresponding ordinary planar derivatives.
Projection through the raw Haar vector integrals produces the exact
normalizer and covariance expressions. All integrals are proved integrable
at every capped fixed placement, including coincidences and zero weights.
The actual weak and Lipschitz results then give ordinary a.e. derivatives,
with actual with-density chart laws inheriting them by absolute continuity.
The author has not executed Lean on this candidate. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace BigOperators

namespace PeriodicAttractiveLogGas.MovingPoleDerivativeIdentification

open WeakChartCalculus WeakChartDerivative MovingPoleNumerators MovingPoleIntegrability
open MovingPoleWeakLimit
open MovingPoleCharts MovingPoleCalculus MovingPoleNormalized GreenPointWeights
open MeshCells MeshAdjacentCells LabelOccupations ConditionalParameters

variable {ι : Type*} [Fintype ι]

/-- Exact coordinate description of the Euclidean block projection. -/
theorem sourceProjection_single [DecidableEq ι] (j i : ι) (k : Fin 2) :
    sourceProjection j (EuclideanSpace.single (i, k) (1 : ℝ)) =
      if i = j then EuclideanSpace.single k 1 else 0 := by
  classical
  by_cases h : i = j
  · subst i
    ext l
    simp [sourceProjection_apply, PiLp.single_apply]
  · ext l
    simp [sourceProjection_apply, h, Ne.symm h]

theorem sourceProjection_adjoint_apply [DecidableEq ι] (j i : ι) (z : PlanarSpace) (k : Fin 2) :
    (sourceProjection j).adjoint z (i, k) = if i = j then z k else 0 := by
  classical
  calc
    (sourceProjection j).adjoint z (i, k) =
        inner ℝ (EuclideanSpace.single (i, k) (1 : ℝ)) ((sourceProjection j).adjoint z) := by
      simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
    _ = inner ℝ (sourceProjection j (EuclideanSpace.single (i, k) (1 : ℝ))) z :=
      (sourceProjection j).adjoint_inner_right _ _
    _ = if i = j then z k else 0 := by
      rw [sourceProjection_single]
      split_ifs <;> simp [EuclideanSpace.inner_single_left]

theorem sourceProjection_adjoint [DecidableEq ι] (i j : ι) (z : PlanarSpace) :
    sourceProjection i ((sourceProjection j).adjoint z) = if i = j then z else 0 := by
  classical
  ext k
  rw [sourceProjection_apply, sourceProjection_adjoint_apply]
  by_cases h : i = j <;> simp [h]

/-- There is no dimension or norm-comparison factor in extraction of a
source block from the full physical Riesz vector. -/
theorem sourceProjection_fullGradient (j : ι) (G : ι → PlanarSpace) :
    sourceProjection j (fullGradient G) = G j := by
  classical
  simp only [fullGradient, map_sum, sourceProjection_adjoint]
  simp

def sourceVariation (j : ι) (X : SourceSpace ι) (z : PlanarSpace) : SourceSpace ι :=
  X + (sourceProjection j).adjoint (z - sourceProjection j X)

theorem sourceVariation_apply [DecidableEq ι] (j i : ι)
    (X : SourceSpace ι) (z : PlanarSpace) (k : Fin 2) :
    sourceVariation j X z (i, k) = if i = j then z k else X (i, k) := by
  classical
  change X (i, k) + (sourceProjection j).adjoint (z - sourceProjection j X) (i, k) = _
  rw [sourceProjection_adjoint_apply]
  by_cases h : i = j
  · subst i
    simp only [ite_true]
    change X (j, k) + (z k - X (j, k)) = z k
    ring
  · simp [h]

@[simp] theorem sourceVariation_self (j : ι) (X : SourceSpace ι) :
    sourceVariation j X (sourceProjection j X) = X := by
  simp [sourceVariation]

theorem hasFDerivAt_sourceVariation (j : ι) (X : SourceSpace ι) (z : PlanarSpace) :
    HasFDerivAt (sourceVariation j X) (sourceProjection j).adjoint z := by
  have h := (sourceProjection j).adjoint.hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (sourceProjection j X))
  simpa only [sourceVariation, Function.comp_def, id_eq, ContinuousLinearMap.comp_id]
    using! h.const_add X

/-- The projected full Riesz field is the genuine ordinary derivative in
one planar source variable with all other coordinates fixed. -/
theorem hasFDerivAt_sourceBlock {f : SourceSpace ι → ℝ} {X G : SourceSpace ι}
    (hf : HasFDerivAt f (InnerProductSpace.toDual ℝ (SourceSpace ι) G) X) (j : ι) :
    HasFDerivAt (fun z ↦ f (sourceVariation j X z))
      (InnerProductSpace.toDual ℝ PlanarSpace (sourceProjection j G)) (sourceProjection j X) := by
  have hf' : HasFDerivAt f (InnerProductSpace.toDual ℝ (SourceSpace ι) G)
      (sourceVariation j X (sourceProjection j X)) := by simpa only [sourceVariation_self] using hf
  have h := hf'.comp (sourceProjection j X) (hasFDerivAt_sourceVariation j X (sourceProjection j X))
  have he : (InnerProductSpace.toDual ℝ (SourceSpace ι) G).comp (sourceProjection j).adjoint =
      InnerProductSpace.toDual ℝ PlanarSpace (sourceProjection j G) := by
    ext v
    exact (sourceProjection j).adjoint_inner_right G v
  simpa only [sourceVariation_self, he, Function.comp_def] using! h

def factorBlock (F : SourceSpace ι → Torus → ℝ) (j : ι) (X : SourceSpace ι) (z : Torus) :
    PlanarSpace := sourceProjection j (torusFactorGradient F X z)

theorem factorBlock_eq_ordinaryGradient {F : SourceSpace ι → Torus → ℝ}
    {X : SourceSpace ι} {z : Torus} (hF : DifferentiableAt ℝ (fun Y ↦ F Y z) X) (j : ι) :
    factorBlock F j X z = (InnerProductSpace.toDual ℝ PlanarSpace).symm
      (fderiv ℝ (fun u ↦ F (sourceVariation j X u) z) (sourceProjection j X)) := by
  have h := hasFDerivAt_sourceBlock (hasFDerivAt_ordinaryGradient hF) j
  rw [h.fderiv]
  exact ((InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _).symm

theorem torusFactorGradient_one (X : SourceSpace ι) (z : Torus) :
    torusFactorGradient (fun _ _ ↦ (1 : ℝ)) X z = 0 := by
  simp [torusFactorGradient]

theorem sourceProjection_torusProductGradient (w : ι → ℝ)
    (F : SourceSpace ι → Torus → ℝ) (j : ι) (X : SourceSpace ι) (z : Torus) :
    sourceProjection j (torusProductGradient w F X z) =
      torusWeight (sources X) w z • factorBlock F j X z +
        F X z • sourceGradient (sources X) w j z := by
  simp only [torusProductGradient, map_add, map_smul, sourceProjection_fullGradient, factorBlock]

/-- Undoing normalization preserves actual integrability because the raw
normalizer is strictly positive and finite as a real integral. -/
theorem integrable_weight_smul_of_pointLaw {μ : Measure Torus}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (y : ι → Torus) (w : ι → ℝ) (hz : 0 < ∫ z, torusWeight y w z ∂μ)
    {H : Torus → E} (hH : Integrable H (pointLaw μ y w)) :
    Integrable (fun z ↦ torusWeight y w z • H z) μ := by
  have hi0 : Integrable (fun z ↦ pointDensity μ y w z • H z) μ :=
    (pointLaw_integrable_iff y w hz H).mp hH
  have hi := hi0.smul (∫ z, torusWeight y w z ∂μ)
  apply hi.congr
  exact ae_of_all _ fun z ↦ by
    change (∫ z, torusWeight y w z ∂μ) • (pointDensity μ y w z • H z) = _
    rw [smul_smul, pointDensity]
    congr 1
    field_simp [hz.ne']

theorem integrable_sourceGradient_of_pointLaw {μ : Measure Torus}
    (y : ι → Torus) (w : ι → ℝ) (hz : 0 < ∫ z, torusWeight y w z ∂μ) (j : ι)
    (hG : Integrable (fun z ↦ greenGradient (z - y j)) (pointLaw μ y w)) :
    Integrable (sourceGradient y w j) μ := by
  have hi : Integrable (fun z ↦ torusWeight y w z • greenGradient (z - y j)) μ :=
    integrable_weight_smul_of_pointLaw y w hz hG
  have hi' : Integrable (fun z ↦ -w j • (torusWeight y w z •
      greenGradient (z - y j))) μ := hi.smul (-w j)
  apply hi'.congr
  exact ae_of_all _ fun z ↦ by
    change (-w j) • (torusWeight y w z • greenGradient (z - y j)) =
      (-w j * torusWeight y w z) • greenGradient (z - y j)
    exact (mul_smul (-w j) (torusWeight y w z) (greenGradient (z - y j))).symm

theorem integrable_factor_sourceGradient_of_pointLaw {μ : Measure Torus}
    (y : ι → Torus) (w : ι → ℝ) (hz : 0 < ∫ z, torusWeight y w z ∂μ)
    (j : ι) (f : Torus → ℝ)
    (hG : Integrable (fun z ↦ f z • greenGradient (z - y j)) (pointLaw μ y w)) :
    Integrable (fun z ↦ f z • sourceGradient y w j z) μ := by
  have hi0 : Integrable (fun z ↦ torusWeight y w z • (f z • greenGradient (z - y j))) μ :=
    integrable_weight_smul_of_pointLaw y w hz hG
  have hi := hi0.smul (-w j)
  apply hi.congr
  exact ae_of_all _ fun z ↦ by
    simp only [sourceGradient, Pi.smul_apply, smul_smul]
    congr 1
    ring

theorem rawNormalizerGradient_block (w : ι → ℝ) {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) (X : SourceSpace ι)
    (hG : ∀ j, Integrable (sourceGradient (sources X) w j)
      (torusMeasure.restrict (patchDomain J hJ a b))) (j : ι) :
    sourceProjection j (rawNormalizerGradient w J hJ a b X) =
      ∫ z in patchDomain J hJ a b, sourceGradient (sources X) w j z ∂torusMeasure := by
  have he : torusProductGradient w (fun _ _ ↦ (1 : ℝ)) X =
      fun z ↦ fullGradient (fun i ↦ sourceGradient (sources X) w i z) := by
    funext z
    simp only [torusProductGradient, torusFactorGradient_one, smul_zero, one_smul, zero_add]
  rw [rawNormalizerGradient, rawNumeratorGradient, he, integral_fullGradient hG,
    sourceProjection_fullGradient]

theorem rawNumeratorGradient_block (w : ι → ℝ) {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι)
    (hD : Integrable (fun z ↦ torusWeight (sources X) w z • torusFactorGradient F X z)
      (torusMeasure.restrict (patchDomain J hJ a b)))
    (hG : ∀ j, Integrable (fun z ↦ F X z • sourceGradient (sources X) w j z)
      (torusMeasure.restrict (patchDomain J hJ a b))) (j : ι) :
    sourceProjection j (rawNumeratorGradient w J hJ a b F X) =
      (∫ z in patchDomain J hJ a b, torusWeight (sources X) w z • factorBlock F j X z ∂torusMeasure) +
      ∫ z in patchDomain J hJ a b, F X z • sourceGradient (sources X) w j z ∂torusMeasure := by
  have hP : Integrable (torusProductGradient w F X)
      (torusMeasure.restrict (patchDomain J hJ a b)) :=
    hD.add (integrable_fullGradient hG)
  rw [rawNumeratorGradient, ← (sourceProjection j).integral_comp_comm hP]
  simp_rw [sourceProjection_torusProductGradient]
  apply integral_add
  · simpa only [map_smul, factorBlock] using (sourceProjection j).integrable_comp hD
  · exact hG j

def conditionalMean (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι) : ℝ :=
  ∫ z, F X z ∂pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w

def logBlock (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (j : ι) (X : SourceSpace ι) : PlanarSpace :=
  (-w j) • ∫ z, greenGradient (z - sources X j)
    ∂pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w

def meanBlock (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (j : ι) (X : SourceSpace ι) : PlanarSpace :=
  (∫ z, factorBlock F j X z ∂pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w) -
    w j • vectorCovariance (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w)
      (F X) (fun z ↦ greenGradient (z - sources X j))

/-- Pointwise identities of the actual full weak fields with the physical
source formulas. The integrability inputs are discharged by the capped
theorem below, even for a coefficient which is exactly zero. -/
theorem rawGradient_blocks (w : ι → ℝ) {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι)
    (hz : 0 < rawNormalizer w J hJ a b X)
    (hD : Integrable (torusFactorGradient F X)
      (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w))
    (hG : ∀ j, Integrable (fun z ↦ greenGradient (z - sources X j))
      (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w) ∧
      Integrable (fun z ↦ F X z • greenGradient (z - sources X j))
        (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w)) :
    ∀ j, sourceProjection j (rawLogGradient w J hJ a b X) = logBlock w J hJ a b j X ∧
      sourceProjection j (rawMeanGradient w J hJ a b F X) = meanBlock w J hJ a b F j X := by
  have hz' : 0 < ∫ z in patchDomain J hJ a b, torusWeight (sources X) w z ∂torusMeasure := by
    simpa only [rawNormalizer_eq_integral] using hz
  have hg (j : ι) := integrable_sourceGradient_of_pointLaw (sources X) w hz' j (hG j).1
  have hfg (j : ι) := integrable_factor_sourceGradient_of_pointLaw (sources X) w hz' j (F X) (hG j).2
  have hd := integrable_weight_smul_of_pointLaw (sources X) w hz' hD
  intro j
  constructor
  · rw [rawLogGradient, logGradient, map_smul, rawNormalizerGradient_block w hJ a b X hg j]
    simpa only [rawNormalizer_eq_integral, logBlock] using
      normalized_sourceGradient_eq (sources X) w j hz'
  · rw [rawMeanGradient, quotientGradient, map_sub, map_smul, map_smul,
      rawNormalizerGradient_block w hJ a b X hg j,
      rawNumeratorGradient_block w hJ a b F X hd hfg j]
    simpa only [rawNormalizer_eq_integral, rawNumerator, meanBlock] using
      source_quotient_field_eq_covariance (sources X) w j hz' (F X) (factorBlock F j X)

/-- Local chart smoothness gives ordinary source differentiability at every
point of the closed integration patch, without conditions elsewhere. -/
theorem differentiableAt_factor_source {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    {X : SourceSpace ι} (hX : X ∈ S) {z : Torus} (hz : z ∈ closure (patchDomain J hJ a b)) :
    DifferentiableAt ℝ (fun Y ↦ F Y z) X := by
  rw [closure_patchDomain hJ] at hz
  obtain ⟨Z, hZ, rfl⟩ := hz
  have h := ((hf.contDiffAt ⟨hX, hZ⟩).differentiableAt one_ne_zero).comp X
    ((differentiableAt_id : DifferentiableAt ℝ (fun Y : SourceSpace ι ↦ Y) X).prodMk
      (differentiableAt_const Z))
  simpa only [Function.comp_def, id_eq, torusFactor] using! h

theorem factorBlock_eq_ordinaryGradient_on_patch {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    {X : SourceSpace ι} (hX : X ∈ S) {z : Torus} (hz : z ∈ closure (patchDomain J hJ a b)) (j : ι) :
    factorBlock F j X z = (InnerProductSpace.toDual ℝ PlanarSpace).symm
      (fderiv ℝ (fun u ↦ F (sourceVariation j X u) z) (sourceProjection j X)) :=
  factorBlock_eq_ordinaryGradient (differentiableAt_factor_source hJ a b hf hX hz) j

theorem weakGradientOn_congr_value {d : Type*} [Fintype d] {S : Set (ChartSpace d)}
    (hS : MeasurableSet S) {f g : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    (h : WeakGradientOn S f G) (he : EqOn f g S) : WeakGradientOn S g G := by
  have hae : f =ᵐ[(volume : Measure (ChartSpace d)).restrict S] g :=
    (ae_restrict_mem hS).mono fun x hx ↦ he hx
  refine ⟨h.value_integrable.congr hae, h.gradient_integrable, ?_⟩
  intro ψ hψ hc hs v
  calc
    (∫ x in S, g x * fderiv ℝ ψ x v) = ∫ x in S, f x * fderiv ℝ ψ x v := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    _ = _ := h.identity ψ hψ hc hs v

/-- Actual finiteness, weak formulas and ordinary derivatives on a physical
source chart. The conditional mean is the probability integral itself. -/
structure SourceCalculus (w : ι → ℝ) (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) (S : Set (SourceSpace ι))
    (F : SourceSpace ι → Torus → ℝ) : Prop where
  normalization : RawNormalizedCalculus w J hJ a b S F
  finiteness : ∀ X ∈ S,
    let ν := pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w
    Integrable (F X) ν ∧ Integrable (torusFactorGradient F X) ν ∧
      ∀ Y : Torus, Integrable (fun z ↦ greenGradient (z - Y)) ν ∧
        Integrable (fun z ↦ F X z • greenGradient (z - Y)) ν
  blocks : ∀ X ∈ S, ∀ j,
    sourceProjection j (rawLogGradient w J hJ a b X) = logBlock w J hJ a b j X ∧
      sourceProjection j (rawMeanGradient w J hJ a b F X) = meanBlock w J hJ a b F j X
  mean_weak : WeakGradientOn S (conditionalMean w J hJ a b F) (rawMeanGradient w J hJ a b F)
  mean_lipschitz : ∃ C : ℝ≥0, LipschitzOnWith C (conditionalMean w J hJ a b F) S
  ordinary : ∀ᵐ X ∂(volume : Measure (SourceSpace ι)).restrict S,
    HasFDerivAt (rawLog w J hJ a b)
      (InnerProductSpace.toDual ℝ (SourceSpace ι) (rawLogGradient w J hJ a b X)) X ∧
    HasFDerivAt (conditionalMean w J hJ a b F)
      (InnerProductSpace.toDual ℝ (SourceSpace ι) (rawMeanGradient w J hJ a b F X)) X

/-- An assembly lemma. Its already proved raw weak/Lipschitz and finite
moment inputs are all instantiated by the capped theorem below. -/
theorem sourceCalculus_of_raw (w : ι → ℝ) {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) {S : Set (SourceSpace ι)}
    (hS : IsCompact S) (hconv : Convex ℝ S) (F : SourceSpace ι → Torus → ℝ)
    (hr : RawNormalizedCalculus w J hJ a b S F)
    (hi : ∀ X ∈ S,
      let ν := pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w
      Integrable (F X) ν ∧ Integrable (torusFactorGradient F X) ν ∧
        ∀ Y : Torus, Integrable (fun z ↦ greenGradient (z - Y)) ν ∧
          Integrable (fun z ↦ F X z • greenGradient (z - Y)) ν) :
    SourceCalculus w J hJ a b S F := by
  have he : EqOn (rawMean w J hJ a b F) (conditionalMean w J hJ a b F) S :=
    fun X hX ↦ hr.mean_eq_integral X hX
  have hm := weakGradientOn_congr_value hS.measurableSet hr.mean_weak he
  obtain ⟨Clog, Cmean, hlog, hmean⟩ := hr.lipschitz
  have hl : LipschitzOnWith Cmean (conditionalMean w J hJ a b F) S := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro X hX Y hY
    rw [← he hX, ← he hY]
    exact lipschitzOnWith_iff_norm_sub_le.mp hmean hX hY
  refine ⟨hr, hi, ?_, hm, ⟨Cmean, hl⟩, ?_⟩
  · intro X hX
    exact rawGradient_blocks w hJ a b F X (hr.normalizer_pos X hX) (hi X hX).2.1
      (fun j ↦ (hi X hX).2.2 (sources X j))
  · filter_upwards [ae_hasFDerivAt_of_weakGradientOn hS hconv hr.log_weak hlog,
      ae_hasFDerivAt_of_weakGradientOn hS hconv hm hl] with X hX hY
    exact ⟨hX, hY⟩

namespace SourceCalculus

variable {w : ι → ℝ} {J : ℕ} {hJ : 0 < J} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace ι)} {F : SourceSpace ι → Torus → ℝ}
    (h : SourceCalculus w J hJ a b S F)

include h

theorem integrable_factorBlock (X : SourceSpace ι) (hX : X ∈ S) (j : ι) :
    Integrable (factorBlock F j X)
      (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w) :=
  (sourceProjection j).integrable_comp (h.finiteness X hX).2.1

/-- The exact first displayed weak identity of source Lemma 3.5, tested in
one physical source direction, with the raw Haar normalizer. -/
theorem log_block_weak (hS : MeasurableSet S) (j : ι) (v : PlanarSpace)
    (ψ : SourceSpace ι → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ S) :
    (∫ X in S, rawLog w J hJ a b X * fderiv ℝ ψ X ((sourceProjection j).adjoint v)) =
      -(∫ X in S, inner ℝ (logBlock w J hJ a b j X) v * ψ X) := by
  rw [h.normalization.log_weak.identity ψ hψ hc hs ((sourceProjection j).adjoint v)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS] with X hX
  rw [(sourceProjection j).adjoint_inner_right, (h.blocks X hX j).1]

/-- The exact second weak identity, for the actual normalized probability
integral, including the derivative of the factor. -/
theorem mean_block_weak (hS : MeasurableSet S) (j : ι) (v : PlanarSpace)
    (ψ : SourceSpace ι → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ S) :
    (∫ X in S, conditionalMean w J hJ a b F X * fderiv ℝ ψ X ((sourceProjection j).adjoint v)) =
      -(∫ X in S, inner ℝ (meanBlock w J hJ a b F j X) v * ψ X) := by
  rw [h.mean_weak.identity ψ hψ hc hs ((sourceProjection j).adjoint v)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS] with X hX
  rw [(sourceProjection j).adjoint_inner_right, (h.blocks X hX j).2]

/-- Ordinary planar derivatives with precisely one source variable varied.
These are actual Fréchet derivatives, not only block labels for a weak field. -/
theorem ordinary_source_blocks (hS : MeasurableSet S) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace ι)).restrict S, ∀ j : ι,
      HasFDerivAt (fun z ↦ rawLog w J hJ a b (sourceVariation j X z))
        (InnerProductSpace.toDual ℝ PlanarSpace (logBlock w J hJ a b j X)) (sourceProjection j X) ∧
      HasFDerivAt (fun z ↦ conditionalMean w J hJ a b F (sourceVariation j X z))
        (InnerProductSpace.toDual ℝ PlanarSpace (meanBlock w J hJ a b F j X)) (sourceProjection j X) := by
  filter_upwards [h.ordinary, ae_restrict_mem hS] with X hX hXS
  intro j
  constructor
  · simpa only [(h.blocks X hXS j).1] using hasFDerivAt_sourceBlock hX.1 j
  · simpa only [(h.blocks X hXS j).2] using hasFDerivAt_sourceBlock hX.2 j

/-- Both displayed fields equal the ordinary planar Riesz gradients a.e. -/
theorem ordinary_source_gradients (hS : MeasurableSet S) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace ι)).restrict S, ∀ j : ι,
      (InnerProductSpace.toDual ℝ PlanarSpace).symm
        (fderiv ℝ (fun z ↦ rawLog w J hJ a b (sourceVariation j X z)) (sourceProjection j X)) =
          logBlock w J hJ a b j X ∧
      (InnerProductSpace.toDual ℝ PlanarSpace).symm
        (fderiv ℝ (fun z ↦ conditionalMean w J hJ a b F (sourceVariation j X z))
          (sourceProjection j X)) = meanBlock w J hJ a b F j X := by
  filter_upwards [h.ordinary_source_blocks hS] with X hX
  intro j
  constructor
  · rw [(hX j).1.fderiv]
    exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _
  · rw [(hX j).2.fderiv]
    exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _

/-- Every literal weighted chart measure, including its normalizing scalar,
inherits the ordinary formulas. No positivity or collision-capacity premise
is used for the direction of absolute-continuity transfer. -/
theorem weighted_ordinary_source_blocks (hS : MeasurableSet S) (ρ : SourceSpace ι → ℝ≥0∞)
    (c : ℝ≥0∞) :
    ∀ᵐ X ∂c • (((volume : Measure (SourceSpace ι)).restrict S).withDensity ρ), ∀ j : ι,
      HasFDerivAt (fun z ↦ rawLog w J hJ a b (sourceVariation j X z))
        (InnerProductSpace.toDual ℝ PlanarSpace (logBlock w J hJ a b j X)) (sourceProjection j X) ∧
      HasFDerivAt (fun z ↦ conditionalMean w J hJ a b F (sourceVariation j X z))
        (InnerProductSpace.toDual ℝ PlanarSpace (meanBlock w J hJ a b F j X)) (sourceProjection j X) :=
  (h.ordinary_source_blocks hS).filter_mono
    ((withDensity_absolutelyContinuous _ _).smul_left c).ae_le

theorem sourceChart_weighted_ordinary_source_blocks (hS : MeasurableSet S)
    (ρ : SourceSpace ι → ℝ≥0∞) :
    ∀ᵐ X ∂(sourceChartMeasure S).withDensity ρ, ∀ j : ι,
      HasFDerivAt (fun z ↦ rawLog w J hJ a b (sourceVariation j X z))
        (InnerProductSpace.toDual ℝ PlanarSpace (logBlock w J hJ a b j X)) (sourceProjection j X) ∧
      HasFDerivAt (fun z ↦ conditionalMean w J hJ a b F (sourceVariation j X z))
        (InnerProductSpace.toDual ℝ PlanarSpace (meanBlock w J hJ a b F j X)) (sourceProjection j X) := by
  rw [sourceChartMeasure, withDensity_smul_measure]
  exact h.weighted_ordinary_source_blocks hS ρ _

end SourceCalculus

/-- Full analytic chart assembly for actual capped Green weights. The only
placement premises are geometric label/cap conditions and local C1 data.
All derivative, integrability, weak, Lipschitz and a.e. conclusions are
derived. The supplied Green bounds are the earlier kernel conclusions. -/
theorem capped_sourceCalculus (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (hconv : Convex ℝ S)
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) :
    SourceCalculus (fun i : I ↦ w i) J hJ a b S F := by
  apply sourceCalculus_of_raw _ hJ a b hS hconv F
    (capped_raw_normalized_calculus K hJ hN hβ hβ₀ hC₀ hmesh I S hS hconv η hη hX w hw₀ hw a b hf)
  intro X hXS
  have hi := capped_local_covariance_integrable hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    I hS X hXS (η X) (hη X hXS) (hX X hXS) w hw₀ hw a b hf
  simpa only [pointLaw_patch_eq_raw hJ (by omega) a b] using hi

/-- Literal closed cell product. The integration patch may be a cell or an
adjacent union in either coordinate direction, including wrap. -/
theorem cellChart_sourceCalculus (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart (cellChart I η) (patchClosed b) (torusFactor F J a)) :
    SourceCalculus (fun i : I ↦ w i) J hJ a b (cellChart I η) F :=
  capped_sourceCalculus K hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh I (cellChart I η)
    (isCompact_closedChart J (fun i : I ↦ η i) (fun _ ↦ .cell))
    (convex_closedChart J (fun i : I ↦ η i) (fun _ ↦ .cell))
    (fun _ ↦ η) (fun _ _ ↦ hη) (fun _ hX ↦ cellChart_placement hJ I η hX)
    w hw₀ hw a b hf

/-- Literal source product with at most one adjacent source coordinate and
a cell integration patch. Both endpoint caps, either orientation and wrap
are discharged by the actual closed-chart placement construction. -/
theorem adjacentChart_sourceCalculus (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N) (k : Fin N) (d : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁) (Function.update η k (nextCell J hJ (η k) d)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart (adjacentChart I η k d) (patchClosed .cell) (torusFactor F J a)) :
    SourceCalculus (fun i : I ↦ w i) J hJ a .cell (adjacentChart I η k d) F := by
  obtain ⟨labels, hcap, hplace⟩ := exists_capped_labels_one_adjacent hJ I
    (adjacentChart I η k d) η k d (fixedDelta β₀ C₀ C₁) hη₀ hη₁
    (fun _ hX ↦ adjacentChart_cell_placement hJ I η k d hX)
    (fun _ hX hk ↦ adjacentChart_edge_placement hJ I η k d hX hk)
  exact capped_sourceCalculus K hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh I (adjacentChart I η k d)
    (isCompact_closedChart J (fun i : I ↦ η i) (adjacentShapes I k d))
    (convex_closedChart J (fun i : I ↦ η i) (adjacentShapes I k d))
    labels (fun X _ ↦ hcap X) hplace w hw₀ hw a .cell hf

end PeriodicAttractiveLogGas.MovingPoleDerivativeIdentification
