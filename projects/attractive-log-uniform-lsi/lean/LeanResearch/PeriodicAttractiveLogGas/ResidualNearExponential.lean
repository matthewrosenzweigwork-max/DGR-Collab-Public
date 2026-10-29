import LeanResearch.PeriodicAttractiveLogGas.ReferenceResidual
import LeanResearch.PeriodicAttractiveLogGas.ResidualCellGraph
import LeanResearch.PeriodicAttractiveLogGas.CanonicalIndependentRealizations
import Mathlib.Probability.Independence.Integration

/-! Supplied near-part residual exponential estimate, source lines 2602–2630.
The actual cell graph, reference residual and coordinate product laws are used. -/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.ResidualNearExponential
open MeshCells MeshNearbyGeometry LabelOccupations ResidualCellGraph
open ReferenceResidual CanonicalPairs CanonicalRowHolder

def universalConstant : ℝ := 8 * Real.sqrt 2 * Real.exp 1

theorem universalConstant_pos : 0 < universalConstant := by
  unfold universalConstant
  positivity

def rationalBound (x : ℝ) : ℝ := (1 + x ^ 2) / (1 - x ^ 2)

theorem rationalBound_pos {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    0 < rationalBound x := by
  have hd : 0 < 1 - x ^ 2 := by nlinarith
  exact div_pos (by positivity) hd

/-- The exact scalar logarithmic estimate used before summing over edges. -/
theorem log_rationalBound_le {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.log (rationalBound x) ≤ (8 / 3 : ℝ) * x ^ 2 := by
  have hd : 0 < 1 - x ^ 2 := by nlinarith
  have hh := Real.log_le_sub_one_of_pos (rationalBound_pos hx hxhalf)
  apply hh.trans
  unfold rationalBound
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hd).mpr
  have hm := mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 4 * x ^ 2 by nlinarith)
  nlinarith

theorem rationalBound_le_exp {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    rationalBound x ≤ Real.exp ((8 / 3 : ℝ) * x ^ 2) := by
  rw [← Real.exp_log (rationalBound_pos hx hxhalf)]
  exact Real.exp_le_exp.mpr (log_rationalBound_le hx hxhalf)

theorem pair_mem_cellEdges_iff {J R : ℕ} (a b : MeshIndex J) :
    ({a, b} : Finset (MeshIndex J)) ∈ cellEdges R ↔ periodicIndexDistance a b ≤ R := by
  constructor
  · intro he
    have hi : ({a, b} : Finset (MeshIndex J)) ∈ incidentEdges R a :=
      Finset.mem_filter.mpr ⟨he, by simp⟩
    rw [incidentEdges_eq_image] at hi
    obtain ⟨c, hc, hec⟩ := Finset.mem_image.mp hi
    have hcb : c = b := pair_finset_injective a hec
    subst c
    exact (mem_nearbyCells _ _).mp hc
  · intro hab
    exact mem_cellEdges.mpr ⟨a, b, (mem_nearbyCells _ _).mpr hab, rfl⟩

section EdgeKernels
variable {J m R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
  (η : Fin m → MeshIndex J) (e : Finset (MeshIndex J))

/-- Only kernels whose unordered pair of cell labels is this edge survive.
This includes a loop when both labels coincide. -/
def edgeKernel (i j : Fin m) (x y : Torus) : ℝ :=
  if ({η i, η j} : Finset (MeshIndex J)) = e then residual (μ (η i)) (μ (η j)) x y else 0

omit [∀ a, IsProbabilityMeasure (μ a)] in
theorem edgeKernel_of_pair {i j : Fin m}
    (h : ({η i, η j} : Finset (MeshIndex J)) = e) :
    edgeKernel μ η e i j = residual (μ (η i)) (μ (η j)) := by
  funext x y
  simp only [edgeKernel, h, ite_true]

omit [∀ a, IsProbabilityMeasure (μ a)] in
theorem edgeKernel_of_not_pair {i j : Fin m}
    (h : ({η i, η j} : Finset (MeshIndex J)) ≠ e) :
    edgeKernel μ η e i j = fun _ _ => 0 := by
  funext x y
  simp only [edgeKernel, h, ite_false]

include hmesh hμ in
/-- Original source inputs for every surviving edge kernel, derived from the
actual reference residual; no factorial moment or canonicality is assumed. -/
theorem edgeKernel_source_inputs (he : e ∈ cellEdges R) :
    (∀ i j, Measurable (Function.uncurry (edgeKernel μ η e i j))) ∧
    (∀ i j, ∀ᵐ y ∂μ (η j), (∫ x, edgeKernel μ η e i j x y ∂μ (η i)) = 0) ∧
    (∀ i j, ∀ᵐ x ∂μ (η i), (∫ y, edgeKernel μ η e i j x y ∂μ (η j)) = 0) ∧
    (∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (μ (η i)) (edgeKernel μ η e i j) p) (μ (η j)) +
        essSup (rightMoment (μ (η j)) (edgeKernel μ η e i j) p) (μ (η i)) ≤
          ENNReal.ofReal (2 * nearScale R ^ p * (p.factorial : ℝ))) := by
  have hnear (i j : Fin m) (h : ({η i, η j} : Finset (MeshIndex J)) = e) :
      periodicIndexDistance (η i) (η j) ≤ R := by
    apply (pair_mem_cellEdges_iff _ _).mp
    simpa only [h] using he
  have hb (i j : Fin m) (h : ({η i, η j} : Finset (MeshIndex J)) = e)
      (p : ℕ) (hp : 1 ≤ p) :=
    near_residual_bounds hJ hmesh (η i) (η j) (hnear i j h)
      (μ (η i)) (μ (η j)) (hμ _) (hμ _) hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : ({η i, η j} : Finset (MeshIndex J)) = e
    · rw [edgeKernel_of_pair μ η e h]
      exact (hb i j h 1 le_rfl).1
    · rw [edgeKernel_of_not_pair μ η e h]
      exact measurable_const
  · intro i j
    by_cases h : ({η i, η j} : Finset (MeshIndex J)) = e
    · rw [edgeKernel_of_pair μ η e h]
      exact (hb i j h 1 le_rfl).2.2.2.2.1
    · rw [edgeKernel_of_not_pair μ η e h]
      simp
  · intro i j
    by_cases h : ({η i, η j} : Finset (MeshIndex J)) = e
    · rw [edgeKernel_of_pair μ η e h]
      exact (hb i j h 1 le_rfl).2.2.2.2.2.1
    · rw [edgeKernel_of_not_pair μ η e h]
      simp
  · intro p hp i j
    by_cases h : ({η i, η j} : Finset (MeshIndex J)) = e
    · rw [edgeKernel_of_pair μ η e h]
      have hm := (hb i j h p hp).2.2.2.2.2.2
      have hC : 0 ≤ nearScale R ^ p * (p.factorial : ℝ) :=
        mul_nonneg (pow_nonneg (nearScale_nonneg R) p) (Nat.cast_nonneg _)
      calc
        _ ≤ ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) +
            ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) := add_le_add hm.1 hm.2
        _ = _ := by rw [← ENNReal.ofReal_add hC hC]; congr 1; ring
    · rw [edgeKernel_of_not_pair μ η e h]
      change essSup (fun _y : Torus => ∫⁻ _x : Torus, ‖(0 : ℝ)‖ₑ ^ p ∂μ (η i)) (μ (η j)) +
        essSup (fun _x : Torus => ∫⁻ _y : Torus, ‖(0 : ℝ)‖ₑ ^ p ∂μ (η j)) (μ (η i)) ≤ _
      simp [show p ≠ 0 by omega]
end EdgeKernels

/-- Increasing enumeration of the actual particle subset, preserving the original i<j. -/
def edgeEnumeration {J N : ℕ} (η : LabelVector J N) (e : Finset (MeshIndex J)) :
    Fin (edgeParticleCount η e) ↪o Fin N :=
  (edgeParticles η e).orderEmbOfFin rfl

def edgeLabels {J N : ℕ} (η : LabelVector J N) (e : Finset (MeshIndex J)) :
    Fin (edgeParticleCount η e) → MeshIndex J := fun i => η (edgeEnumeration η e i)

def edgeVector {J N : ℕ} (η : LabelVector J N) (e : Finset (MeshIndex J))
    (X : Fin N → Torus) : Fin (edgeParticleCount η e) → Torus := fun i => X (edgeEnumeration η e i)

/-- The actual canonical sum on an edge's independent particle coordinates. -/
def edgeSum {J N : ℕ} (μ : MeshIndex J → Measure Torus) (η : LabelVector J N)
    (e : Finset (MeshIndex J)) (X : Fin N → Torus) : ℝ :=
  canonicalSum (edgeKernel μ (edgeLabels η e) e) (edgeVector η e X)

def upperPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

@[simp] theorem mem_upperPairs {N : ℕ} (ij : Fin N × Fin N) :
    ij ∈ upperPairs N ↔ ij.1 < ij.2 := by simp [upperPairs]

theorem canonicalSum_eq_sum_pairs {N : ℕ} (h : Fin N → Fin N → Torus → Torus → ℝ)
    (X : Fin N → Torus) :
    canonicalSum h X = ∑ ij ∈ upperPairs N, h ij.1 ij.2 (X ij.1) (X ij.2) := by
  unfold canonicalSum CanonicalDecoupling.pairSum upperKernel upperPairs
  rw [Finset.sum_filter, Finset.sum_product]

theorem restricted_pair_sum_reindex {N : ℕ} (s : Finset (Fin N))
    (h : Fin N → Fin N → Torus → Torus → ℝ) (X : Fin N → Torus) :
    (∑ ij ∈ (upperPairs N).filter (fun ij => ij.1 ∈ s ∧ ij.2 ∈ s),
      h ij.1 ij.2 (X ij.1) (X ij.2)) =
    canonicalSum (fun i j => h (s.orderEmbOfFin rfl i) (s.orderEmbOfFin rfl j))
      (fun i => X (s.orderEmbOfFin rfl i)) := by
  rw [canonicalSum_eq_sum_pairs]
  symm
  let f := s.orderEmbOfFin rfl
  apply Finset.sum_bij (fun ij _ => (f ij.1, f ij.2))
  · intro ij hij
    apply Finset.mem_filter.mpr
    exact ⟨(mem_upperPairs _).mpr (f.strictMono ((mem_upperPairs _).mp hij)),
      s.orderEmbOfFin_mem rfl ij.1, s.orderEmbOfFin_mem rfl ij.2⟩
  · intro ij _ pq _ he
    exact Prod.ext (f.injective (congrArg Prod.fst he)) (f.injective (congrArg Prod.snd he))
  · intro ij hij
    obtain ⟨hlt, hi, hj⟩ := Finset.mem_filter.mp hij
    obtain ⟨i, hi'⟩ := (s.orderIsoOfFin rfl).surjective ⟨ij.1, hi⟩
    obtain ⟨j, hj'⟩ := (s.orderIsoOfFin rfl).surjective ⟨ij.2, hj⟩
    have hei : f i = ij.1 := congrArg Subtype.val hi'
    have hej : f j = ij.2 := congrArg Subtype.val hj'
    refine ⟨(i, j), (mem_upperPairs _).mpr ?_, Prod.ext hei hej⟩
    exact f.lt_iff_lt.mp (by simpa only [hei, hej] using (mem_upperPairs _).mp hlt)
  · intro _ _
    rfl

/-- Every nonzero summand belongs to the edge's actual particle set. -/
theorem edgeSum_eq_pair_sum {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (e : Finset (MeshIndex J)) (X : Fin N → Torus) :
    edgeSum μ η e X = ∑ ij ∈ upperPairs N,
      if ({η ij.1, η ij.2} : Finset (MeshIndex J)) = e then
        residual (μ (η ij.1)) (μ (η ij.2)) (X ij.1) (X ij.2) else 0 := by
  have hr := restricted_pair_sum_reindex (edgeParticles η e) (edgeKernel μ η e) X
  change (∑ ij ∈ (upperPairs N).filter
    (fun ij => ij.1 ∈ edgeParticles η e ∧ ij.2 ∈ edgeParticles η e),
      edgeKernel μ η e ij.1 ij.2 (X ij.1) (X ij.2)) = edgeSum μ η e X at hr
  rw [← hr, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij _
  by_cases hp : ({η ij.1, η ij.2} : Finset (MeshIndex J)) = e
  · have hi : ij.1 ∈ edgeParticles η e := by
      apply (mem_sourceIndices η Finset.univ e _).mpr
      exact ⟨Finset.mem_univ _, hp ▸ (by simp : η ij.1 ∈ ({η ij.1, η ij.2} : Finset (MeshIndex J)))⟩
    have hj : ij.2 ∈ edgeParticles η e := by
      apply (mem_sourceIndices η Finset.univ e _).mpr
      exact ⟨Finset.mem_univ _, hp ▸ (by simp : η ij.2 ∈ ({η ij.1, η ij.2} : Finset (MeshIndex J)))⟩
    simp [hi, hj, edgeKernel, hp]
  · simp [edgeKernel, hp]

theorem canonicalSum_eq_zero_of_card_le_one {m : ℕ} (hm : m ≤ 1)
    (h : Fin m → Fin m → Torus → Torus → ℝ) (X : Fin m → Torus) :
    canonicalSum h X = 0 := by
  rw [canonicalSum_eq_sum_pairs]
  apply Finset.sum_eq_zero
  intro ij hij
  have hh := (mem_upperPairs _).mp hij
  have hi := ij.1.isLt
  have hj := ij.2.isLt
  have hlt : ij.1.val < ij.2.val := hh
  omega

theorem edgeSum_eq_zero_of_count_le_one {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (e : Finset (MeshIndex J))
    (hm : edgeParticleCount η e ≤ 1) (X : Fin N → Torus) : edgeSum μ η e X = 0 :=
  canonicalSum_eq_zero_of_card_le_one hm _ _

/-- The literal near pair sum divided by the total particle number. -/
def nearResidualSum {J N : ℕ} (R : ℕ) (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (X : Fin N → Torus) : ℝ :=
  (∑ ij ∈ upperPairs N, if periodicIndexDistance (η ij.1) (η ij.2) ≤ R then
    residual (μ (η ij.1)) (μ (η ij.2)) (X ij.1) (X ij.2) else 0) / N

theorem sum_edgeSum_eq_near {J N : ℕ} (R : ℕ) (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (X : Fin N → Torus) :
    (∑ e ∈ cellEdges R, edgeSum μ η e X) / N = nearResidualSum R μ η X := by
  simp_rw [edgeSum_eq_pair_sum]
  rw [Finset.sum_comm]
  unfold nearResidualSum
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.sum_ite_eq]
  simp only [pair_mem_cellEdges_iff]

section EdgeExponential
variable {J N R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
  (η : LabelVector J N) (e : Finset (MeshIndex J))

theorem measurePreserving_edgeVector : MeasurePreserving (edgeVector η e)
    (Measure.pi (fun i => μ (η i))) (Measure.pi (fun i => μ (edgeLabels η e i))) := by
  have hi : iIndepFun (fun i (X : Fin N → Torus) => X i) (Measure.pi (fun i => μ (η i))) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have his := hi.precomp (edgeEnumeration η e).injective
  exact CanonicalIndependentRealizations.measurePreserving_independentVector
    (fun i => μ (edgeLabels η e i)) (Measure.pi (fun i => μ (η i)))
    (fun i X => X (edgeEnumeration η e i)) (fun _ => measurable_pi_apply _) his
    (fun i => (measurePreserving_eval (fun j => μ (η j)) (edgeEnumeration η e i)).map_eq)

include hmesh hμ in
theorem measurable_edgeSum (he : e ∈ cellEdges R) : Measurable (edgeSum μ η e) := by
  have hs := edgeKernel_source_inputs hJ hmesh μ hμ (edgeLabels η e) e he
  have hm := CanonicalPairs.measurable_pairSum (upperKernel (edgeKernel μ (edgeLabels η e) e))
    (measurable_upperKernel _ (fun i j _ => hs.1 i j))
  exact hm.comp (measurePreserving_edgeVector μ η e).measurable

include hmesh hμ in
/-- Actual edge exponential integrability at its true particle cardinality.
Zero particles are treated directly, without division by their cardinality. -/
theorem edge_exponential_bound (he : e ∈ cellEdges R) {a : ℝ} (ha : 0 ≤ a)
    (hx : a * universalConstant * nearScale R * (edgeParticleCount η e : ℝ) < 1) :
    Integrable (fun X => Real.exp (a * edgeSum μ η e X)) (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, Real.exp (a * edgeSum μ η e X) ∂Measure.pi (fun i => μ (η i))) ≤
        rationalBound (a * universalConstant * nearScale R * (edgeParticleCount η e : ℝ)) := by
  by_cases hm : edgeParticleCount η e = 0
  · have hz (X : Fin N → Torus) : edgeSum μ η e X = 0 :=
      edgeSum_eq_zero_of_count_le_one μ η e (by omega) X
    simp only [hz, mul_zero, Real.exp_zero, hm, Nat.cast_zero, rationalBound, zero_pow (by omega : 2 ≠ 0),
      add_zero, sub_zero, div_one]
    exact ⟨integrable_const _, by simp⟩
  · have hmpos : 1 ≤ edgeParticleCount η e := by omega
    have hmr : (edgeParticleCount η e : ℝ) ≠ 0 := by exact_mod_cast hm
    have hs := edgeKernel_source_inputs hJ hmesh μ hμ (edgeLabels η e) e he
    have hb := canonical_pairs (fun i => μ (edgeLabels η e i)) (edgeKernel μ (edgeLabels η e) e)
      hmpos (fun i j _ => hs.1 i j) (fun i j _ => hs.2.1 i j)
      (fun i j _ => hs.2.2.1 i j) (nearScale_nonneg R)
      (fun p hp i j _ => hs.2.2.2 p hp i j)
    have harg : |a * (edgeParticleCount η e : ℝ)| *
        (8 * Real.sqrt 2 * Real.exp 1 * nearScale R) =
        a * universalConstant * nearScale R * (edgeParticleCount η e : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg ha (Nat.cast_nonneg _))]
      unfold universalConstant
      ring
    have hE := hb.2.2.2.2.1 (a * (edgeParticleCount η e : ℝ)) (by simpa only [harg] using hx)
    have hfun : (fun Y => Real.exp ((a * (edgeParticleCount η e : ℝ)) *
        canonicalSum (edgeKernel μ (edgeLabels η e) e) Y / (edgeParticleCount η e : ℝ))) =
        (fun Y => Real.exp (a * canonicalSum (edgeKernel μ (edgeLabels η e) e) Y)) := by
      funext Y
      congr 1
      field_simp [hmr]
    rw [hfun, harg] at hE
    have hmp := measurePreserving_edgeVector μ η e
    have hI : Integrable (fun X => Real.exp (a * edgeSum μ η e X))
        (Measure.pi (fun i => μ (η i))) := hmp.integrable_comp_of_integrable hE.1
    refine ⟨hI, ?_⟩
    have heq : (∫ X, Real.exp (a * edgeSum μ η e X) ∂Measure.pi (fun i => μ (η i))) =
        ∫ Y, Real.exp (a * canonicalSum (edgeKernel μ (edgeLabels η e) e) Y)
          ∂Measure.pi (fun i => μ (edgeLabels η e i)) :=
      CanonicalDecoupling.integral_comp_of_measurePreserving hmp hE.1.aestronglyMeasurable
    exact heq.trans_le hE.2
end EdgeExponential

section DisjointBlocks
variable {N : ℕ}

def DependsOnCoordinates {β : Type*} (s : Finset (Fin N)) (f : (Fin N → Torus) → β) : Prop :=
  ∀ X Y, (∀ i ∈ s, X i = Y i) → f X = f Y

def fillCoordinates (s : Finset (Fin N)) (Y : s → Torus) : Fin N → Torus :=
  fun i => if h : i ∈ s then Y ⟨i, h⟩ else 0

theorem measurable_fillCoordinates (s : Finset (Fin N)) : Measurable (fillCoordinates s) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ s
  · simpa only [fillCoordinates, dite_eq_left hi] using (measurable_pi_apply (⟨i, hi⟩ : s))
  · simpa only [fillCoordinates, dite_eq_right hi] using (measurable_const : Measurable (fun _ : s → Torus => (0 : Torus)))

/-- Disjoint coordinate blocks are independent under the actual product law. -/
theorem indepFun_of_disjoint_coordinates (ν : Fin N → Measure Torus)
    [∀ i, IsProbabilityMeasure (ν i)] {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : (Fin N → Torus) → β} {g : (Fin N → Torus) → γ}
    (hf : Measurable f) (hg : Measurable g) (s t : Finset (Fin N))
    (hst : Disjoint s t) (hfs : DependsOnCoordinates s f) (hgt : DependsOnCoordinates t g) :
    IndepFun f g (Measure.pi ν) := by
  have hi : iIndepFun (fun i (X : Fin N → Torus) => X i) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hb := hi.indepFun_finset s t hst (fun i => measurable_pi_apply i)
  have hfg := hb.comp (hf.comp (measurable_fillCoordinates s)) (hg.comp (measurable_fillCoordinates t))
  have hf' : (f ∘ fillCoordinates s) ∘ (fun X : Fin N → Torus => fun i : s => X i) = f := by
    funext X
    apply hfs
    intro i hi
    simp [fillCoordinates, hi]
  have hg' : (g ∘ fillCoordinates t) ∘ (fun X : Fin N → Torus => fun i : t => X i) = g := by
    funext X
    apply hgt
    intro i hi
    simp [fillCoordinates, hi]
  simpa only [hf', hg'] using hfg

/-- True block factorization, proved by finite induction and binary independence.
The extended formulation permits infinite integrals and therefore assumes no integrability. -/
theorem lintegral_prod_disjoint_blocks {ι : Type*} [DecidableEq ι]
    (ν : Fin N → Measure Torus) [∀ i, IsProbabilityMeasure (ν i)]
    (s : Finset ι) (A : ι → Finset (Fin N)) (F : ι → (Fin N → Torus) → ℝ≥0∞)
    (hF : ∀ i ∈ s, Measurable (F i))
    (hdep : ∀ i ∈ s, DependsOnCoordinates (A i) (F i))
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    (∫⁻ X, ∏ i ∈ s, F i X ∂Measure.pi ν) = ∏ i ∈ s, ∫⁻ X, F i X ∂Measure.pi ν := by
  classical
  revert hF hdep hdis
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert i s hi ih =>
    intro hF hdep hdis
    have hm : Measurable (fun X => ∏ j ∈ s, F j X) :=
      Finset.measurable_prod s (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have hds : DependsOnCoordinates (s.biUnion A) (fun X => ∏ j ∈ s, F j X) := by
      intro X Y hXY
      apply Finset.prod_congr rfl
      intro j hj
      apply hdep j (Finset.mem_insert_of_mem hj)
      intro k hk
      exact hXY k (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩)
    have hd : Disjoint (A i) (s.biUnion A) := by
      apply Finset.disjoint_left.mpr
      intro k hki hks
      obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hks
      have hij : i ≠ j := by
        intro h
        subst j
        exact hi hj
      exact Finset.disjoint_left.mp (hdis i (Finset.mem_insert_self _ _)
        j (Finset.mem_insert_of_mem hj) hij) hki hkj
    have hind := indepFun_of_disjoint_coordinates ν (hF i (Finset.mem_insert_self _ _)) hm
      (A i) (s.biUnion A) hd (hdep i (Finset.mem_insert_self _ _)) hds
    have heq := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (hF i (Finset.mem_insert_self _ _)) hm hind
    have hrest := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      (fun j hj => hdep j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk => hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    simp only [Finset.prod_insert hi]
    change (∫⁻ X, (F i * (fun X => ∏ j ∈ s, F j X)) X ∂Measure.pi ν) = _
    rw [heq, hrest]

theorem edgeSum_depends_on_coordinates {J : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (e : Finset (MeshIndex J)) :
    DependsOnCoordinates (edgeParticles η e) (edgeSum μ η e) := by
  intro X Y hXY
  apply congrArg (canonicalSum (edgeKernel μ (edgeLabels η e) e))
  funext i
  exact hXY _ ((edgeParticles η e).orderEmbOfFin_mem rfl i)

end DisjointBlocks

/-- Exponential moments of actual disjoint coordinate blocks factor, and the
resulting finite bound proves integrability of the full product. -/
theorem exponential_disjoint_block_bound {N : ℕ} {ι : Type*} [DecidableEq ι]
    (ν : Fin N → Measure Torus) [∀ i, IsProbabilityMeasure (ν i)]
    (s : Finset ι) (A : ι → Finset (Fin N)) (G : ι → (Fin N → Torus) → ℝ)
    (hG : ∀ i ∈ s, Measurable (G i))
    (hdep : ∀ i ∈ s, DependsOnCoordinates (A i) (G i))
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    (a : ℝ) (b : ι → ℝ)
    (hb : ∀ i ∈ s, Integrable (fun X => Real.exp (a * G i X)) (Measure.pi ν) ∧
      (∫ X, Real.exp (a * G i X) ∂Measure.pi ν) ≤ Real.exp (b i)) :
    Integrable (fun X => Real.exp (a * ∑ i ∈ s, G i X)) (Measure.pi ν) ∧
      (∫ X, Real.exp (a * ∑ i ∈ s, G i X) ∂Measure.pi ν) ≤ Real.exp (∑ i ∈ s, b i) := by
  let F := fun i X => ENNReal.ofReal (Real.exp (a * G i X))
  have hF : ∀ i ∈ s, Measurable (F i) := fun i hi => (((hG i hi).const_mul a).exp).ennreal_ofReal
  have hFd : ∀ i ∈ s, DependsOnCoordinates (A i) (F i) := by
    intro i hi X Y hXY
    dsimp [F]
    rw [hdep i hi X Y hXY]
  have he (X : Fin N → Torus) : ENNReal.ofReal (Real.exp (a * ∑ i ∈ s, G i X)) = ∏ i ∈ s, F i X := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le
  have hFi (i : ι) (hi : i ∈ s) : (∫⁻ X, F i X ∂Measure.pi ν) ≤ ENNReal.ofReal (Real.exp (b i)) := by
    change (∫⁻ X, ENNReal.ofReal (Real.exp (a * G i X)) ∂Measure.pi ν) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hb i hi).1
      (Eventually.of_forall fun X => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hb i hi).2
  have hl : (∫⁻ X, ENNReal.ofReal (Real.exp (a * ∑ i ∈ s, G i X)) ∂Measure.pi ν) ≤
      ENNReal.ofReal (Real.exp (∑ i ∈ s, b i)) := by
    simp_rw [he]
    rw [lintegral_prod_disjoint_blocks ν s A F hF hFd hdis, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos (b i)).le)]
    exact Finset.prod_le_prod hFi
  have hm : Measurable (fun X => Real.exp (a * ∑ i ∈ s, G i X)) :=
    ((Finset.measurable_sum s hG).const_mul a).exp
  have hi := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall fun X => (Real.exp_pos _).le)).mp (hl.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun X => (Real.exp_pos _).le)]
  exact hl

/-- Finite Hölder with individual exponential bounds. Normalization preserves
the average of the color bounds, rather than replacing them by a common maximum. -/
theorem exponential_sum_holder {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {a : ℕ} (ha : 1 ≤ a) (G : Fin a → Ω → ℝ) (hG : ∀ i, Measurable (G i)) (b : Fin a → ℝ)
    (hb : ∀ i, Integrable (fun X => Real.exp ((a : ℝ) * G i X)) ρ ∧
      (∫ X, Real.exp ((a : ℝ) * G i X) ∂ρ) ≤ Real.exp (b i)) :
    Integrable (fun X => Real.exp (∑ i, G i X)) ρ ∧
      (∫ X, Real.exp (∑ i, G i X) ∂ρ) ≤ Real.exp ((∑ i, b i) / a) := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  let H := fun i X => Real.exp (G i X - b i / a)
  have hH : ∀ i, Measurable (H i) := fun i => ((hG i).sub measurable_const).exp
  have hpow (i : Fin a) : (fun X => H i X ^ a) =
      fun X => Real.exp (-b i) * Real.exp ((a : ℝ) * G i X) := by
    funext X
    dsimp [H]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    field_simp [ha0]
    ring
  have hHi (i : Fin a) : Integrable (fun X => H i X ^ a) ρ := by
    rw [hpow]
    exact (hb i).1.const_mul _
  have hHb (i : Fin a) : (∫ X, H i X ^ a ∂ρ) ≤ 1 := by
    rw [hpow, integral_const_mul]
    calc
      _ ≤ Real.exp (-b i) * Real.exp (b i) := mul_le_mul_of_nonneg_left (hb i).2 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hHE (i : Fin a) : (∫⁻ X, ‖H i X‖ₑ ^ a ∂ρ) ≤ ENNReal.ofReal 1 := by
    have he (X : Ω) : ‖H i X‖ₑ ^ a = ENNReal.ofReal (H i X ^ a) := by
      rw [NearLogMomentBounds.enorm_pow_eq_ofReal_abs_pow,
        abs_of_pos (show 0 < H i X from Real.exp_pos _)]
    simp_rw [he]
    rw [← ofReal_integral_eq_lintegral_ofReal (hHi i)
      (Eventually.of_forall fun X => pow_nonneg (Real.exp_pos _).le a)]
    exact ENNReal.ofReal_le_ofReal (hHb i)
  obtain ⟨hI, hB⟩ := CanonicalRowHolder.integrable_prod_and_integral_abs_le ha H hH (by norm_num : (0 : ℝ) ≤ 1) hHE
  have hprod (X : Ω) : (∏ i, H i X) = Real.exp ((∑ i, G i X) - (∑ i, b i) / a) := by
    dsimp [H]
    rw [← Real.exp_sum, Finset.sum_sub_distrib, Finset.sum_div]
  have hpos (X : Ω) : 0 ≤ ∏ i, H i X := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have habs (X : Ω) : |∏ i, H i X| = ∏ i, H i X := abs_of_nonneg (hpos X)
  have hB' : (∫ X, ∏ i, H i X ∂ρ) ≤ 1 := by
    simpa only [habs] using hB
  have he (X : Ω) : Real.exp (∑ i, G i X) =
      Real.exp ((∑ i, b i) / a) * ∏ i, H i X := by
    rw [hprod, ← Real.exp_add]
    congr 1
    ring
  have hi : Integrable (fun X => Real.exp (∑ i, G i X)) ρ := by
    simp_rw [he]
    exact hI.const_mul _
  refine ⟨hi, ?_⟩
  simp_rw [he]
  rw [integral_const_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hB' (Real.exp_pos ((∑ i, b i) / a)).le

def colorCount (R : ℕ) : ℕ := 2 * (2 * R + 1) ^ 2

theorem colorCount_pos (R : ℕ) : 0 < colorCount R := by unfold colorCount; positivity

theorem colorCount_cast (R : ℕ) : (colorCount R : ℝ) = 2 * (2 * (R : ℝ) + 1) ^ 2 := by
  simp [colorCount]

theorem sum_color_fibers {ι : Type*} [DecidableEq ι] {a : ℕ} (s : Finset ι)
    (c : ι → Fin a) (f : ι → ℝ) :
    (∑ q : Fin a, ∑ i ∈ s.filter (fun i => c i = q), f i) = ∑ i ∈ s, f i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

def edgeExponent {J N : ℕ} (R : ℕ) (τ : ℝ) (η : LabelVector J N) (e : Finset (MeshIndex J)) : ℝ :=
  (2 * τ * (colorCount R : ℝ) / N) * universalConstant * nearScale R * (edgeParticleCount η e : ℝ)

theorem edgeExponent_nonneg {J N : ℕ} (R : ℕ) {τ : ℝ} (hτ : 0 ≤ τ)
    (η : LabelVector J N) (e : Finset (MeshIndex J)) : 0 ≤ edgeExponent R τ η e := by
  unfold edgeExponent
  have hC := universalConstant_pos.le
  have hL := nearScale_nonneg R
  positivity

theorem edgeExponent_le_half {J N R : ℕ} (hN : 0 < N) {β₀ τ t : ℝ}
    (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀) (ht : 0 ≤ t)
    (hcap : 24 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R * t ≤ 1)
    {η : LabelVector J N} (hη : OccupationCap t η) {e : Finset (MeshIndex J)}
    (he : e ∈ cellEdges R) : edgeExponent R τ η e ≤ 1 / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let D := (colorCount R : ℝ) * universalConstant * nearScale R
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) universalConstant_pos.le) (nearScale_nonneg R)
  have hc : 24 * β₀ * D * t ≤ 1 := by simpa only [D, mul_assoc] using hcap
  have hm := edgeParticleCount_le_cap ht hη he
  calc
    edgeExponent R τ η e = (2 * τ * D / N) * (edgeParticleCount η e : ℝ) := by
      unfold edgeExponent D
      ring
    _ ≤ (2 * τ * D / N) * (2 * t * N) :=
      mul_le_mul_of_nonneg_left hm (div_nonneg (by positivity) hNr.le)
    _ = 4 * τ * D * t := by field_simp; ring
    _ ≤ 4 * (3 * β₀) * D * t := by gcongr
    _ ≤ 1 / 2 := by linarith

/-- The exact graph square sum and source cap close the logarithmic color cost. -/
theorem average_edge_cost_le {J N R : ℕ} (hN : 0 < N) (hmesh : 8 * (R + 1) ≤ J)
    {β₀ τ t : ℝ} (hβ : 0 ≤ β₀) (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀) (ht : 0 ≤ t)
    (hcap : 24 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R * t ≤ 1)
    {η : LabelVector J N} (hη : OccupationCap t η) :
    (∑ e ∈ cellEdges R, (8 / 3 : ℝ) * edgeExponent R τ η e ^ 2) / (colorCount R : ℝ) ≤
      4 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hχ : (0 : ℝ) < colorCount R := by exact_mod_cast colorCount_pos R
  let D := (colorCount R : ℝ) * universalConstant * nearScale R
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hχ.le universalConstant_pos.le) (nearScale_nonneg R)
  have hc : 24 * β₀ * D * t ≤ 1 := by simpa only [D, mul_assoc] using hcap
  have hs : (∑ e ∈ cellEdges R, (edgeParticleCount η e : ℝ) ^ 2) ≤ t * (colorCount R : ℝ) * N ^ 2 := by
    simpa only [colorCount_cast] using sum_sq_edgeParticleCount hmesh ht hη
  have hex (e : Finset (MeshIndex J)) : edgeExponent R τ η e =
      (2 * τ * D / N) * (edgeParticleCount η e : ℝ) := by unfold edgeExponent D; ring
  calc
    _ = ((8 / 3 : ℝ) * (2 * τ * D / N) ^ 2 *
        (∑ e ∈ cellEdges R, (edgeParticleCount η e : ℝ) ^ 2)) / (colorCount R : ℝ) := by
      simp_rw [hex, mul_pow, ← mul_assoc]
      rw [← Finset.mul_sum]
    _ ≤ ((8 / 3 : ℝ) * (2 * τ * D / N) ^ 2 * (t * (colorCount R : ℝ) * N ^ 2)) /
        (colorCount R : ℝ) := by gcongr
    _ = (32 / 3 : ℝ) * τ ^ 2 * D ^ 2 * t := by field_simp; ring
    _ ≤ (32 / 3 : ℝ) * (3 * β₀) ^ 2 * D ^ 2 * t := by gcongr
    _ = 96 * (β₀ * D) ^ 2 * t := by ring
    _ ≤ 4 * β₀ * D := by
      have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * β₀ * D by positivity)
      nlinarith
    _ = _ := by dsimp [D]; ring

/-- The complete supplied NEAR-part bound on the actual reference product law.
All edge integrability, independence, moment, coloring and count inputs have
been derived above. Zero coupling and zero/single-particle edges are retained. -/
theorem near_exponential_bound {J N R : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hmesh : 8 * (R + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    {β₀ τ t : ℝ} (hβ : 0 ≤ β₀) (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀) (ht : 0 ≤ t)
    (hcap : 24 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R * t ≤ 1)
    (η : LabelVector J N) (hη : OccupationCap t η) :
    Integrable (fun X => Real.exp (2 * τ * nearResidualSum R μ η X)) (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, Real.exp (2 * τ * nearResidualSum R μ η X) ∂Measure.pi (fun i => μ (η i))) ≤
        Real.exp (4 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R) ∧
      Real.log (∫ X, Real.exp (2 * τ * nearResidualSum R μ η X) ∂Measure.pi (fun i => μ (η i))) ≤
        4 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R := by
  classical
  have hNp : 0 < N := by omega
  have hχp := colorCount_pos R
  obtain ⟨c, hc⟩ := exists_cell_edge_coloring hmesh
  change Finset (MeshIndex J) → Fin (colorCount R) at c
  let C := fun q : Fin (colorCount R) => (cellEdges R).filter (fun e => c e = q)
  let G := fun q X => (2 * τ / N) * ∑ e ∈ C q, edgeSum μ η e X
  let b := fun q => ∑ e ∈ C q, (8 / 3 : ℝ) * edgeExponent R τ η e ^ 2
  let a : ℝ := 2 * τ * (colorCount R : ℝ) / N
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hmember (q : Fin (colorCount R)) (e : Finset (MeshIndex J)) (he : e ∈ C q) : e ∈ cellEdges R :=
    (Finset.mem_filter.mp he).1
  have hG : ∀ q, Measurable (G q) := by
    intro q
    exact (Finset.measurable_sum (C q) (fun e he => measurable_edgeSum hJ hmesh μ hμ η e (hmember q e he))).const_mul _
  have hedge (e : Finset (MeshIndex J)) (he : e ∈ cellEdges R) :
      Integrable (fun X => Real.exp (a * edgeSum μ η e X)) (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, Real.exp (a * edgeSum μ η e X) ∂Measure.pi (fun i => μ (η i))) ≤
        Real.exp ((8 / 3 : ℝ) * edgeExponent R τ η e ^ 2) := by
    have hx := edgeExponent_le_half hNp hτ hτβ ht hcap hη he
    have hx0 := edgeExponent_nonneg R hτ η e
    have hh := edge_exponential_bound hJ hmesh μ hμ η e he ha (by
      change edgeExponent R τ η e < 1
      linarith)
    exact ⟨hh.1, hh.2.trans (rationalBound_le_exp hx0 hx)⟩
  have hcolor : ∀ q : Fin (colorCount R),
      Integrable (fun X => Real.exp ((colorCount R : ℝ) * G q X)) (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, Real.exp ((colorCount R : ℝ) * G q X) ∂Measure.pi (fun i => μ (η i))) ≤ Real.exp (b q) := by
    intro q
    have hd : ∀ e ∈ C q, ∀ d ∈ C q, e ≠ d → Disjoint (edgeParticles η e) (edgeParticles η d) := by
      intro e he d hd hne
      apply edgeParticles_disjoint η
      exact hc e (hmember q e he) d (hmember q d hd) hne
        ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hd).2.symm)
    have hh := exponential_disjoint_block_bound (fun i => μ (η i)) (C q) (edgeParticles η)
      (edgeSum μ η) (fun e he => measurable_edgeSum hJ hmesh μ hμ η e (hmember q e he))
      (fun e _ => edgeSum_depends_on_coordinates μ η e) hd a
      (fun e => (8 / 3 : ℝ) * edgeExponent R τ η e ^ 2)
      (fun e he => hedge e (hmember q e he))
    have heq : (fun X => Real.exp ((colorCount R : ℝ) * G q X)) =
        (fun X => Real.exp (a * ∑ e ∈ C q, edgeSum μ η e X)) := by
      funext X
      congr 1
      dsimp [G, a]
      ring
    rw [heq]
    exact hh
  have hsumG (X : Fin N → Torus) : (∑ q, G q X) = 2 * τ * nearResidualSum R μ η X := by
    dsimp [G, C]
    rw [← Finset.mul_sum, sum_color_fibers, ← sum_edgeSum_eq_near R μ η X]
    ring
  have hsumb : (∑ q, b q) = ∑ e ∈ cellEdges R, (8 / 3 : ℝ) * edgeExponent R τ η e ^ 2 :=
    sum_color_fibers (cellEdges R) c _
  have hcost : (∑ q, b q) / (colorCount R : ℝ) ≤
      4 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R := by
    rw [hsumb]
    exact average_edge_cost_le hNp hmesh hβ hτ hτβ ht hcap hη
  have hH := exponential_sum_holder (Measure.pi (fun i => μ (η i)))
    (Nat.succ_le_iff.mpr hχp) G hG b hcolor
  simp_rw [hsumG] at hH
  have hbound := hH.2.trans (Real.exp_le_exp.mpr hcost)
  refine ⟨hH.1, hbound, ?_⟩
  have hB0 : 0 ≤ 4 * β₀ * (colorCount R : ℝ) * universalConstant * nearScale R := by
    have hC := universalConstant_pos.le
    have hL := nearScale_nonneg R
    positivity
  by_cases hz : (∫ X, Real.exp (2 * τ * nearResidualSum R μ η X) ∂Measure.pi (fun i => μ (η i))) = 0
  · rw [hz, Real.log_zero]
    exact hB0
  · have hp : 0 < ∫ X, Real.exp (2 * τ * nearResidualSum R μ η X) ∂Measure.pi (fun i => μ (η i)) :=
      lt_of_le_of_ne (integral_nonneg fun X => (Real.exp_pos _).le) (Ne.symm hz)
    simpa only [Real.log_exp] using Real.log_le_log hp hbound

end PeriodicAttractiveLogGas.ResidualNearExponential
