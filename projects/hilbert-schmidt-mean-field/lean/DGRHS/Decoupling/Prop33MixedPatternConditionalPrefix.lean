import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Pi
import DGRHS.Decoupling.HeterogeneousProduct
/-!
Records-only, uncompiled Lean unit: the conditional product-integral composition
in the all-order Prop. 3.3 induction, with lower-order hypotheses stated on
the explicit source section-kernel diagonals and after those definitions. The lower-order hypotheses are applied
only to the two explicit finite section-kernel families below; no order-k tail
bound is assumed.

For a source application, P is the finite ordered-injective k-tuple type,
A and B are the ordered p- and q-tuple types obtained by restricting the slot
pattern, and `left`/`right` are those restriction maps. The source family is
`F t u v`, with u and v the values in the two slot blocks. The kernel builders
sum over the fibers of those restriction maps, so they preserve every ordered
coefficient, including the cross-block disjointness constraint encoded by P.
The source-specific slot restrictions/evaluators instantiate these parameters.

The measurable-operation boundary is made explicit in the section 3c helper:
measurability of each summand plus `[MeasurableAdd₂ E]` and measurable norm
makes each finite section event measurable. This is additional well-definedness
data for arbitrary nonseparable Borel Banach targets, as recorded in the
Prop. 3.3 measurability audit.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Decoupling.Prop33

/-- Ordered injective k-tuples of indices in `Fin n`, matching the source
summation over distinct ordered indices. -/
abbrev OrderedTuple (n k : ℕ) := {t : Fin k → Fin n // Function.Injective t}

variable {P A B X Y Z W E : Type*} [NormedAddCommGroup E]
variable [Fintype P] [Fintype A] [Fintype B]
variable [DecidableEq P] [DecidableEq A] [DecidableEq B]

/-- First section kernel: fix the B-block data and collect every original
ordered term whose A-block tuple is `a`. -/
def leftSectionKernel (left : P → A) (F : P → X → Y → E)
    (y : Y) (a : A) (x : X) : E :=
  ∑ p ∈ Finset.univ.filter (fun p => left p = a), F p x y

/-- Second section kernel: fix the already-decoupled A-block data and collect
every original ordered term whose B-block tuple is `b`. -/
def rightSectionKernel (right : P → B) (F : P → X → Y → E)
    (x : X) (b : B) (y : Y) : E :=
  ∑ p ∈ Finset.univ.filter (fun p => right p = b), F p x y

/-- The first section-kernel family sums back to the original finite statistic.
For the source instantiation, `left p` is the ordered tuple of indices in the
true slots of p. -/
theorem sum_leftSectionKernel (left : P → A) (F : P → X → Y → E)
    (x : X) (y : Y) :
    (∑ a, leftSectionKernel left F y a x) = ∑ p, F p x y := by
  classical
  unfold leftSectionKernel
  have hmap : ∀ p ∈ (Finset.univ : Finset P), left p ∈ (Finset.univ : Finset A) := by
    intro p hp
    simp
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => F p x y)]

/-- The second section-kernel family also sums back to the same statistic.
Here `right p` is the ordered tuple of indices in the false slots. -/
theorem sum_rightSectionKernel (right : P → B) (F : P → X → Y → E)
    (x : X) (y : Y) :
    (∑ b, rightSectionKernel right F x b y) = ∑ p, F p x y := by
  classical
  unfold rightSectionKernel
  have hmap : ∀ p ∈ (Finset.univ : Finset P), right p ∈ (Finset.univ : Finset B) := by
    intro p hp
    simp
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => F p x y)]

/-- Section event closure used by conditional induction (the Prop. 3.3 event
3c boundary). A measurable finite sum remains measurable after fixing the
retained parameter. -/
lemma measurable_fixed_finite_section
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace E]
    [MeasurableAdd₂ E]
    (left : P → A) (F : P → X → Y → E)
    (hF : ∀ p, Measurable (fun z : X × Y => F p z.1 z.2))
    (y : Y) (a : A) :
    Measurable (fun x => leftSectionKernel left F y a x) := by
  classical
  unfold leftSectionKernel
  apply Finset.measurable_sum
  intro p hp
  exact (hF p).comp (measurable_id.prodMk measurable_const)

lemma measurable_fixed_finite_section_right
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace E]
    [MeasurableAdd₂ E]
    (right : P → B) (F : P → X → Y → E)
    (hF : ∀ p, Measurable (fun z : X × Y => F p z.1 z.2))
    (x : X) (b : B) :
    Measurable (fun y => rightSectionKernel right F x b y) := by
  classical
  unfold rightSectionKernel
  apply Finset.measurable_sum
  intro p hp
  exact (hF p).comp (measurable_const.prodMk measurable_id)

/-- Integrate a family of fiberwise bounds over the second coordinate. This is
the sectionwise lower-order induction step from an original mixed statistic to
a statistic decoupled in its first block. -/
lemma measure_prod_fiberwise_bound_symm
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {s : Set (α × β)} {t : Set (γ × β)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hfiber : ∀ y, μ ((fun x => (x, y)) ⁻¹' s) ≤
      c * ρ ((fun z => (z, y)) ⁻¹' t)) :
    (μ.prod ν) s ≤ c * (ρ.prod ν) t := by
  rw [Measure.prod_apply_symm hs, Measure.prod_apply_symm ht]
  calc
    (∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν) ≤
        ∫⁻ y, c * ρ ((fun z => (z, y)) ⁻¹' t) ∂ν :=
      lintegral_mono hfiber
    _ = c * ∫⁻ y, ρ ((fun z => (z, y)) ⁻¹' t) ∂ν :=
      lintegral_const_mul' _ _ hc

/-- Integrate a family of fiberwise bounds over the first coordinate. This is
the second lower-order application, which decouples the remaining repeated-copy
block while keeping the already-decoupled block fixed. -/
lemma measure_prod_fiberwise_bound
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {s : Set (α × β)} {t : Set (α × γ)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hfiber : ∀ x, ν ((fun y => (x, y)) ⁻¹' s) ≤
      c * ρ ((fun z => (x, z)) ⁻¹' t)) :
    (μ.prod ν) s ≤ c * (μ.prod ρ) t := by
  rw [Measure.prod_apply hs, Measure.prod_apply ht]
  calc
    (∫⁻ x, ν ((fun y => (x, y)) ⁻¹' s) ∂μ) ≤
        ∫⁻ x, c * ρ ((fun z => (x, z)) ⁻¹' t) ∂μ :=
      lintegral_mono hfiber
    _ = c * ∫⁻ x, ρ ((fun z => (x, z)) ⁻¹' t) ∂μ :=
      lintegral_const_mul' _ _ hc

/-- Exact product-law composition of the two conditional lower-order
inequalities. `hp` is the order-p bound applied to `leftSectionKernel`; `hq`
is the order-q bound applied to `rightSectionKernel` after the first block has
been independently copied. The RHS threshold is written as `t / Cp` so that
it is exactly the result of applying the order-q theorem at that threshold.
The source form `t ≤ Cp * (Cq * ‖V‖)` follows by real arithmetic and Cp>0. -/
theorem mixedPattern_conditional_induction
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    [MeasurableAdd₂ E]
    {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {σ : Measure W}
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ]
    (U : X × Y → E) (H : Z × Y → E) (V : Z × W → E)
    (hU : Measurable U) (hH : Measurable H) (hV : Measurable V)
    (t Cp Cq : ℝ) (hCp : 0 < Cp) (hCq : 0 < Cq)
    (hIHp : ∀ y,
      μ {x | t ≤ ‖U (x, y)‖} ≤
        ENNReal.ofReal Cp * ρ {z | t ≤ Cp * ‖H (z, y)‖})
    (hIHq : ∀ z,
      ν {y | t ≤ Cp * ‖H (z, y)‖} ≤
        ENNReal.ofReal Cq * σ {w | t / Cp ≤ Cq * ‖V (z, w)‖}) :
    (μ.prod ν) {xy | t ≤ ‖U xy‖} ≤
      (ENNReal.ofReal Cp * ENNReal.ofReal Cq) *
        (ρ.prod σ) {zw | t / Cp ≤ Cq * ‖V zw‖} := by
  have hUset : MeasurableSet {xy : X × Y | t ≤ ‖U xy‖} := by
    exact measurableSet_le measurable_const (Measurable.norm hU)
  have hHset : MeasurableSet {zy : Z × Y | t ≤ Cp * ‖H zy‖} := by
    have hnorm : Measurable (fun zy : Z × Y => Cp * ‖H zy‖) :=
      measurable_const.mul (Measurable.norm hH)
    exact measurableSet_le measurable_const hnorm
  have hVset : MeasurableSet {zw : Z × W | t / Cp ≤ Cq * ‖V zw‖} := by
    have hnorm : Measurable (fun zw : Z × W => Cq * ‖V zw‖) :=
      measurable_const.mul (Measurable.norm hV)
    exact measurableSet_le measurable_const hnorm
  have hCpTop : ENNReal.ofReal Cp ≠ ∞ := ENNReal.ofReal_ne_top
  have hCqTop : ENNReal.ofReal Cq ≠ ∞ := ENNReal.ofReal_ne_top
  have hFirst := measure_prod_fiberwise_bound_symm (μ := μ) (ν := ν) (ρ := ρ)
    hUset hHset (ENNReal.ofReal Cp) hCpTop hIHp
  have hSecond := measure_prod_fiberwise_bound (μ := ρ) (ν := ν) (ρ := σ)
    hHset hVset (ENNReal.ofReal Cq) hCqTop hIHq
  calc
    (μ.prod ν) {xy | t ≤ ‖U xy‖} ≤
        ENNReal.ofReal Cp * (ρ.prod ν) {zy | t ≤ Cp * ‖H zy‖} := hFirst
    _ ≤ ENNReal.ofReal Cp *
        (ENNReal.ofReal Cq * (ρ.prod σ) {zw | t / Cp ≤ Cq * ‖V zw‖}) :=
      mul_le_mul_of_nonneg_left hSecond zero_le
    _ = (ENNReal.ofReal Cp * ENNReal.ofReal Cq) *
        (ρ.prod σ) {zw | t / Cp ≤ Cq * ‖V zw‖} := by rw [mul_assoc]

end DGRHS.Decoupling.Prop33
end

set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Decoupling.Prop33.sum_leftSectionKernel
#print axioms DGRHS.Decoupling.Prop33.sum_leftSectionKernel
#check @DGRHS.Decoupling.Prop33.sum_rightSectionKernel
#print axioms DGRHS.Decoupling.Prop33.sum_rightSectionKernel
#check @DGRHS.Decoupling.Prop33.mixedPattern_conditional_induction
#print axioms DGRHS.Decoupling.Prop33.mixedPattern_conditional_induction
