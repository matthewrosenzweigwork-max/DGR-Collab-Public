import DGPS.SingularCounterexample.BarrierKernel
import SharpSymmetricLSI.Defs.D08_Gibbs

/-! Measurable, lower-bounded Hamiltonians use the frozen legacy Gibbs definitions. -/

open MeasureTheory
open scoped ENNReal

namespace DGPS.SingularCounterexample

/-- Measurability of pair potentials suffices for the frozen zero-confinement Hamiltonian. -/
theorem zero_hamiltonian_measurable {d N : ℕ}
    (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ)
    (hW : Measurable (Function.uncurry W)) :
    Measurable (SharpLSI.hamiltonian (fun _ => 0) W N) := by
  have hp (i j : Fin N) : Measurable (fun X : SharpLSI.Config N d => W (X i) (X j)) := by
    have hpair : Measurable (fun X : SharpLSI.Config N d => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hW.comp hpair
  unfold SharpLSI.hamiltonian
  exact (Finset.measurable_sum _ fun _ _ => measurable_const).add
    (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => hp i j))

/-- The ordered double sum and its `1/(2N)` factor are retained verbatim. -/
theorem zero_hamiltonian_lower_bound {d N : ℕ}
    (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ) {a : ℝ}
    (ha : ∀ x y, a ≤ W x y) (X : SharpLSI.Config N d) :
    1 / (2 * (N : ℝ)) * (∑ _i : Fin N, ∑ _j : Fin N, a) ≤
      SharpLSI.hamiltonian (fun _ => 0) W N X := by
  unfold SharpLSI.hamiltonian
  simp only [Finset.sum_const_zero, zero_add]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ha (X i) (X j))
    (by positivity)

private theorem integrable_exp_neg_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {H : Ω → ℝ} (hH : Measurable H)
    {a : ℝ} (ha : ∀ x, a ≤ H x) : Integrable (fun x => Real.exp (-H x)) μ := by
  refine (integrable_const (Real.exp (-a))).mono' hH.neg.exp.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (neg_le_neg (ha x))

/-- A lower bound suffices for positivity of the legacy real partition function. -/
theorem partitionFn_pos_of_hamiltonian_lower_bound {d N : ℕ}
    (V : SharpLSI.Torus d → ℝ) (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ)
    (hH : Measurable (SharpLSI.hamiltonian V W N)) {a : ℝ}
    (ha : ∀ X, a ≤ SharpLSI.hamiltonian V W N X) :
    0 < SharpLSI.partitionFn V W N := by
  exact integral_exp_pos (integrable_exp_neg_lower_bound volume hH ha)

/-- The singular case needs no upper bound on the Hamiltonian. -/
theorem partitionFn_integrable_of_hamiltonian_lower_bound {d N : ℕ}
    (V : SharpLSI.Torus d → ℝ) (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ)
    (hH : Measurable (SharpLSI.hamiltonian V W N)) {a : ℝ}
    (ha : ∀ X, a ≤ SharpLSI.hamiltonian V W N X) :
    Integrable (fun X => Real.exp (-SharpLSI.hamiltonian V W N X)) :=
  integrable_exp_neg_lower_bound volume hH ha

/-- Normalize the same Gibbs density as `SharpLSI.gibbs`, using only a Borel lower bound. -/
theorem gibbs_probability_of_hamiltonian_lower_bound {d N : ℕ}
    (V : SharpLSI.Torus d → ℝ) (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ)
    (hH : Measurable (SharpLSI.hamiltonian V W N)) {a : ℝ}
    (ha : ∀ X, a ≤ SharpLSI.hamiltonian V W N X) :
    IsProbabilityMeasure (SharpLSI.gibbs V W N) := by
  have hZ := partitionFn_pos_of_hamiltonian_lower_bound V W hH ha
  have hint := (partitionFn_integrable_of_hamiltonian_lower_bound V W hH ha).div_const
    (SharpLSI.partitionFn V W N)
  constructor
  unfold SharpLSI.gibbs
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X =>
      (div_pos (Real.exp_pos (-SharpLSI.hamiltonian V W N X)) hZ).le),
    integral_div]
  change ENNReal.ofReal (SharpLSI.partitionFn V W N / SharpLSI.partitionFn V W N) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

/-- The normalized density is bounded above; no lower density bound is asserted. -/
theorem gibbs_density_le_of_hamiltonian_lower_bound {d N : ℕ}
    (V : SharpLSI.Torus d → ℝ) (W : SharpLSI.Torus d → SharpLSI.Torus d → ℝ)
    (hH : Measurable (SharpLSI.hamiltonian V W N)) {a : ℝ}
    (ha : ∀ X, a ≤ SharpLSI.hamiltonian V W N X) (X : SharpLSI.Config N d) :
    ENNReal.ofReal (Real.exp (-SharpLSI.hamiltonian V W N X) / SharpLSI.partitionFn V W N) ≤
      ENNReal.ofReal (Real.exp (-a) / SharpLSI.partitionFn V W N) := by
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (ha X)))
    (partitionFn_pos_of_hamiltonian_lower_bound V W hH ha).le

/-- The baseline plus singular barrier at the frozen positive parameters. -/
noncomputable def perturbedKernel (B : BaselineKernel) (β η : ℝ) (x : Circle) : ℝ :=
  β * (B.g x + η * barrier x)

/-- The pair interaction is the perturbed kernel evaluated at the group difference. -/
noncomputable def perturbedInteraction (B : BaselineKernel) (β η : ℝ)
    (x y : Circle) : ℝ :=
  perturbedKernel B β η (x - y)

theorem perturbedKernel_measurable (B : BaselineKernel) (β η : ℝ) :
    Measurable (perturbedKernel B β η) := by
  exact measurable_const.mul (B.measurable_g.add (measurable_const.mul barrier_measurable))

theorem perturbedInteraction_measurable (B : BaselineKernel) (β η : ℝ) :
    Measurable (Function.uncurry (perturbedInteraction B β η)) := by
  have hd : Measurable (fun p : Circle × Circle => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  exact (perturbedKernel_measurable B β η).comp hd

theorem perturbedInteraction_even (B : BaselineKernel) (β η : ℝ)
    (x y : Circle) :
    perturbedInteraction B β η x y = perturbedInteraction B β η y x := by
  change perturbedKernel B β η (x - y) = perturbedKernel B β η (y - x)
  rw [show y - x = -(x - y) by abel]
  simp only [perturbedKernel, B.even_g, barrier_even]

@[simp] theorem perturbedInteraction_self (B : BaselineKernel) (β η : ℝ)
    (x : Circle) : perturbedInteraction B β η x x = 0 := by
  change perturbedKernel B β η (x - x) = 0
  simp [perturbedKernel, B.zero_g, barrier_zero]

theorem perturbedInteraction_borel_lower_bound (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    Measurable (Function.uncurry (perturbedInteraction B β η)) ∧
      ∃ C : ℝ, ∀ x y, -C ≤ perturbedInteraction B β η x y := by
  rcases B.bounded_g with ⟨G, _hG, hbound⟩
  refine ⟨perturbedInteraction_measurable B β η, ⟨β * G, ?_⟩⟩
  intro x y
  have hg : -G ≤ B.g (x - y) := (abs_le.mp (hbound (x - y))).1
  have hbar : 0 ≤ barrier (x - y) := barrier_nonneg _
  have hbase : -(β * G) ≤ β * B.g (x - y) := by
    calc
      -(β * G) = β * (-G) := by ring
      _ ≤ β * B.g (x - y) := mul_le_mul_of_nonneg_left hg hβ.le
  have hrep : 0 ≤ β * (η * barrier (x - y)) := by positivity
  change -(β * G) ≤ β * (B.g (x - y) + η * barrier (x - y))
  nlinarith

theorem perturbedInteraction_even_and_zero (B : BaselineKernel) (β η : ℝ)
    (x y : Circle) :
    perturbedInteraction B β η x y = perturbedInteraction B β η y x ∧
      perturbedInteraction B β η x x = 0 :=
  ⟨perturbedInteraction_even B β η x y, perturbedInteraction_self B β η x⟩

theorem singular_hamiltonian_measurable (B : BaselineKernel) {β η : ℝ}
    (_hβ : 0 < β) (_hη : 0 < η) (N : ℕ) :
    Measurable (SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N) := by
  exact zero_hamiltonian_measurable (perturbedInteraction B β η)
    (perturbedInteraction_measurable B β η)

theorem singular_hamiltonian_lower_bounded (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (_hN : 0 < N) :
    ∃ C : ℝ, ∀ X : SharpLSI.Config N 1,
      C ≤ SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X := by
  rcases perturbedInteraction_borel_lower_bound B hβ hη with ⟨_, ⟨c, hc⟩⟩
  let C : ℝ := 1 / (2 * (N : ℝ)) *
    (∑ _i : Fin N, ∑ _j : Fin N, (-c : ℝ))
  refine ⟨C, ?_⟩
  intro X
  have hgeneric := zero_hamiltonian_lower_bound (perturbedInteraction B β η) hc X
  change 1 / (2 * (N : ℝ)) * (∑ _i : Fin N, ∑ _j : Fin N, (-c : ℝ)) ≤
    SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X
  exact hgeneric

theorem singular_hamiltonian_measurable_and_lower_bounded (B : BaselineKernel)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    Measurable (SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N) ∧
      ∃ C : ℝ, ∀ X : SharpLSI.Config N 1,
        C ≤ SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X :=
  ⟨singular_hamiltonian_measurable B hβ hη N,
    singular_hamiltonian_lower_bounded B hβ hη hN⟩

theorem singular_partition_pos (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    0 < SharpLSI.partitionFn (fun _ => 0) (perturbedInteraction B β η) N := by
  rcases singular_hamiltonian_lower_bounded B hβ hη hN with ⟨a, ha⟩
  have hH := singular_hamiltonian_measurable B hβ hη N
  exact partitionFn_pos_of_hamiltonian_lower_bound (fun _ => 0)
    (perturbedInteraction B β η) hH ha

theorem singular_partition_finite (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    Integrable (fun X : SharpLSI.Config N 1 =>
      Real.exp (-SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X)) := by
  rcases singular_hamiltonian_lower_bounded B hβ hη hN with ⟨a, ha⟩
  exact partitionFn_integrable_of_hamiltonian_lower_bound (fun _ => 0)
    (perturbedInteraction B β η) (singular_hamiltonian_measurable B hβ hη N) ha

theorem singular_gibbs_isProbabilityMeasure (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N) := by
  rcases singular_hamiltonian_lower_bounded B hβ hη hN with ⟨a, ha⟩
  have hH := singular_hamiltonian_measurable B hβ hη N
  exact gibbs_probability_of_hamiltonian_lower_bound (fun _ => 0)
    (perturbedInteraction B β η) hH ha

theorem singular_gibbs_density_upper_bound (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    ∃ C : ℝ, ∀ X : SharpLSI.Config N 1,
      ENNReal.ofReal (Real.exp (-SharpLSI.hamiltonian (fun _ => 0)
        (perturbedInteraction B β η) N X) /
          SharpLSI.partitionFn (fun _ => 0) (perturbedInteraction B β η) N) ≤
        ENNReal.ofReal C := by
  rcases singular_hamiltonian_lower_bounded B hβ hη hN with ⟨a, ha⟩
  have hH := singular_hamiltonian_measurable B hβ hη N
  refine ⟨Real.exp (-a) / SharpLSI.partitionFn (fun _ => 0)
    (perturbedInteraction B β η) N, ?_⟩
  intro X
  exact gibbs_density_le_of_hamiltonian_lower_bound (fun _ => 0)
    (perturbedInteraction B β η) hH ha X

end DGPS.SingularCounterexample
