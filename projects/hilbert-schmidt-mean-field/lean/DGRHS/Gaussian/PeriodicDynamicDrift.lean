import DGRHS.Gaussian.PeriodicDynamicCalculus
import DGRHS.Gaussian.PeriodicDynamicBase
import DGRHS.Gaussian.PeriodicBoundedBackgroundL2
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
Packet P11c, unit 3 (part 1): the backward-adjoint algebra of Proposition 8.2 (`prop:finiteNAdjointDuality`,
TeX 3859-3877, proof 3879-3930) on the torus, for an abstract periodic interaction force `F`.

`PeriodicForceData` records exactly the properties of the gradient of the periodic kernel that the
proof of Proposition 8.2 uses: measurability, oddness, and a uniform section bound of the `n = 1`
transport kernel `⟪F(x-y), v x - v y⟫` for Lipschitz `v` (both the Riesz and the LOG forces satisfy it;
see `PeriodicRieszForceData`, `PeriodicLogForceData`).  The proof is kernel-independent: with
`h(x,y) = ⟪F(x-y), ∇q(x) - ∇q(y)⟫` and the backward equation `∂_r q + β⁻¹ Δ q = ∫ h(·,y) dμ`, the
instantaneous drift satisfies `empirical drift - mean drift = -(1/2) A_1(∇q)`.
-/

noncomputable section
open MeasureTheory Laplacian Set
open scoped NNReal RealInnerProductSpace ENNReal BigOperators Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The properties of a periodic interaction force used by the dynamical statements. -/
structure PeriodicForceData (ι : Type u) [Fintype ι] [Nonempty ι] where
  F : PeriodicTorus ι → EuclideanSpace ℝ ι
  measurable : Measurable F
  odd : ∀ z, F (-z) = -F z
  section_bound : ∀ K : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : PeriodicTorus ι → EuclideanSpace ℝ ι}, LipschitzWith K v → ∀ x : PeriodicTorus ι,
      Integrable (fun y => periodicForcePair F v (x, y)) (periodicHaar ι) ∧
      ∫ y, |periodicForcePair F v (x, y)| ∂periodicHaar ι ≤ C

namespace PeriodicForceData
variable (D : PeriodicForceData ι)

lemma F_zero : D.F 0 = 0 := by
  have h := D.odd 0
  rw [neg_zero] at h
  have h2 : ⟪D.F 0, D.F 0⟫ = ⟪D.F 0, -D.F 0⟫ := by rw [← h]
  rw [inner_neg_right] at h2
  have h3 : ⟪D.F 0, D.F 0⟫ = 0 := by linarith
  exact inner_self_eq_zero.mp h3

lemma pair_swap (v : PeriodicTorus ι → E) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicForcePair D.F v p.swap = periodicForcePair D.F v p := by
  unfold periodicForcePair
  have h1 : p.swap.1 - p.swap.2 = -(p.1 - p.2) := by simp
  rw [Prod.fst_swap, Prod.snd_swap, show p.2 - p.1 = -(p.1 - p.2) by abel, D.odd]
  rw [show v p.2 - v p.1 = -(v p.1 - v p.2) by abel, inner_neg_left, inner_neg_right, neg_neg]

lemma pair_diag (v : PeriodicTorus ι → E) (x : PeriodicTorus ι) :
    periodicForcePair D.F v (x, x) = 0 := by
  simp [periodicForcePair, D.F_zero]

lemma measurable_pair {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    Measurable (periodicForcePair D.F v) := by
  unfold periodicForcePair
  have hF : Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι => D.F (p.1 - p.2)) :=
    D.measurable.comp (measurable_fst.sub measurable_snd)
  have hv' : Measurable v := hv.continuous.measurable
  exact hF.inner ((hv'.comp measurable_fst).sub (hv'.comp measurable_snd))

/-- Section integrability against a capped density. -/
lemma section_density (K : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ x : PeriodicTorus ι, Integrable (fun y => periodicForcePair D.F v (x, y))
        (periodicCappedDensityMeasure ρ) ∧
      ∫ y, |periodicForcePair D.F v (x, y)| ∂periodicCappedDensityMeasure ρ ≤ M * C := by
  obtain ⟨C, hC, hb⟩ := D.section_bound K
  refine ⟨C, hC, ?_⟩
  intro v hv ρ M hM hρ x
  obtain ⟨hi, hbound⟩ := hb hv x
  have hle := periodicCappedDensityMeasure_le ρ M hρ
  have hi' : Integrable (fun y => periodicForcePair D.F v (x, y))
      (ENNReal.ofReal M • periodicHaar ι) := hi.smul_measure ENNReal.ofReal_ne_top
  refine ⟨hi'.mono_measure hle, ?_⟩
  calc ∫ y, |periodicForcePair D.F v (x, y)| ∂periodicCappedDensityMeasure ρ
      ≤ ∫ y, |periodicForcePair D.F v (x, y)| ∂(ENNReal.ofReal M • periodicHaar ι) :=
        integral_mono_measure hle (Filter.Eventually.of_forall fun _ => abs_nonneg _) hi'.abs
    _ = M * ∫ y, |periodicForcePair D.F v (x, y)| ∂periodicHaar ι := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hM]; rfl
    _ ≤ M * C := mul_le_mul_of_nonneg_left hbound hM

/-- Pair integrability against a capped density. -/
lemma pair_density_integrable (K : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      Integrable (periodicForcePair D.F v)
        ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ∧
      |∫ p, periodicForcePair D.F v p
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)| ≤ M * C := by
  obtain ⟨C, hC, hs⟩ := D.section_density K
  refine ⟨C, hC, ?_⟩
  intro v hv ρ M hM hρ hprob
  let μ := periodicCappedDensityMeasure ρ
  have hm := D.measurable_pair hv
  have hi : Integrable (periodicForcePair D.F v) (μ.prod μ) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun x => (hs hv ρ M hM hρ x).1, ?_⟩
    refine (integrable_const (M * C)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · have := (hs hv ρ M hM hρ x).2
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs, Function.uncurry_apply_pair] using this
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have : ∀ x, |∫ y, periodicForcePair D.F v (x, y) ∂μ| ≤ M * C := fun x =>
    (abs_integral_le_integral_abs).trans (hs hv ρ M hM hρ x).2
  calc |∫ x, ∫ y, periodicForcePair D.F v (x, y) ∂μ ∂μ| ≤ ∫ x, |∫ y, periodicForcePair D.F v (x, y) ∂μ| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, M * C ∂μ := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall this)
    _ = M * C := by simp

end PeriodicForceData

/-- The double sum of `⟪F(x_i - x_j), v x_i⟫` is half the sum of the pair kernel. -/
lemma periodic_force_double_sum (D : PeriodicForceData ι) (N : ℕ) (x : Fin N → PeriodicTorus ι)
    (v : PeriodicTorus ι → E) :
    ∑ i : Fin N, ∑ j : Fin N, ⟪D.F (x i - x j), v (x i)⟫ =
      (1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, periodicForcePair D.F v (x i, x j) := by
  have h1 : ∀ i j : Fin N, periodicForcePair D.F v (x i, x j) =
      ⟪D.F (x i - x j), v (x i)⟫ + ⟪D.F (x j - x i), v (x j)⟫ := by
    intro i j
    unfold periodicForcePair
    rw [inner_sub_right, show x j - x i = -(x i - x j) by abel, D.odd, inner_neg_left]
    ring
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => ⟪D.F (x j - x i), v (x j)⟫)]
  ring

/-- The off-diagonal sum of the pair kernel is its full double sum (the diagonal vanishes). -/
lemma periodic_offDiagonalSum_pair (D : PeriodicForceData ι) (N : ℕ) (x : Fin N → PeriodicTorus ι)
    (v : PeriodicTorus ι → E) :
    DGRHS.CanonicalVariance.offDiagonalSum (periodicForcePair D.F v) x =
      ∑ i : Fin N, ∑ j : Fin N, periodicForcePair D.F v (x i, x j) := by
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  have hp := Finset.sum_union (f := fun p : Fin N × Fin N => periodicForcePair D.F v (x p.1, x p.2))
    (Finset.disjoint_diag_offDiag (Finset.univ : Finset (Fin N)))
  rw [Finset.diag_union_offDiag, Finset.sum_product] at hp
  have hz : (∑ p ∈ (Finset.univ : Finset (Fin N)).diag,
      periodicForcePair D.F v (x p.1, x p.2)) = 0 := by
    simp [Finset.diag, D.pair_diag]
  rw [hz, zero_add] at hp
  exact hp.symm

/-- The backward-adjoint algebra: empirical drift minus mean drift equals `-(1/2) A_1`. -/
theorem periodic_drift_algebra (D : PeriodicForceData ι) {K : ℝ≥0} {v : PeriodicTorus ι → E}
    (hv : LipschitzWith K v) (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (hsec : ∀ z, Integrable (fun y => periodicForcePair D.F v (z, y)) μ)
    (hpair : Integrable (periodicForcePair D.F v) (μ.prod μ))
    (L : PeriodicTorus ι → ℝ) (hL : ∀ z, L z = ∫ y, periodicForcePair D.F v (z, y) ∂μ)
    (N : ℕ) (hN : 0 < N) (x : Fin N → PeriodicTorus ι) :
    ((∫ z, L z ∂sourceRieszLocalEmpiricalLaw N x) -
        ((N : ℝ) ^ 2)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, ⟪D.F (x i - x j), v (x i)⟫) -
      ((∫ z, L z ∂μ) - (1 / 2 : ℝ) * ∫ p, periodicForcePair D.F v p ∂μ.prod μ) =
    -(1 / 2 : ℝ) * sourceTransportEnergy μ (periodicForcePair D.F v) N x := by
  have hsym : ∀ a b, periodicForcePair D.F v (a, b) = periodicForcePair D.F v (b, a) := fun a b =>
    (D.pair_swap v (a, b)).symm
  rw [sourceTransportEnergy_raw μ (periodicForcePair D.F v) hsym N hN x,
    periodic_offDiagonalSum_pair D N x v]
  have hdbl := periodic_force_double_sum D N x v
  rw [hdbl, integral_sourceRieszLocalEmpiricalLaw]
  have hμ : (∫ z, L z ∂μ) = ∫ p, periodicForcePair D.F v p ∂μ.prod μ := by
    rw [integral_prod _ hpair]
    exact integral_congr_ae (Filter.Eventually.of_forall hL)
  rw [hμ]
  have hpot : ∀ i, DGRHS.potential μ (fun a b => periodicForcePair D.F v (a, b)) (x i) = L (x i) :=
    fun i => (hL (x i)).symm
  simp_rw [hpot]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.PeriodicForceData.section_density
#print axioms DGRHS.Periodic.PeriodicForceData.pair_density_integrable
#print axioms DGRHS.Periodic.periodic_drift_algebra
