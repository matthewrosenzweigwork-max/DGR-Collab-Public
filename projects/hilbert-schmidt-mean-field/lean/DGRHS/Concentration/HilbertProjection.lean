import DGRHS.Concentration.HilbertMoments
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Set.Finite.Lattice

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped InnerProductSpace Topology
namespace DGRHS.Concentration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

omit [CompleteSpace H] in
lemma projection_approximation_error (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (x a : H) (ha : a ∈ K) : ‖K.starProjection x-x‖ ≤ 2*‖x-a‖ := by
  have hfix : K.starProjection a=a := K.starProjection_eq_self_iff.mpr ha
  calc
    _ = ‖K.starProjection (x-a)+(a-x)‖ := by rw [map_sub,hfix]; congr 1; abel
    _ ≤ ‖K.starProjection (x-a)‖+‖a-x‖ := norm_add_le _ _
    _ ≤ ‖x-a‖+‖a-x‖ := add_le_add (K.norm_starProjection_apply_le _) le_rfl
    _ = _ := by rw [norm_sub_rev a x]; ring

/-- Nested finite spans built from the actual simple approximations, with no ambient separability. -/
def hilbertApproximationSubspace (μ : Fin n → Measure Ω) (Z : Fin n → Ω → H)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) (r : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (⋃ s : Fin (r+1), ⋃ i : Fin n,
    Set.range ((hZ i).stronglyMeasurable_mk.approx s.val : Ω → H))

instance hilbertApproximationSubspace_finiteDimensional
    (μ : Fin n → Measure Ω) (Z : Fin n → Ω → H)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) (r : ℕ) :
    FiniteDimensional ℝ (hilbertApproximationSubspace μ Z hZ r) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_iUnion fun s : Fin (r+1) ↦
    Set.finite_iUnion fun i : Fin n ↦ ((hZ i).stronglyMeasurable_mk.approx s.val).finite_range)

omit [CompleteSpace H] in
lemma hilbert_approximation_mem
    (μ : Fin n → Measure Ω) (Z : Fin n → Ω → H)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) (r : ℕ) (i : Fin n) (x : Ω) :
    (hZ i).stronglyMeasurable_mk.approx r x ∈ hilbertApproximationSubspace μ Z hZ r := by
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨⟨r,Nat.lt_succ_self r⟩,Set.mem_iUnion.mpr ⟨i,⟨x,rfl⟩⟩⟩

omit [CompleteSpace H] in
lemma hilbert_approximation_subspace_mono
    (μ : Fin n → Measure Ω) (Z : Fin n → Ω → H)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) {r s : ℕ} (hrs : r ≤ s) :
    hilbertApproximationSubspace μ Z hZ r ≤ hilbertApproximationSubspace μ Z hZ s := by
  apply Submodule.span_mono
  intro x hx
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨⟨a.val,by omega⟩,Set.mem_iUnion.mpr ⟨i,hi⟩⟩

omit [CompleteSpace H] in
lemma hilbert_projection_tendsto_ae
    (μ : Fin n → Measure Ω) (Z : Fin n → Ω → H)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) (i : Fin n) :
    ∀ᵐ x ∂μ i, Tendsto (fun r ↦ (hilbertApproximationSubspace μ Z hZ r).starProjection (Z i x))
      atTop (𝓝 (Z i x)) := by
  filter_upwards [(hZ i).ae_eq_mk] with x hx
  have ha := (hZ i).stronglyMeasurable_mk.tendsto_approx x
  rw [← hx] at ha
  have hb : Tendsto (fun r ↦ 2*‖Z i x-(hZ i).stronglyMeasurable_mk.approx r x‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero,norm_sub_rev] using (ha.sub_const (Z i x)).norm.const_mul 2
  have hh := squeeze_zero (fun r ↦ norm_nonneg ((hilbertApproximationSubspace μ Z hZ r).starProjection (Z i x)-Z i x))
    (fun r ↦ projection_approximation_error _ (Z i x) _ (hilbert_approximation_mem μ Z hZ r i x)) hb
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hh

/-- A real finite-rank projection preserves every original structural moment input. -/
theorem projected_hilbert_integer_moment (K : Submodule ℝ H) [FiniteDimensional ℝ K]
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B C D : ℝ) (hBpos : 0 ≤ B) (hCpos : 0 ≤ C) (hDpos : 0 ≤ D)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hTrace : (∑ i, ∫ x, ‖Z i x‖^2 ∂μ i) ≤ C^2)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, (empiricalNormOnProduct (fun i x ↦ K.orthogonalProjectionOnto (Z i x)) ω)^m ∂Measure.pi μ)^(1/(m : ℝ)) ≤
      12*(C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B) := by
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let Y := fun i x ↦ K.orthogonalProjectionOnto (Z i x)
  have hY : ∀ i, AEStronglyMeasurable (Y i) (μ i) := fun i ↦
    K.orthogonalProjectionOnto.continuous.comp_aestronglyMeasurable (hZ i)
  have hYb : ∀ i, ∀ᵐ x ∂μ i, ‖Y i x‖ ≤ B := fun i ↦ (hB i).mono fun x hx ↦
    (K.norm_orthogonalProjectionOnto_apply_le _).trans hx
  have hYm : ∀ i, ∫ x, Y i x ∂μ i = 0 := by
    intro i
    rw [K.orthogonalProjectionOnto.integral_comp_comm (bounded_hilbert_integrable (hZ i) (hB i)),hMean i]
    exact map_zero _
  have hYtr : (∑ i, ∫ x, ‖Y i x‖^2 ∂μ i) ≤ C^2 := by
    apply le_trans _ hTrace
    apply Finset.sum_le_sum
    intro i _
    have hleft := bounded_square (hY i).norm ((hYb i).mono fun x hx ↦ by simpa using hx)
    have hright := bounded_square (hZ i).norm ((hB i).mono fun x hx ↦ by simpa using hx)
    apply integral_mono (integrable_of_ae_abs_le hleft.1 hleft.2) (integrable_of_ae_abs_le hright.1 hright.2)
    intro x
    nlinarith [K.norm_orthogonalProjectionOnto_apply_le (Z i x),norm_nonneg (Y i x),norm_nonneg (Z i x)]
  have hYw : ∀ u : K, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Y i x))^2 ∂μ i) ≤ D^2 := by
    intro u hu
    simpa only [Y,K.inner_orthogonalProjectionOnto_eq_of_mem_left] using hWeak (u : H) hu
  exact finite_hilbert_integer_moment μ Y B C D hBpos hCpos hDpos hY hYb hYm hYtr hYw m hm

#print axioms DGRHS.Concentration.projection_approximation_error
#print axioms DGRHS.Concentration.hilbert_projection_tendsto_ae
#print axioms DGRHS.Concentration.projected_hilbert_integer_moment
end DGRHS.Concentration
