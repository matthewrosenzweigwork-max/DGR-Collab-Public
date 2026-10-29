import LeanResearch.PeriodicAttractiveLogGas.GreenLocalWeak
import LeanResearch.PeriodicAttractiveLogGas.QuadraticPotential
import LeanResearch.PeriodicAttractiveLogGas.WeylRegularity

/-! Weak harmonic residuals and actual smooth representatives of the constructed
Green lift. The local logarithmic residual includes the pole in its domain;
the global quadratic residual is considered only off the integer lattice. -/

noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology ContDiff Laplacian

namespace PeriodicAttractiveLogGas

def greenLogResidual (x : PlanarSpace) : ℝ :=
  greenLift x - planarLogKernel x - planarGreenQuadratic x

def greenQuadraticResidual (x : PlanarSpace) : ℝ := greenLift x - planarGreenQuadratic x

theorem locallyIntegrable_greenLogResidual : LocallyIntegrable greenLogResidual volume :=
  (locallyIntegrable_greenLift.sub locallyIntegrable_planarLogKernel).sub
    contDiff_planarGreenQuadratic.continuous.locallyIntegrable

theorem locallyIntegrable_greenQuadraticResidual :
    LocallyIntegrable greenQuadraticResidual volume :=
  locallyIntegrable_greenLift.sub contDiff_planarGreenQuadratic.continuous.locallyIntegrable

/-- Cancellation of the delta mass and the constant term holds for every local
test, including tests that do not vanish at the pole. -/
theorem weaklyHarmonic_greenLogResidual :
    PlanarWeaklyHarmonicOn (euclideanOpenBox (centeredBoxAnchor 0)) greenLogResidual := by
  refine ⟨locallyIntegrable_greenLogResidual.locallyIntegrableOn _, ?_⟩
  intro φ hφ hφc hφs
  have hs := hφs.trans (euclideanOpenBox_subset_fundamentalBox (centeredBoxAnchor 0))
  have hzero := euclideanOpenBox_subset_fundamentalBox (centeredBoxAnchor 0)
    (mem_centeredOpenBox (0 : PlanarSpace))
  have hG := greenLift_weak_equation_box_zero hφ hφc hs hzero
  have hL := integral_planarLogKernel_mul_neg_laplacian (hφ.of_le (by simp)) hφc
  have hQ := integral_planarGreenQuadratic_mul_neg_laplacian hφ hφc
  have hiG := integrable_greenLift_mul_neg_laplacian hφ hφc
  have hiL := integrable_planarLogKernel_mul_neg_laplacian (hφ.of_le (by simp)) hφc
  have hiQ := integrable_planarGreenQuadratic_mul_neg_laplacian hφ hφc
  have hiGL : Integrable (fun x ↦ greenLift x * -Δ φ x -
      planarLogKernel x * -Δ φ x) volume := hiG.sub hiL
  have hcancel : (∫ x, greenLogResidual x * -Δ φ x) = 0 := by
    simp only [greenLogResidual, sub_mul]
    rw [integral_sub hiGL hiQ, integral_sub hiG hiL, hG, hL, hQ]
    ring
  have heq : (fun x ↦ greenLogResidual x * Δ φ x) =
      (fun x ↦ -(greenLogResidual x * -Δ φ x)) := by
    funext x
    simp only [mul_neg, neg_neg]
  rw [heq, integral_neg, hcancel, neg_zero]

/-- A smooth harmonic remainder exists on the entire open fundamental chart. -/
theorem exists_greenLogRemainder :
    ∃ h : PlanarSpace → ℝ,
      ContDiffOn ℝ ∞ h (euclideanOpenBox (centeredBoxAnchor 0)) ∧
      HarmonicOnNhd h (euclideanOpenBox (centeredBoxAnchor 0)) ∧
      greenLogResidual =ᵐ[volume.restrict (euclideanOpenBox (centeredBoxAnchor 0))] h :=
  exists_smooth_harmonic_representative_open weaklyHarmonic_greenLogResidual
    (isOpen_euclideanOpenBox _)

/-- Away from all lattice poles, the quadratic subtraction is weakly harmonic
on each open fundamental-box chart. -/
theorem weaklyHarmonic_greenQuadraticResidual_chart (a : PlanarSpace) :
    PlanarWeaklyHarmonicOn (euclideanOpenBox a ∩ offIntegerLattice)
      greenQuadraticResidual := by
  refine ⟨locallyIntegrable_greenQuadraticResidual.locallyIntegrableOn _, ?_⟩
  intro φ hφ hφc hφs
  have hs : tsupport φ ⊆ euclideanFundamentalBox a :=
    hφs.trans (inter_subset_left.trans (euclideanOpenBox_subset_fundamentalBox a))
  have ha : tsupport φ ⊆ offIntegerLattice := hφs.trans inter_subset_right
  have hG := greenLift_weak_equation_box_away hφ hφc hs ha
  have hQ := integral_planarGreenQuadratic_mul_neg_laplacian hφ hφc
  have hiG := integrable_greenLift_mul_neg_laplacian hφ hφc
  have hiQ := integrable_planarGreenQuadratic_mul_neg_laplacian hφ hφc
  have hcancel : (∫ x, greenQuadraticResidual x * -Δ φ x) = 0 := by
    simp only [greenQuadraticResidual, sub_mul]
    rw [integral_sub hiG hiQ, hG, hQ, sub_self]
  have heq : (fun x ↦ greenQuadraticResidual x * Δ φ x) =
      (fun x ↦ -(greenQuadraticResidual x * -Δ φ x)) := by
    funext x
    simp only [mul_neg, neg_neg]
  rw [heq, integral_neg, hcancel, neg_zero]

/-- Chartwise weak harmonicity supplies one smooth harmonic residual on the
whole complement of the integer lattice, by proved overlap and a.e. gluing. -/
theorem exists_greenQuadraticRemainder :
    ∃ h : PlanarSpace → ℝ, ContDiffOn ℝ ∞ h offIntegerLattice ∧
      HarmonicOnNhd h offIntegerLattice ∧
      greenQuadraticResidual =ᵐ[volume.restrict offIntegerLattice] h := by
  apply exists_smooth_harmonic_representative_of_local isOpen_offIntegerLattice
  intro x hx
  let a := centeredBoxAnchor x
  have hopen : IsOpen (euclideanOpenBox a ∩ offIntegerLattice) :=
    (isOpen_euclideanOpenBox a).inter isOpen_offIntegerLattice
  have hmem : x ∈ euclideanOpenBox a ∩ offIntegerLattice := ⟨mem_centeredOpenBox x, hx⟩
  obtain ⟨W, h, hWo, hxW, hWV, hsm, hhar, hae⟩ :=
    exists_smooth_harmonic_representative_nhds
      (weaklyHarmonic_greenQuadraticResidual_chart a) hopen hmem
  exact ⟨W, h, hWo, hxW, hWV.trans inter_subset_right, hsm, hhar, hae⟩

/-- An actual representative of the Green lift is smooth at every nonlattice
point. This theorem is independent of any pointwise regularity of the L2 choice. -/
theorem exists_regular_greenLift :
    ∃ G : PlanarSpace → ℝ, ContDiffOn ℝ ∞ G offIntegerLattice ∧
      greenLift =ᵐ[volume.restrict offIntegerLattice] G := by
  obtain ⟨h, hsm, _, hae⟩ := exists_greenQuadraticRemainder
  refine ⟨fun x ↦ h x + planarGreenQuadratic x,
    hsm.add contDiff_planarGreenQuadratic.contDiffOn, ?_⟩
  filter_upwards [hae] with x hx
  change greenLift x - planarGreenQuadratic x = h x at hx
  linarith

def smoothGreenLift : PlanarSpace → ℝ := Classical.choose exists_regular_greenLift

theorem contDiffOn_smoothGreenLift : ContDiffOn ℝ ∞ smoothGreenLift offIntegerLattice :=
  (Classical.choose_spec exists_regular_greenLift).1

theorem greenLift_ae_smoothGreenLift :
    greenLift =ᵐ[volume.restrict offIntegerLattice] smoothGreenLift :=
  (Classical.choose_spec exists_regular_greenLift).2

def smoothGreenLogRemainder : PlanarSpace → ℝ := Classical.choose exists_greenLogRemainder

theorem contDiffOn_smoothGreenLogRemainder :
    ContDiffOn ℝ ∞ smoothGreenLogRemainder (euclideanOpenBox (centeredBoxAnchor 0)) :=
  (Classical.choose_spec exists_greenLogRemainder).1

theorem harmonicOnNhd_smoothGreenLogRemainder :
    HarmonicOnNhd smoothGreenLogRemainder (euclideanOpenBox (centeredBoxAnchor 0)) :=
  (Classical.choose_spec exists_greenLogRemainder).2.1

theorem greenLogResidual_ae_remainder :
    greenLogResidual =ᵐ[volume.restrict (euclideanOpenBox (centeredBoxAnchor 0))]
      smoothGreenLogRemainder :=
  (Classical.choose_spec exists_greenLogRemainder).2.2

theorem mem_offIntegerLattice_of_mem_centeredOpenBox {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    x ∈ offIntegerLattice := by
  intro heq
  apply hne
  apply injOn_torusQuotient_box (centeredBoxAnchor 0)
    (euclideanOpenBox_subset_fundamentalBox _ hx)
    (euclideanOpenBox_subset_fundamentalBox _ (mem_centeredOpenBox 0))
  exact heq.trans torusQuotient_zero.symm

/-- Pointwise compatibility of the global off-lattice representative with the
logarithm-plus-quadratic-plus-harmonic expansion on the punctured origin chart. -/
theorem smoothGreenLift_local_expansion {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    smoothGreenLift x = planarLogKernel x + planarGreenQuadratic x +
      smoothGreenLogRemainder x := by
  let U := euclideanOpenBox (centeredBoxAnchor 0) ∩ offIntegerLattice
  have hU : IsOpen U := (isOpen_euclideanOpenBox _).inter isOpen_offIntegerLattice
  have hG : ContinuousOn smoothGreenLift U :=
    contDiffOn_smoothGreenLift.continuousOn.mono inter_subset_right
  have hL : ContDiffOn ℝ ∞ planarLogKernel U := by
    intro y hy
    apply (contDiffAt_planarLogKernel ?_).contDiffWithinAt
    intro hz
    have hn := hy.2
    apply hn
    rw [hz, torusQuotient_zero]
  have hH : ContinuousOn (fun y ↦ planarLogKernel y + planarGreenQuadratic y +
      smoothGreenLogRemainder y) U :=
    (hL.continuousOn.add contDiff_planarGreenQuadratic.continuous.continuousOn).add
      (contDiffOn_smoothGreenLogRemainder.continuousOn.mono inter_subset_left)
  have hgae : greenLift =ᵐ[volume.restrict U] smoothGreenLift :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right greenLift_ae_smoothGreenLift
  have hhae : greenLogResidual =ᵐ[volume.restrict U] smoothGreenLogRemainder :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left greenLogResidual_ae_remainder
  have hae : smoothGreenLift =ᵐ[volume.restrict U]
      (fun y ↦ planarLogKernel y + planarGreenQuadratic y + smoothGreenLogRemainder y) := by
    filter_upwards [hgae, hhae] with y hy hz
    change greenLift y - planarLogKernel y - planarGreenQuadratic y =
      smoothGreenLogRemainder y at hz
    linarith
  exact (Measure.eqOn_open_of_ae_eq hae hU hG hH)
    ⟨hx, mem_offIntegerLattice_of_mem_centeredOpenBox hx hne⟩

end PeriodicAttractiveLogGas
