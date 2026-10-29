import LeanResearch.PeriodicAttractiveLogGas.CollectiveSecondMoment

/-! Actual ordinary Laplacian calculation for the localized second moment.
The fixed-configuration field and the moving self-source are distinguished:
the diagonal pair is identically zero, whereas its first-slot divergence
at the diagonal is nonzero. All derivative identities below are derived
from the constructed C2 cutoff and the ordinary C2 configuration calculus.
See `research/reviews/localized-virial-laplacian-development.md` for checks.
-/

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators RealInnerProductSpace Laplacian

namespace PeriodicAttractiveLogGas.LocalizedVirialLaplacian

open LocalizedVirialCutoffs CollectiveSecondMoment CollectiveIntegrationByParts SeparatedRadius
open MovingPoleNumerators MovingPoleDerivativeIdentification

private theorem basis_inner_sum (a b : PlanarSpace) :
    (∑ k : Fin 2, inner ℝ a (EuclideanSpace.single k 1) *
      inner ℝ b (EuclideanSpace.single k 1)) = inner ℝ a b := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem cutoff_gradient_trace {s : ℝ} (hs : 0 < s) (u : PlanarSpace) :
    (∑ k : Fin 2, inner ℝ
      (fderiv ℝ (phiGradientEuclidean s) u (EuclideanSpace.single k 1))
      (EuclideanSpace.single k 1)) = Δ (phiEuclidean s) u := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (phiEuclidean s)
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_phiGradientEuclidean_apply hs, InnerProductSpace.toDual_symm_apply,
    EuclideanSpace.basisFun_apply]

theorem pairFirstGradient_fderiv_apply {s : ℝ} (hs : 0 < s) (u v t : PlanarSpace) :
    fderiv ℝ (fun w : PlanarSpace ↦ pairFirstGradient s w v) u t = phiEuclidean s v •
      (‖u - v‖ ^ 2 • fderiv ℝ (phiGradientEuclidean s) u t +
        (2 * inner ℝ (u - v) t) • phiGradientEuclidean s u +
        ((2 * phiEuclidean s u) • t + (2 * inner ℝ (phiGradientEuclidean s u) t) • (u - v))) := by
  have hg := ((contDiff_phiGradientEuclidean hs).differentiable (by norm_num) u).hasFDerivAt
  have h1 := (((hasFDerivAt_id u).sub_const v).norm_sq).smul hg
  have h2 := ((hasFDerivAt_phiEuclidean hs u).const_mul 2).smul
    ((hasFDerivAt_id u).sub_const v)
  have hd := (h1.add h2).const_smul (phiEuclidean s v)
  have he : fderiv ℝ (fun w : PlanarSpace ↦ pairFirstGradient s w v) u =
      phiEuclidean s v •
        ((‖u - v‖ ^ 2 • fderiv ℝ (phiGradientEuclidean s) u +
          ((2 : ℝ) • innerSL ℝ (u - v)).smulRight (phiGradientEuclidean s u)) +
        ((2 * phiEuclidean s u) • ContinuousLinearMap.id ℝ PlanarSpace +
          ((2 : ℝ) • innerSL ℝ (phiGradientEuclidean s u)).smulRight (u - v))) := by
    convert! hd.fderiv using 1
    ext r
    simp only [smul_apply, add_apply, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_apply, id_eq]
    simp only [two_smul ℝ, two_smul ℕ]
  rw [he]
  simp only [smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]

theorem pairFirstGradient_trace {s : ℝ} (hs : 0 < s) (u v : PlanarSpace) :
    (∑ k : Fin 2, inner ℝ
      (fderiv ℝ (fun w : PlanarSpace ↦ pairFirstGradient s w v) u (EuclideanSpace.single k 1))
      (EuclideanSpace.single k 1)) = phiEuclidean s v *
      (‖u - v‖ ^ 2 * Δ (phiEuclidean s) u +
        4 * inner ℝ (phiGradientEuclidean s u) (u - v) + 4 * phiEuclidean s u) := by
  have hpoint (k : Fin 2) : inner ℝ
      (fderiv ℝ (fun w : PlanarSpace ↦ pairFirstGradient s w v) u (EuclideanSpace.single k 1))
      (EuclideanSpace.single k 1) = phiEuclidean s v *
      (‖u - v‖ ^ 2 * inner ℝ
          (fderiv ℝ (phiGradientEuclidean s) u (EuclideanSpace.single k 1))
          (EuclideanSpace.single k 1) +
        4 * (inner ℝ (phiGradientEuclidean s u) (EuclideanSpace.single k 1) *
          inner ℝ (u - v) (EuclideanSpace.single k 1)) + 2 * phiEuclidean s u) := by
    rw [pairFirstGradient_fderiv_apply hs]
    simp only [inner_smul_left, inner_add_left, conj_trivial,
      EuclideanSpace.inner_single_left, PiLp.single_apply, ite_true, mul_one]
    ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, cutoff_gradient_trace hs, basis_inner_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The diagonal pair itself has zero derivative, but the first-slot trace
has this exact value. This is the correction in the configuration Laplacian. -/
theorem pairFirstGradient_trace_diagonal {s : ℝ} (hs : 0 < s) (u : PlanarSpace) :
    (∑ k : Fin 2, inner ℝ
      (fderiv ℝ (fun w : PlanarSpace ↦ pairFirstGradient s w u) u (EuclideanSpace.single k 1))
      (EuclideanSpace.single k 1)) = 4 * phiEuclidean s u ^ 2 := by
  rw [pairFirstGradient_trace hs]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul, inner_zero_right, mul_zero, zero_add]
  ring

theorem sourceProjection_variation {N : ℕ} (i j : Fin N) (Y : Gradient N) (z : PlanarSpace) :
    sourceProjection j (sourceVariation i Y z) = if j = i then z else sourceProjection j Y := by
  classical
  ext k
  rw [sourceProjection_apply, sourceVariation_apply]
  split_ifs <;> rfl

theorem configuration_variation_apply {N : ℕ} (i j : Fin N) (Y : Gradient N) (z : PlanarSpace) :
    configurationQuotient N (sourceVariation i Y z) j =
      if j = i then torusQuotient z else configurationQuotient N Y j := by
  change torusQuotient (sourceProjection j (sourceVariation i Y z)) = _
  rw [sourceProjection_variation]
  split_ifs <;> rfl

theorem directional_second_eq_particle_section {N : ℕ} (V : C2Function N)
    (i : Fin N) (Y : Gradient N) (v : PlanarSpace) :
    inner ℝ ((V.directional ((sourceProjection i).adjoint v)).gradient (configurationQuotient N Y))
      ((sourceProjection i).adjoint v) =
    fderiv ℝ (fun z : PlanarSpace ↦ inner ℝ
      (V.particleGradient i (configurationQuotient N (sourceVariation i Y z))) v)
      (sourceProjection i Y) v := by
  have he : (fun z : PlanarSpace ↦ inner ℝ
      (V.particleGradient i (configurationQuotient N (sourceVariation i Y z))) v) =
      fun z ↦ (V.directional ((sourceProjection i).adjoint v)).value
        (configurationQuotient N (sourceVariation i Y z)) := by
    funext z
    exact ((sourceProjection i).adjoint_inner_right _ _).symm
  rw [he]
  have hd := hasFDerivAt_sourceBlock
    ((V.directional ((sourceProjection i).adjoint v)).differential Y) i
  rw [hd.fderiv]
  exact (sourceProjection i).adjoint_inner_right _ _

theorem laplacian_eq_particle_sections {N : ℕ} (V : C2Function N) (Y : Gradient N) :
    V.laplacian (configurationQuotient N Y) = ∑ i : Fin N, ∑ k : Fin 2,
      fderiv ℝ (fun z : PlanarSpace ↦ inner ℝ
        (V.particleGradient i (configurationQuotient N (sourceVariation i Y z)))
        (EuclideanSpace.single k 1)) (sourceProjection i Y) (EuclideanSpace.single k 1) := by
  change (∑ ik : Fin N × Fin 2, inner ℝ
    ((V.directional (EuclideanSpace.single ik 1)).gradient (configurationQuotient N Y))
      (EuclideanSpace.single ik 1)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have he : (sourceProjection i).adjoint (EuclideanSpace.single k 1) =
      EuclideanSpace.single (i, k) 1 := by
    ext jk
    rcases jk with ⟨j, l⟩
    simp only [sourceProjection_adjoint_apply, PiLp.single_apply, Prod.mk.injEq]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  rw [← he, directional_second_eq_particle_section]

/-- Literal first-slot sum with the moving diagonal pair removed. The next
identity identifies it with the actual Q particle section. -/
def offDiagonalField {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (i : Fin N) (z : PlanarSpace) : PlanarSpace :=
  (1 / (N : ℝ)) • ∑ j : Fin N, if j = i then 0 else
    pairFirstGradient s (chartPosition ξ (torusQuotient z)) (chartPosition ξ (X j))

theorem Q_particle_section {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus)
    (Y : Gradient N) (i : Fin N) (z : PlanarSpace) :
    (QFunction ξ hs hsmall).particleGradient i
      (configurationQuotient N (sourceVariation i Y z)) =
      offDiagonalField ξ s (configurationQuotient N Y) i z := by
  rw [QFunction_particleGradient hN]
  simp only [G, offDiagonalField, configuration_variation_apply, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [ite_true, pairFirstGradient_self]
  · simp only [ite_eq_right hj]

private theorem contDiff_firstSlot_lift {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (v : PlanarSpace) :
    ContDiff ℝ 1 (fun z : PlanarSpace ↦ pairFirstGradient s (chartPosition ξ (torusQuotient z)) v) :=
  contDiff_chart_lift (contDiff_pairFirstGradient hs v)
    (fun u hu ↦ pairFirstGradient_eq_zero_outer hs hu v) (by linarith : 4 * s < 1 / 2) ξ

theorem contDiff_offDiagonalField {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N) (i : Fin N) :
    ContDiff ℝ 1 (offDiagonalField ξ s X i) := by
  change ContDiff ℝ 1 (fun z : PlanarSpace ↦ (1 / (N : ℝ)) • ∑ j : Fin N,
    if j = i then 0 else pairFirstGradient s (chartPosition ξ (torusQuotient z)) (chartPosition ξ (X j)))
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j _
  by_cases hj : j = i
  · simp only [ite_eq_left hj]
    exact contDiff_const
  · simp only [ite_eq_right hj]
    exact contDiff_firstSlot_lift hs hsmall ξ _

theorem fderiv_offDiagonalField_apply {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N)
    (i : Fin N) (y t : PlanarSpace) :
    fderiv ℝ (offDiagonalField ξ s X i) y t = (1 / (N : ℝ)) • ∑ j : Fin N,
      if j = i then 0 else fderiv ℝ (fun u : PlanarSpace ↦ pairFirstGradient s u (chartPosition ξ (X j)))
        (chartPosition ξ (torusQuotient y)) t := by
  let F (j : Fin N) (z : PlanarSpace) := if j = i then (0 : PlanarSpace) else
    pairFirstGradient s (chartPosition ξ (torusQuotient z)) (chartPosition ξ (X j))
  have hF (j : Fin N) : ContDiff ℝ 1 (F j) := by
    by_cases hj : j = i
    · simp only [F, ite_eq_left hj]
      exact contDiff_const
    · simp only [F, ite_eq_right hj]
      exact contDiff_firstSlot_lift hs hsmall ξ _
  have hd : HasFDerivAt (offDiagonalField ξ s X i)
      ((1 / (N : ℝ)) • ∑ j : Fin N, fderiv ℝ (F j) y) y :=
    (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ ↦
      ((hF j).differentiable (by norm_num) y).hasFDerivAt).const_smul (1 / (N : ℝ))
  rw [hd.fderiv, smul_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · simp only [F, ite_eq_left hj, fderiv_const_apply, zero_apply]
  · simp only [F, ite_eq_right hj]
    rw [chart_lift_fderiv (fun u hu ↦ pairFirstGradient_eq_zero_outer hs hu (chartPosition ξ (X j)))
      (by linarith : 4 * s < 1 / 2)]

theorem offDiagonalField_trace {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (X : Configuration N) (i : Fin N) (y : PlanarSpace) :
    (∑ k : Fin 2, inner ℝ (fderiv ℝ (offDiagonalField ξ s X i) y (EuclideanSpace.single k 1))
      (EuclideanSpace.single k 1)) = (1 / (N : ℝ)) * ∑ j : Fin N,
      if j = i then 0 else phi ξ s (X j) *
        (‖chartPosition ξ (torusQuotient y) - chartPosition ξ (X j)‖ ^ 2 *
          Δ (phiEuclidean s) (chartPosition ξ (torusQuotient y)) +
          4 * inner ℝ (phiGradientEuclidean s (chartPosition ξ (torusQuotient y)))
            (chartPosition ξ (torusQuotient y) - chartPosition ξ (X j)) +
          4 * phi ξ s (torusQuotient y)) := by
  have hp (k : Fin 2) : inner ℝ (fderiv ℝ (offDiagonalField ξ s X i) y (EuclideanSpace.single k 1))
      (EuclideanSpace.single k 1) = (1 / (N : ℝ)) * ∑ j : Fin N,
      if j = i then 0 else inner ℝ
        (fderiv ℝ (fun u : PlanarSpace ↦ pairFirstGradient s u (chartPosition ξ (X j)))
          (chartPosition ξ (torusQuotient y)) (EuclideanSpace.single k 1)) (EuclideanSpace.single k 1) := by
    rw [fderiv_offDiagonalField_apply hs hsmall, inner_smul_left, conj_trivial, sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i <;> simp only [hj, ite_true, ite_false, inner_zero_left]
  simp_rw [hp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · simp only [ite_eq_left hj, Finset.sum_const_zero]
  · simp only [ite_eq_right hj]
    rw [pairFirstGradient_trace hs, phiEuclidean_chart, phiEuclidean_chart]

/-- The literal source ordinary Laplacian, including exclusion of the
identically zero moving diagonal pair. This holds at collisions as well. -/
theorem QFunction_laplacian {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N) :
    (QFunction ξ hs hsmall).laplacian X = (1 / (N : ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
      if j = i then 0 else phi ξ s (X j) *
        (‖chartPosition ξ (X i) - chartPosition ξ (X j)‖ ^ 2 *
          Δ (phiEuclidean s) (chartPosition ξ (X i)) +
          4 * inner ℝ (phiGradientEuclidean s (chartPosition ξ (X i)))
            (chartPosition ξ (X i) - chartPosition ξ (X j)) + 4 * phi ξ s (X i)) := by
  obtain ⟨Y, rfl⟩ := configurationQuotient_surjective N X
  rw [laplacian_eq_particle_sections, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∑ k : Fin 2, fderiv ℝ (fun z : PlanarSpace ↦ inner ℝ
      ((QFunction ξ hs hsmall).particleGradient i (configurationQuotient N (sourceVariation i Y z)))
        (EuclideanSpace.single k 1)) (sourceProjection i Y) (EuclideanSpace.single k 1)) =
      ∑ k : Fin 2, inner ℝ
        (fderiv ℝ (offDiagonalField ξ s (configurationQuotient N Y) i)
          (sourceProjection i Y) (EuclideanSpace.single k 1)) (EuclideanSpace.single k 1) := by
    apply Finset.sum_congr rfl
    intro k _
    simp_rw [Q_particle_section hN hs hsmall]
    rw [fderiv_inner_apply ℝ
      ((contDiff_offDiagonalField hs hsmall ξ (configurationQuotient N Y) i).differentiable
        (by norm_num) (sourceProjection i Y))
      (differentiableAt_const (EuclideanSpace.single k (1 : ℝ) : PlanarSpace))]
    simp only [fderiv_const_apply, zero_apply, inner_zero_right, zero_add]
  rw [he, offDiagonalField_trace hs hsmall]
  rfl

private theorem sum_offDiagonal_eq_sum_sub {N : ℕ} (f : Fin N → ℝ) (i : Fin N) :
    (∑ j : Fin N, if j = i then 0 else f j) = (∑ j : Fin N, f j) - f i := by
  have he : (∑ j : Fin N, if j = i then 0 else f j) + f i = ∑ j : Fin N, f j := by
    calc
      _ = (∑ j : Fin N, if j = i then 0 else f j) +
          ∑ j : Fin N, if j = i then f j else 0 := by simp
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i <;> simp only [hj, ite_true, ite_false, zero_add, add_zero]
  linarith

/-- The source annular error, written using the actual S and D sums. -/
def laplacianError {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (i : Fin N) : ℝ :=
  4 * inner ℝ (phiGradientEuclidean s (chartPosition ξ (X i)))
    (D ξ s X (chartPosition ξ (X i))) +
    Δ (phiEuclidean s) (chartPosition ξ (X i)) * S ξ s X (chartPosition ξ (X i))

theorem QFunction_laplacian_split {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N) :
    (QFunction ξ hs hsmall).laplacian X =
      (4 / (N : ℝ)) * (mass ξ s X ^ 2 - ∑ i : Fin N, phi ξ s (X i) ^ 2) +
        (1 / (N : ℝ)) * ∑ i : Fin N, laplacianError ξ s X i := by
  let F (i j : Fin N) := phi ξ s (X j) *
    (‖chartPosition ξ (X i) - chartPosition ξ (X j)‖ ^ 2 *
      Δ (phiEuclidean s) (chartPosition ξ (X i)) +
      4 * inner ℝ (phiGradientEuclidean s (chartPosition ξ (X i)))
        (chartPosition ξ (X i) - chartPosition ξ (X j)) + 4 * phi ξ s (X i))
  have hrow (i : Fin N) : (∑ j : Fin N, F i j) =
      4 * phi ξ s (X i) * mass ξ s X + laplacianError ξ s X i := by
    simp only [laplacianError, S, D, mass, inner_sum, inner_smul_right, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [F]
    ring
  have hdiag (i : Fin N) : F i i = 4 * phi ξ s (X i) ^ 2 := by
    simp only [F, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul, inner_zero_right, mul_zero, zero_add]
    ring
  have hfirst : (∑ i : Fin N, 4 * phi ξ s (X i) * mass ξ s X) = 4 * mass ξ s X ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    change 4 * mass ξ s X * mass ξ s X = _
    ring
  calc
    _ = (1 / (N : ℝ)) * ∑ i : Fin N, (4 * phi ξ s (X i) * mass ξ s X +
        laplacianError ξ s X i - 4 * phi ξ s (X i) ^ 2) := by
      rw [QFunction_laplacian hN hs hsmall]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j : Fin N, if j = i then 0 else F i j) = _
      rw [sum_offDiagonal_eq_sum_sub, hrow, hdiag]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hfirst, ← Finset.mul_sum]
      ring

theorem mass_square_sub_sq_sum_nonneg {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    0 ≤ mass ξ s X ^ 2 - ∑ i : Fin N, phi ξ s (X i) ^ 2 := by
  have hs : (∑ i : Fin N, phi ξ s (X i) ^ 2) ≤ mass ξ s X ^ 2 := by
    calc
      _ ≤ ∑ i : Fin N, mass ξ s X * phi ξ s (X i) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : phi ξ s (X i) ≤ mass ξ s X :=
          Finset.single_le_sum (fun j _ ↦ (phi_mem_Icc ξ s (X j)).1) (Finset.mem_univ i)
        nlinarith [mul_le_mul_of_nonneg_right hi (phi_mem_Icc ξ s (X i)).1]
      _ = _ := by rw [← Finset.mul_sum]; change mass ξ s X * mass ξ s X = _; ring
  exact sub_nonneg.mpr hs

theorem mass_square_sub_sq_sum_lower {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    mass ξ s X * (mass ξ s X - 1) ≤ mass ξ s X ^ 2 - ∑ i : Fin N, phi ξ s (X i) ^ 2 := by
  have hs : (∑ i : Fin N, phi ξ s (X i) ^ 2) ≤ mass ξ s X := by
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨hl, hu⟩ := phi_mem_Icc ξ s (X i)
    nlinarith
  nlinarith

theorem laplacian_phiEuclidean_eq_zero_inner {s : ℝ} (hs : 0 < s)
    {u : PlanarSpace} (hu : ‖u‖ ≤ 2 * s) : Δ (phiEuclidean s) u = 0 := by
  by_cases hne : u = 0
  · subst u
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (phiEuclidean s)
      (EuclideanSpace.basisFun (Fin 2) ℝ)]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      second_fderiv_phiEuclidean_zero hs, zero_apply, Finset.sum_const_zero]
  · rw [laplacian_phiEuclidean hne, second_deriv_phiProfile_eq_zero_inner hs hu,
      deriv_phiProfile_eq_zero_inner hs hu, zero_div, add_zero]

theorem laplacian_phiEuclidean_eq_zero_outer {s : ℝ} (hs : 0 < s)
    {u : PlanarSpace} (hu : 4 * s ≤ ‖u‖) : Δ (phiEuclidean s) u = 0 := by
  have hne : u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < 4 * s) hu)
  rw [laplacian_phiEuclidean hne, second_deriv_phiProfile_eq_zero_outer hs hu,
    deriv_phiProfile_eq_zero_outer hs hu, zero_div, add_zero]

private theorem error_expression_bound {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) :
    |4 * inner ℝ (phiGradientEuclidean s u) (D ξ s X u) +
      Δ (phiEuclidean s) u * S ξ s X u| ≤ 224 * mass ξ s X := by
  have hM := mass_nonneg ξ s X
  have h1 : |4 * inner ℝ (phiGradientEuclidean s u) (D ξ s X u)| ≤ 32 * mass ξ s X := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      _ ≤ 4 * (‖phiGradientEuclidean s u‖ * ‖D ξ s X u‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ 4 * ((1 / s) * (8 * s * mass ξ s X)) := mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_phiGradientEuclidean_le hs u) (norm_D_le hs ξ X hu)
          (norm_nonneg _) (by positivity)) (by norm_num)
      _ = _ := by field_simp [hs.ne']; ring
  have h2 : |Δ (phiEuclidean s) u * S ξ s X u| ≤ 192 * mass ξ s X := by
    rw [abs_mul, abs_of_nonneg (S_nonneg ξ s X u)]
    calc
      _ ≤ (3 / s ^ 2) * (64 * s ^ 2 * mass ξ s X) :=
        mul_le_mul (abs_laplacian_phiEuclidean_le hs u) (S_le hs ξ X hu)
          (S_nonneg ξ s X u) (by positivity)
      _ = _ := by field_simp [hs.ne']; ring
  exact (abs_add_le _ _).trans (by linarith)

theorem laplacianError_eq_zero_of_not_annulus {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (i : Fin N)
    (hi : ¬(2 * s < torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < 4 * s)) :
    laplacianError ξ s X i = 0 := by
  by_cases hinner : torusEuclideanDist (X i) ξ ≤ 2 * s
  · have hu : ‖chartPosition ξ (X i)‖ ≤ 2 * s := by simpa only [norm_chartPosition] using hinner
    simp only [laplacianError, phiGradientEuclidean_eq_zero_inner hs hu,
      laplacian_phiEuclidean_eq_zero_inner hs hu, inner_zero_left, zero_mul, mul_zero, add_zero]
  · have hout : 4 * s ≤ torusEuclideanDist (X i) ξ := by
      by_contra h
      exact hi ⟨lt_of_not_ge hinner, lt_of_not_ge h⟩
    have hu : 4 * s ≤ ‖chartPosition ξ (X i)‖ := by simpa only [norm_chartPosition] using hout
    simp only [laplacianError, phiGradientEuclidean_eq_zero_outer hs hu,
      laplacian_phiEuclidean_eq_zero_outer hs hu, inner_zero_left, zero_mul, mul_zero, add_zero]

/-- Exact 224 annular error, using the source hard annulus including neither
joining radius; both cutoff jets vanish at those radii. -/
theorem abs_sum_laplacianError_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) :
    |∑ i : Fin N, laplacianError ξ s X i| ≤ 224 * mass ξ s X * annulusCount ξ s X := by
  calc
    _ ≤ ∑ i : Fin N, |laplacianError ξ s X i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, if 2 * s < torusEuclideanDist (X i) ξ ∧
        torusEuclideanDist (X i) ξ < 4 * s then 224 * mass ξ s X else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact error_expression_bound hs ξ X (by rw [norm_chartPosition]; exact hi.2.le)
      · rw [laplacianError_eq_zero_of_not_annulus hs ξ X i hi, abs_zero]
    _ = _ := by
      rw [annulusCount_real_eq hs, Finset.mul_sum]
      simp only [mul_ite, mul_one, mul_zero]

theorem QFunction_laplacian_lower {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N) :
    (4 * mass ξ s X * (mass ξ s X - 1) - 224 * mass ξ s X * annulusCount ξ s X) / N ≤
      (QFunction ξ hs hsmall).laplacian X := by
  have hn : (0 : ℝ) ≤ 1 / N := by positivity
  have hE := (neg_le_abs (∑ i : Fin N, laplacianError ξ s X i)).trans
    (abs_sum_laplacianError_le hs ξ X)
  have hlow := mul_le_mul_of_nonneg_left (mass_square_sub_sq_sum_lower ξ s X)
    (show 0 ≤ 4 / (N : ℝ) by positivity)
  have herr := mul_le_mul_of_nonneg_left (show
      -(224 * mass ξ s X * annulusCount ξ s X) ≤ ∑ i : Fin N, laplacianError ξ s X i by linarith) hn
  rw [QFunction_laplacian_split hN hs hsmall]
  calc
    _ = (4 / (N : ℝ)) * (mass ξ s X * (mass ξ s X - 1)) +
        (1 / (N : ℝ)) * -(224 * mass ξ s X * annulusCount ξ s X) := by ring
    _ ≤ _ := add_le_add hlow herr

/-- The nonnegative first sum is retained separately for the source small
positive mass case, where M*(M-1) would give an unnecessarily negative term. -/
theorem QFunction_laplacian_lower_nonnegative_first {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N) :
    -(224 * mass ξ s X * annulusCount ξ s X / N) ≤ (QFunction ξ hs hsmall).laplacian X := by
  have hE := (neg_le_abs (∑ i : Fin N, laplacianError ξ s X i)).trans
    (abs_sum_laplacianError_le hs ξ X)
  have herr := mul_le_mul_of_nonneg_left (show
      -(224 * mass ξ s X * annulusCount ξ s X) ≤ ∑ i : Fin N, laplacianError ξ s X i by linarith)
    (show 0 ≤ 1 / (N : ℝ) by positivity)
  have hfirst := mul_nonneg (show 0 ≤ 4 / (N : ℝ) by positivity)
    (mass_square_sub_sq_sum_nonneg ξ s X)
  rw [QFunction_laplacian_split hN hs hsmall]
  convert (le_add_of_nonneg_left hfirst).trans' herr using 1
  ring

end PeriodicAttractiveLogGas.LocalizedVirialLaplacian
