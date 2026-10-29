import SharpSymmetricLSI.Paper.LyapSchmidt5

/-!
# Section 4.2 (lane s42; R14): the reduction map and the implicit function (4.5)

With `P = QCraw` the projection onto `YC`, `FC (a, y) = P(log(1 + kC a + Py) + T(kC a + Py)) +
(y - Py)` on `ℝⁿ × C(𝕋^d)`. On `y ∈ YC` its first summand is `P_{E^⊥} g(k + y)` (manuscript
(4.3), (4.5)), and `FC (a, y) = 0` iff `y ∈ YC` and `P_{E^⊥} g(k + y) = 0`
(`FC_eq_zero_iff`). `FC` is `C^∞` near `0`, `FC 0 = 0`, its partial derivative in `y` at `0` is
`1 + T P` (invertible) and in `a` is `P (I + T) kC = 0`. (The second summand extends the
reduction from `YC` to all of `C(𝕋^d)`.)
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section map
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)

/-- `(a, y) ↦ kC a + P y`. -/
def LC : EuclideanSpace ℝ (Fin n) × CT d →L[ℝ] CT d :=
  (kC hyp hφ).coprod (QCraw hyp hφ)

theorem LC_apply (p : EuclideanSpace ℝ (Fin n) × CT d) :
    LC hyp hφ p = kC hyp hφ p.1 + QCraw hyp hφ p.2 := by
  simp [LC]

/-- `h ↦ log(1 + h) + T h`. -/
def PhiC (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (h : CT d) : CT d :=
  logC h + TC hyp μ h

/-- The extended Lyapunov–Schmidt map. -/
def FC (p : EuclideanSpace ℝ (Fin n) × CT d) : CT d :=
  QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) (LC hyp hφ p)) + (p.2 - QCraw hyp hφ p.2)

theorem hasFDerivAt_PhiC (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {h : CT d}
    (hh : h ∈ posSet) : HasFDerivAt (PhiC hyp μ) (logCDeriv h + TC hyp μ) h :=
  (hasFDerivAt_logC hh).add (TC hyp μ).hasFDerivAt

theorem hasFDerivAt_FC {p : EuclideanSpace ℝ (Fin n) × CT d} (hp : LC hyp hφ p ∈ posSet) :
    HasFDerivAt (FC hyp hφ) ((QCraw hyp hφ).comp
      ((logCDeriv (LC hyp hφ p) + TC hyp (μ : Measure (Torus d))).comp (LC hyp hφ)) +
      (ContinuousLinearMap.snd ℝ _ _ - (QCraw hyp hφ).comp (ContinuousLinearMap.snd ℝ _ _))) p := by
  have h1 := (QCraw hyp hφ).hasFDerivAt.comp p
    ((hasFDerivAt_PhiC hyp (μ : Measure (Torus d)) hp).comp p (LC hyp hφ).hasFDerivAt)
  have h2 : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × CT d => q.2 - QCraw hyp hφ q.2)
      (ContinuousLinearMap.snd ℝ _ _ - (QCraw hyp hφ).comp (ContinuousLinearMap.snd ℝ _ _)) p :=
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (CT d) -
      (QCraw hyp hφ).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (CT d)) :
        EuclideanSpace ℝ (Fin n) × CT d →L[ℝ] CT d)).hasFDerivAt
  exact h1.add h2

theorem contDiffAt_FC {p : EuclideanSpace ℝ (Fin n) × CT d} (hp : LC hyp hφ p ∈ posSet) :
    ContDiffAt ℝ ∞ (FC hyp hφ) p := by
  have hQ : ContDiff ℝ ∞ (fun u : CT d => QCraw hyp hφ u) := by exact ContinuousLinearMap.contDiff _
  have hT : ContDiff ℝ ∞ (fun u : CT d => TC hyp (μ : Measure (Torus d)) u) := by
    exact ContinuousLinearMap.contDiff _
  have hL : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin n) × CT d => LC hyp hφ q) := by
    exact ContinuousLinearMap.contDiff _
  have hS : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin n) × CT d => q.2 - QCraw hyp hφ q.2) := by
    exact (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (CT d) -
      (QCraw hyp hφ).comp (ContinuousLinearMap.snd ℝ _ _)).contDiff
  have hPhi : ContDiffAt ℝ ∞ (PhiC hyp (μ : Measure (Torus d))) (LC hyp hφ p) :=
    (contDiffAt_logC hp).add hT.contDiffAt
  exact (hQ.contDiffAt.comp p (hPhi.comp p hL.contDiffAt)).add hS.contDiffAt

/-- The open set where `FC` is smooth. -/
def OC : Set (EuclideanSpace ℝ (Fin n) × CT d) := LC hyp hφ ⁻¹' posSet

theorem isOpen_OC : IsOpen (OC hyp hφ) := isOpen_posSet.preimage (LC hyp hφ).continuous

theorem zero_mem_OC : (0 : EuclideanSpace ℝ (Fin n) × CT d) ∈ OC hyp hφ := by
  show LC hyp hφ 0 ∈ posSet
  rw [map_zero]; intro x; simp

theorem contDiffOn_FC : ContDiffOn ℝ ∞ (FC hyp hφ) (OC hyp hφ) := fun p hp =>
  (contDiffAt_FC hyp hφ hp).contDiffWithinAt

theorem FC_zero : FC hyp hφ 0 = 0 := by
  simp [FC, PhiC, map_zero, logC_zero]

theorem TC_kC (a : EuclideanSpace ℝ (Fin n)) :
    TC hyp (μ : Measure (Torus d)) (kC hyp hφ a) = -kC hyp hφ a := by
  simp [kC, ContinuousLinearMap.sum_apply, map_sum, TC_phiC hyp hφ, Finset.sum_neg_distrib]

/-- Zeros of `FC`: `y ∈ YC` and `P(log(1 + kC a + y) + T(kC a + y)) = 0`. -/
theorem FC_eq_zero_iff (p : EuclideanSpace ℝ (Fin n) × CT d) :
    FC hyp hφ p = 0 ↔ QCraw hyp hφ p.2 = p.2 ∧
      QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) (kC hyp hφ p.1 + p.2)) = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := eq_zero_of_add_compl hyp hφ (QCraw_mem hyp hφ _) h
    refine ⟨h2, ?_⟩
    rw [LC_apply, h2] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    simp only [FC, LC_apply, h1, h2, sub_self, add_zero]

theorem fderiv_FC_zero : fderiv ℝ (FC hyp hφ) 0 = (QCraw hyp hφ).comp
    ((ContinuousLinearMap.id ℝ (CT d) + TC hyp (μ : Measure (Torus d))).comp (LC hyp hφ)) +
    (ContinuousLinearMap.snd ℝ _ _ - (QCraw hyp hφ).comp (ContinuousLinearMap.snd ℝ _ _)) := by
  rw [(hasFDerivAt_FC hyp hφ (zero_mem_OC hyp hφ)).fderiv, map_zero, logCDeriv_zero]

/-- `∂_y FC (0) = 1 + T P`. -/
theorem fderiv_FC_inr :
    (fderiv ℝ (FC hyp hφ) 0).comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (CT d)) =
      1 + TPC hyp hφ := by
  rw [fderiv_FC_zero]
  ext k : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.inr_apply, LC_apply, map_zero, zero_add, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.one_apply,
    map_add]
  rw [QCraw_idem, show QCraw hyp hφ (TC hyp (μ : Measure (Torus d)) (QCraw hyp hφ k)) =
    TPC hyp hφ k from QCraw_of_mem hyp hφ (TP_mem_YC hyp hφ k)]
  abel

/-- `∂_a FC (0) = 0`. -/
theorem fderiv_FC_inl :
    (fderiv ℝ (FC hyp hφ) 0).comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (CT d)) =
      0 := by
  rw [fderiv_FC_zero]
  ext a : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.inl_apply, LC_apply, map_zero, add_zero, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_snd', sub_zero,
    ContinuousLinearMap.zero_apply]
  rw [TC_kC hyp hφ a, add_neg_cancel, map_zero]

end map

end SharpLSI
