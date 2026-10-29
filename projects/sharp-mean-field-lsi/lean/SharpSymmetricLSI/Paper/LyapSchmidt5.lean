import SharpSymmetricLSI.Paper.LyapSchmidt4

/-!
# Section 4.2 (lane s42; R14): `I + T` is invertible on `Y = E^⊥ ∩ {μ(u) = 0}`

`T` maps `YC` into itself (centering and selfadjointness). With `P = QCraw` the projection onto
`YC`, the operator `1 + T P` on `C(𝕋^d)` is a continuous linear equivalence: it is injective
(`ker(I+T) = E` and `YC ⊥ E`), and `T P = R + F` with `‖R‖ < 1` and `F` of finite rank (a
uniform finite-rank approximation of the centered kernel), so the Fredholm alternative
(`isInvertible_one_add`) applies. (`1 + TPC` is `(I+T)|_Y ⊕ id` on `C = Y ⊕ (span{1} + E)`; working
on all of `C(𝕋^d)` avoids normed structures on the subtype `YC`.)
-/

noncomputable section
open MeasureTheory Filter Real Topology
open scoped BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section inv
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp

/-- A continuous function vanishing `μ`-a.e. vanishes (the density of `μ` is positive). -/
theorem CT_eq_zero_of_ae (hμ : IsMinimizer V W μ) {u : CT d}
    (h : (⇑u) =ᵐ[(μ : Measure (Torus d))] 0) : u = 0 := by
  set ub : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact u
  have h0 : ∫ x, ub x * ub x ∂(μ : Measure (Torus d)) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h] with x hx
    simp [ub, hx]
  have := bcf_eq_zero_of_sq hyp hμ ub h0
  ext x
  have := congrArg (fun f : Torus d →ᵇ ℝ => f x) this
  simpa [ub] using this

include hφ

theorem TC_mem_YC {y : CT d} (hy : y ∈ YC hyp hφ) :
    TC hyp (μ : Measure (Torus d)) y ∈ YC hyp hφ := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨h1, h2⟩ := (mem_YC hyp hφ).mp hy
  rw [mem_YC]
  refine ⟨?_, fun i => ?_⟩
  · show ∫ x, Top W μm (⇑y) x ∂μm = 0
    exact integral_Top hyp μm (integrable_CT hyp μm y)
  · show ∫ x, Top W μm (⇑y) x * phiC hyp hφ i x ∂μm = 0
    rw [integral_mul_phiC hyp hφ,
      ← Top_selfadjoint hyp μm (memL20_CT hyp μm h1) (memL20_phi hyp hφ i)]
    have e : ∀ x, y x * Top W μm (φ i) x = -(y x * phiC hyp hφ i x) := fun x => by
      show y x * Top W μm (φ i) x = -(y x * -Top W μm (φ i) x); ring
    simp_rw [e]
    rw [integral_neg, h2 i, neg_zero]

/-- `T P`. -/
def TPC : CT d →L[ℝ] CT d := (TC hyp (μ : Measure (Torus d))).comp (QCraw hyp hφ)

theorem TP_mem_YC (u : CT d) : TPC hyp hφ u ∈ YC hyp hφ :=
  TC_mem_YC hyp hφ (QCraw_mem hyp hφ u)

include hμ

/-- `1 + T P` is injective. -/
theorem injective_one_add_TP : Function.Injective ⇑(1 + TPC hyp hφ : CT d →L[ℝ] CT d) := by
  set μm := (μ : Measure (Torus d))
  rw [injective_iff_map_eq_zero]
  intro k hk
  have hk' : k + TPC hyp hφ k = 0 := by simpa using hk
  set y := QCraw hyp hφ k with hydef
  have hyY : y ∈ YC hyp hφ := QCraw_mem hyp hφ k
  -- `y + T y = 0`
  have hy0 : y + TC hyp μm y = 0 := by
    have := congrArg (QCraw hyp hφ) hk'
    rw [map_add, map_zero, QCraw_of_mem hyp hφ (TP_mem_YC hyp hφ k)] at this
    exact this
  have hy' : ∀ x, y x + Top W μm (⇑y) x = 0 := fun x => by
    have := congrArg (fun z : CT d => z x) hy0
    simpa [TC_apply] using this
  obtain ⟨h1, h2⟩ := (mem_YC hyp hφ).mp hyY
  have hker : InKerIT' W μm (⇑y) := ⟨memL20_CT hyp μm h1, Eventually.of_forall fun x => hy' x⟩
  obtain ⟨a, ha⟩ := hφ.2.2 _ hker
  have hφφ : ∀ i j, Integrable (fun x => φ i x * φ j x) μm := fun i j =>
    (memL20_phi hyp hφ i).1.integrable_mul (memL20_phi hyp hφ j).1
  have ha0 : ∀ j, a j = 0 := fun j => by
    have h := h2 j
    rw [integral_mul_phiC hyp hφ] at h
    have e : ∫ x, y x * φ j x ∂μm = ∫ x, ∑ i, a i * (φ i x * φ j x) ∂μm := by
      refine integral_congr_ae ?_
      filter_upwards [ha] with x hx
      rw [hx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum _ fun i _ => (hφφ i j).const_mul (a i)] at h
    have e2 : ∀ i, ∫ x, a i * (φ i x * φ j x) ∂μm = a i * (if i = j then 1 else 0) := fun i => by
      rw [← hφ.2.1 i j, integral_const_mul]
    simp_rw [e2] at h
    simpa using h
  have hzero : (⇑y) =ᵐ[μm] 0 := by
    filter_upwards [ha] with x hx
    rw [hx]; simp [ha0]
  have hy00 : y = 0 := CT_eq_zero_of_ae hyp hμ hzero
  have : TPC hyp hφ k = 0 := by
    show TC hyp μm (QCraw hyp hφ k) = 0
    rw [← hydef, hy00, map_zero]
  rw [this, add_zero] at hk'
  exact hk'

/-- **`1 + T P` is invertible on `C(𝕋^d)`.** -/
theorem isInvertible_one_add_TP :
    (1 + TPC hyp hφ : CT d →L[ℝ] CT d).IsInvertible := by
  set μm := (μ : Measure (Torus d))
  have hK := continuous_centeredKernel hyp μm
  set q := ‖QCraw hyp hφ‖ with hq
  set ε := 1 / (2 * (q + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨m, f, g, hfg⟩ := exists_finiteRank_approx hK hε0
  -- the finite-rank part
  set TM : CT d →L[ℝ] CT d := ∑ i, (pairC μm (g i)).smulRight (f i) with hTM
  have hTM_apply : ∀ u x, TM u x = ∑ i, f i x * ∫ y, u y * g i y ∂μm := fun u x => by
    simp [hTM, ContinuousLinearMap.sum_apply, ContinuousMap.sum_apply, pairC_apply, mul_comm]
  set R : CT d →L[ℝ] CT d := (TC hyp μm - TM).comp (QCraw hyp hφ) with hR
  set F : CT d →L[ℝ] CT d := TM.comp (QCraw hyp hφ) with hF
  have hsplit : TPC hyp hφ = R + F := by
    ext u : 1
    show TC hyp μm (QCraw hyp hφ u) = (TC hyp μm - TM) (QCraw hyp hφ u) + TM (QCraw hyp hφ u)
    rw [ContinuousLinearMap.sub_apply, sub_add_cancel]
  -- `‖T - T_M‖ ≤ ε` on mean-zero functions
  have hD : ∀ y : CT d, y ∈ YC hyp hφ → ‖(TC hyp μm - TM) y‖ ≤ ε * ‖y‖ := fun y hy => by
    obtain ⟨h1, -⟩ := (mem_YC hyp hφ).mp hy
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    rw [Real.norm_eq_abs]
    have i1 : Integrable (fun z => centeredKernel W μm x z * y z) μm :=
      integrable_of_continuous ((cont_right hK x).mul y.continuous)
    have i2 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        Integrable (fun z => f i x * (g i z * y z)) μm := fun i _ =>
      integrable_of_continuous (continuous_const.mul ((g i).continuous.mul y.continuous))
    have e : (TC hyp μm - TM) y x =
        ∫ z, (centeredKernel W μm x z - ∑ i, f i x * g i z) * y z ∂μm := by
      rw [ContinuousLinearMap.sub_apply, ContinuousMap.sub_apply, TC_apply,
        Top_eq_integral hyp μm (memL20_CT hyp μm h1) x, hTM_apply]
      have e1 : (fun z => (centeredKernel W μm x z - ∑ i, f i x * g i z) * y z) =
          fun z => centeredKernel W μm x z * y z - ∑ i, f i x * (g i z * y z) := by
        funext z; rw [sub_mul, Finset.sum_mul]
        congr 1; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, integral_sub i1 (integrable_finsetSum _ i2), integral_finsetSum _ i2]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    rw [e]
    refine abs_integral_le_of_bdd fun z => ?_
    rw [abs_mul]
    exact mul_le_mul (hfg x z).le (abs_CT_le _ z) (abs_nonneg _) hε0.le
  have hRn : ‖R‖ < 1 := by
    have hq0 : 0 ≤ q := ContinuousLinearMap.opNorm_nonneg _
    have hb : ‖R‖ ≤ ε * q := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
      calc ‖R u‖ ≤ ε * ‖QCraw hyp hφ u‖ := hD _ (QCraw_mem hyp hφ u)
        _ ≤ ε * (q * ‖u‖) := mul_le_mul_of_nonneg_left ((QCraw hyp hφ).le_opNorm u) hε0.le
        _ = ε * q * ‖u‖ := by ring
    have : ε * q < 1 := by
      rw [hε, one_div, inv_mul_eq_div, div_lt_one (by positivity)]; linarith
    linarith
  have hFfin : FiniteDimensional ℝ (LinearMap.range (F : CT d →ₗ[ℝ] CT d)) := by
    have hS : FiniteDimensional ℝ (Submodule.span ℝ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ (Set.range f)) ?_
    rintro _ ⟨u, rfl⟩
    have e : (F : CT d →ₗ[ℝ] CT d) u =
        ∑ i, (∫ z, QCraw hyp hφ u z * g i z ∂μm) • f i := by
      simp [hF, hTM, ContinuousLinearMap.sum_apply, pairC_apply]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj := injective_one_add_TP hyp hμ hφ
  rw [hsplit, ← add_assoc] at hinj ⊢
  exact isInvertible_one_add hRn hFfin hinj

end inv

end SharpLSI
