import SharpSymmetricLSI.Paper.Sec42Spectral1
import SharpSymmetricLSI.Paper.LyapSchmidt5

/-!
# Section 4.2 (lane s42; R15): (4.13) `I + T ≥ σ I` from `ker(I+T) = 0`

`T` on `L²(μ)`: `T u = ∫ K(·,y) u(y) dμ(y)` (centered kernel, R17). On `L²_0(μ)` the form
`⟨u, (I+T) u⟩` is `secondVar` (R14), nonnegative at a minimizer; `T = T_M + R` with `T_M` of
finite rank and `‖R‖ ≤ 1/2` (finite-rank approximation of `K`). If the kernel is trivial, the
abstract lemma `exists_coercive` gives `σ > 0` with `σ ‖h‖² ≤ secondVar h`.
-/

noncomputable section
open MeasureTheory Filter Real Topology

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

section L2op
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

/-- `x ↦ ∫ F(x,y) u(y) dμ(y)` for a continuous kernel and `u ∈ L¹`. -/
theorem continuous_kernel_integral {F : Torus d → Torus d → ℝ}
    (hF : Continuous (Function.uncurry F)) {u : Torus d → ℝ} (hu : Integrable u μ) :
    Continuous fun x => ∫ y, F x y * u y ∂μ := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hF
  refine continuous_of_dominated (bound := fun y => B * |u y|) (fun x => ?_) (fun x => ?_)
    (hu.abs.const_mul B) (Eventually.of_forall fun y => (cont_left hF y).mul continuous_const)
  · exact ((cont_right hF x).aestronglyMeasurable).mul hu.aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB (x, y)) (abs_nonneg _)

theorem abs_kernel_integral_le {F : Torus d → Torus d → ℝ} {B : ℝ} (hB : ∀ x y, |F x y| ≤ B)
    {u : Torus d → ℝ} (hu : Integrable u μ) (x : Torus d) :
    |∫ y, F x y * u y ∂μ| ≤ B * ∫ y, |u y| ∂μ := by
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    (hu.abs.const_mul B) (Eventually.of_forall fun y => ?_)
  show |F x y * u y| ≤ B * |u y|
  rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB x y) (abs_nonneg _)

theorem integral_abs_le_norm_L2 (u : Lp ℝ 2 μ) : ∫ y, |u y| ∂μ ≤ ‖u‖ := by
  have h1 := integral_abs_le_sqrt' (Lp.memLp u)
  have h2 : ‖u‖ ^ 2 = ∫ y, u y ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    congr 1; funext y; simp [sq]
  rw [← h2, Real.sqrt_sq (norm_nonneg _)] at h1
  exact h1

theorem memLp_kernel_integral {F : Torus d → Torus d → ℝ}
    (hF : Continuous (Function.uncurry F)) (u : Lp ℝ 2 μ) :
    MemLp (fun x => ∫ y, F x y * u y ∂μ) 2 μ := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hF
  have hu : Integrable (⇑u) μ := (Lp.memLp u).integrable one_le_two
  exact MemLp.of_bound (continuous_kernel_integral hyp μ hF hu).aestronglyMeasurable
    (B * ∫ y, |u y| ∂μ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_kernel_integral_le hyp μ (fun x y => hB (x, y)) hu x)

/-- The integral operator of a continuous kernel on `L²(μ)`. -/
def kerOp {F : Torus d → Torus d → ℝ} (hF : Continuous (Function.uncurry F)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_kernel_integral hyp μ hF u).toLp _
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        have hu : Integrable (⇑u) μ := (Lp.memLp u).integrable one_le_two
        have hv : Integrable (⇑v) μ := (Lp.memLp v).integrable one_le_two
        obtain ⟨B, hB⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hF
        have iu : Integrable (fun y => F x y * u y) μ :=
          Integrable.mono' (hu.abs.const_mul B) ((cont_right hF x).aestronglyMeasurable.mul
            hu.aestronglyMeasurable) (Eventually.of_forall fun y => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul_of_nonneg_right (hB (x, y)) (abs_nonneg _))
        have iv : Integrable (fun y => F x y * v y) μ :=
          Integrable.mono' (hv.abs.const_mul B) ((cont_right hF x).aestronglyMeasurable.mul
            hv.aestronglyMeasurable) (Eventually.of_forall fun y => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul_of_nonneg_right (hB (x, y)) (abs_nonneg _))
        simp only [Pi.add_apply]
        rw [← integral_add iu iv]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u v] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        ring }
    (exists_bound_of_continuous (X := Torus d × Torus d) hF).choose fun u => by
      obtain hB := (exists_bound_of_continuous (X := Torus d × Torus d) hF).choose_spec
      have hu : Integrable (⇑u) μ := (Lp.memLp u).integrable one_le_two
      have hB0 : 0 ≤ (exists_bound_of_continuous (X := Torus d × Torus d) hF).choose :=
        (abs_nonneg _).trans (hB (Classical.arbitrary _))
      show ‖((memLp_kernel_integral hyp μ hF u).toLp _ : Lp ℝ 2 μ)‖ ≤ _
      refine (Lp.norm_le_of_ae_bound (C := (exists_bound_of_continuous (X := Torus d × Torus d)
        hF).choose * ‖u‖) (by positivity) ?_).trans
        (by simp [measureUnivNNReal, measure_univ])
      filter_upwards [MemLp.coeFn_toLp (memLp_kernel_integral hyp μ hF u)] with x hx
      rw [hx, Real.norm_eq_abs]
      refine (abs_kernel_integral_le hyp μ (fun x y => hB (x, y)) hu x).trans ?_
      exact mul_le_mul_of_nonneg_left (integral_abs_le_norm_L2 hyp μ u) hB0

theorem kerOp_ae {F : Torus d → Torus d → ℝ} (hF : Continuous (Function.uncurry F))
    (u : Lp ℝ 2 μ) :
    (kerOp hyp μ hF u : Torus d → ℝ) =ᵐ[μ] fun x => ∫ y, F x y * u y ∂μ := by
  show ((memLp_kernel_integral hyp μ hF u).toLp _ : Torus d → ℝ) =ᵐ[μ] _
  exact MemLp.coeFn_toLp _

end L2op

theorem coeFn_finsetSum_L2 {μ : Measure (Torus d)} {ι : Type*} (s : Finset ι)
    (F : ι → Lp ℝ 2 μ) : (⇑(∑ i ∈ s, F i) : Torus d → ℝ) =ᵐ[μ] ∑ i ∈ s, ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply]

section coercive
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- **(4.13)**: if `ker(I+T) = 0` then `I + T ≥ σ` on `L²_0(μ)`. -/
theorem secondVar_coercive_of_ker
    (hker : ∀ h, InKerIT' W μ h → h =ᵐ[(μ : Measure (Torus d))] 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ h, MemL20 μ h →
      σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h := by
  set μm := (μ : Measure (Torus d))
  have hK := continuous_centeredKernel hyp μm
  set T2 := kerOp hyp μm hK with hT2
  -- the constant function and the subspace `L²_0`
  set one : Lp ℝ 2 μm := (memLp_const (1 : ℝ)).toLp _ with hone
  have hone_ae : (one : Torus d → ℝ) =ᵐ[μm] fun _ => 1 := MemLp.coeFn_toLp _
  have hinner_one : ∀ u : Lp ℝ 2 μm, ⟪one, u⟫ = ∫ x, u x ∂μm := fun u => by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hone_ae] with x hx
    simp [hx]
  set P : Lp ℝ 2 μm → Prop := fun u => ⟪one, u⟫ = 0 with hP
  have hPc : IsClosed {u | P u} := isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hPlin : ∀ u v (t : ℝ), P u → P v → P (v + t • u) := fun u v t hu hv => by
    simp only [hP, inner_add_right, inner_smul_right] at hu hv ⊢
    rw [hu, hv]; ring
  -- `T2 u = T u` on mean-zero functions
  have hT2ae : ∀ u : Lp ℝ 2 μm, (T2 u : Torus d → ℝ) =ᵐ[μm]
      fun x => ∫ y, centeredKernel W μm x y * u y ∂μm := fun u => kerOp_ae hyp μm hK u
  obtain ⟨BK, hBK⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hK
  have hint : ∀ u : Lp ℝ 2 μm, Integrable (⇑u) μm := fun u => (Lp.memLp u).integrable one_le_two
  -- the double integral of the kernel
  have hprod : ∀ u v : Lp ℝ 2 μm, Integrable
      (Function.uncurry fun x y => v x * centeredKernel W μm x y * u y) (μm.prod μm) := by
    intro u v
    have h1 : Integrable (fun z : Torus d × Torus d => v z.1 * u z.2) (μm.prod μm) :=
      (hint v).mul_prod (hint u)
    refine (h1.bdd_mul (c := BK) (hK.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)).congr
      (Eventually.of_forall fun z => ?_)
    · rw [Real.norm_eq_abs]; exact hBK z
    · simp only [Function.uncurry]; ring
  have hinnerT : ∀ u v : Lp ℝ 2 μm,
      ⟪v, T2 u⟫ = ∫ x, ∫ y, v x * centeredKernel W μm x y * u y ∂μm ∂μm := fun u v => by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT2ae u] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, ← integral_mul_const]
    congr 1; funext y; ring
  -- symmetry
  have hsymmT : ∀ u v : Lp ℝ 2 μm, ⟪v, T2 u⟫ = ⟪u, T2 v⟫ := fun u v => by
    rw [hinnerT, hinnerT, integral_integral_swap (hprod u v)]
    congr 1; funext y; congr 1; funext x
    rw [centeredKernel_symm_coerc hyp μm x y]; ring
  -- `T2` has mean zero
  have hmeanT : ∀ u : Lp ℝ 2 μm, ⟪one, T2 u⟫ = 0 := fun u => by
    rw [hinnerT, integral_integral_swap (hprod u one)]
    have h0 : ∀ y, ∫ x, one x * centeredKernel W μm x y * u y ∂μm = 0 := fun y => by
      have e : ∫ x, one x * centeredKernel W μm x y * u y ∂μm =
          (∫ x, centeredKernel W μm x y ∂μm) * u y := by
        rw [← integral_mul_const]
        refine integral_congr_ae ?_
        filter_upwards [hone_ae] with x hx
        rw [hx]; ring
      rw [e]
      have : ∫ x, centeredKernel W μm x y ∂μm = 0 := by
        simp_rw [centeredKernel_symm_coerc hyp μm _ y]; exact integral_centeredKernel hyp μm y
      rw [this, zero_mul]
    simp_rw [h0, integral_zero]
  -- the finite-rank decomposition
  obtain ⟨m, f, g, hfg⟩ := exists_finiteRank_approx hK (by norm_num : (0 : ℝ) < 1 / 2)
  set fL : Fin m → Lp ℝ 2 μm := fun i => ContinuousMap.toLp (E := ℝ) 2 μm ℝ (f i) with hfL
  set gL : Fin m → Lp ℝ 2 μm := fun i => ContinuousMap.toLp (E := ℝ) 2 μm ℝ (g i) with hgL
  set TM : Lp ℝ 2 μm →L[ℝ] Lp ℝ 2 μm := ∑ i, (innerSL ℝ (gL i)).smulRight (fL i) with hTM
  have hTMae : ∀ u : Lp ℝ 2 μm, (TM u : Torus d → ℝ) =ᵐ[μm]
      fun x => ∑ i, f i x * ∫ y, g i y * u y ∂μm := fun u => by
    have h1 : TM u = ∑ i, ⟪gL i, u⟫ • fL i := by
      simp [hTM, ContinuousLinearMap.sum_apply]
    have hfae : ∀ i, (fL i : Torus d → ℝ) =ᵐ[μm] f i := fun i =>
      ContinuousMap.coeFn_toLp (E := ℝ) (μ := μm) (p := 2) (𝕜 := ℝ) (f i)
    have hgi : ∀ i, ⟪gL i, u⟫ = ∫ y, g i y * u y ∂μm := fun i => by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (μ := μm) (p := 2) (𝕜 := ℝ) (g i)]
        with y hy
      rw [RCLike.inner_apply, conj_trivial, hy]; ring
    rw [h1]
    have hsum := coeFn_finsetSum_L2 (Finset.univ : Finset (Fin m))
      (fun i => (⟪gL i, u⟫ • fL i : Lp ℝ 2 μm))
    have hsmul : ∀ i, ((⟪gL i, u⟫ • fL i : Lp ℝ 2 μm) : Torus d → ℝ) =ᵐ[μm]
        fun x => ⟪gL i, u⟫ * f i x := fun i => by
      filter_upwards [Lp.coeFn_smul (⟪gL i, u⟫) (fL i), hfae i] with x h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hall : ∀ᵐ x ∂μm, ∀ i, ((⟪gL i, u⟫ • fL i : Lp ℝ 2 μm) : Torus d → ℝ) x =
        ⟪gL i, u⟫ * f i x := ae_all_iff.mpr hsmul
    filter_upwards [hsum, hall] with x h1 h2
    rw [h1, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 i, hgi i, mul_comm]
  set R : Lp ℝ 2 μm →L[ℝ] Lp ℝ 2 μm := T2 - TM with hR
  have hRn : ‖R‖ < 1 := by
    have hb : ‖R‖ ≤ 1 / 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun u => ?_
      refine (Lp.norm_le_of_ae_bound (C := 1 / 2 * ‖u‖) (by positivity) ?_).trans
        (by simp [measureUnivNNReal, measure_univ])
      filter_upwards [ContinuousLinearMap.sub_apply T2 TM u ▸ Lp.coeFn_sub (T2 u) (TM u),
        hT2ae u, hTMae u] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
      have e : ∫ y, centeredKernel W μm x y * u y ∂μm - ∑ i, f i x * ∫ y, g i y * u y ∂μm =
          ∫ y, (centeredKernel W μm x y - ∑ i, f i x * g i y) * u y ∂μm := by
        have i1 : Integrable (fun y => centeredKernel W μm x y * u y) μm :=
          Integrable.mono' ((hint u).abs.const_mul BK) ((cont_right hK x).aestronglyMeasurable.mul
            (hint u).aestronglyMeasurable) (Eventually.of_forall fun y => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul_of_nonneg_right (hBK (x, y)) (abs_nonneg _))
        have i2 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
            Integrable (fun y => f i x * (g i y * u y)) μm := fun i _ => by
          obtain ⟨Bg, hBg⟩ := exists_bound_of_continuous (g i).continuous
          exact (Integrable.mono' ((hint u).abs.const_mul Bg) ((g i).continuous.aestronglyMeasurable.mul
            (hint u).aestronglyMeasurable) (Eventually.of_forall fun y => by
              rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
              exact mul_le_mul_of_nonneg_right (hBg y) (abs_nonneg _))).const_mul _
        have e1 : (fun y => (centeredKernel W μm x y - ∑ i, f i x * g i y) * u y) =
            fun y => centeredKernel W μm x y * u y - ∑ i, f i x * (g i y * u y) := by
          funext y; rw [sub_mul, Finset.sum_mul]
          congr 1; exact Finset.sum_congr rfl fun i _ => by ring
        rw [e1, integral_sub i1 (integrable_finsetSum _ i2), integral_finsetSum _ i2]
        simp_rw [integral_const_mul]
      rw [e]
      refine (abs_kernel_integral_le hyp μm (fun x y => (hfg x y).le) (hint u) x).trans ?_
      exact mul_le_mul_of_nonneg_left (integral_abs_le_norm_L2 hyp μm u) (by norm_num)
    linarith
  have hTMfin : FiniteDimensional ℝ (LinearMap.range (TM : Lp ℝ 2 μm →ₗ[ℝ] Lp ℝ 2 μm)) := by
    have hS : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fL)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ (Set.range fL)) ?_
    rintro _ ⟨u, rfl⟩
    have e : (TM : Lp ℝ 2 μm →ₗ[ℝ] Lp ℝ 2 μm) u = ∑ i, ⟪gL i, u⟫ • fL i := by
      simp [hTM, ContinuousLinearMap.sum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hA : (1 + R + TM : Lp ℝ 2 μm →L[ℝ] Lp ℝ 2 μm) = 1 + T2 := by
    rw [hR]; abel
  -- the form is `secondVar`
  have hmem : ∀ u : Lp ℝ 2 μm, P u → MemL20 μm (⇑u) := fun u hu =>
    ⟨Lp.memLp u, by rw [← hinner_one]; exact hu⟩
  have hform : ∀ u : Lp ℝ 2 μm, P u → ⟪u, (1 + T2) u⟫ = secondVar W μm (⇑u) := fun u hu => by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, inner_add_right,
      MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_add]
    · unfold secondVar
      refine integral_congr_ae ?_
      filter_upwards [hT2ae u] with x hx
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hx, ← Top_eq_integral hyp μm (hmem u hu) x]
      ring
    · exact (Lp.memLp u).integrable_mul (Lp.memLp u)
    · exact ((Lp.memLp u).integrable_mul (Lp.memLp (T2 u))).congr
        (Eventually.of_forall fun x => by simp [RCLike.inner_apply, mul_comm])
  -- apply the abstract lemma
  have hAP : ∀ u, P u → P ((1 + R + TM) u) := fun u hu => by
    rw [hA]
    simp only [hP, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      inner_add_right, hmeanT, add_zero]
    exact hu
  have hsymmA : ∀ u v, P u → P v → ⟪v, (1 + R + TM) u⟫ = ⟪u, (1 + R + TM) v⟫ :=
    fun u v _ _ => by
    rw [hA]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, inner_add_right]
    rw [hsymmT u v, real_inner_comm v u]
  have hposA : ∀ u, P u → 0 ≤ ⟪u, (1 + R + TM) u⟫ := fun u hu => by
    rw [hA, hform u hu]; exact secondVar_nonneg hyp hμ (hmem u hu)
  have hdefA : ∀ u, P u → ⟪u, (1 + R + TM) u⟫ = 0 → u = 0 := fun u hu h0 => by
    have h1 := norm_sq_apply_le hPlin hAP hsymmA hposA hu
    rw [h0, mul_zero] at h1
    have h2 : (1 + R + TM) u = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h1 (sq_nonneg _))
      exact norm_eq_zero.mp this
    rw [hA] at h2
    have h3 : u + T2 u = 0 := by
      have e : (1 + T2) u = u + T2 u := by
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply]
      rw [← e]; exact h2
    have hker' : InKerIT' W μm (⇑u) := by
      refine ⟨hmem u hu, ?_⟩
      filter_upwards [Lp.coeFn_add u (T2 u), hT2ae u, Lp.coeFn_zero ℝ 2 μm] with x h4 h5 h6
      have h7 : ((u + T2 u : Lp ℝ 2 μm) : Torus d → ℝ) x = 0 := by rw [h3]; exact h6
      rw [h4, Pi.add_apply, h5] at h7
      show u x + Top W μm (⇑u) x = 0
      rw [Top_eq_integral hyp μm (hmem u hu) x]
      exact h7
    exact Lp.ext ((hker _ hker').trans (Lp.coeFn_zero ℝ 2 μm).symm)
  obtain ⟨σ, hσ0, hσ⟩ := exists_coercive hRn hTMfin hPc hPlin hAP hsymmA hposA hdefA
  refine ⟨σ, hσ0, fun h hh => ?_⟩
  set u : Lp ℝ 2 μm := hh.1.toLp h
  have hu_ae : (u : Torus d → ℝ) =ᵐ[μm] h := MemLp.coeFn_toLp hh.1
  have hPu : P u := by
    show ⟪one, u⟫ = 0
    rw [hinner_one, integral_congr_ae hu_ae]; exact hh.2
  have hn : ‖u‖ ^ 2 = ∫ x, h x ^ 2 ∂μm := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu_ae] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx]; ring
  have hs : secondVar W μm (⇑u) = secondVar W μm h := by
    unfold secondVar
    refine integral_congr_ae ?_
    filter_upwards [hu_ae] with x hx
    rw [hx, Top_congr_ae hyp μm hu_ae x]
  have := hσ u hPu
  rw [hA, hform u hPu, hs, hn] at this
  exact this

end coercive

end SharpLSI
