import SharpSymmetricLSI.Paper.Sec42Spectral2
import SharpSymmetricLSI.Statements.R15_Contraction
import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# Proposition 2.3 (lane s42; R04): existence of `C = (I+T)^{-1}` (6.11)

`T` acts on `L²(μ)` as the integral operator of the centered kernel (`T2op`); it is symmetric,
kills constants and maps into mean-zero functions, and on mean-zero `u`,
`⟨u, (I+T)u⟩ = secondVar u ≥ σ ‖u‖²` (R15). Adding the rank-one projection onto constants gives
a coercive operator `A'` on all of `L²(μ)` (`coercive_A'`); Lax–Milgram solves
`(I+T) u_j = e_{j+1}` with `u_j` mean-zero. With `C_{kj} = ⟨e_{k+1}, u_j⟩`, Parseval in the
reference basis gives `∑_k (δ_{ik} + T_{ik}) C_{kj} = ⟨e_{i+1}, (I+T) u_j⟩ = δ_{ij}`
(`exists_inverseOfIPlus`).
-/

noncomputable section
open MeasureTheory Filter Topology

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

theorem L2_inner_eq_integral {μ : Measure (Torus d)} (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

section inv
variable (hyp : Hyp V W KV KW) (μ : ProbabilityMeasure (Torus d))
include hyp

local notation "μm" => ((μ : ProbabilityMeasure (Torus d)) : Measure (Torus d))

/-- `T` on `L²(μ)`. -/
def T2op : Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)) :=
  kerOp hyp (μ : Measure (Torus d)) (continuous_centeredKernel hyp (μ : Measure (Torus d)))

/-- The constant `1` in `L²(μ)`. -/
def oneL : Lp ℝ 2 (μ : Measure (Torus d)) := (memLp_const (1 : ℝ)).toLp _

omit hyp in
theorem oneL_ae : (oneL μ : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] fun _ => 1 :=
  MemLp.coeFn_toLp _

omit hyp in
theorem inner_oneL (u : Lp ℝ 2 (μ : Measure (Torus d))) :
    ⟪oneL μ, u⟫ = ∫ x, u x ∂(μ : Measure (Torus d)) := by
  rw [L2_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [oneL_ae μ] with x hx
  rw [hx, one_mul]

omit hyp in
theorem inner_oneL_self : ⟪oneL μ, oneL μ⟫ = 1 := by
  rw [inner_oneL]
  have : ∫ x, (oneL μ : Torus d → ℝ) x ∂(μ : Measure (Torus d)) =
      ∫ _x, (1 : ℝ) ∂(μ : Measure (Torus d)) := integral_congr_ae (oneL_ae μ)
  rw [this]; simp

theorem T2op_ae (u : Lp ℝ 2 (μ : Measure (Torus d))) :
    (T2op hyp μ u : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))]
      fun x => ∫ y, centeredKernel W (μ : Measure (Torus d)) x y * u y ∂(μ : Measure (Torus d)) :=
  kerOp_ae hyp _ _ u

theorem integrable_prod_kernel (u v : Lp ℝ 2 (μ : Measure (Torus d))) :
    Integrable (Function.uncurry fun x y =>
      v x * centeredKernel W (μ : Measure (Torus d)) x y * u y)
      ((μ : Measure (Torus d)).prod (μ : Measure (Torus d))) := by
  have hK := continuous_centeredKernel hyp μm
  obtain ⟨BK, hBK⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hK
  have hint : ∀ w : Lp ℝ 2 μm, Integrable (⇑w) μm := fun w => (Lp.memLp w).integrable one_le_two
  have h1 : Integrable (fun z : Torus d × Torus d => v z.1 * u z.2) (Measure.prod μm μm) :=
    (hint v).mul_prod (hint u)
  refine (h1.bdd_mul (c := BK) (hK.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)).congr
    (Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs]; exact hBK z
  · simp only [Function.uncurry]; ring

theorem inner_T2op (u v : Lp ℝ 2 (μ : Measure (Torus d))) :
    ⟪v, T2op hyp μ u⟫ = ∫ x, ∫ y, v x * centeredKernel W (μ : Measure (Torus d)) x y * u y
      ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d)) := by
  rw [L2_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [T2op_ae hyp μ u] with x hx
  rw [hx, ← integral_const_mul]
  congr 1; funext y; ring

theorem inner_T2op_symm (u v : Lp ℝ 2 (μ : Measure (Torus d))) :
    ⟪v, T2op hyp μ u⟫ = ⟪u, T2op hyp μ v⟫ := by
  rw [inner_T2op, inner_T2op, integral_integral_swap (integrable_prod_kernel hyp μ u v)]
  congr 1; funext y; congr 1; funext x
  rw [centeredKernel_symm_coerc hyp (μ : Measure (Torus d)) x y]; ring

theorem inner_oneL_T2op (u : Lp ℝ 2 (μ : Measure (Torus d))) : ⟪oneL μ, T2op hyp μ u⟫ = 0 := by
  rw [inner_T2op, integral_integral_swap (integrable_prod_kernel hyp μ u (oneL μ))]
  have h0 : ∀ y, ∫ x, (oneL μ : Torus d → ℝ) x * centeredKernel W μm x y * u y ∂μm = 0 := by
    intro y
    have e : ∫ x, (oneL μ : Torus d → ℝ) x * centeredKernel W μm x y * u y ∂μm =
        (∫ x, centeredKernel W μm x y ∂μm) * u y := by
      rw [← integral_mul_const]
      refine integral_congr_ae ?_
      filter_upwards [oneL_ae μ] with x hx
      rw [hx]; ring
    rw [e]
    have : ∫ x, centeredKernel W μm x y ∂μm = 0 := by
      simp_rw [centeredKernel_symm_coerc hyp μm _ y]; exact integral_centeredKernel hyp μm y
    rw [this, zero_mul]
  simp_rw [h0, integral_zero]

theorem T2op_oneL : T2op hyp μ (oneL μ) = 0 :=
  ext_inner_left ℝ fun v => by
    rw [inner_T2op_symm, inner_oneL_T2op, inner_zero_right]

theorem norm_sq_eq_integral (u : Lp ℝ 2 (μ : Measure (Torus d))) :
    ‖u‖ ^ 2 = ∫ y, u y ^ 2 ∂(μ : Measure (Torus d)) := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  congr 1; funext y; ring

/-- On mean-zero `u`, the form of `I + T` is `secondVar`. -/
theorem inner_IT_eq_secondVar {u : Lp ℝ 2 (μ : Measure (Torus d))} (hu : ⟪oneL μ, u⟫ = 0) :
    ⟪u, u + T2op hyp μ u⟫ = secondVar W (μ : Measure (Torus d)) (⇑u) := by
  have hmem : MemL20 μm (⇑u) := ⟨Lp.memLp u, by rw [← inner_oneL]; exact hu⟩
  rw [inner_add_right, L2_inner_eq_integral, L2_inner_eq_integral, ← integral_add]
  · unfold secondVar
    refine integral_congr_ae ?_
    filter_upwards [T2op_ae hyp μ u] with x hx
    rw [hx, ← Top_eq_integral hyp μm hmem x]
    ring
  · exact (Lp.memLp u).integrable_mul (Lp.memLp u)
  · exact (Lp.memLp u).integrable_mul (Lp.memLp (T2op hyp μ u))

/-- `I + T + P_1`, with `P_1 u = ⟨1,u⟩ 1`. -/
def Aop : Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)) :=
  1 + T2op hyp μ + (innerSL ℝ (oneL μ)).smulRight (oneL μ)

theorem Aop_apply (u : Lp ℝ 2 (μ : Measure (Torus d))) :
    Aop hyp μ u = u + T2op hyp μ u + ⟪oneL μ, u⟫ • oneL μ := by
  simp [Aop]

variable (hd : 1 ≤ d) (hr : 0 < rStar V W) (hμ : IsMinimizer V W μ)
include hd hr hμ

theorem coercive_Aop : ∃ c : ℝ, 0 < c ∧
    ∀ u, c * ‖u‖ * ‖u‖ ≤ ⟪u, Aop hyp μ u⟫ := by
  obtain ⟨-, -, -, σ, hσ, hσ'⟩ := minSet_singleton hd hyp hr hμ
  refine ⟨min σ 1, lt_min hσ one_pos, fun u => ?_⟩
  set c := ⟪oneL μ, u⟫
  set u0 := u - c • oneL μ
  have hone := inner_oneL_self μ
  have hu0 : ⟪oneL μ, u0⟫ = 0 := by
    simp only [u0, inner_sub_right, inner_smul_right, hone, c]; ring
  have hu : u = u0 + c • oneL μ := by simp [u0]
  have hT : T2op hyp μ u = T2op hyp μ u0 := by
    rw [hu, map_add, map_smul, T2op_oneL, smul_zero, add_zero]
  have hsv := hσ' (⇑u0) ⟨Lp.memLp u0, by rw [← inner_oneL]; exact hu0⟩
  rw [← norm_sq_eq_integral hyp μ, ← inner_IT_eq_secondVar hyp μ hu0] at hsv
  have hT0 : ⟪oneL μ, T2op hyp μ u0⟫ = 0 := inner_oneL_T2op hyp μ u0
  have hu0' : ⟪u0, oneL μ⟫ = 0 := by rw [real_inner_comm]; exact hu0
  -- the form
  have hform : ⟪u, Aop hyp μ u⟫ = ⟪u0, u0 + T2op hyp μ u0⟫ + 2 * c ^ 2 := by
    rw [Aop_apply, hT, hu]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hone, hu0, hu0', hT0]
    ring
  have hnorm : ‖u‖ ^ 2 = ‖u0‖ ^ 2 + c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hu]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hone, hu0, hu0']
    ring
  rw [hform]
  have h1 : min σ 1 * ‖u0‖ ^ 2 ≤ σ * ‖u0‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  have h2 : min σ 1 * c ^ 2 ≤ 2 * c ^ 2 := by
    have := min_le_right σ 1
    nlinarith [sq_nonneg c]
  calc min σ 1 * ‖u‖ * ‖u‖ = min σ 1 * ‖u‖ ^ 2 := by ring
    _ = min σ 1 * ‖u0‖ ^ 2 + min σ 1 * c ^ 2 := by rw [hnorm]; ring
    _ ≤ _ := by linarith

/-- Solving `(I+T) u = f` for mean-zero `f`, with `u` mean-zero (Lax–Milgram). -/
theorem exists_solve_IT {f : Lp ℝ 2 (μ : Measure (Torus d))} (hf : ⟪oneL μ, f⟫ = 0) :
    ∃ u, ⟪oneL μ, u⟫ = 0 ∧ u + T2op hyp μ u = f := by
  obtain ⟨c, hc, hcoer⟩ := coercive_Aop hyp μ hd hr hμ
  set B : Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] ℝ :=
    (innerSL ℝ).comp (Aop hyp μ)
  have hB : IsCoercive B := ⟨c, hc, fun u => by
    show c * ‖u‖ * ‖u‖ ≤ ⟪Aop hyp μ u, u⟫
    rw [real_inner_comm]; exact hcoer u⟩
  set E := hB.continuousLinearEquivOfBilin
  have hE : ∀ v, E v = Aop hyp μ v := fun v => ext_inner_right ℝ fun w => by
    rw [IsCoercive.continuousLinearEquivOfBilin_apply]; rfl
  set u := E.symm f
  have hAu : Aop hyp μ u = f := by rw [← hE]; exact E.apply_symm_apply f
  have hone := inner_oneL_self μ
  have hmean : ⟪oneL μ, u⟫ = 0 := by
    have := congrArg (fun g => ⟪oneL μ, g⟫) hAu
    simp only [Aop_apply, inner_add_right, inner_smul_right, hone, inner_oneL_T2op, hf] at this
    linarith
  refine ⟨u, hmean, ?_⟩
  rw [← hAu, Aop_apply, hmean, zero_smul, add_zero]

/-- **(6.11): `C = (I+T)^{-1}` exists.** -/
theorem exists_inverseOfIPlus {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ C, IsInverseOfIPlus (Tmat W (μ : Measure (Torus d)) e) C := by
  -- the basis in `L²`
  set EL : ℕ → Lp ℝ 2 μm := fun n => (he.memH1 n).2.1.toLp (e n)
  have hEL : ∀ n, (EL n : Torus d → ℝ) =ᵐ[μm] e n := fun n => MemLp.coeFn_toLp _
  have hinEL : ∀ n (x : Lp ℝ 2 μm), ⟪EL n, x⟫ = ∫ y, e n y * x y ∂μm := fun n x => by
    rw [L2_inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hEL n] with y hy
    rw [hy]
  have horth : Orthonormal ℝ EL := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinEL, ← he.orthonormal i j]
    refine integral_congr_ae ?_
    filter_upwards [hEL j] with y hy
    rw [hy]
  have hite : ∀ a c, ⟪EL a, EL c⟫ = if a = c then 1 else 0 := orthonormal_iff_ite.mp horth
  have hsp : (Submodule.span ℝ (Set.range EL))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h0 : ∀ n, ∫ y, x y * e n y ∂μm = 0 := fun n => by
      have := (Submodule.mem_orthogonal _ x).1 hx (EL n)
        (Submodule.subset_span ⟨n, rfl⟩)
      rw [hinEL] at this
      rw [← this]; congr 1; funext y; ring
    have := he.complete (⇑x) (Lp.memLp x) h0
    exact (Lp.eq_zero_iff_ae_eq_zero).2 this
  set b := HilbertBasis.mkOfOrthogonalEqBot horth hsp
  have hb : ∀ n, b n = EL n := fun n => by
    simp [b, HilbertBasis.coe_mkOfOrthogonalEqBot]
  -- `⟨e_0, x⟩ = ⟨1, x⟩`
  have hEL0 : ∀ x : Lp ℝ 2 μm, ⟪EL 0, x⟫ = ⟪oneL μ, x⟫ := fun x => by
    rw [hinEL, inner_oneL, he.zero]; simp
  -- the solutions
  have hsol : ∀ j, ∃ u, ⟪oneL μ, u⟫ = 0 ∧ u + T2op hyp μ u = EL (j + 1) := fun j => by
    refine exists_solve_IT hyp μ hd hr hμ ?_
    rw [← hEL0, hite]; simp
  choose u hu0 hu using hsol
  refine ⟨fun k j => ⟪EL (k + 1), u j⟫, fun j => ⟨?_, fun i => ?_⟩⟩
  · -- columns in `ℓ²` (Bessel)
    have := (horth.comp (· + 1) (add_left_injective 1)).inner_products_summable (x := u j)
    simpa [Real.norm_eq_abs, sq_abs] using this
  -- the matrix of `T`
  have hTmat : ∀ i k, Tmat W μm e i k = ⟪EL (i + 1), T2op hyp μ (EL (k + 1))⟫ := fun i k => by
    rw [inner_T2op]
    unfold Tmat
    refine integral_congr_ae ?_
    filter_upwards [hEL (i + 1)] with x hx
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [hEL (k + 1)] with y hy
    rw [hy]; ring
  set w := EL (i + 1) + T2op hyp μ (EL (i + 1))
  have hterm : ∀ k, ((if i = k then 1 else 0) + Tmat W μm e i k) * ⟪EL (k + 1), u j⟫ =
      ⟪w, b (k + 1)⟫ * ⟪b (k + 1), u j⟫ := fun k => by
    rw [hb, hTmat, inner_add_left, inner_T2op_symm hyp μ (EL (k + 1)) (EL (i + 1)),
      real_inner_comm (EL (k + 1)) (T2op hyp μ (EL (i + 1))), hite]
    simp only [Nat.add_right_cancel_iff]
  -- Parseval
  have hpar := b.hasSum_inner_mul_inner w (u j)
  have hb0 : ⟪w, b 0⟫ * ⟪b 0, u j⟫ = 0 := by rw [hb, hEL0, hu0, mul_zero]
  have hshift : HasSum (fun k => ⟪w, b (k + 1)⟫ * ⟪b (k + 1), u j⟫) ⟪w, u j⟫ := by
    have := (hasSum_nat_add_iff' 1).2 hpar
    simpa [hb0] using this
  have hval : ⟪w, u j⟫ = if i = j then 1 else 0 := by
    rw [inner_add_left, real_inner_comm (u j) (T2op hyp μ (EL (i + 1))),
      inner_T2op_symm hyp μ (EL (i + 1)) (u j), ← inner_add_right, hu j, hite]
    simp only [Nat.add_right_cancel_iff]
  refine ⟨?_, ?_⟩
  · -- absolute summability
    have s1 := (horth.comp (· + 1) (add_left_injective 1)).inner_products_summable (x := w)
    have s2 := (horth.comp (· + 1) (add_left_injective 1)).inner_products_summable (x := u j)
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) ((s1.add s2).div_const 2)
    rw [hterm, hb, abs_mul]
    simp only [Function.comp, Real.norm_eq_abs, sq_abs]
    rw [real_inner_comm (EL (k + 1)) w]
    have := two_mul_le_add_sq |⟪EL (k + 1), w⟫| |⟪EL (k + 1), u j⟫|
    rw [sq_abs, sq_abs] at this
    linarith
  · rw [← hval, ← hshift.tsum_eq]
    exact tsum_congr hterm

end inv

end SharpLSI
