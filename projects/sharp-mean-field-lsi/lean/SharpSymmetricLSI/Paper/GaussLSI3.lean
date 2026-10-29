import SharpSymmetricLSI.Paper.GaussLSI2
import SharpSymmetricLSI.Paper.Prop23Assembly1
import SharpSymmetricLSI.Paper.ULimit4

/-!
# (8.13) (lane s42), step 1: `⟨v_fn, (I+T)^{-1} v_fn⟩ = ⟨v, C v⟩`

For finitely supported `v`, let `v_fn = ∑_{j<n} v_j e_{j+1} ∈ L²_0(μ)` and `u` the mean-zero
solution of `(I+T) u = v_fn` (Paper/Prop23Assembly1). For every `C` with
`IsInverseOfIPlus (Tmat W μ e) C`, `⟨v_fn, u⟩ = ∑_{i,j<n} v_i C_{ij} v_j` (`inner_solve_eq_quad`).

Proof: the coefficients `c_i = ⟨e_{i+1}, u⟩` and `x = C v` both solve `y + T y = v` in `ℓ²`
(Parseval in the reference basis, resp. `IsInverseOfIPlus`); since `T` is symmetric and
Hilbert–Schmidt, `∑ v_i c_i = ∑ ((I+T)x)_i c_i = ∑ x_l ((I+T)c)_l = ∑ v_l x_l`.
-/

noncomputable section
open MeasureTheory Filter Topology Finset

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

theorem summable_sq_finsetSum {f : ℕ → ℕ → ℝ} (s : Finset ℕ)
    (hf : ∀ j ∈ s, Summable fun l => f j l ^ 2) :
    Summable fun l => (∑ j ∈ s, f j l) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ((h1.add h2).mul_left 2).of_nonneg_of_le (fun _ => sq_nonneg _) fun l => ?_
    nlinarith [sq_nonneg (f a l - ∑ j ∈ s, f j l)]

/-- **`⟨v_fn, (I+T)^{-1} v_fn⟩ = ⟨v, Cv⟩`.** -/
theorem inner_solve_eq_quad (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) (n : ℕ) (v : ℕ → ℝ) :
    ∃ u : Lp ℝ 2 (μ : Measure (Torus d)), ⟪oneL μ, u⟫ = 0 ∧
      u + T2op hyp μ u = ∑ i ∈ range n, v i • (he.memH1 (i + 1)).2.1.toLp (e (i + 1)) ∧
      ⟪∑ i ∈ range n, v i • (he.memH1 (i + 1)).2.1.toLp (e (i + 1)), u⟫ =
        ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j := by
  set μm := (μ : Measure (Torus d))
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
      have := (Submodule.mem_orthogonal _ x).1 hx (EL n) (Submodule.subset_span ⟨n, rfl⟩)
      rw [hinEL] at this
      rw [← this]; congr 1; funext y; ring
    exact (Lp.eq_zero_iff_ae_eq_zero).2 (he.complete (⇑x) (Lp.memLp x) h0)
  set b := HilbertBasis.mkOfOrthogonalEqBot horth hsp
  have hb : ∀ n, b n = EL n := fun n => by simp [b, HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hEL0 : ∀ x : Lp ℝ 2 μm, ⟪EL 0, x⟫ = ⟪oneL μ, x⟫ := fun x => by
    rw [hinEL, inner_oneL, he.zero]; simp; rfl
  set vL := ∑ i ∈ range n, v i • EL (i + 1)
  have hvL : ∀ i, ⟪EL (i + 1), vL⟫ = vtr v n i := fun i => by
    simp only [vL, inner_sum, inner_smul_right, hite, Nat.add_right_cancel_iff, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_range, vtr]
  have hvL0 : ⟪oneL μ, vL⟫ = 0 := by
    rw [← hEL0]
    simp only [vL, inner_sum, inner_smul_right, hite]
    simp
  obtain ⟨u, hu0, hu⟩ := exists_solve_IT hyp μ hd hr hμ hvL0
  refine ⟨u, hu0, hu, ?_⟩
  -- the matrix of `T`
  have hTmat : ∀ i k, Tmat W μm e i k = ⟪T2op hyp μ (EL (i + 1)), EL (k + 1)⟫ := fun i k => by
    rw [real_inner_comm, ← inner_T2op_symm hyp μ (EL (k + 1)) (EL (i + 1)), inner_T2op]
    unfold Tmat
    refine integral_congr_ae ?_
    filter_upwards [hEL (i + 1)] with x hx
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [hEL (k + 1)] with y hy
    rw [hy]; ring
  set c : ℕ → ℝ := fun i => ⟪EL (i + 1), u⟫
  set x : ℕ → ℝ := fun l => ∑ j ∈ range n, C l j * v j
  have hc2 : Summable fun i => c i ^ 2 := by
    have := (horth.comp (· + 1) (add_left_injective 1)).inner_products_summable (x := u)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hx2 : Summable fun l => x l ^ 2 :=
    summable_sq_finsetSum (f := fun j l => C l j * v j) (range n) fun j _ =>
      ((hC j).1.mul_right (v j ^ 2)).congr fun l => by ring
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  -- (1) `c + T c = v`
  have h1 : ∀ i, HasSum (fun l => Tmat W μm e i l * c l) (vtr v n i - c i) := fun i => by
    have hpar := b.hasSum_inner_mul_inner (T2op hyp μ (EL (i + 1))) u
    have hb0 : ⟪T2op hyp μ (EL (i + 1)), b 0⟫ * ⟪b 0, u⟫ = 0 := by rw [hb, hEL0, hu0, mul_zero]
    have hsh := (hasSum_nat_add_iff' 1).2 hpar
    simp only [Finset.range_one, Finset.sum_singleton, hb0, sub_zero] at hsh
    have e1 : ⟪T2op hyp μ (EL (i + 1)), u⟫ = vtr v n i - c i := by
      have := congrArg (fun g => ⟪EL (i + 1), g⟫) hu
      simp only [inner_add_right, hvL] at this
      rw [real_inner_comm, inner_T2op_symm hyp μ (EL (i + 1)) u]
      linarith
    rw [e1] at hsh
    refine hsh.congr_fun fun l => ?_
    simp only [hb, hTmat, c]
  -- (2) `x + T x = v`
  have h2 : ∀ i, HasSum (fun l => Tmat W μm e i l * x l) (vtr v n i - x i) := fun i => by
    have hcol : ∀ j, HasSum (fun l => ((if i = l then 1 else 0) + Tmat W μm e i l) * C l j)
        (if i = j then 1 else 0) := fun j => by
      have := ((hC j).2 i)
      have hs : Summable fun l => ((if i = l then 1 else 0) + Tmat W μm e i l) * C l j :=
        this.1.of_abs
      rw [← this.2]; exact hs.hasSum
    have hsum := hasSum_sum (s := range n) fun j _ => (hcol j).mul_left (v j)
    have hval : ∑ j ∈ range n, v j * (if i = j then (1 : ℝ) else 0) = vtr v n i := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, vtr]
    rw [hval] at hsum
    have hδ : HasSum (fun l => (if i = l then (1 : ℝ) else 0) * x l) (x i) := by
      have := hasSum_ite_eq i (x i)
      refine this.congr_fun fun l => ?_
      by_cases h : i = l
      · subst h; simp
      · simp [h, Ne.symm h]
    have := hsum.sub hδ
    refine this.congr_fun fun l => ?_
    simp only [x, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- (3) symmetry of the double sum
  have hprod : Summable (Function.uncurry fun i l => Tmat W μm e i l * x l * c i) := by
    have hxc : Summable fun p : ℕ × ℕ => (x p.2 * c p.1) ^ 2 := by
      have := (hx2.mul_of_nonneg hc2 (fun _ => sq_nonneg _) (fun _ => sq_nonneg _))
      refine (this.comp_injective (Equiv.prodComm ℕ ℕ).injective).congr fun p => ?_
      simp [Equiv.prodComm, mul_pow]
    refine ((hS.add hxc).div_const 2).of_norm_bounded fun p => ?_
    rw [Real.norm_eq_abs]
    simp only [Function.uncurry]
    have := two_mul_le_add_sq |Tmat W μm e p.1 p.2| |x p.2 * c p.1|
    rw [sq_abs, sq_abs] at this
    rw [mul_assoc, abs_mul]
    linarith
  have hz : ∀ i, (∑' l, Tmat W μm e i l * x l) = vtr v n i - x i := fun i => (h2 i).tsum_eq
  have hy : ∀ i, (∑' l, Tmat W μm e i l * c l) = vtr v n i - c i := fun i => (h1 i).tsum_eq
  have hvt2 := summable_sq_vtr (v := v) n
  have hzc : Summable fun i => (vtr v n i - x i) * c i :=
    (tsum_mul_sq_le (summable_sq_sub hvt2 hx2) hc2).1
  have hyx : Summable fun l => (vtr v n l - c l) * x l :=
    (tsum_mul_sq_le (summable_sq_sub hvt2 hc2) hx2).1
  have hxc : Summable fun i => x i * c i := (tsum_mul_sq_le hx2 hc2).1
  have hcx : Summable fun l => c l * x l := (tsum_mul_sq_le hc2 hx2).1
  have hdouble : ∑' i, (vtr v n i - x i) * c i = ∑' l, (vtr v n l - c l) * x l := by
    calc ∑' i, (vtr v n i - x i) * c i = ∑' i, ∑' l, Tmat W μm e i l * x l * c i := by
          refine tsum_congr fun i => ?_; rw [← hz i, ← tsum_mul_right]
      _ = ∑' l, ∑' i, Tmat W μm e i l * x l * c i := hprod.tsum_comm.symm
      _ = ∑' l, (vtr v n l - c l) * x l := by
          refine tsum_congr fun l => ?_
          rw [← hy l, ← tsum_mul_right]
          refine tsum_congr fun i => ?_
          rw [hT i l]; ring
  have hmain : ∑' i, vtr v n i * c i = ∑' l, vtr v n l * x l := by
    have e1 : ∑' i, vtr v n i * c i = ∑' i, x i * c i + ∑' i, (vtr v n i - x i) * c i := by
      rw [← hxc.tsum_add hzc]; exact tsum_congr fun i => by ring
    have e2 : ∑' l, vtr v n l * x l = ∑' l, c l * x l + ∑' l, (vtr v n l - c l) * x l := by
      rw [← hcx.tsum_add hyx]; exact tsum_congr fun l => by ring
    rw [e1, e2, hdouble]
    congr 1
    exact tsum_congr fun i => by ring
  have lhs : ⟪vL, u⟫ = ∑' i, vtr v n i * c i := by
    rw [tsum_eq_sum (s := range n) fun i hi => by rw [vtr_eq_zero hi, zero_mul]]
    simp only [vL, sum_inner, real_inner_smul_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [vtr, Finset.mem_range.mp hi, ite_true, c]
  have rhs : ∑' l, vtr v n l * x l = ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j := by
    rw [tsum_eq_sum (s := range n) fun i hi => by rw [vtr_eq_zero hi, zero_mul]]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [vtr, Finset.mem_range.mp hi, ite_true, x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [lhs, hmain, rhs]

end SharpLSI
