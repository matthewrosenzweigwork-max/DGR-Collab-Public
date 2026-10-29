import SharpSymmetricLSI.Paper.GaussForm25

/-!
# R32 (G1): the variables `ξ_j = ⟨v_j, z⟩` are i.i.d. `N(0,1)` under `γ`

* `map_eq_gaussianReal_of_L2`: an `L²` limit of centered Gaussians with converging variances is
  centered Gaussian with the limit variance (characteristic functions).
* `map_xi_eq_pi`: if `⟨v_i, C v_j⟩ = δ_{ij}` and `ξ_j` are the row variables of `v`
  (`IsRowVariable v γ j (ξ j)`), then `(ξ_0, …, ξ_{J-1})` has law `N(0,1)^{⊗J}` under `γ`
  (Cramér–Wold: each `∑ t_j ξ_j` is `N(0, |t|²)`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped InnerProductSpace ENNReal NNReal

namespace SharpLSI

/-- `‖e^{itx} - e^{ity}‖ ≤ |t||x - y|`. -/
theorem norm_cexp_sub_le (t x y : ℝ) :
    ‖cexp (t * x * I) - cexp (t * y * I)‖ ≤ ‖t * (x - y)‖ := by
  have e : cexp (t * x * I) - cexp (t * y * I) =
      cexp (t * y * I) * (cexp (I * ↑(t * (x - y))) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  have h1 : ‖cexp (↑t * ↑y * I)‖ = 1 := by
    rw [← Complex.ofReal_mul]; exact Complex.norm_exp_ofReal_mul_I _
  rw [e, norm_mul, h1, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- **`L²` limits of centered Gaussians are centered Gaussian.** -/
theorem map_eq_gaussianReal_of_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hY : AEMeasurable Y P) {s : ℕ → ℝ≥0} {v : ℝ≥0}
    (hlaw : ∀ n, P.map (X n) = gaussianReal 0 (s n)) (hs : Tendsto s atTop (𝓝 v))
    (hL2 : Tendsto (fun n => eLpNorm (X n - Y) 2 P) atTop (𝓝 0)) :
    P.map Y = gaussianReal 0 v := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hcY : charFun (P.map Y) t = ∫ ω, cexp (t * Y ω * I) ∂P := by
    rw [charFun_apply_real, integral_map hY (by fun_prop)]
  have hcX : ∀ n, charFun (P.map (X n)) t = ∫ ω, cexp (t * X n ω * I) ∂P := fun n => by
    rw [charFun_apply_real, integral_map (hX n).aemeasurable (by fun_prop)]
  -- convergence of the characteristic functions
  have hconv : Tendsto (fun n => ∫ ω, cexp (t * X n ω * I) ∂P) atTop
      (𝓝 (∫ ω, cexp (t * Y ω * I) ∂P)) := by
    refine tendsto_integral_of_L1' _ (Eventually.of_forall fun n => ?_) ?_
    · refine Integrable.of_bound (C := 1) (by fun_prop) (Eventually.of_forall fun ω => ?_)
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
    · have hle : ∀ n, eLpNorm ((fun ω => cexp (t * X n ω * I)) - fun ω => cexp (t * Y ω * I)) 1 P
          ≤ ‖t‖ₑ * eLpNorm (X n - Y) 2 P := fun n => by
        have hc : Continuous fun y : ℝ => cexp (t * y * I) := by fun_prop
        have hm : AEStronglyMeasurable
            ((fun ω => cexp (t * X n ω * I)) - fun ω => cexp (t * Y ω * I)) P :=
          ((hc.measurable.comp (hX n)).aestronglyMeasurable).sub
            (hc.measurable.comp_aemeasurable hY).aestronglyMeasurable
        refine (eLpNorm_mono (g := fun ω => t * (X n ω - Y ω)) hm fun ω => ?_).trans ?_
        · exact norm_cexp_sub_le t (X n ω) (Y ω)
        · have : (fun ω => t * (X n ω - Y ω)) = t • (X n - Y) := by funext ω; simp
          rw [this, eLpNorm_const_smul]
          gcongr
          exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      have h0 : Tendsto (fun n => ‖t‖ₑ * eLpNorm (X n - Y) 2 P) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (a := ‖t‖ₑ) hL2 (Or.inr enorm_ne_top)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun _ => bot_le) hle
  have hlim : Tendsto (fun n => charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 v) t)) := by
    simp_rw [hlaw, charFun_gaussianReal]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have hs' : Tendsto (fun n => ((s n : ℝ) : ℂ)) atTop (𝓝 ((v : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (NNReal.continuous_coe.tendsto _ |>.comp hs)
    exact tendsto_const_nhds.sub ((hs'.mul tendsto_const_nhds).div_const _)
  rw [hcY]
  simp_rw [hcX] at hlim
  exact tendsto_nhds_unique hconv hlim

section joint
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (hCs : ∀ a b, C a b = C b a)
  {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
  {v : ℕ → ℕ → ℝ} (hv2 : ∀ j, Summable fun i => v j i ^ 2)
  (hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0)
  {ξ : ℕ → (ℕ → ℝ) → ℝ} (hξ : ∀ j, IsRowVariable v γ j (ξ j))
include hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ

omit hγ hv2 hvC hξ in
/-- `⟨x, C x⟩` over the first `n` coordinates is `⟨P_n x, (I+T)⁻¹ P_n x⟩`. -/
theorem quad_trunc_eq (w : L2N) (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, w a * C a b * w b =
      ⟪truncL2N n w, (ipT hS hσ0 hσ).symm (truncL2N n w)⟫_ℝ := by
  have htr : ∀ a, truncL2N n w a = if a < n then w a else 0 := fun a => rfl
  rw [inner_L2N, tsum_eq_sum (s := Finset.range n) fun a ha => by
    simp only [Finset.mem_range] at ha; simp [htr, ha]]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← tsum_C_mul hT hS hσ0 hσ hC hCs, tsum_eq_sum (s := Finset.range n) fun b hb => by
    simp only [Finset.mem_range] at hb; simp [htr, hb], Finset.mul_sum]
  simp only [Finset.mem_range] at ha
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [Finset.mem_range] at hb
  simp only [htr, ha, hb, if_true]; ring

/-- **`∑ t_j ξ_j` is `N(0, |t|²)`.** -/
theorem map_lin_xi {J : ℕ} (t : Fin J → ℝ) :
    γ.map (fun z => ∑ j : Fin J, t j * ξ j z) =
      gaussianReal 0 (∑ j : Fin J, t j ^ 2).toNNReal := by
  have := hγ.1
  set w : ℕ → ℝ := fun q => ∑ j : Fin J, t j * v j q with hw
  have hw2 : Summable fun q => w q ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun q => sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin J => t j * v j q))
      ?_
    refine Summable.mul_left _ (summable_sum fun j _ => ?_)
    simp_rw [mul_pow]; exact (hv2 j).mul_left _
  set W : L2N := mkL2N w hw2
  set V : ℕ → L2N := fun j => mkL2N (v j) (hv2 j)
  have hWV : W = ∑ j : Fin J, t j • V j := by
    ext q
    simp only [W, V, mkL2N_apply, hw, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]
  set Cop := (ipT hS hσ0 hσ).symm
  have hVV : ∀ i j, ⟪V i, Cop (V j)⟫_ℝ = if i = j then 1 else 0 := fun i j => by
    rw [inner_L2N, ← hvC i j]
    refine tsum_congr fun a => ?_
    rw [← tsum_C_mul hT hS hσ0 hσ hC hCs]
    rfl
  have hWW : ⟪W, Cop W⟫_ℝ = ∑ j : Fin J, t j ^ 2 := by
    rw [hWV, map_sum, sum_inner]
    simp_rw [inner_sum, map_smul, real_inner_smul_left, real_inner_smul_right, hVV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Fin.val_injective.ne (Ne.symm hj)])
      (by simp)]
    rw [if_pos rfl]; ring
  -- the approximants
  set X : ℕ → (ℕ → ℝ) → ℝ := fun n z => ∑ q ∈ Finset.range n, w q * z q
  have hX : ∀ n, Measurable (X n) := fun n => measurable_linSum _ _
  have hlaw : ∀ n, γ.map (X n) = gaussianReal 0
      (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, w a * C a b * w b).toNNReal :=
    fun n => hγ.2 _ _
  have hQ : Tendsto (fun n => ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, w a * C a b * w b)
      atTop (𝓝 (∑ j : Fin J, t j ^ 2)) := by
    have hQn : ∀ n, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, w a * C a b * w b =
        ⟪truncL2N n W, Cop (truncL2N n W)⟫_ℝ := fun n =>
      quad_trunc_eq hT hS hσ0 hσ hC hCs W n
    simp_rw [hQn]
    rw [← hWW]
    have hc : Continuous fun x : L2N => ⟪x, Cop x⟫_ℝ := by fun_prop
    exact (hc.tendsto W).comp (tendsto_truncL2N W)
  have hY : AEMeasurable (fun z => ∑ j : Fin J, t j * ξ j z) γ :=
    Finset.aemeasurable_fun_sum _ fun j _ =>
      ((hξ j).1.aestronglyMeasurable.aemeasurable).const_mul _
  refine map_eq_gaussianReal_of_L2 hX hY hlaw
    ((continuous_real_toNNReal.tendsto _).comp hQ) ?_
  -- `L²` convergence
  have hdiff : ∀ n, X n - (fun z => ∑ j : Fin J, t j * ξ j z) = ∑ j : Fin J,
      t j • (fun z => (∑ q ∈ Finset.range n, v j q * z q) - ξ j z) := fun n => by
    have hpt : ∀ z, X n z - ∑ j : Fin J, t j * ξ j z =
        ∑ j : Fin J, t j * ((∑ q ∈ Finset.range n, v j q * z q) - ξ j z) := fun z => by
      simp only [X, hw, Finset.sum_mul, mul_sub, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
    funext z
    rw [Pi.sub_apply, hpt z, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hm : ∀ (j : Fin J) n, AEStronglyMeasurable
      (t j • fun z => (∑ q ∈ Finset.range n, v j q * z q) - ξ j z) γ := fun j n =>
    ((measurable_linSum _ _).aestronglyMeasurable.sub (hξ j).1.aestronglyMeasurable).const_smul _
  have hle : ∀ n, eLpNorm (X n - fun z => ∑ j : Fin J, t j * ξ j z) 2 γ ≤
      ∑ j : Fin J, ‖t j‖ₑ *
        eLpNorm (fun z => (∑ q ∈ Finset.range n, v j q * z q) - ξ j z) 2 γ := fun n => by
    rw [hdiff]
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    exact Finset.sum_le_sum fun j _ => eLpNorm_const_smul_le
  have h0 : Tendsto (fun n => ∑ j : Fin J, ‖t j‖ₑ *
      eLpNorm (fun z => (∑ q ∈ Finset.range n, v j q * z q) - ξ j z) 2 γ) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin J)) fun j _ =>
      ENNReal.Tendsto.const_mul (a := ‖t j‖ₑ) (hξ j).2 (Or.inr enorm_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hle

/-- **The `ξ_j` are i.i.d. `N(0,1)` under `γ`.** -/
theorem map_xi_eq_pi (J : ℕ) :
    γ.map (fun z => fun j : Fin J => ξ j z) =
      Measure.pi (fun _ : Fin J => gaussianReal 0 1) := by
  have := hγ.1
  have hΞ : AEMeasurable (fun z => fun j : Fin J => ξ j z) γ :=
    aemeasurable_pi_iff.2 fun j => (hξ j).1.aestronglyMeasurable.aemeasurable
  have hE : (γ.map fun z => fun j : Fin J => ξ j z).map (WithLp.toLp 2) =
      (Measure.pi (fun _ : Fin J => gaussianReal 0 1)).map (WithLp.toLp 2) := by
    rw [map_pi_eq_stdGaussian]
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_stdGaussian, charFun_apply, integral_map (WithLp.measurable_toLp 2 _).aemeasurable
      (by fun_prop), integral_map hΞ (by fun_prop)]
    set tt : Fin J → ℝ := WithLp.ofLp t
    have hin : ∀ z : ℕ → ℝ, ⟪WithLp.toLp 2 (fun j : Fin J => ξ j z), t⟫_ℝ =
        ∑ j : Fin J, tt j * ξ j z := fun z => by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [tt, mul_comm]
    simp_rw [hin]
    have h2 : ∫ z, cexp (↑(∑ j : Fin J, tt j * ξ j z) * I) ∂γ =
        charFun (γ.map fun z => ∑ j : Fin J, tt j * ξ j z) 1 := by
      have hY : AEMeasurable (fun z => ∑ j : Fin J, tt j * ξ j z) γ :=
        Finset.aemeasurable_fun_sum _ fun j _ =>
          ((hξ j).1.aestronglyMeasurable.aemeasurable).const_mul _
      rw [charFun_apply_real, integral_map hY (by fun_prop)]
      simp
    rw [h2, map_lin_xi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ tt, charFun_gaussianReal]
    have hn : ‖t‖ ^ 2 = ∑ j : Fin J, tt j ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [tt]
    have hq : 0 ≤ ∑ j : Fin J, tt j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [show ((‖t‖ : ℝ) : ℂ) ^ 2 = ((∑ j : Fin J, tt j ^ 2 : ℝ) : ℂ) by
      rw [← hn]; push_cast; ring, Real.coe_toNNReal _ hq]
    congr 1; push_cast; ring
  have hinj := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin J)) => ν.map WithLp.ofLp) hE
  simp only at hinj
  rw [Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _),
    Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)] at hinj
  have hid : (WithLp.ofLp ∘ WithLp.toLp 2 : (Fin J → ℝ) → Fin J → ℝ) = id := rfl
  rwa [hid, Measure.map_id, Measure.map_id] at hinj

end joint

end SharpLSI
