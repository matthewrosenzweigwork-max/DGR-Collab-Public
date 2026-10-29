import SharpSymmetricLSI.Paper.R29Joint1

/-!
# Truncated joint law of `(∑ x_α B_{α,N}, U_N, Z_N)` (Phase 3, lane D; R29 joint law)

For a finite set `S` of occupations and a truncation level, the triple
`(∑_{α∈S} x_α B_{α,N}, ½∑_{a,b} T_{ab} Z_a Z_b + D_N, (Z_n)_{n<J})` is a fixed continuous function
of the normalized sums and of almost surely convergent rest data, hence converges in law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section ker
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

/-- The kernel data with the modification `emod`. -/
theorem kerData_emod :
    KerData (μ : Measure (Torus d)) (centeredKernel W μ) (emod he) (Tmat W μ e) := by
  set μm := (μ : Measure (Torus d))
  have hae : ∀ i, e i =ᵐ[μm] emod he i := fun i => (emod_ae_eq he i).symm
  refine ⟨measurable_centeredKernel hyp μm, centeredKernel_bdd hyp μm, centeredKernel_symm' hyp μ,
    fun w => ?_, measurable_emod he, memLp_emod he, integral_emod_mul he,
    integral_emod_succ he, fun a b => ?_, hasSum_Tmat_sq hyp hμ he⟩
  · simp_rw [centeredKernel_symm' hyp μ _ w]; exact integral_centeredKernel hyp _ w
  · unfold Tmat
    refine integral_congr_ae ?_
    filter_upwards [hae (a + 1)] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hae (b + 1)] with y hy
    rw [hx, hy]

omit hyp hμ he in
/-- `fluct = zSum`. -/
theorem fluct_eq_zSum (e0 : ℕ → Torus d → ℝ) {N : ℕ} (n : ℕ) (X : Config N d) :
    fluct e0 N n X = zSum e0 N n X := by
  unfold fluct zSum
  rw [Real.rpow_neg (Nat.cast_nonneg N), ← Real.sqrt_eq_rpow]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The truncated joint law.** -/
theorem tendstoInDistribution_trunc (S : Finset (ℕ →₀ ℕ)) (x0 : (ℕ →₀ ℕ) → ℝ) (J R : ℕ) :
    TendstoInDistribution
      (fun N (ω : ℕ → Torus d) =>
        (∑ α ∈ S, x0 α * occBasis (emod he) α N (fun i : Fin N => ω i),
          1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), Tmat W μ e a b *
            (zSum (emod he) N a (fun i : Fin N => ω i) * zSum (emod he) N b (fun i : Fin N => ω i)) +
            1 / 2 * ((∑ k ∈ Finset.range N,
              hdiag (centeredKernel W μ) (Tmat W μ e) (emod he) (R + J) (ω k)) / N),
          fun n : Fin J => zSum (emod he) N n (fun i : Fin N => ω i)))
      atTop
      (fun z => (∑ α ∈ S, x0 α * hermiteBasis α z,
        1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J),
          Tmat W μ e a b * (z a * z b) +
          1 / 2 * ∫ x, hdiag (centeredKernel W μ) (Tmat W μ e) (emod he) (R + J) x
            ∂(μ : Measure (Torus d)),
        fun n : Fin J => z n))
      (fun _ => Measure.infinitePi fun _ : ℕ => (μ : Measure (Torus d))) gammaRef := by
  set μm := (μ : Measure (Torus d))
  set κ := centeredKernel W μ
  set T := Tmat W μ e
  have hDk := kerData_emod hyp hμ he
  set K := R + J + ∑ α ∈ S, (α.support.sup id + 1)
  set D := ∑ α ∈ S, occSize α
  have hJK : J ≤ K := by omega
  have hRK : R + J ≤ K := Nat.le_add_right _ _
  have hA : ∀ α ∈ S, ∀ n, K ≤ n → α n = 0 := fun α hα n hn => by
    by_contra h
    have h1 : n ≤ α.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)
    have h2 : α.support.sup id + 1 ≤ ∑ α ∈ S, (α.support.sup id + 1) :=
      Finset.single_le_sum (f := fun α : ℕ →₀ ℕ => α.support.sup id + 1) (fun _ _ => Nat.zero_le _) hα
    omega
  have hD : ∀ α ∈ S, occSize α ≤ D := fun α hα =>
    Finset.single_le_sum (f := occSize) (fun _ _ => Nat.zero_le _) hα
  set f : Fin K → Torus d → ℝ := fun k => emod he (k + 1)
  set P := Measure.infinitePi fun _ : ℕ => μm
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_emod he _
  have hfL : ∀ k, MemLp (f k) 2 μm := fun k => memLp_emod he _
  have hclt : TendstoInDistribution (cltVec f) atTop (gaussVec K) (fun _ => P) gammaRef :=
    tendstoInDistribution_cltVec hfm hfL (fun k => integral_emod_succ he _) fun a b => by
      simp only [f]; rw [integral_emod_mul]
      by_cases h : a = b
      · simp [h]
      · have : (a : ℕ) ≠ b := fun h' => h (Fin.ext h')
        simp [h, this]
  -- the diagonal term
  set Dt : ℕ → (ℕ → Torus d) → ℝ := fun N ω =>
    1 / 2 * ((∑ k ∈ Finset.range N, hdiag κ T (emod he) (R + J) (ω k)) / N)
  set cD : ℝ := 1 / 2 * ∫ x, hdiag κ T (emod he) (R + J) x ∂μm
  have hDm : ∀ N, Measurable (Dt N) := fun N =>
    ((Finset.measurable_sum _ fun k _ => (hDk.measurable_hdiag _).comp
      (measurable_pi_apply k)).div_const _).const_mul _
  have hDae : ∀ᵐ ω ∂P, Tendsto (fun N => Dt N ω) atTop (𝓝 cD) := by
    filter_upwards [slln_infinitePi (hDk.measurable_hdiag (R + J)) (hDk.integrable_hdiag _)]
      with ω hω
    exact hω.const_mul _
  -- the rest data
  have hrm : ∀ N, Measurable fun ω => (restN S (D := D) f N ω, Dt N ω) := fun N =>
    (measurable_restN_emod he S K D N).prodMk (hDm N)
  have hrest : ∀ᵐ ω ∂P, Tendsto (fun N => (restN S (D := D) f N ω, Dt N ω)) atTop
      (𝓝 (restInf S (K := K) (D := D), cD)) := by
    filter_upwards [restN_tendsto_ae_emod he S K D, hDae] with ω h1 h2
    exact h1.prodMk_nhds h2
  -- the continuous map
  set G : EuclideanSpace ℝ (Fin K) × (RestSp K D S × ℝ) → ℝ × ℝ × (Fin J → ℝ) := fun u =>
    (∑ α : S, x0 α * (occPhi S hJK (u.1, u.2.1)).1 α,
      1 / 2 * ∑ a : Fin (R + J), ∑ b : Fin (R + J), T a b *
        (u.1 (Fin.castLE hRK a) * u.1 (Fin.castLE hRK b)) + u.2.2,
      (occPhi S hJK (u.1, u.2.1)).2)
  have hG : Continuous G := by
    have h1 : Continuous fun u : EuclideanSpace ℝ (Fin K) × (RestSp K D S × ℝ) =>
        occPhi S hJK (u.1, u.2.1) :=
      (continuous_occPhi S hJK).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have h1' : Continuous fun u : EuclideanSpace ℝ (Fin K) × (RestSp K D S × ℝ) =>
        (occPhi S hJK (u.1, u.2.1)).1 := continuous_fst.comp h1
    refine Continuous.prodMk (continuous_finsetSum _ fun α _ =>
      continuous_const.mul ((continuous_apply α).comp h1'))
      (Continuous.prodMk ?_ (continuous_snd.comp h1))
    have hu : ∀ i : Fin K, Continuous fun u : EuclideanSpace ℝ (Fin K) × (RestSp K D S × ℝ) =>
        u.1 i := fun i => (PiLp.continuous_apply 2 (fun _ : Fin K => ℝ) i).comp continuous_fst
    refine Continuous.add ?_ (continuous_snd.comp continuous_snd)
    refine continuous_const.mul ?_
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact continuous_const.mul ((hu _).mul (hu _))
  have hdist := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const hG
    (tendstoInMeasure_of_tendsto_ae (fun N => (hrm N).aestronglyMeasurable) hrest)
    (fun N => (hrm N).aemeasurable)
  -- identify the sequence and the limit
  have hcv : ∀ N (ω : ℕ → Torus d) (a : Fin (R + J)),
      cltVec f N ω (Fin.castLE hRK a) = zSum (emod he) N a (fun i : Fin N => ω i) := fun N ω a => by
    simp only [cltVec, zSum, f, PiLp.toLp_apply, Fin.val_castLE]
    rw [Fin.sum_univ_eq_sum_range (fun k => emod he (↑a + 1) (ω k))]
  have hseq : ∀ N, 1 ≤ N → ∀ ω, G (cltVec f N ω, (restN S (D := D) f N ω, Dt N ω)) =
      (∑ α ∈ S, x0 α * occBasis (emod he) α N (fun i : Fin N => ω i),
        1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), T a b *
          (zSum (emod he) N a (fun i : Fin N => ω i) * zSum (emod he) N b (fun i : Fin N => ω i)) +
          Dt N ω,
        fun n : Fin J => zSum (emod he) N n (fun i : Fin N => ω i)) := by
    intro N hN ω
    have hpw := occPhi_pathwise hJK hA hD (emod_zero he) hN ω
    simp only [G]
    rw [hpw]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only
      rw [← Finset.sum_coe_sort S]
    · simp only
      congr 1
      simp_rw [hcv]
      rw [sum_fin_fin_eq_range (fun a b => T a b * (zSum (emod he) N a (fun i : Fin N => ω i) *
        zSum (emod he) N b (fun i : Fin N => ω i)))]
    · funext n
      simp only
      exact fluct_eq_zSum _ n _
  have hlim : ∀ z, G (gaussVec K z, (restInf S (K := K) (D := D), cD)) =
      (∑ α ∈ S, x0 α * hermiteBasis α z,
        1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), T a b * (z a * z b) + cD,
        fun n : Fin J => z n) := by
    intro z
    simp only [G]
    rw [occPhi_limit hJK hA hD z]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only
      rw [← Finset.sum_coe_sort S]
    · simp only
      congr 1
      simp only [gaussVec, PiLp.toLp_apply, Fin.val_castLE]
      rw [sum_fin_fin_eq_range (fun a b => T a b * (z a * z b))]
  have hlimfun : (fun z => G (gaussVec K z, (restInf S (K := K) (D := D), cD))) =
      fun z => (∑ α ∈ S, x0 α * hermiteBasis α z,
        1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), T a b * (z a * z b) + cD,
        fun n : Fin J => z n) := funext hlim
  rw [hlimfun] at hdist
  have hrestr : ∀ N, Measurable fun (ω : ℕ → Torus d) (i : Fin N) => ω i := fun N => by fun_prop
  have hzm : ∀ N a, Measurable fun ω : ℕ → Torus d => zSum (emod he) N a (fun i : Fin N => ω i) :=
    fun N a => by
      unfold zSum
      exact (Finset.measurable_sum _ fun l _ => (measurable_emod he _).comp
        (measurable_pi_apply (X := fun _ : ℕ => Torus d) _)).const_mul _
  have hBm : ∀ N α, Measurable fun ω : ℕ → Torus d => occBasis (emod he) α N (fun i : Fin N => ω i) :=
    fun N α => by
      unfold occBasis
      exact (Finset.measurable_sum _ fun c _ => Finset.measurable_prod _ fun i _ =>
        (measurable_emod he _).comp (measurable_pi_apply (X := fun _ : ℕ => Torus d) _)).const_mul _
  refine ⟨fun N => ?_, hdist.aemeasurable_limit, ?_⟩
  · refine Measurable.aemeasurable (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))
    · exact Finset.measurable_sum _ fun α _ => (hBm N α).const_mul _
    · exact ((Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
        ((hzm N a).mul (hzm N b)).const_mul _).const_mul _).add (hDm N)
    · exact measurable_pi_iff.mpr fun n => hzm N n
  · refine hdist.tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    congr 2
    funext ω
    exact hseq N hN ω

end ker

end SharpLSI
