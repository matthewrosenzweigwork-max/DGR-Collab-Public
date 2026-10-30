import DGPS.Lipschitz.T01CovarianceMatrix
import DGPS.Lipschitz.T01OccupationCompactness
import SharpSymmetricLSI.Paper.R29Joint3

/-!
# The actual common-reference symmetric joint law

The positive spectral matrix is the actual centered-kernel matrix on the same reference and
basis as occupation compactness. Zero row and column coefficients are removed explicitly.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI

variable {d : ℕ}

private def positivePairEquiv : (ℕ × ℕ) ≃ {p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2} where
  toFun p := ⟨(p.1 + 1, p.2 + 1), by omega⟩
  invFun p := (p.1.1 - 1, p.1.2 - 1)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> omega

/-- Parseval on the physical positive spectral modes; the deterministic constant is removed. -/
theorem t01_hasSum_positive_kernel_sq (S : Spec d) (aux : Aux S) (D : KData d)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (hK : ∀ x y, D.K x y = D.K y x) :
    HasSum (fun p : ℕ × ℕ => TK S D.K (p.1 + 1) (p.2 + 1) ^ 2)
      (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu) := by
  have hs := hasSum_prod_sq S D
  rw [← hasSum_subtype_iff_of_support_subset
    (s := {p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2})] at hs
  · exact positivePairEquiv.hasSum_iff.mpr hs
  · intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    by_contra hn
    apply hp
    have hz : p.1 = 0 ∨ p.2 = 0 := by
      simp only [Set.mem_setOf_eq, not_and_or, not_le] at hn
      omega
    rcases hz with hz | hz
    · rw [show TK S D.K p.1 p.2 = 0 from hz ▸ TK_zero_left S D aux.v0 hc _]
      simp
    · rw [show TK S D.K p.1 p.2 = 0 from hz ▸ TK_zero_right S D aux.v0 hc hK _]
      simp

/-- The exact legacy kernel-data interface for the common actual reference witness. -/
theorem t01_actual_kernelData_emod (J : InteractionData d) (S : Spec d) (aux : Aux S)
    (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) [IsProbabilityMeasure S.mu] :
    KerData S.mu (SharpLSI.centeredKernel J.W S.mu) (emod he) (Tmat J.W S.mu S.v) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hDs : D.K = SharpLSI.centeredKernel J.W S.mu :=
    hD.trans (legacy_centeredKernel_eq J S.mu).symm
  have hsym : ∀ x y, D.K x y = D.K y x := by
    intro x y
    rw [hD]
    exact centeredKernel_symm J S.mu x y
  have hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
    intro y
    simp only [hD, centeredKernel_symm J S.mu _ y]
    exact integral_centeredKernel_right J S.mu y
  have hae : ∀ i, S.v i =ᵐ[S.mu] emod he i := fun i => (emod_ae_eq he i).symm
  refine ⟨?_, ?_, ?_, ?_, measurable_emod he, memLp_emod he,
    integral_emod_mul he, integral_emod_succ he, ?_, ?_⟩
  · rw [← hDs]
    exact D.Kc.measurable
  · obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn D.Kc.continuousOn
    refine ⟨B, fun x y => ?_⟩
    rw [← hDs]
    simpa only [Real.norm_eq_abs, Function.uncurry] using hB (x, y) (Set.mem_univ _)
  · rw [← hDs]
    exact hsym
  · rw [← hDs]
    exact hc
  · intro a b
    unfold Tmat
    refine integral_congr_ae ?_
    filter_upwards [hae (a + 1)] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hae (b + 1)] with y hy
    rw [hx, hy]
  · have hs := t01_hasSum_positive_kernel_sq S aux D hc hsym
    simp only [← t01_Tmat_eq_TK S D J hD] at hs
    rw [← hDs, ← integral_prod _ (D.integrable_K2 S)]
    exact hs

private theorem t01_memLp_occBasis {ν : Measure (Torus d)} [IsProbabilityMeasure ν]
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis ν e lam)
    (α : ℕ →₀ ℕ) (N : ℕ) :
    MemLp (occBasis e α N) 2 (Measure.pi fun _ : Fin N => ν) := by
  unfold occBasis
  exact (memLp_finsetSum _ fun c _ => memLp_prod_eval fun i => he.memLp _).const_mul _

section Joint

variable {W : Torus d → Torus d → ℝ} {μ : ProbabilityMeasure (Torus d)}
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hDk : KerData (μ : Measure (Torus d)) (SharpLSI.centeredKernel W μ)
    (emod he) (Tmat W μ e))
include he hDk

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The truncated joint law.** -/
private theorem t01_tendstoInDistribution_trunc (S : Finset (ℕ →₀ ℕ)) (x0 : (ℕ →₀ ℕ) → ℝ) (J R : ℕ) :
    TendstoInDistribution
      (fun N (ω : ℕ → Torus d) =>
        (∑ α ∈ S, x0 α * occBasis (emod he) α N (fun i : Fin N => ω i),
          1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), Tmat W μ e a b *
            (zSum (emod he) N a (fun i : Fin N => ω i) * zSum (emod he) N b (fun i : Fin N => ω i)) +
            1 / 2 * ((∑ k ∈ Finset.range N,
              hdiag (SharpLSI.centeredKernel W μ) (Tmat W μ e) (emod he) (R + J) (ω k)) / N),
          fun n : Fin J => zSum (emod he) N n (fun i : Fin N => ω i)))
      atTop
      (fun z => (∑ α ∈ S, x0 α * hermiteBasis α z,
        1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J),
          Tmat W μ e a b * (z a * z b) +
          1 / 2 * ∫ x, hdiag (SharpLSI.centeredKernel W μ) (Tmat W μ e) (emod he) (R + J) x
            ∂(μ : Measure (Torus d)),
        fun n : Fin J => z n))
      (fun _ => Measure.infinitePi fun _ : ℕ => (μ : Measure (Torus d))) gammaRef := by
  set μm := (μ : Measure (Torus d))
  set κ := SharpLSI.centeredKernel W μ
  set T := Tmat W μ e
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

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The joint law (7.4)–(7.5) (iii).** -/
theorem t01_joint_law_of_kernelData {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q) (J : ℕ)
    {Ns : ℕ → ℕ} (hNs : Tendsto Ns atTop atTop) (Ψ : (k : ℕ) → Config (Ns k) d → ℝ)
    (hΨL : ∀ k, MemLp (Ψ k) 2 (Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d))))
    (x0 : (ℕ →₀ ℕ) → ℝ) {Ψinf : (ℕ → ℝ) → ℝ} (hΨinf : MemLp Ψinf 2 gammaRef)
    (hcoef : ∀ α, Tendsto (fun k => ∫ X, Ψ k X * occBasis e α (Ns k) X
      ∂(Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d)))) atTop (𝓝 (x0 α)))
    (S : ℕ → Finset (ℕ →₀ ℕ)) {εt : ℕ → ℝ} (hεt : Tendsto εt atTop (𝓝 0))
    (htail : ∀ R k, ∫ X, (Ψ k X - ∑ α ∈ S R, (∫ Y, Ψ k Y * occBasis e α (Ns k) Y
        ∂(Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d)))) * occBasis e α (Ns k) X) ^ 2
        ∂(Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d))) ≤ εt R)
    (htailInf : ∀ R, ∫ z, (Ψinf z - ∑ α ∈ S R, x0 α * hermiteBasis α z) ^ 2 ∂gammaRef ≤ εt R)
    (g : ℝ × ℝ × (Fin J → ℝ) →ᵇ ℝ) :
    Tendsto (fun k => ∫ X, g (Ψ k X, Ucentered W μ (Ns k) X, fun n => fluct e (Ns k) n X)
        ∂(Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d)))) atTop
      (𝓝 (∫ z, g (Ψinf z, Uinf W μ Q z, fun n => z n) ∂gammaRef)) := by
  set μm := (μ : Measure (Torus d))
  set κ := SharpLSI.centeredKernel W μ
  set T := Tmat W μ e
  set P := Measure.infinitePi fun _ : ℕ => μm
  set e' := emod he
  set PN : (k : ℕ) → Measure (Config (Ns k) d) := fun k => Measure.pi fun _ : Fin (Ns k) => μm
  -- measurable modifications
  set Ψm : (k : ℕ) → Config (Ns k) d → ℝ := fun k => (hΨL k).aestronglyMeasurable.mk (Ψ k)
  have hΨm : ∀ k, Measurable (Ψm k) := fun k =>
    (hΨL k).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hΨΨ : ∀ k, Ψ k =ᵐ[PN k] Ψm k := fun k => (hΨL k).aestronglyMeasurable.ae_eq_mk
  set Ψi := hΨinf.aestronglyMeasurable.mk Ψinf
  have hΨi : Measurable Ψi := hΨinf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hΨiΨ : Ψinf =ᵐ[gammaRef] Ψi := hΨinf.aestronglyMeasurable.ae_eq_mk
  have hΨiL : MemLp Ψi 2 gammaRef := hΨinf.ae_eq hΨiΨ
  -- the objects
  set Vk : ℕ → (ℕ → Torus d) → ℝ × ℝ × (Fin J → ℝ) := fun k ω =>
    (Ψm k (fun i => ω i), Ugen κ (Ns k) (fun i => ω i),
      fun n => zSum e' (Ns k) n (fun i : Fin (Ns k) => ω i))
  set Wk : ℕ → ℕ → (ℕ → Torus d) → ℝ × ℝ × (Fin J → ℝ) := fun R k ω =>
    (∑ α ∈ S R, x0 α * occBasis e' α (Ns k) (fun i : Fin (Ns k) => ω i),
      1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), T a b *
        (zSum e' (Ns k) a (fun i : Fin (Ns k) => ω i) * zSum e' (Ns k) b (fun i : Fin (Ns k) => ω i)) +
        1 / 2 * ((∑ l ∈ Finset.range (Ns k), hdiag κ T e' (R + J) (ω l)) / (Ns k)),
      fun n : Fin J => zSum e' (Ns k) n (fun i : Fin (Ns k) => ω i))
  set Y : (ℕ → ℝ) → ℝ × ℝ × (Fin J → ℝ) := fun z => (Ψi z, Q z / 2 + diagMean W μ / 2, fun n => z n)
  set Yr : ℕ → (ℕ → ℝ) → ℝ × ℝ × (Fin J → ℝ) := fun R z =>
    (∑ α ∈ S R, x0 α * hermiteBasis α z,
      1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J), T a b * (z a * z b) +
        1 / 2 * ∫ x, hdiag κ T e' (R + J) x ∂μm, fun n : Fin J => z n)
  have hW : ∀ R, TendstoInDistribution (Wk R) atTop (Yr R) (fun _ => P) gammaRef := fun R =>
    TendstoInDistribution.comp_atTop (t01_tendstoInDistribution_trunc he hDk (S R) x0 J R) hNs
  -- the error sizes
  set κ' : ℕ → Torus d → Torus d → ℝ := fun R x y => κ x y - kTrunc T e' (R + J) x y
  set εp : ℕ → ℝ := fun R => max (εt R) 0
  set δ : ℕ → ℝ := fun R => Real.sqrt (εp R) + 1 / ((R : ℝ) + 1) +
    Real.sqrt (1 / 2 * ∫ p, κ' R p.1 p.2 ^ 2 ∂(μm.prod μm)) +
    1 / 2 * Real.sqrt (2 * ((∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) - sqSum T (R + J)))
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun R => Real.sqrt (εp R)) atTop (𝓝 0) := by
      have hm : Tendsto εp atTop (𝓝 0) := by
        have := hεt.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
        simpa [εp] using this
      have := (Real.continuous_sqrt.tendsto 0).comp hm
      rw [Real.sqrt_zero] at this
      exact this
    have h2 : Tendsto (fun R : ℕ => 1 / ((R : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hA := (hDk.tendsto_integral_kappa_sub_kTrunc_sq).comp (tendsto_add_atTop_nat J)
    have h3 := (Real.continuous_sqrt.tendsto _).comp (hA.const_mul (1 / 2))
    have hB := (tendsto_sqSum (T := T) hDk.hs.summable).comp (tendsto_add_atTop_nat J)
    have h4 := ((Real.continuous_sqrt.tendsto _).comp
      ((tendsto_const_nhds (x := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2)).sub hB |>.const_mul 2)).const_mul
      (1 / 2)
    have h := ((h1.add h2).add h3).add h4
    simp only [mul_zero, sub_self, Real.sqrt_zero, add_zero] at h
    exact h
  -- norms of triples
  have hnorm : ∀ (a b : ℝ), ‖((a, b, (0 : Fin J → ℝ)) : ℝ × ℝ × (Fin J → ℝ))‖ ≤ |a| + |b| :=
    fun a b => by
      rw [Prod.norm_def, Prod.norm_def, norm_zero, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (by linarith [abs_nonneg b]) (max_le (by linarith [abs_nonneg a])
        (by positivity))
  -- coefficient notation
  set c : (k : ℕ) → (ℕ →₀ ℕ) → ℝ := fun k α => ∫ Y, Ψ k Y * occBasis e α (Ns k) Y ∂PN k
  have hB1 : ∀ k α, ∫ X, |occBasis e α (Ns k) X| ∂PN k ≤ 1 := fun k α => by
    refine (integral_abs_le_sqrt' (t01_memLp_occBasis he α (Ns k))).trans ?_
    rw [Real.sqrt_le_one]
    by_cases hN : occSize α ≤ Ns k
    · have := integral_occBasis_mul he.memLp he.orthonormal hN hN (N := Ns k)
      simp only [↓reduceIte] at this
      rw [show (fun X => occBasis e α (Ns k) X ^ 2) = fun X => occBasis e α (Ns k) X *
        occBasis e α (Ns k) X from funext fun X => sq _]
      exact this.le
    · rw [occBasis_zero_of_lt (show Ns k < occSize α by omega)]; simp
  -- the `Ψ` error on the finite product
  have hΨerr : ∀ R k, ∫ X, |Ψ k X - ∑ α ∈ S R, x0 α * occBasis e α (Ns k) X| ∂PN k ≤
      Real.sqrt (εp R) + ∑ α ∈ S R, |c k α - x0 α| := fun R k => by
    have hBL : ∀ α, MemLp (occBasis e α (Ns k)) 2 (PN k) := fun α => t01_memLp_occBasis he α _
    have hd : MemLp (fun X => Ψ k X - ∑ α ∈ S R, c k α * occBasis e α (Ns k) X) 2 (PN k) :=
      (hΨL k).sub (memLp_finsetSum _ fun α _ => (hBL α).const_mul _)
    have hpt : ∀ X, |Ψ k X - ∑ α ∈ S R, x0 α * occBasis e α (Ns k) X| ≤
        |Ψ k X - ∑ α ∈ S R, c k α * occBasis e α (Ns k) X| +
          ∑ α ∈ S R, |c k α - x0 α| * |occBasis e α (Ns k) X| := fun X => by
      have : Ψ k X - ∑ α ∈ S R, x0 α * occBasis e α (Ns k) X =
          (Ψ k X - ∑ α ∈ S R, c k α * occBasis e α (Ns k) X) +
            ∑ α ∈ S R, (c k α - x0 α) * occBasis e α (Ns k) X := by
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [this]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ((Finset.abs_sum_le_sum_abs _ _).trans
        (le_of_eq (Finset.sum_congr rfl fun α _ => abs_mul _ _))))
    have hi2 : Integrable (fun X => ∑ α ∈ S R, |c k α - x0 α| * |occBasis e α (Ns k) X|) (PN k) :=
      integrable_finsetSum _ fun α _ => ((hBL α).integrable one_le_two).abs.const_mul _
    calc ∫ X, |Ψ k X - ∑ α ∈ S R, x0 α * occBasis e α (Ns k) X| ∂PN k
        ≤ ∫ X, (|Ψ k X - ∑ α ∈ S R, c k α * occBasis e α (Ns k) X| +
            ∑ α ∈ S R, |c k α - x0 α| * |occBasis e α (Ns k) X|) ∂PN k :=
          integral_mono_of_nonneg (Eventually.of_forall fun X => abs_nonneg _)
            ((hd.integrable one_le_two).abs.add hi2) (Eventually.of_forall hpt)
      _ = ∫ X, |Ψ k X - ∑ α ∈ S R, c k α * occBasis e α (Ns k) X| ∂PN k +
            ∑ α ∈ S R, |c k α - x0 α| * ∫ X, |occBasis e α (Ns k) X| ∂PN k := by
          rw [integral_add (hd.integrable one_le_two).abs hi2, integral_finsetSum _ fun α _ =>
            ((hBL α).integrable one_le_two).abs.const_mul _]
          simp_rw [integral_const_mul]
      _ ≤ Real.sqrt (εp R) + ∑ α ∈ S R, |c k α - x0 α| * 1 := by
          gcongr with α hα
          · refine (integral_abs_le_sqrt' hd).trans (Real.sqrt_le_sqrt ?_)
            exact (htail R k).trans (le_max_left _ _)
          · exact hB1 k α
      _ = _ := by simp
  -- the `U` error
  have hκ'm : ∀ R, Measurable (Function.uncurry (κ' R)) := fun R =>
    hDk.meas.sub (hDk.measurable_kTrunc _)
  have hκ's : ∀ R x y, κ' R x y = κ' R y x := fun R x y => by
    simp only [κ']; rw [show κ x y = κ y x from hDk.symm x y, hDk.kTrunc_symm]
  have hκ'c : ∀ R w, ∫ y, κ' R y w ∂μm = 0 := fun R w => by
    obtain ⟨B, hB⟩ := hDk.bdd
    simp only [κ']
    rw [integral_sub (integrable_of_bdd (f := fun y => κ y w)
      (hDk.meas.comp (measurable_id.prodMk measurable_const)) fun y => hB y w)
      (hDk.integrable_kTrunc_left _ w), hDk.cent, hDk.integral_kTrunc_left, sub_zero]
  have hκ'L : ∀ R, MemLp (fun p : Torus d × Torus d => κ' R p.1 p.2) 2 (μm.prod μm) := fun R =>
    hDk.memLp_kappa.sub (hDk.memLp_kTrunc _)
  have hoff : ∀ R k, 1 ≤ Ns k → ∫ X, |offDiag (κ' R) (Ns k) X| ∂PN k ≤
      Real.sqrt (1 / 2 * ∫ p, κ' R p.1 p.2 ^ 2 ∂(μm.prod μm)) := fun R k hN =>
    (integral_abs_le_sqrt' (memLp_offDiag (hκ'L R))).trans (Real.sqrt_le_sqrt
      (integral_offDiag_sq_le hN (hκ'm R).aestronglyMeasurable (hκ's R) (hκ'c R) (hκ'L R)))
  -- the pathwise decomposition
  have hrestr : ∀ k, Measurable fun (ω : ℕ → Torus d) (i : Fin (Ns k)) => ω i := fun k => by
    fun_prop
  have hptV : ∀ R k, 1 ≤ Ns k → ∀ ω, Vk k ω - Wk R k ω =
      (Ψm k (fun i => ω i) - ∑ α ∈ S R, x0 α * occBasis e' α (Ns k) (fun i : Fin (Ns k) => ω i),
        offDiag (κ' R) (Ns k) (fun i : Fin (Ns k) => ω i), 0) := by
    intro R k hN ω
    have hdec := Ugen_decomp hDk hN (R + J) (fun i : Fin (Ns k) => ω i)
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [Vk, Wk, Prod.snd_sub, Prod.fst_sub]
      rw [hdec, Fin.sum_univ_eq_sum_range (fun l => κ (ω l) (ω l) - kTrunc T e' (R + J) (ω l) (ω l))]
      simp only [hdiag, κ']
      ring
    · funext n
      simp [Vk, Wk]
  -- the coefficients converge on each finite set
  have hcS : ∀ R, Tendsto (fun k => ∑ α ∈ S R, |c k α - x0 α|) atTop (𝓝 0) := fun R => by
    have := tendsto_finsetSum (S R) fun α _ => ((hcoef α).sub_const (x0 α)).abs
    simpa using this
  have hzm : ∀ N a, Measurable fun ω : ℕ → Torus d => zSum e' N a (fun i : Fin N => ω i) :=
    fun N a => by
      unfold zSum
      exact (Finset.measurable_sum _ fun l _ => (measurable_emod he _).comp
        (measurable_pi_apply (X := fun _ : ℕ => Torus d) _)).const_mul _
  have hBm : ∀ N α, Measurable fun ω : ℕ → Torus d => occBasis e' α N (fun i : Fin N => ω i) :=
    fun N α => by
      unfold occBasis
      exact (Finset.measurable_sum _ fun c _ => Finset.measurable_prod _ fun i _ =>
        (measurable_emod he _).comp (measurable_pi_apply (X := fun _ : ℕ => Torus d) _)).const_mul _
  have hVm : ∀ k, Measurable (Vk k) := fun k => by
    refine Measurable.prodMk ((hΨm k).comp (hrestr k)) (Measurable.prodMk ?_
      (measurable_pi_iff.mpr fun n => hzm _ _))
    unfold Ugen
    exact (Finset.measurable_sum (f := fun (i : Fin (Ns k)) (ω : ℕ → Torus d) =>
        ∑ j : Fin (Ns k), κ (ω i) (ω j)) _
      fun i _ => Finset.measurable_sum (f := fun (j : Fin (Ns k)) (ω : ℕ → Torus d) =>
        κ (ω i) (ω j)) _
      fun j _ => hDk.meas.comp (f := fun ω : ℕ → Torus d => (ω (i : ℕ), ω (j : ℕ)))
        ((measurable_pi_apply (i : ℕ)).prodMk (measurable_pi_apply (j : ℕ)))).const_mul _
  have hWm : ∀ R k, Measurable (Wk R k) := fun R k => by
    refine Measurable.prodMk (Finset.measurable_sum _ fun α _ => (hBm _ α).const_mul _)
      (Measurable.prodMk ?_ (measurable_pi_iff.mpr fun n => hzm _ _))
    exact ((Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      ((hzm _ a).mul (hzm _ b)).const_mul _).const_mul _).add
      (((Finset.measurable_sum _ fun l _ => (hDk.measurable_hdiag _).comp
        (measurable_pi_apply l)).div_const _).const_mul _)
  have hVW : ∀ R, ∀ᶠ k in atTop, Integrable (fun ω => ‖Vk k ω - Wk R k ω‖) P ∧
      ∫ ω, ‖Vk k ω - Wk R k ω‖ ∂P ≤ δ R := by
    intro R
    have hpos : (0 : ℝ) < 1 / ((R : ℝ) + 1) := by positivity
    filter_upwards [hNs.eventually_ge_atTop 1, (tendsto_order.mp (hcS R)).2 _ hpos] with k hN hck
    set F : Config (Ns k) d → ℝ := fun X =>
      |Ψm k X - ∑ α ∈ S R, x0 α * occBasis e' α (Ns k) X| + |offDiag (κ' R) (Ns k) X|
    have hBL' : ∀ α, MemLp (occBasis e' α (Ns k)) 2 (PN k) := fun α =>
      (t01_memLp_occBasis he α (Ns k)).ae_eq (by
        filter_upwards [occBasis_fluct_ae_eq he (Ns k)] with X hX
        unfold occBasis
        congr 1
        exact Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => (hX _ _).symm)
    have hF1 : MemLp (fun X => Ψm k X - ∑ α ∈ S R, x0 α * occBasis e' α (Ns k) X) 2 (PN k) :=
      ((hΨL k).ae_eq (hΨΨ k)).sub (memLp_finsetSum _ fun α _ => (hBL' α).const_mul _)
    have hFi : Integrable F (PN k) :=
      (hF1.integrable one_le_two).abs.add ((memLp_offDiag (hκ'L R)).integrable one_le_two).abs
    have hFP : Integrable (fun ω : ℕ → Torus d => F (fun i : Fin (Ns k) => ω i)) P := by
      have : Integrable F (P.map fun (ω : ℕ → Torus d) (i : Fin (Ns k)) => ω i) := by
        rw [infinitePi_map_fin μm (Ns k)]; exact hFi
      exact this.comp_measurable (hrestr k)
    have hle : ∀ ω, ‖Vk k ω - Wk R k ω‖ ≤ F (fun i : Fin (Ns k) => ω i) := fun ω => by
      rw [hptV R k hN ω]; exact hnorm _ _
    have hm : AEStronglyMeasurable (fun ω => ‖Vk k ω - Wk R k ω‖) P :=
      ((hVm k).sub (hWm R k)).norm.aestronglyMeasurable
    refine ⟨hFP.mono' hm (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hle ω), ?_⟩
    calc ∫ ω, ‖Vk k ω - Wk R k ω‖ ∂P ≤ ∫ ω, F (fun i : Fin (Ns k) => ω i) ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hFP
            (Eventually.of_forall hle)
      _ = ∫ X, F X ∂PN k := integral_restrict_fin hFi.aestronglyMeasurable
      _ ≤ (Real.sqrt (εp R) + 1 / ((R : ℝ) + 1)) +
            Real.sqrt (1 / 2 * ∫ p, κ' R p.1 p.2 ^ 2 ∂(μm.prod μm)) := by
          rw [integral_add (hF1.integrable one_le_two).abs
            ((memLp_offDiag (hκ'L R)).integrable one_le_two).abs]
          refine add_le_add ?_ (hoff R k hN)
          have he1 : ∫ X, |Ψm k X - ∑ α ∈ S R, x0 α * occBasis e' α (Ns k) X| ∂PN k =
              ∫ X, |Ψ k X - ∑ α ∈ S R, x0 α * occBasis e α (Ns k) X| ∂PN k := by
            refine integral_congr_ae ?_
            filter_upwards [hΨΨ k, occBasis_fluct_ae_eq he (Ns k)] with X h1 h2
            have hB : ∀ α, occBasis e' α (Ns k) X = occBasis e α (Ns k) X := fun α => by
              unfold occBasis
              congr 1
              exact Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => h2 _ _
            simp only [hB, ← h1]
          rw [he1]
          exact (hΨerr R k).trans (by linarith)
      _ ≤ δ R := by
          have : 0 ≤ 1 / 2 * Real.sqrt (2 * ((∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) - sqSum T (R + J))) :=
            by positivity
          simp only [δ]; linarith
  -- the limit side
  have hdm : ∀ R, ∫ x, hdiag κ T e' (R + J) x ∂μm =
      diagMean W μ - ∑ a ∈ Finset.range (R + J), T a a := fun R => by
    obtain ⟨B, hB⟩ := hDk.bdd
    simp only [hdiag]
    rw [integral_sub (integrable_of_bdd (f := fun x => κ x x)
      (hDk.meas.comp (measurable_id.prodMk measurable_id)) fun x => hB x x)
      (hDk.integrable_kTrunc_diag _), hDk.integral_kTrunc_diag]
    rfl
  have hYm : AEStronglyMeasurable Y gammaRef :=
    hΨi.aestronglyMeasurable.prodMk
      (((hQ.1.aestronglyMeasurable.aemeasurable.div_const 2).add_const _).aestronglyMeasurable.prodMk
      (measurable_pi_iff.mpr fun n => measurable_pi_apply _).aestronglyMeasurable)
  have hYrm : ∀ R, AEStronglyMeasurable (Yr R) gammaRef := fun R =>
    (Finset.aestronglyMeasurable_fun_sum _ fun α _ =>
      (memLp_hermiteBasis α).aestronglyMeasurable.const_mul _).prodMk
      ((((Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
        ((measurable_pi_apply a).mul (measurable_pi_apply b)).const_mul _).const_mul _).add_const
          _).aestronglyMeasurable.prodMk
        (measurable_pi_iff.mpr fun n => measurable_pi_apply _).aestronglyMeasurable)
  have hptY : ∀ R z, Y z - Yr R z = (Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z,
      (Q z - quadTrunc T (R + J) z) / 2, 0) := fun R z => by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [Y, Yr, Prod.snd_sub, Prod.fst_sub]
      rw [hdm, quadTrunc_eq]; ring
    · funext n; simp [Y, Yr]
  have hYY : ∀ R, Integrable (fun z => ‖Y z - Yr R z‖) gammaRef ∧
      ∫ z, ‖Y z - Yr R z‖ ∂gammaRef ≤ δ R := by
    intro R
    have h1L : MemLp (fun z => Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z) 2 gammaRef :=
      hΨiL.sub (memLp_finsetSum _ fun α _ => (memLp_hermiteBasis α).const_mul _)
    have h2L : MemLp (fun z => Q z - quadTrunc T (R + J) z) 2 gammaRef :=
      hQ.1.sub (memLp_quadTrunc T (R + J))
    have hFi : Integrable (fun z => |Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z| +
        |Q z - quadTrunc T (R + J) z| / 2) gammaRef :=
      (h1L.integrable one_le_two).abs.add ((h2L.integrable one_le_two).abs.div_const 2)
    have hle : ∀ z, ‖Y z - Yr R z‖ ≤ |Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z| +
        |Q z - quadTrunc T (R + J) z| / 2 := fun z => by
      rw [hptY]
      refine (hnorm _ _).trans (le_of_eq ?_)
      rw [abs_div, abs_two]
    have hm : AEStronglyMeasurable (fun z => ‖Y z - Yr R z‖) gammaRef :=
      ((hYm).sub (hYrm R)).norm
    refine ⟨hFi.mono' hm (Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hle z), ?_⟩
    calc ∫ z, ‖Y z - Yr R z‖ ∂gammaRef
        ≤ ∫ z, (|Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z| +
            |Q z - quadTrunc T (R + J) z| / 2) ∂gammaRef :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hFi
            (Eventually.of_forall hle)
      _ = ∫ z, |Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z| ∂gammaRef +
            (∫ z, |Q z - quadTrunc T (R + J) z| ∂gammaRef) / 2 := by
          rw [integral_add (h1L.integrable one_le_two).abs
            ((h2L.integrable one_le_two).abs.div_const 2), integral_div]
      _ ≤ Real.sqrt (εp R) + Real.sqrt (2 * ((∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) - sqSum T (R + J))) / 2 := by
          refine add_le_add ((integral_abs_le_sqrt' h1L).trans (Real.sqrt_le_sqrt ?_))
            (div_le_div_of_nonneg_right ((integral_abs_le_sqrt' h2L).trans (le_of_eq ?_))
              (by norm_num))
          · have e1 : ∫ z, (Ψi z - ∑ α ∈ S R, x0 α * hermiteBasis α z) ^ 2 ∂gammaRef =
                ∫ z, (Ψinf z - ∑ α ∈ S R, x0 α * hermiteBasis α z) ^ 2 ∂gammaRef :=
              integral_congr_ae (hΨiΨ.mono fun z hz => by simp only [hz])
            rw [e1]; exact (htailInf R).trans (le_max_left _ _)
          · rw [integral_secondChaos_sub_trunc_sq hDk.T_symm hDk.hs.summable hQ]
      _ ≤ δ R := by
          have h0 : 0 ≤ 1 / ((R : ℝ) + 1) := by positivity
          have h0' : 0 ≤ Real.sqrt (1 / 2 * ∫ p, κ' R p.1 p.2 ^ 2 ∂(μm.prod μm)) := Real.sqrt_nonneg _
          simp only [δ]; linarith
  -- conclusion
  have hconv := tendstoInDistribution_of_approx (fun k => (hVm k).aemeasurable) hYm.aemeasurable
    hW hδ hVW hYY
  have h := TendstoInDistribution.tendsto_integral_bcf hconv g
  have hL : ∀ k, ∫ ω, g (Vk k ω) ∂P = ∫ X, g (Ψ k X, Ucentered W μ (Ns k) X,
      fun n => fluct e (Ns k) n X) ∂PN k := fun k => by
    have hGm : AEStronglyMeasurable (fun X : Config (Ns k) d => g (Ψm k X, Ugen κ (Ns k) X,
        fun n : Fin J => zSum e' (Ns k) n X)) (PN k) := by
      refine (g.continuous.measurable.comp (Measurable.prodMk (hΨm k) (Measurable.prodMk ?_
        (measurable_pi_iff.mpr fun n => ?_)))).aestronglyMeasurable
      · unfold Ugen
        exact (Finset.measurable_sum (f := fun (i : Fin (Ns k)) (X : Config (Ns k) d) =>
            ∑ j : Fin (Ns k), κ (X i) (X j)) _
          fun i _ => Finset.measurable_sum (f := fun (j : Fin (Ns k)) (X : Config (Ns k) d) =>
            κ (X i) (X j)) _
          fun j _ => hDk.meas.comp (f := fun X : Config (Ns k) d => (X i, X j))
            ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).const_mul _
      · unfold zSum
        exact (Finset.measurable_sum _ fun l _ => (measurable_emod he _).comp
          (measurable_pi_apply l)).const_mul _
    rw [integral_restrict_fin hGm]
    refine integral_congr_ae ?_
    filter_upwards [hΨΨ k, occBasis_fluct_ae_eq he (Ns k)] with X h1 h2
    have hz : ∀ n : Fin J, zSum e' (Ns k) n X = fluct e (Ns k) n X := fun n => by
      rw [fluct_eq_zSum]
      unfold zSum
      congr 1
      exact Finset.sum_congr rfl fun l _ => h2 _ _
    simp only [hz, ← h1]
    rfl
  have hR : ∫ z, g (Y z) ∂gammaRef = ∫ z, g (Ψinf z, Uinf W μ Q z, fun n => z n) ∂gammaRef := by
    refine integral_congr_ae ?_
    filter_upwards [hΨiΨ] with z hz
    simp only [Y, hz]
    rfl
  rw [hR] at h
  exact h.congr hL

end Joint

private theorem t01_hermite_projection_tail (S : Spec d)
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 gammaRef) {B L : ℝ} (hL : 0 < L)
    (hpar : HasSum (fun α : ℕ →₀ ℕ => (∫ z, F z * hermiteBasis α z ∂gammaRef) ^ 2)
      (∫ z, F z ^ 2 ∂gammaRef))
    (hE : ∀ T : Finset (ℕ →₀ ℕ), ∑ α ∈ T, occEnergy S.lam α *
      (∫ z, F z * hermiteBasis α z ∂gammaRef) ^ 2 ≤ B)
    (T : Finset (ℕ →₀ ℕ)) (hT : ∀ α, occEnergy S.lam α ≤ L → α ∈ T) :
    ∫ z, (F z - ∑ α ∈ T, (∫ y, F y * hermiteBasis α y ∂gammaRef) * hermiteBasis α z) ^ 2
      ∂gammaRef ≤ B / L := by
  let c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ z, F z * hermiteBasis α z ∂gammaRef
  have hΛ : ∀ α, 0 ≤ occEnergy S.lam α := fun α =>
    Finset.sum_nonneg fun j _ => mul_nonneg (S.lam_nonneg _) (Nat.cast_nonneg _)
  have hEs : Summable fun α => occEnergy S.lam α * c α ^ 2 :=
    summable_of_sum_le (fun α => mul_nonneg (hΛ α) (sq_nonneg _)) hE
  have hEt : ∑' α, occEnergy S.lam α * c α ^ 2 ≤ B :=
    Real.tsum_le_of_sum_le (fun α => mul_nonneg (hΛ α) (sq_nonneg _)) hE
  rw [integral_sub_sum_sq T c hF memLp_hermiteBasis]
  simp_rw [integral_hermiteBasis_mul]
  have h3 : ∑ α ∈ T, ∑ β ∈ T, c α * c β * (if α = β then (1 : ℝ) else 0) =
      ∑ α ∈ T, c α ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    simp [Finset.sum_ite_eq, hα, sq]
  rw [h3, ← hpar.tsum_eq]
  have hsplit : ∑' α, c α ^ 2 - ∑ α ∈ T, c α ^ 2 =
      ∑' α, (if α ∈ T then 0 else c α ^ 2) := by
    have : ∀ α, c α ^ 2 = (if α ∈ T then c α ^ 2 else 0) +
        (if α ∈ T then 0 else c α ^ 2) := fun α => by split_ifs <;> simp
    rw [tsum_congr this, Summable.tsum_add (summable_of_ne_finset_zero (s := T)
      fun α hα => by simp [hα]) (hpar.summable.of_nonneg_of_le
        (fun α => by split_ifs <;> positivity)
        fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl),
      tsum_eq_sum (s := T) fun α hα => by simp [hα]]
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    ring
  have hle : ∑' α, (if α ∈ T then 0 else c α ^ 2) ≤
      ∑' α, occEnergy S.lam α * c α ^ 2 / L := by
    refine Summable.tsum_le_tsum (fun α => ?_)
      (hpar.summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
        fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl) (hEs.div_const L)
    split_ifs with h
    · exact div_nonneg (mul_nonneg (hΛ α) (sq_nonneg _)) hL.le
    · have he : L < occEnergy S.lam α := by
        by_contra hn
        exact h (hT α (by linarith))
      rw [le_div_iff₀ hL]
      nlinarith [sq_nonneg (c α)]
  rw [tsum_div_const] at hle
  have hAlg : ∑' α, c α ^ 2 - 2 * ∑ α ∈ T, c α * c α + ∑ α ∈ T, c α ^ 2 =
      ∑' α, c α ^ 2 - ∑ α ∈ T, c α ^ 2 := by simp only [← sq]; ring
  rw [hAlg, hsplit]
  exact hle.trans (div_le_div_of_nonneg_right hEt hL.le)

/-- Joint compactness on the same actual reference and positive spectral coordinates.
The limiting second chaos is constructed from the actual centered-kernel matrix. -/
theorem t01_reference_compactness_joint (J : InteractionData d) (S : Spec d) (aux : Aux S)
    (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, SharpLSI.FL.Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (htend : Tendsto S.lam atTop atTop) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (Ψ : (n : ℕ) → Config (Ns n) d → ℝ)
    (hH : ∀ n, MemH1C (Measure.pi fun _ : Fin (Ns n) => S.mu) (Ψ n))
    (hs : ∀ n, ∀ σ : Equiv.Perm (Fin (Ns n)),
      (fun X => Ψ n (X ∘ σ)) =ᵐ[Measure.pi (fun _ : Fin (Ns n) => S.mu)] Ψ n)
    (B : ℝ)
    (hM : ∀ n, ∫ X, Ψ n X ^ 2 ∂Measure.pi (fun _ : Fin (Ns n) => S.mu) ≤ B)
    (hE : ∀ n, (SharpLSI.FL.refEnergy S.mu (Ψ n)).toReal ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψinf : (ℕ → ℝ) → ℝ, MemLp Ψinf 2 gammaRef ∧
      ∃ Q : (ℕ → ℝ) → ℝ, IsSecondChaos (Tmat J.W S.mu S.v) Q ∧
      Tendsto (fun k => ∫ X, Ψ (φ k) X ^ 2 ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu))
        atTop (𝓝 (∫ z, Ψinf z ^ 2 ∂gammaRef)) ∧
      ∀ (J' : ℕ) (g : ℝ × ℝ × (Fin J' → ℝ) →ᵇ ℝ),
        Tendsto (fun k => ∫ X, g (Ψ (φ k) X, Ucentered J.W S.mu (Ns (φ k)) X,
          fun n => fluct S.v (Ns (φ k)) n X)
            ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) atTop
          (𝓝 (∫ z, g (Ψinf z, Uinf J.W S.mu Q z, fun n => z n) ∂gammaRef)) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hKD := t01_actual_kernelData_emod J S aux D hD he
  obtain ⟨Q, hQ⟩ := exists_secondChaos hKD.T_symm hKD.hs.summable
  obtain ⟨φ, hφ, Ψinf, hΨinf, hl2, hmass, hpt, hCoeffE, hpar⟩ :=
    t01_reference_occupation_compactness S he hC1 hlam0 hlam1 hmono htend Ns Ψ hH hs B hM hE
  refine ⟨φ, hφ, Ψinf, hΨinf, Q, hQ, hmass, ?_⟩
  intro J' g
  let T : ℕ → Finset (ℕ →₀ ℕ) := fun R =>
    (t01_finite_occupation_energy_sublevel S hmono hlam1 htend ((R : ℝ) + 1)).toFinset
  have hT : ∀ (R : ℕ) α, occEnergy S.lam α ≤ (R : ℝ) + 1 → α ∈ T R := by
    intro R α hα
    simpa [T] using hα
  have hε : Tendsto (fun R : ℕ => B / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
    rw [mul_zero] at h
    exact h.congr fun R => by rw [mul_one_div]
  have hpre : ∀ R k, ∫ X, (Ψ (φ k) X - ∑ α ∈ T R,
      (∫ Y, Ψ (φ k) Y * occBasis S.v α (Ns (φ k)) Y
        ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) * occBasis S.v α (Ns (φ k)) X) ^ 2
        ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu) ≤ B / ((R : ℝ) + 1) := fun R k =>
    t01_reference_occupation_projection_tail S he hC1 hlam0 (hH (φ k)) (hs (φ k))
      (hE (φ k)) (by positivity) (T R) (hT R)
  have hlim : ∀ R, ∫ z, (Ψinf z - ∑ α ∈ T R,
      (∫ y, Ψinf y * hermiteBasis α y ∂gammaRef) * hermiteBasis α z) ^ 2 ∂gammaRef ≤
        B / ((R : ℝ) + 1) := fun R =>
    t01_hermite_projection_tail S hΨinf (by positivity) hpar hCoeffE (T R) (hT R)
  exact t01_joint_law_of_kernelData (μ := specProbability_LIP016 S) he hKD hQ J'
    (hNs.comp hφ.tendsto_atTop) (fun k => Ψ (φ k))
    (fun k => (measurableEmbedding_flat.memLp_map_measure_iff).mp (hH (φ k)).2.1)
    (fun α => ∫ z, Ψinf z * hermiteBasis α z ∂gammaRef) hΨinf hpt T hε hpre hlim g

end DGPS.Lipschitz
