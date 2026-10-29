import SharpSymmetricLSI.Paper.R29Joint2

/-!
# The joint law of `(Ψ_k, U_{N_k}, Z_{N_k})` (Phase 3, lane D; R29 (iii))

`Ψ_k` is `L²`-close to `∑_{α∈S_R} x_α B_{α,N}`, `U_N` to its truncation; the truncated triple
converges in law (`tendstoInDistribution_trunc`), and the approximation lemma
`tendstoInDistribution_of_approx` concludes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem TendstoInDistribution.comp_atTop {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] {P : Measure Ω}
    [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q] {X : ℕ → Ω → E}
    {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ => P) Q) {Ns : ℕ → ℕ}
    (hNs : Tendsto Ns atTop atTop) :
    TendstoInDistribution (fun k => X (Ns k)) atTop Z (fun _ => P) Q :=
  ⟨fun k => h.forall_aemeasurable (Ns k), h.aemeasurable_limit, h.tendsto.comp hNs⟩

theorem integral_restrict_fin {N : ℕ} {ν : Measure (Torus d)} [IsProbabilityMeasure ν]
    {G : Config N d → ℝ} (hG : AEStronglyMeasurable G (Measure.pi fun _ : Fin N => ν)) :
    ∫ ω, G (fun i : Fin N => ω i) ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∫ X, G X ∂(Measure.pi fun _ : Fin N => ν) := by
  have hrm : Measurable fun (ω : ℕ → Torus d) (i : Fin N) => ω i := by fun_prop
  have e1 := integral_map (μ := Measure.infinitePi fun _ : ℕ => ν) hrm.aemeasurable
    (f := G) (by rw [infinitePi_map_fin ν N]; exact hG)
  rw [infinitePi_map_fin ν N] at e1
  exact e1.symm

section joint
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The joint law (7.4)–(7.5) (iii).** -/
theorem joint_law_occ {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q) (J : ℕ)
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
  set κ := centeredKernel W μ
  set T := Tmat W μ e
  have hDk := kerData_emod hyp hμ he
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
    TendstoInDistribution.comp_atTop (tendstoInDistribution_trunc hyp hμ he (S R) x0 J R) hNs
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
    refine (integral_abs_le_sqrt' (memLp_occBasis hyp hμ he α (Ns k))).trans ?_
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
    have hBL : ∀ α, MemLp (occBasis e α (Ns k)) 2 (PN k) := fun α => memLp_occBasis hyp hμ he α _
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
      (memLp_occBasis hyp hμ he α (Ns k)).ae_eq (by
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

end joint

end SharpLSI
