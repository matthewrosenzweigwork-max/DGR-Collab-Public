import SharpSymmetricLSI.Paper.GaussFormClause5

/-!
# R32 form clause (lane s42): `ℰ_∞(F(ξ)) = ∫ ∑_j ν_j (∂_jF(ξ))² dγ`

`form_clause_xi`: the form clause of R32 `gaussian_diagonalization`, conditional on
Proposition 2.1 (through the diagonalizing data `v, ν, ξ` and the Parseval fact `hCv` of
GaussForm24).
* `≤`: Paper/GaussFormClause4 (`gaussForm_xi_le`).
* `≥`: the cylinders `c_n` of `cylApprox_comp_xi` (lane-r19 FormDuality4; inputs `hW` and the
  generator relation `gen_xi_of_prop21`, Paper/GaussFormClause1) satisfy `c_n → F(ξ)`,
  `L c_n → L_ξ F(ξ) = ∑ ν_j (∂_{jj}F - ξ_j ∂_jF)(ξ)`, so with `ℰ(c_n) = ∫ c_n(-Lc_n)`
  (`cyl_ibp_self`) the easy half of the duality (`dual_le_gaussForm`, GaussForm31) gives
  `ℰ_∞(F(ξ)) ≥ ∫ F(ξ)(-L_ξ F(ξ)) = ∫ ∑ ν_j (∂_jF(ξ))²` (Paper/GaussFormClause5 under the law
  `N(0,1)^{⊗J}` of `ξ`, GaussForm26 `map_xi_eq_pi`).
-/

noncomputable section
open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal ContDiff InnerProductSpace

namespace SharpLSI

/-- `∫ a_n b_n → ∫ a b` for `a_n → a`, `b_n → b` in `L²`. -/
theorem tendsto_integral_mul_L2 {α : Type*} [MeasurableSpace α] {P : Measure α}
    {a b : ℕ → α → ℝ} {a₀ b₀ : α → ℝ} (ha : ∀ n, MemLp (a n) 2 P) (hb : ∀ n, MemLp (b n) 2 P)
    (ha₀ : MemLp a₀ 2 P) (hb₀ : MemLp b₀ 2 P)
    (hat : Tendsto (fun n => eLpNorm (a n - a₀) 2 P) atTop (𝓝 0))
    (hbt : Tendsto (fun n => eLpNorm (b n - b₀) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, a n x * b n x ∂P) atTop (𝓝 (∫ x, a₀ x * b₀ x ∂P)) := by
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := P) (p := 2) (E := ℝ) (ι := ℕ)
    (fi := atTop) a ha a₀ ha₀).2 hat
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := P) (p := 2) (E := ℝ) (ι := ℕ)
    (fi := atTop) b hb b₀ hb₀).2 hbt
  have h := Filter.Tendsto.inner (𝕜 := ℝ) h1 h2
  simp only [inner_toLp_two] at h
  exact h

section main
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **The form clause of R32 `gaussian_diagonalization`.** -/
theorem form_clause_xi (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (h21 : Prop21Conclusion V W μ)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {v : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {ξ : ℕ → (ℕ → ℝ) → ℝ}
    (hv : ∀ j, Summable (fun i => v j i ^ 2) ∧ Summable (fun i => (lamShift lam i * v j i) ^ 2))
    (hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0)
    (hvΛ : ∀ i j, ∑' a, lamShift lam a * v i a * v j a = if i = j then ν i else 0)
    (hξ : ∀ j, IsRowVariable v γ j (ξ j))
    (hCv : ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i))
    (J : ℕ) (F : (Fin J → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) :
    gaussForm (lamShift lam) γ (fun z => F (fun j => ξ j z)) =
      ∫⁻ z, ENNReal.ofReal (∑ j : Fin J, ν j *
        (fderiv ℝ F (fun i => ξ i z) (Pi.single j 1)) ^ 2) ∂γ := by
  haveI := hγ.1
  set lam' := lamShift lam
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs : ∀ a b, C a b = C b a := fun a b => C_symm_of_secOp hT hS hσ0 hσ hC a b
  have hv2 : ∀ j, Summable fun i => v j i ^ 2 := fun j => (hv j).1
  have hvl : ∀ j, Summable fun i => (lam' i * v j i) ^ 2 := fun j => (hv j).2
  have hlam : ∀ i, 0 ≤ lam' i := fun i => he.lam_nonneg' (i + 1)
  refine le_antisymm (gaussForm_xi_le hF hFc hv2 hvl hvΛ hξ) ?_
  -- the data of the lower bound
  obtain ⟨Y, hY⟩ := exists_rowVariables_of_prop21 hyp hμ he h21 hC hγ
  have hPSD : ∀ N, (blockMat C N).PosSemidef := blockMat_posSemidef_of_prop21 hyp hμ he h21 hC
  have hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ := fun i => memLp_coord_gamma hγ i
  have hYm : ∀ i, MemLp (Y i) 2 γ := fun i => (hY i).1
  have hsum : ∀ j k : ℕ, Summable fun i => lam' i * v j i * v k i := fun j k => by
    refine Summable.of_norm_bounded (((hvl j).add (hv2 k)).div_const 2) fun i => ?_
    rw [Real.norm_eq_abs, show lam' i * v j i * v k i = (lam' i * v j i) * v k i by ring, abs_mul]
    nlinarith [sq_nonneg (|lam' i * v j i| - |v k i|), sq_abs (lam' i * v j i), sq_abs (v k i)]
  have hW : ∀ j k, Tendsto (fun N => ∑ i ∈ Finset.range N, lam' i * v j i * v k i) atTop
      (𝓝 (if j = k then ν j else 0)) := fun j k => by
    rw [← hvΛ j k]; exact (hsum j k).hasSum.tendsto_sum_nat
  have hLξ := gen_xi_of_prop21 hyp hμ he h21 hC hγ hv hvC hvΛ hξ hCv hY
  obtain ⟨c, hc1, hc2⟩ := cylApprox_comp_xi (γ := γ) (lam' := lam') (Y := Y) (v := v) (ν := ν)
    (ξ := ξ) hz hYm hξ hW hLξ hF hFc
  -- the limit objects
  set f : (ℕ → ℝ) → ℝ := fun z => F (fun j => ξ j z) with hfdef
  set Gen : (ℕ → ℝ) → ℝ := fun z => ∑ j : Fin J, ν j * (pd (pd F j) j (fun i => ξ i z) -
    ξ j z * pd F j (fun i => ξ i z)) with hGdef
  have hξm : ∀ j, AEStronglyMeasurable (ξ j) γ := fun j => (hξ j).1.aestronglyMeasurable
  have hξv : AEMeasurable (fun z => fun j : Fin J => ξ j z) γ :=
    AEMeasurable.of_eval (f := fun z (j : Fin J) => ξ j z) fun j => (hξm j).aemeasurable
  obtain ⟨BF, hBF⟩ := hFc.exists_bound_of_continuous hF.continuous
  have hfL : MemLp f 2 γ := MemLp.of_bound
    (hF.continuous.comp_aestronglyMeasurable hξv.aestronglyMeasurable) BF
    (Eventually.of_forall fun z => hBF _)
  have hpdc : ∀ j : Fin J, Continuous (pd F j) := fun j => (contDiff_pd hF j).continuous
  have hpd2c : ∀ j : Fin J, Continuous (pd (pd F j) j) := fun j =>
    (contDiff_pd (contDiff_pd hF j) j).continuous
  have hGL : MemLp Gen 2 γ := by
    refine memLp_finsetSum (ε' := ℝ) _ fun j _ => (MemLp.sub ?_ ?_).const_mul (ν j)
    · obtain ⟨B2, hB2⟩ := (hasCompactSupport_pd (hasCompactSupport_pd hFc j) j).exists_bound_of_continuous
        (hpd2c j)
      exact MemLp.of_bound ((hpd2c j).comp_aestronglyMeasurable hξv.aestronglyMeasurable) B2
        (Eventually.of_forall fun z => hB2 _)
    · obtain ⟨B1, hB1⟩ := (hasCompactSupport_pd hFc j).exists_bound_of_continuous (hpdc j)
      have hb : MemLp (fun z => pd F j (fun i => ξ i z)) ∞ γ :=
        memLp_top_of_bound ((hpdc j).comp_aestronglyMeasurable hξv.aestronglyMeasurable) B1
          (Eventually.of_forall fun z => hB1 _)
      have := hb.mul (hξ j).1 (r := 2)
      refine this.congr_norm ((hξm j).mul ((hpdc j).comp_aestronglyMeasurable
        hξv.aestronglyMeasurable)) (Eventually.of_forall fun z => ?_)
      simp only [Pi.mul_apply, norm_mul]; ring
  -- convergence of `∫ f (-L c_n)` and of `ℰ(c_n) = ∫ c_n (-L c_n)`
  have hgen : ∀ n, MemLp (fun z => -((c n).gen lam' Y z)) 2 γ := fun n =>
    (memLp_gen hγ hY lam' (c n)).neg
  have hgent : Tendsto (fun n => eLpNorm ((fun z => -((c n).gen lam' Y z)) - fun z => -Gen z) 2 γ)
      atTop (𝓝 0) := by
    refine hc2.congr fun n => ?_
    rw [← eLpNorm_neg]
    congr 1; funext z; simp only [Pi.sub_apply, Pi.neg_apply]; ring
  have hevt : Tendsto (fun n => eLpNorm ((c n).eval - f) 2 γ) atTop (𝓝 0) :=
    hc1.congr fun n => by congr 1
  have hA : Tendsto (fun n => ∫ z, f z * (-((c n).gen lam' Y z)) ∂γ) atTop
      (𝓝 (∫ z, f z * (-Gen z) ∂γ)) :=
    tendsto_integral_mul_L2 (a := fun _ => f) (fun _ => hfL) hgen hfL hGL.neg
      (by simp) hgent
  have hB : Tendsto (fun n => (c n).formR lam' γ) atTop (𝓝 (∫ z, f z * (-Gen z) ∂γ)) := by
    have h := tendsto_integral_mul_L2 (a := fun n => (c n).eval) (fun n => (c n).memLp_eval) hgen
      hfL hGL.neg hevt hgent
    refine h.congr fun n => ?_
    exact cyl_ibp_self hγ hPSD hC hY lam' (c n)
  set Tval := ∫ z, f z * (-Gen z) ∂γ
  have hlow : ENNReal.ofReal Tval ≤ gaussForm lam' γ f := by
    have hconv : Tendsto (fun n => 2 * ∫ z, f z * (-((c n).gen lam' Y z)) ∂γ -
        (c n).formR lam' γ) atTop (𝓝 Tval) := by
      have := (hA.const_mul 2).sub hB
      rwa [show 2 * Tval - Tval = Tval by ring] at this
    exact le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp hconv)
      (Eventually.of_forall fun n => dual_le_gaussForm hγ hPSD hC hY hlam (c n) hfL)
  -- `Tval` is the target
  have hν : ∀ j, 0 ≤ ν j := fun j => by
    have h := hvΛ j j
    rw [if_pos rfl] at h
    rw [← h]
    exact tsum_nonneg fun a => by
      rw [show lam' a * v j a * v j a = lam' a * (v j a) ^ 2 by ring]
      exact mul_nonneg (hlam a) (sq_nonneg _)
  set π := Measure.pi fun _ : Fin J => gaussianReal 0 1
  have hmap : γ.map (fun z => fun j : Fin J => ξ j z) = π :=
    map_xi_eq_pi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ J
  set H₁ : (Fin J → ℝ) → ℝ := fun y => ∑ j : Fin J, ν j *
    (F y * (y j * pd F j y - pd (pd F j) j y))
  set H₂ : (Fin J → ℝ) → ℝ := fun y => ∑ j : Fin J, ν j * pd F j y ^ 2
  have hH₁c : Continuous H₁ := continuous_finsetSum _ fun j _ => continuous_const.mul
    (hF.continuous.mul (((continuous_apply j).mul (hpdc j)).sub (hpd2c j)))
  have hH₂c : Continuous H₂ := continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((hpdc j).pow 2)
  have hT1 : Tval = ∫ y, H₁ y ∂π := by
    rw [← hmap, integral_map hξv (hH₁c.aestronglyMeasurable)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hfdef, hGdef, H₁]
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hBF0 : 0 ≤ BF := (norm_nonneg _).trans (hBF 0)
  have iterm : ∀ j : Fin J, Integrable (fun y => F y * (y j * pd F j y - pd (pd F j) j y)) π :=
    fun j => by
      obtain ⟨B1, hB1⟩ := (hasCompactSupport_pd hFc j).exists_bound_of_continuous (hpdc j)
      obtain ⟨B2, hB2⟩ := (hasCompactSupport_pd (hasCompactSupport_pd hFc j) j
        ).exists_bound_of_continuous (hpd2c j)
      refine (((integrable_coord_pi j).abs.mul_const (BF * B1)).add
        (integrable_const (BF * B2))).mono' ((hF.continuous.mul (((continuous_apply j).mul
          (hpdc j)).sub (hpd2c j))).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
      have h1 := hBF y
      have h2 := hB1 y
      have h3 := hB2 y
      rw [Real.norm_eq_abs] at h1 h2 h3
      have hB10 : 0 ≤ B1 := (abs_nonneg _).trans h2
      rw [Real.norm_eq_abs, abs_mul]
      have h4 : |y j * pd F j y - pd (pd F j) j y| ≤ |y j| * B1 + B2 := by
        refine (abs_sub _ _).trans (add_le_add ?_ h3)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      calc |F y| * |y j * pd F j y - pd (pd F j) j y| ≤ BF * (|y j| * B1 + B2) :=
            mul_le_mul h1 h4 (abs_nonneg _) hBF0
        _ = |y j| * (BF * B1) + BF * B2 := by ring
  have iH2 : ∀ j : Fin J, Integrable (fun y => pd F j y ^ 2) π := fun j => by
    obtain ⟨B1, hB1⟩ := (hasCompactSupport_pd hFc j).exists_bound_of_continuous (hpdc j)
    exact integrable_of_bdd_cont ((hpdc j).pow 2) (B := B1 ^ 2) fun y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using hB1 y) 2
  have hT2 : ∫ y, H₁ y ∂π = ∫ y, H₂ y ∂π := by
    simp only [H₁, H₂]
    rw [integral_finsetSum _ fun j _ => (iterm j).const_mul (ν j),
      integral_finsetSum _ fun j _ => (iH2 j).const_mul (ν j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul, integral_stein_sq hF hFc j]
  -- the target as `ofReal`
  have hH₂0 : ∀ y, 0 ≤ H₂ y := fun y => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hν j) (sq_nonneg _)
  obtain ⟨BH, hBH⟩ : ∃ BH, ∀ y, |H₂ y| ≤ BH := by
    choose B1 hB1 using fun j : Fin J =>
      (hasCompactSupport_pd hFc j).exists_bound_of_continuous (hpdc j)
    refine ⟨∑ j : Fin J, |ν j| * B1 j ^ 2, fun y => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)⟩
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (by simpa using hB1 j y) 2)
      (abs_nonneg _)
  have hH₂i : Integrable (fun z => H₂ (fun j : Fin J => ξ j z)) γ :=
    Integrable.of_bound (hH₂c.comp_aestronglyMeasurable hξv.aestronglyMeasurable) BH
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hBH _)
  have htarget : (∫⁻ z, ENNReal.ofReal (∑ j : Fin J, ν j *
      (fderiv ℝ F (fun i => ξ i z) (Pi.single j 1)) ^ 2) ∂γ) = ENNReal.ofReal Tval := by
    rw [hT1, hT2, ← hmap, integral_map hξv hH₂c.aestronglyMeasurable,
      ofReal_integral_eq_lintegral_ofReal hH₂i (Eventually.of_forall fun z => hH₂0 _)]
    rfl
  rw [htarget]
  exact hlow

end main

end SharpLSI
