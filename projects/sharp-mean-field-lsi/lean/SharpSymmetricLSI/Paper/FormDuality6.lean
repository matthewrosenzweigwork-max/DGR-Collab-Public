import SharpSymmetricLSI.Paper.FormDuality5

/-!
# R32 (8.8), part 6: finite Hermite sums in `ξ` (Level 3)

For a finite set `F` of multi-indices and coefficients `t`,
`(∑_{α∈F} t_α H_α, -∑_{α∈F} κ_α t_α H_α) ∈ CylApprox`, where `H_α = h_α(ξ)` and
`κ_α = ∑_j ν_j α_j` (`cylApprox_hermite`). The approximants are the compactly supported
`∑ t_α ∏_k ρ_R(y_k) q_{α_k}(y_k)` (Level 2), and `R → ∞` is dominated convergence in
`L²(γ_ref)` transported along `ξ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open scoped ENNReal ContDiff

namespace SharpLSI

/-- `κ_α = ∑_j ν_j α_j`. -/
noncomputable def kappa (ν : ℕ → ℝ) (α : ℕ →₀ ℕ) : ℝ := α.sum fun j n => ν j * n

theorem kappa_eq_sum_range (ν : ℕ → ℝ) {α : ℕ →₀ ℕ} {m : ℕ} (h : α.support ⊆ Finset.range m) :
    kappa ν α = ∑ j ∈ Finset.range m, ν j * α j := by
  unfold kappa Finsupp.sum
  refine Finset.sum_subset h fun j _ hj => ?_
  have : α j = 0 := by simpa using hj
  simp [this]

/-- `q_{α,k} = hermiteQ (α k)`. -/
noncomputable def hq (α : ℕ →₀ ℕ) (k : ℕ) : ℝ[X] := hermiteQ (α k)

/-- The cut Hermite factor `ρ_{n+1} q_{α,k}`. -/
noncomputable def aCut (n : ℕ) (α : ℕ →₀ ℕ) (k : ℕ) : ℝ → ℝ := cutPoly (hq α k) (n + 1)

/-- The generator factor of the cut Hermite factor. -/
noncomputable def genCut (n : ℕ) (α : ℕ →₀ ℕ) (j : ℕ) (s : ℝ) : ℝ :=
  deriv (deriv (aCut n α j)) s - s * deriv (aCut n α j) s

/-- The generator factor of the Hermite factor. -/
noncomputable def genHerm (α : ℕ →₀ ℕ) (j : ℕ) (s : ℝ) : ℝ :=
  (derivative (derivative (hq α j))).eval s - s * (derivative (hq α j)).eval s

noncomputable def bCut (n : ℕ) (α : ℕ →₀ ℕ) (j k : ℕ) : ℝ → ℝ :=
  if k = j then genCut n α j else aCut n α k

noncomputable def bHerm (α : ℕ →₀ ℕ) (j k : ℕ) : ℝ → ℝ :=
  if k = j then genHerm α j else fun s => (hq α k).eval s

/-- The compactly supported approximant on `ℝ^m`. -/
noncomputable def pCut (F : Finset (ℕ →₀ ℕ)) (t : (ℕ →₀ ℕ) → ℝ) (m n : ℕ) (y : Fin m → ℝ) : ℝ :=
  ∑ α ∈ F, t α * ∏ k : Fin m, aCut n α k (y k)

theorem contDiff_aCut (n : ℕ) (α : ℕ →₀ ℕ) (k : ℕ) : ContDiff ℝ ∞ (aCut n α k) :=
  contDiff_cutPoly _ _

theorem continuous_genCut (n : ℕ) (α : ℕ →₀ ℕ) (j : ℕ) : Continuous (genCut n α j) := by
  have h1 := (contDiff_infty_iff_deriv.mp (contDiff_aCut n α j)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  exact h2.continuous.sub (continuous_id.mul h1.continuous)

theorem continuous_genHerm (α : ℕ →₀ ℕ) (j : ℕ) : Continuous (genHerm α j) :=
  (derivative (derivative (hq α j))).continuous.sub
    (continuous_id.mul (derivative (hq α j)).continuous)

theorem continuous_bCut (n : ℕ) (α : ℕ →₀ ℕ) (j k : ℕ) : Continuous (bCut n α j k) := by
  unfold bCut; split_ifs
  · exact continuous_genCut n α j
  · exact (contDiff_aCut n α k).continuous

theorem continuous_bHerm (α : ℕ →₀ ℕ) (j k : ℕ) : Continuous (bHerm α j k) := by
  unfold bHerm; split_ifs
  · exact continuous_genHerm α j
  · exact (hq α k).continuous

theorem contDiff_pCut (F : Finset (ℕ →₀ ℕ)) (t : (ℕ →₀ ℕ) → ℝ) (m n : ℕ) :
    ContDiff ℝ ∞ (pCut F t m n) := by
  unfold pCut
  exact ContDiff.sum fun α _ => contDiff_const.mul
    (contDiff_prod_coord fun k => contDiff_aCut n α k)

theorem hasCompactSupport_pCut (F : Finset (ℕ →₀ ℕ)) (t : (ℕ →₀ ℕ) → ℝ) (m n : ℕ) :
    HasCompactSupport (pCut F t m n) := by
  have hR : (0 : ℝ) < n + 1 := by positivity
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin m → ℝ) (2 * (n + 1))) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)] at hy
  push_neg at hy
  obtain ⟨k, hk⟩ := hy
  unfold pCut
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ k), mul_zero]
  unfold aCut cutPoly
  rw [rho1_eq_zero hR (by rw [Real.norm_eq_abs] at hk; exact hk.le), zero_mul]

theorem prod_update_sub {m : ℕ} (f : Fin m → ℝ → ℝ) (j : Fin m) (a b : ℝ → ℝ) (y : Fin m → ℝ) :
    ∏ k, Function.update f j a k (y k) - y j * ∏ k, Function.update f j b k (y k) =
      ∏ k, Function.update f j (fun s => a s - s * b s) k (y k) := by
  rw [prod_update_eq, prod_update_eq, prod_update_eq]; ring

/-- The generator of `pCut` on `ℝ^m`. -/
theorem gen_pCut (F : Finset (ℕ →₀ ℕ)) (t : (ℕ →₀ ℕ) → ℝ) (m n : ℕ) (y : Fin m → ℝ)
    (j : Fin m) :
    pd (pd (pCut F t m n) j) j y - y j * pd (pCut F t m n) j y =
      ∑ α ∈ F, t α * ∏ k : Fin m,
        Function.update (fun k : Fin m => aCut n α k) j (genCut n α j) k (y k) := by
  have hf : ∀ α, ∀ k : Fin m, ContDiff ℝ ∞ ((fun k : Fin m => aCut n α k) k) := fun α k =>
    contDiff_aCut n α k
  have hP : ∀ α, ContDiff ℝ ∞ (fun y : Fin m → ℝ => ∏ k : Fin m, aCut n α k (y k)) := fun α =>
    contDiff_prod_coord (hf α)
  have h1 : pd (pCut F t m n) j =
      fun y => ∑ α ∈ F, t α * pd (fun y : Fin m → ℝ => ∏ k : Fin m, aCut n α k (y k)) j y := by
    funext y
    exact pd_finset_sum_mul F (fun α => (hP α).differentiable (by simp)) t j y
  have h2 : pd (pd (pCut F t m n) j) j y = ∑ α ∈ F, t α *
      pd (pd (fun y : Fin m → ℝ => ∏ k : Fin m, aCut n α k (y k)) j) j y := by
    rw [h1]
    exact pd_finset_sum_mul F (fun α => (contDiff_pd (hP α) j).differentiable (by simp)) t j y
  rw [h2, h1]
  simp only
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [pd_pd_prod_coord (hf α), pd_prod_coord (hf α)]
  have := prod_update_sub (fun k : Fin m => aCut n α k) j (deriv (deriv (aCut n α j)))
    (deriv (aCut n α j)) y
  beta_reduce
  have hg : genCut n α j = fun s => deriv (deriv (aCut n α j)) s - s * deriv (aCut n α j) s := rfl
  rw [hg, ← this]
  ring

theorem prod_update_fin_eq {m : ℕ} (a g : ℕ → ℝ → ℝ) (j : Fin m) (w : ℕ → ℝ) :
    ∏ k : Fin m, Function.update (fun k : Fin m => a k) j (g j) k (w k) =
      ∏ k ∈ Finset.range m, (if k = (j : ℕ) then g j else a k) (w k) := by
  rw [← Fin.prod_univ_eq_prod_range (fun k => (if k = (j : ℕ) then g j else a k) (w k)) m]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases h : k = j
  · subst h; simp
  · rw [Function.update_of_ne h, if_neg (fun h' => h (Fin.ext h'))]

/-- `H_α` as a product over `k < m`. -/
theorem Hxi_eq_prod {ξ : ℕ → (ℕ → ℝ) → ℝ} {α : ℕ →₀ ℕ} {m : ℕ}
    (h : α.support ⊆ Finset.range m) (z : ℕ → ℝ) :
    Hxi ξ α z = ∏ k ∈ Finset.range m, (hq α k).eval (ξ k z) := by
  unfold Hxi
  rw [hermiteBasis_eq_prod α h]
  exact Finset.prod_congr rfl fun k _ => hermiteN_eq_eval _ _

theorem prod_bHerm_eq {α : ℕ →₀ ℕ} {m j : ℕ} (hj : j ∈ Finset.range m) (w : ℕ → ℝ) :
    ∏ k ∈ Finset.range m, bHerm α j k (w k) =
      -((α j : ℝ) * ∏ k ∈ Finset.range m, (hq α k).eval (w k)) := by
  rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ (fun k => (hq α k).eval (w k)) hj]
  unfold bHerm
  rw [if_pos rfl]
  have e : ∏ k ∈ (Finset.range m).erase j, (if k = j then genHerm α j else fun s => (hq α k).eval s)
      (w k) = ∏ k ∈ (Finset.range m).erase j, (hq α k).eval (w k) :=
    Finset.prod_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]
  rw [e]
  unfold genHerm hq
  rw [hermiteQ_ode]
  ring

/-! ### Level 3 -/

section level3
variable {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {lam' : ℕ → ℝ} {Y : ℕ → (ℕ → ℝ) → ℝ}
  {v : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ) (hY : ∀ i, MemLp (Y i) 2 γ)
  (hξ : ∀ j, IsRowVariable v γ j (ξ j))
  (hW : ∀ j k, Tendsto (fun N => ∑ i ∈ Finset.range N, lam' i * v j i * v k i) atTop
    (𝓝 (if j = k then ν j else 0)))
  (hLξ : ∀ j, Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ Finset.range N,
    lam' i * v j i * (z i + Y i z) - ν j * ξ j z) 2 γ) atTop (𝓝 0))
  (hΞ : AEMeasurable (fun z j => ξ j z) γ) (hmap : γ.map (fun z j => ξ j z) = gammaRef)
include hz hY hξ hW hLξ hΞ hmap

omit [IsProbabilityMeasure γ] hz hY hξ hW hLξ hΞ hmap in
theorem tendsto_eLpNorm_const_mul_gammaRef {f : ℕ → (ℕ → ℝ) → ℝ} (c : ℝ)
    (h : Tendsto (fun n => eLpNorm (f n) 2 gammaRef) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun y => c * f n y) 2 gammaRef) atTop (𝓝 0) := by
  have e : ∀ n, (fun y => c * f n y) = c • f n := fun n => rfl
  simp_rw [e, eLpNorm_const_smul]
  simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)

/-- **Level 3**: finite Hermite sums in `ξ`. -/
theorem cylApprox_hermite (F : Finset (ℕ →₀ ℕ)) (t : (ℕ →₀ ℕ) → ℝ) :
    CylApprox lam' Y γ (fun z => ∑ α ∈ F, t α * Hxi ξ α z)
      (fun z => -∑ α ∈ F, t α * kappa ν α * Hxi ξ α z) := by
  obtain ⟨m, hm⟩ := Finset.exists_nat_subset_range (F.biUnion Finsupp.support)
  have hsupp : ∀ α ∈ F, α.support ⊆ Finset.range m := fun α hα =>
    (Finset.subset_biUnion_of_mem _ hα).trans hm
  obtain ⟨M, hM0, hM⟩ := exists_rho1_deriv_bound
  have hYm : ∀ i, AEStronglyMeasurable (Y i) γ := fun i => (hY i).aestronglyMeasurable
  -- the functions on `ℕ → ℝ`
  set Φ : ℕ → (ℕ → ℝ) → ℝ := fun n w =>
    ∑ α ∈ F, t α * ∏ k ∈ Finset.range m, aCut n α k (w k) with hΦ
  set Φ₀ : (ℕ → ℝ) → ℝ := fun w => ∑ α ∈ F, t α * ∏ k ∈ Finset.range m, (hq α k).eval (w k)
    with hΦ₀
  set Ψ : ℕ → (ℕ → ℝ) → ℝ := fun n w => ∑ α ∈ F, t α *
    ∑ j ∈ Finset.range m, ν j * ∏ k ∈ Finset.range m, bCut n α j k (w k) with hΨ
  set Ψ₀ : (ℕ → ℝ) → ℝ := fun w => ∑ α ∈ F, t α *
    ∑ j ∈ Finset.range m, ν j * ∏ k ∈ Finset.range m, bHerm α j k (w k) with hΨ₀
  have hcΦ : ∀ n, Continuous (Φ n) := fun n => continuous_finsetSum _ fun α _ =>
    continuous_const.mul (continuous_finsetProd _ fun k _ =>
      (contDiff_aCut n α k).continuous.comp (continuous_apply k))
  have hcΦ₀ : Continuous Φ₀ := continuous_finsetSum _ fun α _ =>
    continuous_const.mul (continuous_finsetProd _ fun k _ =>
      (hq α k).continuous.comp (continuous_apply k))
  have hcΨ : ∀ n, Continuous (Ψ n) := fun n => continuous_finsetSum _ fun α _ =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_finsetProd _ fun k _ => (continuous_bCut n α j k).comp (continuous_apply k)))
  have hcΨ₀ : Continuous Ψ₀ := continuous_finsetSum _ fun α _ =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_finsetProd _ fun k _ => (continuous_bHerm α j k).comp (continuous_apply k)))
  -- identities
  have hFn : ∀ n z, pCut F t m n (fun j : Fin m => ξ j z) = Φ n (fun j => ξ j z) := fun n z => by
    simp only [pCut, hΦ]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fin.prod_univ_eq_prod_range (fun k => aCut n α k (ξ k z)) m]
  have hF₀ : ∀ z, ∑ α ∈ F, t α * Hxi ξ α z = Φ₀ (fun j => ξ j z) := fun z => by
    simp only [hΦ₀]
    exact Finset.sum_congr rfl fun α hα => by rw [Hxi_eq_prod (hsupp α hα)]
  have hGn : ∀ n z, (∑ j : Fin m, ν j * (pd (pd (pCut F t m n) j) j (fun i => ξ i z) -
      ξ j z * pd (pCut F t m n) j (fun i => ξ i z))) = Ψ n (fun j => ξ j z) := fun n z => by
    simp only [hΨ]
    have e1 : ∀ j : Fin m, pd (pd (pCut F t m n) j) j (fun i => ξ i z) -
        ξ j z * pd (pCut F t m n) j (fun i => ξ i z) =
        ∑ α ∈ F, t α * ∏ k ∈ Finset.range m, bCut n α j k (ξ k z) := fun j => by
      rw [gen_pCut]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [prod_update_fin_eq (aCut n α) (genCut n α) j (fun k => ξ k z)]
      rfl
    simp_rw [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => t α * (ν j *
      ∏ k ∈ Finset.range m, bCut n α j k (ξ k z))) m]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hG₀ : ∀ z, -∑ α ∈ F, t α * kappa ν α * Hxi ξ α z = Ψ₀ (fun j => ξ j z) := fun z => by
    simp only [hΨ₀]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Hxi_eq_prod (hsupp α hα), kappa_eq_sum_range ν (hsupp α hα)]
    have e : ∀ j ∈ Finset.range m, ν j * ∏ k ∈ Finset.range m, bHerm α j k (ξ k z) =
        -(ν j * α j * ∏ k ∈ Finset.range m, (hq α k).eval (ξ k z)) := fun j hj => by
      rw [prod_bHerm_eq hj (fun k => ξ k z)]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  -- convergence under `γ_ref`
  have hD : ∀ α, ∀ k, MemLp (domPoly M (hq α k)) 2 (gaussianReal 0 1) := fun α k =>
    memLp_domPoly M _
  have hΦconv : Tendsto (fun n => eLpNorm (fun w => Φ n w - Φ₀ w) 2 gammaRef) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_finset_sum (γ := gammaRef) F
      (f := fun α n w => t α * ∏ k ∈ Finset.range m, aCut n α k (w k))
      (g := fun α w => t α * ∏ k ∈ Finset.range m, (hq α k).eval (w k)) fun α _ => by
        have h := tendsto_prod_gammaRef (Finset.range m) (a := fun n k => aCut n α k)
          (a₀ := fun k s => (hq α k).eval s) (D := fun k => domPoly M (hq α k))
          (fun n k => (contDiff_aCut n α k).continuous) (fun k => (hq α k).continuous)
          (fun k => continuous_domPoly M _) (hD α)
          (fun n k s => abs_cutPoly_le (R := (n : ℝ) + 1) hM0 hM _
            (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) s)
          (fun k s => abs_le_domPoly hM0 _ s)
          (fun k s => (eventually_cutPoly_eq (hq α k) s).mono fun n hn => hn.1)
        have := tendsto_eLpNorm_const_mul_gammaRef (t α) h
        refine this.congr fun n => ?_
        congr 1; funext w; ring
    refine this.congr fun n => ?_
    congr 1
  have hΨconv : Tendsto (fun n => eLpNorm (fun w => Ψ n w - Ψ₀ w) 2 gammaRef) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_finset_sum (γ := gammaRef) F
      (f := fun α n w => t α * ∑ j ∈ Finset.range m, ν j *
        ∏ k ∈ Finset.range m, bCut n α j k (w k))
      (g := fun α w => t α * ∑ j ∈ Finset.range m, ν j *
        ∏ k ∈ Finset.range m, bHerm α j k (w k)) fun α _ => by
        have hj := tendsto_eLpNorm_finset_sum (γ := gammaRef) (Finset.range m)
          (f := fun j n w => ν j * ∏ k ∈ Finset.range m, bCut n α j k (w k))
          (g := fun j w => ν j * ∏ k ∈ Finset.range m, bHerm α j k (w k)) fun j _ => by
            have h := tendsto_prod_gammaRef (Finset.range m) (a := fun n k => bCut n α j k)
              (a₀ := bHerm α j) (D := fun k => domPoly M (hq α k))
              (fun n k => continuous_bCut n α j k) (continuous_bHerm α j)
              (fun k => continuous_domPoly M _) (hD α)
              (fun n k s => by
                have hR : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
                unfold bCut; split_ifs with hk
                · subst hk; exact abs_gen_cutPoly_le (R := (n : ℝ) + 1) hM0 hM _ hR s
                · exact abs_cutPoly_le (R := (n : ℝ) + 1) hM0 hM _ hR s)
              (fun k s => by
                unfold bHerm; split_ifs with hk
                · subst hk; exact abs_gen_le_domPoly hM0 _ s
                · exact abs_le_domPoly hM0 _ s)
              (fun k s => by
                filter_upwards [eventually_cutPoly_eq (hq α j) s,
                  eventually_cutPoly_eq (hq α k) s] with n h1 h2
                unfold bCut bHerm; split_ifs with hk
                · subst hk; unfold genCut genHerm aCut; rw [h1.2.2, h1.2.1]
                · exact h2.1)
            have := tendsto_eLpNorm_const_mul_gammaRef (ν j) h
            refine this.congr fun n => ?_
            congr 1; funext w; ring
        have := tendsto_eLpNorm_const_mul_gammaRef (t α) hj
        refine this.congr fun n => ?_
        congr 1; funext w; rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    refine this.congr fun n => ?_
    congr 1
  -- transport along `ξ`
  have htr : ∀ {h : (ℕ → ℝ) → ℝ}, Continuous h →
      eLpNorm (fun z => h (fun j => ξ j z)) 2 γ = eLpNorm h 2 gammaRef := fun hc =>
    eLpNorm_comp_xi hΞ hmap hc.aestronglyMeasurable
  have hFg : (fun z => ∑ α ∈ F, t α * Hxi ξ α z) = fun z => Φ₀ (fun j => ξ j z) := funext hF₀
  have hGg : (fun z => -∑ α ∈ F, t α * kappa ν α * Hxi ξ α z) = fun z => Ψ₀ (fun j => ξ j z) :=
    funext hG₀
  rw [hFg, hGg]
  refine CylApprox.of_tendsto hYm (Fk := fun n z => Φ n (fun j => ξ j z))
    (Gk := fun n z => Ψ n (fun j => ξ j z)) (fun n => ?_)
    (fun n => (hcΦ n).comp_aestronglyMeasurable hΞ.aestronglyMeasurable)
    (fun n => (hcΨ n).comp_aestronglyMeasurable hΞ.aestronglyMeasurable)
    (hcΦ₀.comp_aestronglyMeasurable hΞ.aestronglyMeasurable)
    (hcΨ₀.comp_aestronglyMeasurable hΞ.aestronglyMeasurable) ?_ ?_
  · have h := cylApprox_comp_xi hz hY hξ hW hLξ (contDiff_pCut F t m n) (hasCompactSupport_pCut F t m n)
    have e1 : (fun z => pCut F t m n (fun j : Fin m => ξ j z)) = fun z => Φ n (fun j => ξ j z) :=
      funext (hFn n)
    have e2 : (fun z => ∑ j : Fin m, ν j * (pd (pd (pCut F t m n) j) j (fun i => ξ i z) -
        ξ j z * pd (pCut F t m n) j (fun i => ξ i z))) = fun z => Ψ n (fun j => ξ j z) :=
      funext (hGn n)
    rw [e1, e2] at h
    exact h
  · refine hΦconv.congr fun n => ?_
    exact (htr ((hcΦ n).sub hcΦ₀)).symm
  · refine hΨconv.congr fun n => ?_
    exact (htr ((hcΨ n).sub hcΨ₀)).symm

end level3

end SharpLSI
