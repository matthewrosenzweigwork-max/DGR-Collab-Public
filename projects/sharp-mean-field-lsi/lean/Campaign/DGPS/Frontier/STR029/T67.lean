import DGPS.Frontier.STR029.T64
import DGPS.Frontier.STR029.T65
import DGPS.Frontier.STR029.T66

/-!
# STR029.67: Bootstrap parameter regularity and preserve the jets

Task id: STR029.67 (node STR029, frontier unit, leaf formalization).
Title: Bootstrap parameter regularity and preserve the jets.

On the open branch interval of STR029.24 and STR029.64, the branch `u_j(h)` is `C^3` in `h` with
values in every periodic space `C^k`. Under the natural inclusions into `C^0`, its first two
parameter derivatives coincide with those computed in `C^{2,1/2}`. The third derivative in each
fixed `C^k` is bounded on every smaller closed interval.

## Provides

* `DGPS.Frontier.STR029.str029_67_bootstrap_parameter_regularity_preserve_jets`: the existence
  conclusion of STR029.64 restated in full, on an interval `Set.Ioo (-δ) δ`, with one further
  clause. For each `j : Fin 3` there is a map `Uα` into `C^{2,1/2}` that is smooth in `h` and
  has the branch as underlying function. For every `k` there is a map `W` into `C^k` that is
  `C^3` in `h`, has the branch as underlying function, has first three jets (orders `0, 1, 2`)
  equal to those of `Uα` after the inclusions into `C^0`, and has a bounded third derivative on
  every closed interval inside `Set.Ioo (-δ) δ`.
* `DGPS.Frontier.STR029.str029_67_bootstrap_parameter_regularity_preserve_jets_branch_regularity`:
  the regularity clause for one branch over an arbitrary open interval, from smoothness of the
  range graph `ψ` and of the critical point `Z`, a parameter-point membership hypothesis, and
  the Euler equation.
* Helpers, all with the suffix `_STR02967`: the inclusions `inclGen`, `incl0`, `inclC2`, `inclα0`;
  the bounded inverse `invCLM` of the second derivative on `C^m`; the constant-mean operator
  `meanConstCLM`; the bootstrap step `step_val`; the induction `bootstrap`; jets through bounded
  maps `iteratedDeriv_clm`; the third-derivative bound `third_bdd`; the jet comparison
  `jets_coincide`; the base-case family `Ua` with `Ua_contDiffOn`; and the interval shrink
  `eventually_param_mem`.

## R5 notes

* Hypotheses. None beyond those of STR029.64. The branch is the constructed data of
  STR029.24 and STR029.64, so the statement is an existence statement with no external input.
* Proof route. The map `Ua` sends `h` to `paramMap` applied to the parameter point and the graph
  value `ψ`, which is smooth by STR029.15 and composition. It gives smooth dependence into
  `C^{2,1/2}`, hence `C^3` into `C^2`. Inductively, assume `C^3` into `C^{m+1}`. STR029.66 puts
  the right side of the Euler equation of STR029.64 in `C^3` into the mean-zero part of `C^m`.
  The bounded inverse of the second derivative (STR029.65), composed with the mean projection,
  gives `C^3` into `C^{m+2}`. The Euler equation identifies this with the branch.
* The branch is not mean-zero. The inverse of the second derivative applied to `u''` returns
  `u - mean u`. The step therefore adds the bounded constant-mean operator applied to the
  previous iterate, so the correction term is also `C^3` in `h`.
* Non-literal reading, all `j`. The statement is proved for every `j : Fin 3`, not only the even
  branch. The Euler equation holds for every `j` by the pointwise lemma of STR029.64.
* Non-literal reading, the interval. The common branch interval of STR029.24 does not record
  that the parameter point `(h z0, h z1, h, h^2 z2)` lies in the open set `U` on which `ψ` is
  smooth. The interval is therefore shrunk to `Set.Ioo (-min δ ε) (min δ ε)`, with `ε` from
  continuity of `Z` at `0`. The STR029.64 clauses are restated on this interval, which is
  contained in the original one and contains `0`. The shrunken radius is the `δ` of the
  statement.
* Non-literal reading, "natural inclusions into `C^0`". These are the continuous linear maps
  `incl0_STR02967 k : C^k → C^0` and `inclα0_STR02967 : C^{2,1/2} → C^0`, both the identity on
  underlying functions.
* Non-literal reading, "`C^3` into `C^k`". It is stated as the existence of a lift
  `W : ℝ → PerCm_STR02966 k` that is `ContDiffOn ℝ 3` on the interval and whose underlying
  function is the branch. The lift is unique because the underlying function determines the
  element.
* Non-literal reading, "first two parameter derivatives". These are `iteratedDeriv i` for
  `i = 0, 1, 2`, compared as `incl0 k (iteratedDeriv i W h) = inclα0 (iteratedDeriv i Uα h)`. The
  derivatives exist because both maps are at least `C^3` on an open interval.
* Non-literal reading, "smaller closed interval". It is `Set.Icc a b ⊆ Set.Ioo (-δ) δ`, with a
  bound `M` on `‖iteratedDeriv 3 W h‖` over `Set.Icc a b`, for each fixed `k`.
* Carriers. `C^k` is `PerCm_STR02966 k` with the sum-of-sup-norms norm of STR029.66. `C^{2,1/2}`
  is `PeriodicC2_STR02969`. The smoothness of `Uα` is stated as `ContDiffOn ℝ ∞`, which is
  stronger than the `C^3` that the spec requires.
* STR029.27 is not used by the proof.
-/

open scoped ContDiff
open Topology
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Inclusions between the spaces `C^k` -/

noncomputable def inclLinGen_STR02967 {k k' : ℕ} (hk : k ≤ k') :
    PerCm_STR02966 k' →ₗ[ℝ] PerCm_STR02966 k where
  toFun f := PerCm_STR02966.mk f.val (isPerCm_of_le_STR02966 hk f.isPerCm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cmN_mono_STR02967 {k k' : ℕ} (hk : k ≤ k') (f : ℝ → ℝ) :
    cmN_STR02966 k f ≤ cmN_STR02966 k' f := by
  induction k', hk using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (cmN_le_succ_STR02966 n f)

noncomputable def inclGen_STR02967 {k k' : ℕ} (hk : k ≤ k') :
    PerCm_STR02966 k' →L[ℝ] PerCm_STR02966 k :=
  (inclLinGen_STR02967 hk).mkContinuous 1 fun f => by
    show cmN_STR02966 k f.val ≤ 1 * cmN_STR02966 k' f.val
    rw [one_mul]
    exact cmN_mono_STR02967 hk f.val

theorem inclGen_val_STR02967 {k k' : ℕ} (hk : k ≤ k') (f : PerCm_STR02966 k') :
    (inclGen_STR02967 hk f).val = f.val := rfl

noncomputable def incl0_STR02967 (k : ℕ) : PerCm_STR02966 k →L[ℝ] PerCm_STR02966 0 :=
  inclGen_STR02967 (Nat.zero_le k)

theorem incl0_val_STR02967 (k : ℕ) (f : PerCm_STR02966 k) : (incl0_STR02967 k f).val = f.val := rfl

theorem cmN_two_STR02967 (f : ℝ → ℝ) :
    cmN_STR02966 2 f = supNorm f + supNorm (deriv f) + supNorm (deriv (deriv f)) := by
  simp [cmN_STR02966, Finset.sum_range_succ, iteratedDeriv_succ]

theorem isPerCm_two_STR02967 {f : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f) :
    IsPerCm_STR02966 2 f := by
  refine ⟨hf.1, ?_⟩
  have h1 : ContDiff ℝ 1 (deriv f) := contDiff_one_iff_deriv.2 ⟨hf.2.2.1, hf.2.2.2.1⟩
  have h2 : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) f :=
    (contDiff_succ_iff_deriv (n := 1)).2 ⟨hf.2.1, fun h => by simp at h, h1⟩
  exact h2

noncomputable def inclC2Lin_STR02967 : PeriodicC2_STR02969 →ₗ[ℝ] PerCm_STR02966 2 where
  toFun f := PerCm_STR02966.mk f.val (isPerCm_two_STR02967 f.isC2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def inclC2_STR02967 : PeriodicC2_STR02969 →L[ℝ] PerCm_STR02966 2 :=
  inclC2Lin_STR02967.mkContinuous 1 fun f => by
    show cmN_STR02966 2 f.val ≤ 1 * c2Norm_STR02901 (1 / 2) f.val
    rw [one_mul, cmN_two_STR02967]
    have := le_c2Norm_STR02969 f.val
    have h4 := circHolder_nonneg_STR02953 (1 / 2) (deriv (deriv f.val))
    rw [c2Norm_parts_STR02969]
    linarith [supNorm_nonneg f.val, supNorm_nonneg (deriv f.val), supNorm_nonneg (deriv (deriv f.val))]

theorem inclC2_val_STR02967 (f : PeriodicC2_STR02969) : (inclC2_STR02967 f).val = f.val := rfl

noncomputable def inclα0_STR02967 : PeriodicC2_STR02969 →L[ℝ] PerCm_STR02966 0 :=
  (incl0_STR02967 2).comp inclC2_STR02967

theorem inclα0_val_STR02967 (f : PeriodicC2_STR02969) : (inclα0_STR02967 f).val = f.val := rfl

/-! ### The inverse of the second derivative as a bounded operator -/

theorem P0_mem_STR02967 {m : ℕ} (f : PerCm_STR02966 m) :
    (P0CLM_STR02966 m f).val ∈ meanZeroPerC_STR02965 m := by
  refine ⟨(P0CLM_STR02966 m f).isPerCm.1, (P0CLM_STR02966 m f).isPerCm.2, ?_⟩
  rw [P0CLM_val_STR02966]
  exact meanT_sub_self_STR02965 f.isPerCm.2.continuous

noncomputable def invLin_STR02967 (m : ℕ) : PerCm_STR02966 m →ₗ[ℝ] PerCm_STR02966 (m + 2) where
  toFun f := PerCm_STR02966.mk (invD2_STR02965 (P0CLM_STR02966 m f).val)
    (by
      have h := invD2_mem_STR02965 m (P0_mem_STR02967 f)
      exact ⟨h.1, h.2.1⟩)
  map_add' f g := by
    apply PerCm_STR02966.ext
    have hf := P0_mem_STR02967 f
    have hg := P0_mem_STR02967 g
    show invD2_STR02965 (P0CLM_STR02966 m (f + g)).val =
      invD2_STR02965 (P0CLM_STR02966 m f).val + invD2_STR02965 (P0CLM_STR02966 m g).val
    rw [map_add, PerCm_STR02966.val_add]
    exact invD2_add_STR02965 hf.2.1.continuous hf.1 hf.2.2 hg.2.1.continuous hg.1 hg.2.2
  map_smul' c f := by
    apply PerCm_STR02966.ext
    have hf := P0_mem_STR02967 f
    show invD2_STR02965 (P0CLM_STR02966 m (c • f)).val = c • invD2_STR02965 (P0CLM_STR02966 m f).val
    rw [map_smul, PerCm_STR02966.val_smul]
    exact invD2_smul_STR02965 c hf.2.1.continuous hf.1 hf.2.2

noncomputable def invCLM_STR02967 (m : ℕ) : PerCm_STR02966 m →L[ℝ] PerCm_STR02966 (m + 2) :=
  (invLin_STR02967 m).mkContinuous ((16 * Real.pi ^ 2 + 4 * Real.pi + 1) * 2) fun f => by
    have h1 := cmNorm_bound_STR02965 m (P0_mem_STR02967 f)
    have h2 : ‖P0CLM_STR02966 m f‖ ≤ 2 * ‖f‖ :=
      ((P0CLM_STR02966 m).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (P0CLM_norm_le_STR02966 m) (norm_nonneg f))
    have hK : 0 ≤ 16 * Real.pi ^ 2 + 4 * Real.pi + 1 := by positivity
    calc ‖invLin_STR02967 m f‖
        = cmNorm_STR02965 (m + 2) (invD2_STR02965 (P0CLM_STR02966 m f).val) := rfl
      _ ≤ (16 * Real.pi ^ 2 + 4 * Real.pi + 1) * cmNorm_STR02965 m (P0CLM_STR02966 m f).val := h1
      _ = (16 * Real.pi ^ 2 + 4 * Real.pi + 1) * ‖P0CLM_STR02966 m f‖ := rfl
      _ ≤ (16 * Real.pi ^ 2 + 4 * Real.pi + 1) * (2 * ‖f‖) := by gcongr
      _ = (16 * Real.pi ^ 2 + 4 * Real.pi + 1) * 2 * ‖f‖ := by ring

theorem invCLM_val_STR02967 (m : ℕ) (f : PerCm_STR02966 m) :
    (invCLM_STR02967 m f).val = invD2_STR02965 (P0CLM_STR02966 m f).val := rfl

/-! ### The constant function carrying the Haar mean -/

noncomputable def meanConstLin_STR02967 (m n : ℕ) : PerCm_STR02966 m →ₗ[ℝ] PerCm_STR02966 n where
  toFun f := PerCm_STR02966.mk (fun _ => meanCm_STR02966 f.val) (isPerCm_const_STR02966 n _)
  map_add' f g := by
    apply PerCm_STR02966.ext
    show (fun _ => meanCm_STR02966 (f.val + g.val)) =
      fun _ => meanCm_STR02966 f.val + meanCm_STR02966 g.val
    rw [meanCm_add_STR02966 f.isPerCm.2.continuous g.isPerCm.2.continuous]
  map_smul' c f := by
    apply PerCm_STR02966.ext
    show (fun _ => meanCm_STR02966 (c • f.val)) = fun _ => c * meanCm_STR02966 f.val
    rw [meanCm_smul_STR02966]

noncomputable def meanConstCLM_STR02967 (m n : ℕ) : PerCm_STR02966 m →L[ℝ] PerCm_STR02966 n :=
  (meanConstLin_STR02967 m n).mkContinuous 1 fun f => by
    rw [PerCm_STR02966.norm_def, PerCm_STR02966.norm_def, one_mul]
    show cmN_STR02966 n (fun _ => meanCm_STR02966 f.val) ≤ cmN_STR02966 m f.val
    rw [cmN_const_STR02966]
    exact (abs_meanCm_le_STR02966 f.isPerCm).trans (supNorm_le_cmN_STR02966 m f.val)

theorem meanConstCLM_val_STR02967 (m n : ℕ) (f : PerCm_STR02966 m) :
    (meanConstCLM_STR02967 m n f).val = fun _ => meanCm_STR02966 f.val := rfl

/-! ### The bootstrap step -/

theorem step_val_STR02967 (m : ℕ) (h r : ℝ) (w : PerCm_STR02966 (m + 1))
    (hu : IsC2Alpha_STR02901 (1 / 2) w.val)
    (hE : ∀ t, deriv (deriv w.val) t = P0_STR02964 (eulerF_STR02964 h r w.val) t) :
    (invCLM_STR02967 m (rhs64_STR02966 m h r w) +
      meanConstCLM_STR02967 (m + 1) (m + 2) w).val = w.val := by
  have hg : (rhs64_STR02966 m h r w).val = deriv (deriv w.val) := by
    funext x
    rw [rhs64_formula_STR02966, hE x]
    rfl
  have h0 : meanCm_STR02966 (deriv (deriv w.val)) = 0 := meanT_dd_zero_STR02964 hu
  have hP : (P0CLM_STR02966 m (rhs64_STR02966 m h r w)).val = deriv (deriv w.val) := by
    rw [P0CLM_val_STR02966, hg, h0]
    funext x
    simp
  have hc : Continuous w.val := hu.2.1.continuous
  have hper2 : Function.Periodic (deriv (deriv w.val)) (2 * Real.pi) :=
    periodic_deriv_STR02966 (periodic_deriv_STR02966 hu.1)
  have hv := isPerCm_two_STR02967 hu
  have hmain : invD2_STR02965 (deriv (deriv w.val)) = fun t => w.val t - meanCm_STR02966 w.val := by
    symm
    refine invD2_eq_STR02965 hu.2.2.2.1 hper2 h0 (isPerCm_sub_const_STR02966 hv _).1 ?_ ?_ ?_
    · exact (isPerCm_sub_const_STR02966 hv _).2
    · exact meanT_sub_self_STR02965 hc
    · have hd : deriv (fun t => w.val t - meanCm_STR02966 w.val) = deriv w.val := by
        funext x
        exact deriv_sub_const _
      rw [hd]
  have e1 : (invCLM_STR02967 m (rhs64_STR02966 m h r w)).val =
      invD2_STR02965 (deriv (deriv w.val)) := by
    rw [invCLM_val_STR02967, hP]
  rw [PerCm_STR02966.val_add, e1, hmain]
  funext x
  show w.val x - meanCm_STR02966 w.val + meanCm_STR02966 w.val = w.val x
  ring

/-! ### The bootstrap induction -/

theorem bootstrap_STR02967 {s : Set ℝ} {r : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hr : ContDiffOn ℝ 3 r s)
    (hu2 : ∀ h ∈ s, IsC2Alpha_STR02901 (1 / 2) (u h))
    (hE : ∀ h ∈ s, ∀ t, deriv (deriv (u h)) t = P0_STR02964 (eulerF_STR02964 h (r h) (u h)) t)
    {W0 : ℝ → PerCm_STR02966 2} (hW0 : ContDiffOn ℝ 3 W0 s)
    (hW0v : ∀ h ∈ s, (W0 h).val = u h) :
    ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 (k + 2), ContDiffOn ℝ 3 W s ∧ ∀ h ∈ s, (W h).val = u h := by
  intro k
  induction k with
  | zero => exact ⟨W0, hW0, hW0v⟩
  | succ k ih =>
    obtain ⟨W, hWC, hWv⟩ := ih
    refine ⟨fun h => invCLM_STR02967 (k + 1) (rhs64_STR02966 (k + 1) h (r h) (W h)) +
      meanConstCLM_STR02967 (k + 1 + 1) (k + 1 + 2) (W h), ?_, ?_⟩
    · exact ((invCLM_STR02967 (k + 1)).contDiff.comp_contDiffOn
        (rhs64_contDiffOn_STR02966 (k + 1) hr hWC)).add
        ((meanConstCLM_STR02967 (k + 1 + 1) (k + 1 + 2)).contDiff.comp_contDiffOn hWC)
    · intro h hh
      have := step_val_STR02967 (k + 1) h (r h) (W h) (by rw [hWv h hh]; exact hu2 h hh)
        (by rw [hWv h hh]; exact hE h hh)
      rw [this, hWv h hh]

/-! ### Jets through bounded linear maps -/

theorem iteratedDeriv_clm_STR02967 {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : ℝ → F} {s : Set ℝ}
    (hs : IsOpen s) {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) {i : ℕ}
    (hi : (i : WithTop ℕ∞) ≤ n) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv i (fun y => L (f y)) x = L (iteratedDeriv i f x) := by
  have hu : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hfx : ContDiffWithinAt ℝ n f s x := hf x hx
  have e1 : iteratedDeriv i (fun y => L (f y)) x =
      iteratedDerivWithin i (fun y => L (f y)) s x :=
    (iteratedDerivWithin_of_isOpen hs hx).symm
  have e2 : iteratedDeriv i f x = iteratedDerivWithin i f s x :=
    (iteratedDerivWithin_of_isOpen hs hx).symm
  rw [e1, e2, iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedDerivWithin_eq_iteratedFDerivWithin]
  have h := L.iteratedFDerivWithin_comp_left hfx hu hx hi
  show (iteratedFDerivWithin ℝ i (L ∘ f) s x) _ = _
  rw [h]
  rfl

theorem third_bdd_STR02967 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {W : ℝ → F}
    {I : Set ℝ} (hI : IsOpen I) (hW : ContDiffOn ℝ 3 W I) {a b : ℝ} (hab : Set.Icc a b ⊆ I) :
    ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M := by
  have hc : ContinuousOn (iteratedDeriv 3 W) I :=
    (hW.continuousOn_iteratedDerivWithin (m := 3) (by norm_num) hI.uniqueDiffOn).congr
      (fun x hx => (iteratedDerivWithin_of_isOpen hI hx).symm)
  exact isCompact_Icc.exists_bound_of_continuousOn (hc.mono hab)

theorem jets_coincide_STR02967 {k : ℕ} {I : Set ℝ} (hI : IsOpen I) {W : ℝ → PerCm_STR02966 k}
    {Uα : ℝ → PeriodicC2_STR02969} (hW : ContDiffOn ℝ 3 W I) (hU : ContDiffOn ℝ 3 Uα I)
    (hv : ∀ h ∈ I, (W h).val = (Uα h).val) {h : ℝ} (hh : h ∈ I) {i : ℕ} (hi : i ≤ 3) :
    incl0_STR02967 k (iteratedDeriv i W h) = inclα0_STR02967 (iteratedDeriv i Uα h) := by
  have hi' : (i : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hi
  rw [← iteratedDeriv_clm_STR02967 (incl0_STR02967 k) hI hW hi' hh,
    ← iteratedDeriv_clm_STR02967 inclα0_STR02967 hI hU hi' hh]
  refine Set.EqOn.iteratedDeriv_of_isOpen (fun y hy => ?_) hI i hh
  apply PerCm_STR02966.ext
  show (W y).val = (Uα y).val
  exact hv y hy

/-! ### The base case from the smooth range graph -/

noncomputable def Ua_STR02967 (ψ : Par_STR02916 → E_STR02969) (Z : ℝ → Fin 3 → ℝ) (h : ℝ) :
    PeriodicC2_STR02969 :=
  (paramMap_STR02915 (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2,
    ψ (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2))).2.2

theorem Ua_val_STR02967 (ψ : Par_STR02916 → E_STR02969) (Z : ℝ → Fin 3 → ℝ) (h : ℝ) :
    (Ua_STR02967 ψ Z h).val = chartU_STR02924 ψ h (Z h) :=
  paramMap_val_STR02915 _ _ _

theorem Ua_contDiffOn_STR02967 {ψ : Par_STR02916 → E_STR02969} {Z : ℝ → Fin 3 → ℝ}
    {U : Set Par_STR02916} {I : Set ℝ} (hψ : ContDiffOn ℝ ∞ ψ U) (hZ : ContDiffOn ℝ ∞ Z I)
    (hmem : ∀ h ∈ I, (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2) ∈ U) :
    ContDiffOn ℝ ∞ (Ua_STR02967 ψ Z) I := by
  have hZi : ∀ i, ContDiffOn ℝ ∞ (fun h => Z h i) I := contDiffOn_pi.1 hZ
  have hpt : ContDiffOn ℝ ∞ (fun h : ℝ => (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2)) I :=
    (contDiffOn_id.mul (hZi 0)).prodMk ((contDiffOn_id.mul (hZi 1)).prodMk
      (contDiffOn_id.prodMk ((contDiffOn_id.pow 2).mul (hZi 2))))
  have hψpt : ContDiffOn ℝ ∞ (fun h : ℝ => ψ (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2)) I :=
    hψ.comp hpt (fun h hh => hmem h hh)
  have hg : ContDiffOn ℝ ∞ (fun h : ℝ => (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2,
      ψ (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2))) I :=
    (contDiffOn_id.mul (hZi 0)).prodMk ((contDiffOn_id.mul (hZi 1)).prodMk
      (contDiffOn_id.prodMk (((contDiffOn_id.pow 2).mul (hZi 2)).prodMk hψpt)))
  exact (contDiff_snd.comp (contDiff_snd.comp paramMap_smooth_STR02915)).comp_contDiffOn hg

theorem eventually_param_mem_STR02967 {U : Set Par_STR02916} (hUo : IsOpen U)
    (hU0 : (0 : Par_STR02916) ∈ U) {η : ℝ} (hη : 0 < η) {Z : Fin 3 → ℝ → Fin 3 → ℝ}
    (hZ : ∀ j, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-ε) ε,
      (h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) ∈ U := by
  have hev : ∀ j : Fin 3, ∀ᶠ h in 𝓝 (0 : ℝ),
      (h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) ∈ U := by
    intro j
    have hZc : ContinuousAt (Z j) 0 :=
      (hZ j).continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hη)
    have hc0 : ContinuousAt (fun h => Z j h 0) 0 := (continuous_apply 0).continuousAt.comp hZc
    have hc1 : ContinuousAt (fun h => Z j h 1) 0 := (continuous_apply 1).continuousAt.comp hZc
    have hc2 : ContinuousAt (fun h => Z j h 2) 0 := (continuous_apply 2).continuousAt.comp hZc
    have hcont : ContinuousAt (fun h : ℝ => (h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2)) 0 :=
      (continuousAt_id.mul hc0).prodMk ((continuousAt_id.mul hc1).prodMk
        (continuousAt_id.prodMk ((continuousAt_id.pow 2).mul hc2)))
    have hval : ((0 : ℝ) * Z j 0 0, (0 : ℝ) * Z j 0 1, (0 : ℝ), (0 : ℝ) ^ 2 * Z j 0 2) =
        (0 : Par_STR02916) :=
      Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) (by simp)))
    refine hcont.eventually_mem (hUo.mem_nhds ?_)
    show ((0 : ℝ) * Z j 0 0, (0 : ℝ) * Z j 0 1, (0 : ℝ), (0 : ℝ) ^ 2 * Z j 0 2) ∈ U
    rw [hval]
    exact hU0
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.1 (Filter.eventually_all.2 hev)
  refine ⟨ε, hε, fun j h hh => hεh ?_ j⟩
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact hh

/-! ### Regularity of one branch -/

theorem str029_67_bootstrap_parameter_regularity_preserve_jets_branch_regularity
    {ψ : Par_STR02916 → E_STR02969} {U : Set Par_STR02916} {Z : ℝ → Fin 3 → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hψ : ContDiffOn ℝ ∞ ψ U) (hZ : ContDiffOn ℝ ∞ Z I)
    (hmem : ∀ h ∈ I, (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2) ∈ U)
    (hE : ∀ h ∈ I, ∀ t, deriv (deriv (chartU_STR02924 ψ h (Z h))) t =
      P0_STR02964 (eulerF_STR02964 h (1 + h ^ 2 * Z h 2) (chartU_STR02924 ψ h (Z h))) t) :
    ∃ Uα : ℝ → PeriodicC2_STR02969, ContDiffOn ℝ ∞ Uα I ∧
      (∀ h ∈ I, (Uα h).val = chartU_STR02924 ψ h (Z h)) ∧
      ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k, ContDiffOn ℝ 3 W I ∧
        (∀ h ∈ I, (W h).val = chartU_STR02924 ψ h (Z h)) ∧
        (∀ h ∈ I, ∀ i : ℕ, i ≤ 2 →
          incl0_STR02967 k (iteratedDeriv i W h) = inclα0_STR02967 (iteratedDeriv i Uα h)) ∧
        (∀ a b : ℝ, Set.Icc a b ⊆ I → ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M) := by
  have hUa : ContDiffOn ℝ ∞ (Ua_STR02967 ψ Z) I := Ua_contDiffOn_STR02967 hψ hZ hmem
  have hUa3 : ContDiffOn ℝ 3 (Ua_STR02967 ψ Z) I := hUa.of_le (WithTop.coe_le_coe.2 le_top)
  have hZ2 : ContDiffOn ℝ ∞ (fun h => Z h 2) I := contDiffOn_pi.1 hZ 2
  have hr : ContDiffOn ℝ 3 (fun h : ℝ => 1 + h ^ 2 * Z h 2) I := by
    have hinf : ContDiffOn ℝ ∞ (fun h : ℝ => 1 + h ^ 2 * Z h 2) I :=
      contDiffOn_const.add ((contDiffOn_id.pow 2).mul hZ2)
    exact hinf.of_le (WithTop.coe_le_coe.2 le_top)
  have hu2 : ∀ h ∈ I, IsC2Alpha_STR02901 (1 / 2) (chartU_STR02924 ψ h (Z h)) :=
    fun h _ => chartU_isC2_STR02924 ψ h (Z h)
  have hboot := bootstrap_STR02967 (s := I) (r := fun h => 1 + h ^ 2 * Z h 2)
    (u := fun h => chartU_STR02924 ψ h (Z h)) hr hu2 hE
    (W0 := fun h => inclC2_STR02967 (Ua_STR02967 ψ Z h))
    (inclC2_STR02967.contDiff.comp_contDiffOn hUa3)
    (fun h _ => by rw [inclC2_val_STR02967, Ua_val_STR02967])
  refine ⟨Ua_STR02967 ψ Z, hUa, fun h _ => Ua_val_STR02967 ψ Z h, fun k => ?_⟩
  obtain ⟨W, hW, hWv⟩ := hboot k
  have hW' : ContDiffOn ℝ 3 (fun h => inclGen_STR02967 (Nat.le_add_right k 2) (W h)) I :=
    (inclGen_STR02967 (Nat.le_add_right k 2)).contDiff.comp_contDiffOn hW
  refine ⟨fun h => inclGen_STR02967 (Nat.le_add_right k 2) (W h), hW', hWv, ?_, ?_⟩
  · intro h hh i hi
    refine jets_coincide_STR02967 hI hW' hUa3 ?_ hh (by omega)
    intro y hy
    show (W y).val = (Ua_STR02967 ψ Z y).val
    rw [hWv y hy, Ua_val_STR02967]
  · intro a b hab
    exact third_bdd_STR02967 hI hW' hab

/-! ### The main statement -/

theorem str029_67_bootstrap_parameter_regularity_preserve_jets :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) ∧
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                (∀ t, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
                (∀ t, gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0) ∧
                (h ≠ 0 →
                  0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
                  fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
                    (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) =
                    1 + h ^ 2 * Z j h 2)) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → ∀ i j : Fin 3, i ≠ j →
                rhoT_STR02901 h (chartU_STR02924 ψ h (Z i h)) ≠
                  rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) ∧
              (∀ j : Fin 3, rhoT_STR02901 0 (chartU_STR02924 ψ 0 (Z j 0)) = qT_STR02901 0 ∧
                ∀ t, gradG_STR02950 0 0 (chartU_STR02924 ψ 0 (Z j 0)) t = 0) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ t,
                deriv (deriv (chartU_STR02924 ψ h (Z 0 h))) t =
                  P0_STR02964
                    (eulerF_STR02964 h (1 + h ^ 2 * Z 0 h 2) (chartU_STR02924 ψ h (Z 0 h))) t) ∧
              (∀ j : Fin 3, ∃ Uα : ℝ → PeriodicC2_STR02969,
                ContDiffOn ℝ ∞ Uα (Set.Ioo (-δ) δ) ∧
                (∀ h ∈ Set.Ioo (-δ) δ, (Uα h).val = chartU_STR02924 ψ h (Z j h)) ∧
                ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k, ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ) ∧
                  (∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z j h)) ∧
                  (∀ h ∈ Set.Ioo (-δ) δ, ∀ i : ℕ, i ≤ 2 →
                    incl0_STR02967 k (iteratedDeriv i W h) =
                      inclα0_STR02967 (iteratedDeriv i Uα h)) ∧
                  (∀ a b : ℝ, Set.Icc a b ⊆ Set.Ioo (-δ) δ →
                    ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M)) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, δ, hδ, hδη, hA, hB, hC, hD⟩ :=
    str029_64_full_euler_ordinary_differential_equation_branch
  obtain ⟨ε, hε, hεU⟩ := eventually_param_mem_STR02967 hUo hU0 hη hZC
  have hsub : Set.Ioo (-(min δ ε)) (min δ ε) ⊆ Set.Ioo (-δ) δ :=
    Set.Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsubη : Set.Ioo (-(min δ ε)) (min δ ε) ⊆ Set.Ioo (-η) η :=
    hsub.trans (Set.Ioo_subset_Ioo (neg_le_neg hδη) hδη)
  have hsubε : Set.Ioo (-(min δ ε)) (min δ ε) ⊆ Set.Ioo (-ε) ε :=
    Set.Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  refine ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, min δ ε, lt_min hδ hε, (min_le_left _ _).trans hδη, fun h hh => hA h (hsub hh),
    fun h hh => hB h (hsub hh), hC, fun h hh => hD h (hsub hh), fun j => ?_⟩
  exact str029_67_bootstrap_parameter_regularity_preserve_jets_branch_regularity
    isOpen_Ioo hψC ((hZC j).mono hsubη) (fun h hh => hεU j h (hsubε hh))
    (fun h hh t => euler_pointwise_STR02964 h (h ^ 2 * Z j h 2) (chartU_isC2_STR02924 ψ h (Z j h))
      (hA h (hsub hh) j).2.1 t)

end DGPS.Frontier.STR029
