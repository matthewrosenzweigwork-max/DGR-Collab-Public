import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Parameter implicit function and differentiated remainders (FOU019)

INTERFACES/common_lemmas.md FOU019. For real Banach spaces `P`, `W`, `V` and a map
`F : P × W → V` that is `C^k` (`k ≥ 1`, finite) at `(p₀, w₀)`, with `F (p₀, w₀) = 0` and
`D_w F (p₀, w₀)` boundedly invertible, there are open neighbourhoods `U ∋ p₀`, `Wn ∋ w₀` and a
map `ψ` with:
* `ψ p₀ = w₀`, and for `p ∈ U`, `ψ p ∈ Wn` and `F (p, ψ p) = 0`;
* uniqueness: `p ∈ U`, `w ∈ Wn`, `F (p, w) = 0` imply `w = ψ p`;
* `ψ` is `C^k` on `U`, and at every `p ∈ U` the partial derivative `D_w F (p, ψ p)` is invertible
  and `Dψ p = -[D_w F (p, ψ p)]⁻¹ ∘ D_p F (p, ψ p)`;
* on every compact `K ⊆ U` the derivatives of orders `0, …, k` are bounded;
* on every compact convex `K ⊆ U`, the Taylor remainder of every order `j < k` is bounded by
  `C ‖q - p‖ ^ (j + 1)` uniformly for `p, q ∈ K`.

The compact sets are arbitrary; in a finite-dimensional parameter space they include the
closed balls around `p₀` inside `U` (`exists_isCompact_convex_nhds_subset`). The order `k` is an
explicit natural number, as required of every application.

Route: Mathlib `ContDiffAt.implicitFunction` and its API, openness of invertible operators
(`ContinuousLinearEquiv.isOpen`), and Taylor's formula with integral remainder
(`map_add_eq_sum_add_integral_iteratedFDeriv`).
-/

open Filter Set
open scoped Topology Nat ContDiff Interval

namespace DGPS.Analysis

variable {P W V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace P] [CompleteSpace W] [CompleteSpace V] in
/-- The derivative of an implicit function, from the chain rule. If `F (p', ψ p') = 0` near `p`,
`ψ` is differentiable at `p`, `F` at `(p, ψ p)`, and `D_w F (p, ψ p)` is invertible, then
`Dψ p = -[D_w F]⁻¹ ∘ D_p F`. -/
theorem hasFDerivAt_of_eventually_eq_zero {F : P × W → V} {ψ : P → W} {p : P}
    (hψ : DifferentiableAt ℝ ψ p) (hF : DifferentiableAt ℝ F (p, ψ p))
    (hzero : ∀ᶠ p' in 𝓝 p, F (p', ψ p') = 0)
    (hinv : (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible) :
    HasFDerivAt ψ (-(fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).inverse ∘L
      (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inl ℝ P W)) p := by
  set A := fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inl ℝ P W
  set B := fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W
  set D := fderiv ℝ ψ p
  have hG : HasFDerivAt (fun p' => F (p', ψ p'))
      (fderiv ℝ F (p, ψ p) ∘L ((ContinuousLinearMap.id ℝ P).prod D)) p :=
    hF.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk hψ.hasFDerivAt)
  have hG0 : HasFDerivAt (fun p' => F (p', ψ p')) (0 : P →L[ℝ] V) p :=
    (hasFDerivAt_const (0 : V) p).congr_of_eventuallyEq hzero
  have hsum : A + B ∘L D = 0 := by
    have h := hG.unique hG0
    rw [← h]
    ext h
    simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, A, B,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
    rw [← map_add]
    simp
  obtain ⟨e, he⟩ := hinv
  have hD : D = -B.inverse ∘L A := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    have hBD : B ∘L D = -A := eq_neg_of_add_eq_zero_right hsum
    ext h
    have := congrArg (fun L : P →L[ℝ] V => e.symm (L h)) hBD
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      neg_apply] at this
    rw [← he] at this
    simpa using this
  rw [← hD]
  exact hψ.hasFDerivAt

omit [CompleteSpace P] in
/-- In a finite-dimensional parameter space, every open neighbourhood of `p₀` contains a compact
convex neighbourhood (a closed ball). -/
theorem exists_isCompact_convex_nhds_subset [FiniteDimensional ℝ P] {U : Set P} {p₀ : P}
    (hU : IsOpen U) (hp₀ : p₀ ∈ U) :
    ∃ K : Set P, IsCompact K ∧ Convex ℝ K ∧ K ∈ 𝓝 p₀ ∧ K ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp₀)
  exact ⟨Metric.closedBall p₀ r, isCompact_closedBall p₀ r, convex_closedBall p₀ r,
    Metric.closedBall_mem_nhds p₀ hr, hrU⟩

omit [CompleteSpace P] in
/-- Taylor remainder bound on a compact convex set inside an open set where `ψ` is `C^(j+1)`. -/
theorem taylor_remainder_bound_of_contDiffOn {ψ : P → W} {U K : Set P} {j : ℕ}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ (j + 1) ψ U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hKc : Convex ℝ K) :
    ∃ C : ℝ, ∀ p ∈ K, ∀ q ∈ K,
      ‖ψ q - ∑ i ∈ Finset.range (j + 1),
          (i ! : ℝ)⁻¹ • iteratedFDeriv ℝ i ψ p (fun _ => q - p)‖ ≤ C * ‖q - p‖ ^ (j + 1) := by
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hψ hU (k := j + 1) (by exact_mod_cast le_rfl)).mono
      hKU)
  refine ⟨max C₀ 0, fun p hp q hq => ?_⟩
  set y := q - p
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • y ∈ K := by
    intro t ht
    have := hKc.add_smul_sub_mem hp hq ht
    simpa [y] using this
  have hcd : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (j + 1) ψ (p + t • y) := fun t ht =>
    hψ.contDiffAt (hU.mem_nhds (hKU (hseg t ht)))
  have htay := map_add_eq_sum_add_integral_iteratedFDeriv (n := j) (x := p) (y := y)
    (fun t ht => by exact_mod_cast hcd t ht)
  have hpq : p + y = q := by simp [y]
  rw [hpq] at htay
  rw [htay, add_sub_cancel_left]
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(1 - t) ^ j • iteratedFDeriv ℝ (j + 1) ψ (p + t • y) (fun _ => y)‖
        ≤ max C₀ 0 * ‖y‖ ^ (j + 1) := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h1 : ‖(1 - t) ^ j‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
    have h2 : ‖iteratedFDeriv ℝ (j + 1) ψ (p + t • y) (fun _ => y)‖
        ≤ max C₀ 0 * ‖y‖ ^ (j + 1) := by
      calc ‖iteratedFDeriv ℝ (j + 1) ψ (p + t • y) (fun _ => y)‖
          ≤ ‖iteratedFDeriv ℝ (j + 1) ψ (p + t • y)‖ * ∏ _i : Fin (j + 1), ‖y‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ max C₀ 0 * ‖y‖ ^ (j + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            exact mul_le_mul_of_nonneg_right ((hC₀ _ (hseg t ht')).trans (le_max_left _ _))
              (by positivity)
    rw [norm_smul]
    calc ‖(1 - t) ^ j‖ * ‖iteratedFDeriv ℝ (j + 1) ψ (p + t • y) (fun _ => y)‖
        ≤ 1 * (max C₀ 0 * ‖y‖ ^ (j + 1)) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = max C₀ 0 * ‖y‖ ^ (j + 1) := one_mul _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [norm_smul]
  have hfac : ‖((j ! : ℝ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j))
  calc ‖((j ! : ℝ))⁻¹‖ * ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ j • iteratedFDeriv ℝ (j + 1) ψ (p + t • y) (fun _ => y)‖
      ≤ 1 * (max C₀ 0 * ‖y‖ ^ (j + 1) * |1 - 0|) :=
        mul_le_mul hfac hint (norm_nonneg _) zero_le_one
    _ = max C₀ 0 * ‖y‖ ^ (j + 1) := by simp

/-- **FOU019.** Parameter implicit function theorem with the derivative formula, uniform bounds
on derivatives through order `k`, and uniform Taylor-remainder bounds of every order `j < k`. -/
theorem parameter_implicit_function_and_differentiated_remainders
    {F : P × W → V} {p₀ : P} {w₀ : W} {k : ℕ} (hk : 1 ≤ k)
    (hF : ContDiffAt ℝ k F (p₀, w₀)) (hF0 : F (p₀, w₀) = 0)
    (hinv : (fderiv ℝ F (p₀, w₀) ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible) :
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ∃ Wn : Set W, IsOpen Wn ∧ w₀ ∈ Wn ∧ ∃ ψ : P → W,
      ψ p₀ = w₀ ∧
      (∀ p ∈ U, ψ p ∈ Wn ∧ F (p, ψ p) = 0) ∧
      (∀ p ∈ U, ∀ w ∈ Wn, F (p, w) = 0 → w = ψ p) ∧
      ContDiffOn ℝ k ψ U ∧
      (∀ p ∈ U, (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible ∧
        HasFDerivAt ψ (-(fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).inverse ∘L
          (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inl ℝ P W)) p) ∧
      (∀ K ⊆ U, IsCompact K → ∀ i ≤ k, ∃ C : ℝ, ∀ p ∈ K, ‖iteratedFDeriv ℝ i ψ p‖ ≤ C) ∧
      (∀ K ⊆ U, IsCompact K → Convex ℝ K → ∀ j < k, ∃ C : ℝ, ∀ p ∈ K, ∀ q ∈ K,
        ‖ψ q - ∑ i ∈ Finset.range (j + 1),
            (i ! : ℝ)⁻¹ • iteratedFDeriv ℝ i ψ p (fun _ => q - p)‖ ≤ C * ‖q - p‖ ^ (j + 1)) := by
  have pn : ((k : ℕ∞ω)) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  have hk1 : (1 : ℕ∞ω) ≤ k := by exact_mod_cast hk
  set u : P × W := (p₀, w₀)
  set ψ := hF.implicitFunction pn hinv
  -- Good set near `u`: `F` is `C^k`, `D_w F` is invertible, and the zero set is the graph.
  have hCk : ∀ᶠ v in 𝓝 u, ContDiffAt ℝ k F v := hF.eventually (by simp)
  have hInv : ∀ᶠ v in 𝓝 u,
      (fderiv ℝ F v ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible := by
    have hcont : ContinuousAt
        (fun v => fderiv ℝ F v ∘L ContinuousLinearMap.inr ℝ P W) u :=
      ((hF.fderiv_right (m := 0) (by simpa using hk1)).continuousAt).clm_comp continuousAt_const
    obtain ⟨e, he⟩ := hinv
    have hopen := (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := W) (F := V)).mem_nhds
      (mem_range_self e)
    rw [he] at hopen
    filter_upwards [hcont.preimage_mem_nhds hopen] with v hv
    obtain ⟨e', he'⟩ := hv
    exact ⟨e', he'⟩
  have hGraph := hF.eventually_apply_eq_iff_implicitFunction pn hinv
  obtain ⟨U₀, Wn, hU₀o, hp₀U₀, hWno, hw₀Wn, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hCk.and (hInv.and hGraph))
  have hψ0 : ψ p₀ = w₀ := hF.implicitFunction_apply_self pn hinv
  have hψk : ContDiffAt ℝ k ψ p₀ := hF.contDiffAt_implicitFunction pn hinv
  have hψW : ψ ⁻¹' Wn ∈ 𝓝 p₀ :=
    hψk.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hWno.mem_nhds hw₀Wn)
  set U := interior (U₀ ∩ ψ ⁻¹' Wn ∩ {p | ContDiffAt ℝ k ψ p})
  have hUo : IsOpen U := isOpen_interior
  have hp₀U : p₀ ∈ U := mem_interior_iff_mem_nhds.mpr
    (inter_mem (inter_mem (hU₀o.mem_nhds hp₀U₀) hψW) (hψk.eventually (by simp)))
  have hUsub : ∀ p ∈ U, p ∈ U₀ ∧ ψ p ∈ Wn ∧ ContDiffAt ℝ k ψ p := fun p hp =>
    let h := interior_subset hp; ⟨h.1.1, h.1.2, h.2⟩
  have hFu : F u = 0 := hF0
  have hzero : ∀ p ∈ U, F (p, ψ p) = 0 := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := hUsub p hp
    have := (hsub (mk_mem_prod h1 h2)).2.2
    rw [hFu] at this
    exact this.mpr rfl
  have hψCk : ContDiffOn ℝ k ψ U := fun p hp => (hUsub p hp).2.2.contDiffWithinAt
  refine ⟨U, hUo, hp₀U, Wn, hWno, hw₀Wn, ψ, hψ0, fun p hp => ⟨(hUsub p hp).2.1, hzero p hp⟩,
    ?_, hψCk, ?_, ?_, ?_⟩
  · intro p hp w hw hFw
    have := (hsub (mk_mem_prod (hUsub p hp).1 hw)).2.2
    rw [hFu] at this
    exact (this.mp hFw).symm
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hUsub p hp
    have hgood := hsub (mk_mem_prod h1 h2)
    refine ⟨hgood.2.1, ?_⟩
    have hk0 : (k : ℕ∞ω) ≠ 0 := pn
    exact hasFDerivAt_of_eventually_eq_zero (h3.differentiableAt (by simpa using Nat.one_le_iff_ne_zero.mp hk))
      (hgood.1.differentiableAt (by simpa using Nat.one_le_iff_ne_zero.mp hk))
      (eventually_of_mem (hUo.mem_nhds hp) hzero) hgood.2.1
  · intro K hKU hK i hi
    exact hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hψCk hUo (by exact_mod_cast hi)).mono hKU)
  · intro K hKU hK hKc j hj
    exact taylor_remainder_bound_of_contDiffOn hUo
      (hψCk.of_le (by exact_mod_cast hj)) hKU hK hKc

end DGPS.Analysis
