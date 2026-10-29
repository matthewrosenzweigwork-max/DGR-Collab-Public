import FullLabeledLSI.Examples.Paper.Sec9DeficitAttain

/-!
# Lemma 9.5, L5: one-site minimality at a minimizing family

Lane C of the Section 9 formalization.  For a minimizing family `G` and any admissible `q`, mixing `q` into
`G` with weight `t → 0⁺` and differentiating `Λ` along the line gives
`oneSite(q) ≥ ∑ θ_a oneSite(ρ_a)` for the common potential `A = commonPotential`
(`commonPotential_eq`: `A = α₀ + ∇Ψ(m̄)·e`).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.Def

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Cmp

/-! ### The gradient of `Ψ` -/

noncomputable def alpha0 (k : ℕ) (a c1 s1 : ℝ) : ℝ := 2 * a ^ 2 * omg k ^ 2 * (c1 ^ 2 + s1 ^ 2)

noncomputable def beta1 (k : ℕ) (a r c1 s1 c2 s2 : ℝ) : ℝ :=
  4 * a * (r - 2 * omg k ^ 2) * c1 + 2 * a ^ 2 * omg k ^ 2 * (2 * c1 * (1 - c2) - 2 * s1 * s2)

noncomputable def beta2 (k : ℕ) (a r c1 s1 c2 s2 : ℝ) : ℝ :=
  4 * a * (r - 2 * omg k ^ 2) * s1 + 2 * a ^ 2 * omg k ^ 2 * (-2 * c1 * s2 + 2 * s1 * (1 + c2))

noncomputable def beta3 (k : ℕ) (a c1 s1 : ℝ) : ℝ := 2 * a ^ 2 * omg k ^ 2 * (-c1 ^ 2 + s1 ^ 2)

noncomputable def beta4 (k : ℕ) (a c1 s1 : ℝ) : ℝ := 2 * a ^ 2 * omg k ^ 2 * (-2 * c1 * s1)

theorem Abasis_eq (k : ℕ) (a r c1 s1 c2 s2 : ℝ) (x : Torus 1) :
    Abasis k a r c1 s1 c2 s2 x =
      alpha0 k a c1 s1 + beta1 k a r c1 s1 c2 s2 * Reg.cosK k x + beta2 k a r c1 s1 c2 s2 * sinK k x +
        beta3 k a c1 s1 * Reg.cosK (2 * (k : ℤ)) x + beta4 k a c1 s1 * sinK (2 * (k : ℤ)) x := rfl

theorem hasDerivAt_PsiV (k : ℕ) (a r : ℝ) (m d : Fin 4 → ℝ) :
    HasDerivAt (fun t : ℝ => PsiV k a r (m + t • d))
      (beta1 k a r (m 0) (m 1) (m 2) (m 3) * d 0 + beta2 k a r (m 0) (m 1) (m 2) (m 3) * d 1 +
        beta3 k a (m 0) (m 1) * d 2 + beta4 k a (m 0) (m 1) * d 3) 0 := by
  have hc1 : HasDerivAt (fun t : ℝ => m 0 + t * d 0) (d 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add (m 0)
  have hs1 : HasDerivAt (fun t : ℝ => m 1 + t * d 1) (d 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 1)).const_add (m 1)
  have hc2 : HasDerivAt (fun t : ℝ => m 2 + t * d 2) (d 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 2)).const_add (m 2)
  have hs2 : HasDerivAt (fun t : ℝ => m 3 + t * d 3) (d 3) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 3)).const_add (m 3)
  have h1 := ((hc1.pow 2).add (hs1.pow 2)).const_mul (2 * a * (r - 2 * omg k ^ 2))
  have h2 := ((((hc1.pow 2).mul (hc2.const_sub 1)).sub (((hc1.mul hs1).mul hs2).const_mul 2)).add
    ((hs1.pow 2).mul (hc2.const_add 1))).const_mul (2 * a ^ 2 * omg k ^ 2)
  have h3 := h1.add h2
  refine (h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [PsiV, Psi, Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · simp only [beta1, beta2, beta3, beta4, Pi.pow_apply, Pi.mul_apply, zero_mul, add_zero]
    norm_num
    ring

/-! ### One-site functional in profile form -/

/-- `βsum(c, d) = ∇Ψ(c)·d`. -/
noncomputable def betaSum (k : ℕ) (a r : ℝ) (c d : Fin 4 → ℝ) : ℝ :=
  beta1 k a r (c 0) (c 1) (c 2) (c 3) * d 0 + beta2 k a r (c 0) (c 1) (c 2) (c 3) * d 1 +
    beta3 k a (c 0) (c 1) * d 2 + beta4 k a (c 0) (c 1) * d 3

theorem oneSite_profile (k : ℕ) (a r : ℝ) (c : Fin 4 → ℝ) {f : Torus 1 → ℝ} (hf : Adm f) :
    oneSite r (Abasis k a r (c 0) (c 1) (c 2) (c 3)) (fun x => f x ^ 2) =
      (Pt k r f).2 + alpha0 k a (c 0) (c 1) + betaSum k a r c (mvecF k f) := by
  obtain ⟨h0, h1, -⟩ := hf.dens
  have hi : Integrable (fun x => f x ^ 2) (haar 1) := integrable_of_integral_eq_one' h1
  have hJ := Jfun_sq r hf
  have hint : ∫ x, Abasis k a r (c 0) (c 1) (c 2) (c 3) x * f x ^ 2 ∂haar 1 =
      alpha0 k a (c 0) (c 1) + betaSum k a r c (mvecF k f) := by
    have e : ∀ x, Abasis k a r (c 0) (c 1) (c 2) (c 3) x * f x ^ 2 =
        f x ^ 2 * (alpha0 k a (c 0) (c 1) + beta1 k a r (c 0) (c 1) (c 2) (c 3) * Reg.cosK k x +
          beta2 k a r (c 0) (c 1) (c 2) (c 3) * sinK k x +
          beta3 k a (c 0) (c 1) * Reg.cosK (2 * (k : ℤ)) x +
          beta4 k a (c 0) (c 1) * sinK (2 * (k : ℤ)) x) := fun x => by
      rw [Abasis_eq]; ring
    simp_rw [e]
    rw [int_basis hi k, h1]
    simp only [betaSum, mvecF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  unfold oneSite
  have : (fisherInfo (densMeasure fun x => f x ^ 2) (haar 1)).toReal -
      2 * r * (klDiv (densMeasure fun x => f x ^ 2) (haar 1)).toReal = Jf r f := by
    rw [← hJ]; rfl
  rw [hint]
  simp only [Pt]
  linarith

/-! ### Mixing a new species into a family -/

theorem deficit_mix {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (G : Family 1) (hG : G.Admissible) {fq : Torus 1 → ℝ} (hfq : Adm fq) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    ∃ H : Family 1, H.Admissible ∧ deficit (attrW (harmKernel k a)) r H =
      Lam k a r ((∑ i, G.θ i • Pt k r (fOf G i)) +
        t • (Pt k r fq - ∑ i, G.θ i • Pt k r (fOf G i))) := by
  set n := G.q with hn
  let θ' : Fin (n + 1) → ℝ := Fin.cons t (fun i => (1 - t) * G.θ i)
  let f' : Fin (n + 1) → Torus 1 → ℝ := Fin.cons fq (fun i => fOf G i)
  have hθ'pos : ∀ j, 0 < θ' j := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [θ', Fin.cons_zero]; exact ht0
    · simp only [θ', Fin.cons_succ]; exact mul_pos (by linarith) (hG.1 i)
  have hs' : ∑ j, θ' j = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [θ', Fin.cons_zero, Fin.cons_succ]
    rw [← Finset.mul_sum, hG.2.1]
    ring
  have hf'adm : ∀ j, Adm (f' j) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [f', Fin.cons_zero]; exact hfq
    · simp only [f', Fin.cons_succ]; exact adm_fOf hG i
  refine ⟨mkFamily θ' f', mkFamily_adm hθ'pos hs' hf'adm, ?_⟩
  rw [deficit_mkFamily hk ha0 ha1 r hθ'pos hs' hf'adm]
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [θ', f', Fin.cons_zero, Fin.cons_succ]
  have : ∑ i : Fin n, ((1 - t) * G.θ i) • Pt k r (fOf G i) =
      (1 - t) • ∑ i, G.θ i • Pt k r (fOf G i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [this]
  module

/-! ### First-order condition -/

theorem betaSum_sub (k : ℕ) (a r : ℝ) (c d e : Fin 4 → ℝ) :
    betaSum k a r c (d - e) = betaSum k a r c d - betaSum k a r c e := by
  simp only [betaSum, Pi.sub_apply]; ring

theorem betaSum_sum (k : ℕ) (a r : ℝ) (c : Fin 4 → ℝ) {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (d : ι → Fin 4 → ℝ) :
    betaSum k a r c (∑ i ∈ s, w i • d i) = ∑ i ∈ s, w i * betaSum k a r c (d i) := by
  simp only [betaSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- If `φ(t) ≥ φ(0)` for `t ∈ (0,1)` and `φ` is differentiable at `0` then `φ'(0) ≥ 0`. -/
theorem deriv_nonneg_of_right {φ : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt φ d 0)
    (h : ∀ t, 0 < t → t < 1 → φ 0 ≤ φ t) : 0 ≤ d := by
  have hs := hd.tendsto_slope_zero_right
  refine ge_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have := h t ht.1 ht.2
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 ht.1.le) (by linarith)

theorem first_order {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (G : Family 1) (hG : G.Admissible)
    (hmin : ∀ H : Family 1, H.Admissible →
      deficit (attrW (harmKernel k a)) r G ≤ deficit (attrW (harmKernel k a)) r H)
    {fq : Torus 1 → ℝ} (hfq : Adm fq) :
    0 ≤ ((Pt k r fq).2 - (∑ i, G.θ i • Pt k r (fOf G i)).2) +
      betaSum k a r (∑ i, G.θ i • Pt k r (fOf G i)).1
        ((Pt k r fq).1 - (∑ i, G.θ i • Pt k r (fOf G i)).1) := by
  set p : PE := ∑ i, G.θ i • Pt k r (fOf G i) with hp
  set P : PE := Pt k r fq with hP
  set φ : ℝ → ℝ := fun t => Lam k a r (p + t • (P - p)) with hφ
  have hφeq : ∀ t, φ t = p.2 + t * (P.2 - p.2) + PsiV k a r (p.1 + t • (P.1 - p.1)) := by
    intro t
    simp only [hφ, Lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
  have hd : HasDerivAt φ ((P.2 - p.2) + betaSum k a r p.1 (P.1 - p.1)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p.2 + t * (P.2 - p.2)) (P.2 - p.2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (P.2 - p.2)).const_add p.2
    have h2 := hasDerivAt_PsiV k a r p.1 (P.1 - p.1)
    have h3 := h1.add h2
    refine (h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · exact hφeq t
    · simp only [betaSum, Pi.sub_apply]
  have hp0 : p = ∑ i, G.θ i • Pt k r (fOf G i) := rfl
  refine deriv_nonneg_of_right hd fun t ht0 ht1 => ?_
  obtain ⟨H, hH, hHdef⟩ := deficit_mix hk ha0 ha1 r G hG hfq ht0 ht1
  have h1 := hmin H hH
  rw [hHdef, deficit_eq_Lam hk ha0 ha1 r G hG] at h1
  simp only [hφ, zero_smul, add_zero]
  exact h1

/-! ### One-site minimality -/

theorem deficit_lower {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ aCos) :
    ∃ M : ℝ, ∀ G : Family 1, G.Admissible → -M ≤ deficit (attrW (harmKernel k a)) r G := by
  obtain ⟨M, hM⟩ := exists_Psi_bound k a r
  refine ⟨M, fun G hG => ?_⟩
  rw [deficit_eq_Lam hk ha0 ha1 r G hG]
  obtain ⟨hb1, hb2⟩ := comb_bounds (k := k) hr0 hr (fun i => (hG.1 i).le) hG.2.1
    (fun i => adm_fOf hG i)
  have := (abs_le.1 (hM _ hb2)).1
  unfold Lam
  linarith

theorem commonPotential_eq_Abasis {k : ℕ} (G : Family 1) (hG : G.Admissible) (a r : ℝ) :
    commonPotential (harmKernel k a) r G.bar =
      Abasis k a r ((∑ i, G.θ i • Pt k r (fOf G i)).1 0) ((∑ i, G.θ i • Pt k r (fOf G i)).1 1)
        ((∑ i, G.θ i • Pt k r (fOf G i)).1 2) ((∑ i, G.θ i • Pt k r (fOf G i)).1 3) := by
  funext x
  rw [commonPotential_eq (integrable_of_integral_eq_one' (bar_integral' G hG)) (bar_integral' G hG)
    k a r x]
  have hpj : ∀ j : Fin 4, (∑ i, G.θ i • Pt k r (fOf G i)).1 j =
      ∑ i, G.θ i * mvecF k (fOf G i) j := by
    intro j
    simp [Prod.fst_sum, Finset.sum_apply, Pt]
  have e1 : ∑ i, G.θ i * mvecF k (fOf G i) 0 = mcos k G.bar := by
    rw [mcos_bar hG]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mvecF, Matrix.cons_val_zero, sq_fOf hG]
  have e2 : ∑ i, G.θ i * mvecF k (fOf G i) 1 = msin k G.bar := by
    rw [msin_bar hG]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mvecF, Matrix.cons_val_one, Matrix.cons_val_zero, sq_fOf hG]
  have e3 : ∑ i, G.θ i * mvecF k (fOf G i) 2 = mcos (2 * (k : ℤ)) G.bar := by
    rw [mcos_bar hG]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mvecF, Matrix.cons_val, sq_fOf hG]
  have e4 : ∑ i, G.θ i * mvecF k (fOf G i) 3 = msin (2 * (k : ℤ)) G.bar := by
    rw [msin_bar hG]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mvecF, Matrix.cons_val, sq_fOf hG]
  rw [hpj 0, hpj 1, hpj 2, hpj 3, e1, e2, e3, e4]

theorem one_site_mean_le {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (G : Family 1) (hG : G.Admissible)
    (hmin : ∀ H : Family 1, H.Admissible →
      deficit (attrW (harmKernel k a)) r G ≤ deficit (attrW (harmKernel k a)) r H)
    {fq : Torus 1 → ℝ} (hfq : Adm fq) :
    ∑ i, G.θ i * oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) ≤
      oneSite r (commonPotential (harmKernel k a) r G.bar) (fun x => fq x ^ 2) := by
  set p : PE := ∑ i, G.θ i • Pt k r (fOf G i) with hp
  set c : Fin 4 → ℝ := p.1 with hc
  rw [commonPotential_eq_Abasis G hG a r]
  have hord : ∀ i, oneSite r (Abasis k a r (c 0) (c 1) (c 2) (c 3)) (G.ρ i) =
      (Pt k r (fOf G i)).2 + alpha0 k a (c 0) (c 1) + betaSum k a r c (mvecF k (fOf G i)) := by
    intro i
    rw [← sq_fOf hG i]
    exact oneSite_profile k a r c (adm_fOf hG i)
  have hmean : ∑ i, G.θ i * oneSite r (Abasis k a r (c 0) (c 1) (c 2) (c 3)) (G.ρ i) =
      p.2 + alpha0 k a (c 0) (c 1) + betaSum k a r c c := by
    simp_rw [hord]
    have h1 : ∑ i, G.θ i * ((Pt k r (fOf G i)).2 + alpha0 k a (c 0) (c 1) +
        betaSum k a r c (mvecF k (fOf G i))) =
        ∑ i, G.θ i * (Pt k r (fOf G i)).2 + alpha0 k a (c 0) (c 1) * ∑ i, G.θ i +
          ∑ i, G.θ i * betaSum k a r c (mvecF k (fOf G i)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hG.2.1]
    have h2 : p.2 = ∑ i, G.θ i * (Pt k r (fOf G i)).2 := by
      simp only [hp, Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
    have h3 : betaSum k a r c c = ∑ i, G.θ i * betaSum k a r c (mvecF k (fOf G i)) := by
      have : c = ∑ i, G.θ i • mvecF k (fOf G i) := by
        simp only [hc, hp, Prod.fst_sum, Prod.smul_fst, Pt]
      exact (congrArg (betaSum k a r c) this).trans (betaSum_sum k a r c Finset.univ G.θ _)
    rw [h2, h3]; ring
  rw [hmean, oneSite_profile k a r c hfq]
  have hfo := first_order hk ha0 ha1 r G hG hmin hfq
  rw [betaSum_sub] at hfo
  have hP1 : (Pt k r fq).1 = mvecF k fq := rfl
  rw [hP1] at hfo
  simp only [hp, hc] at hfo ⊢
  linarith

end SharpLSI.FL.Ex.Def
