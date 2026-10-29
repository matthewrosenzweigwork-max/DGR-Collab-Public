import SharpSymmetricLSI.Paper.FormLiminfS14b
import SharpSymmetricLSI.Paper.GaussForm8

/-!
# R33 cross term (S14c): the Gaussian side, `R → ∞`

`tendsto_alphaR`: `∫ F · H_R(z) dγ → ∫ F · (-L_∞φ) dγ` where `H_R = crossH` built from the
finite-rank kernel data `(s R, a R)` (`tendsto_gauss_row_term`, `neg_gen_eq`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem projJ_coe {J' : ℕ} (c : Cyl) (h : c.J ≤ J') (z : ℕ → ℝ) :
    projJ h (fun n : Fin J' => z n) = fun j : Fin c.J => z j := rfl

theorem extN_coe {J' : ℕ} (z : ℕ → ℝ) {q : ℕ} (hq : q < J') :
    extN (fun n : Fin J' => z n) q = z q := by
  simp [extN, hq]

/-- `crossH1 (z_{<J})` is in `L²(γ)`. -/
theorem memLp_crossH1 {C : ℕ → ℕ → ℝ} {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (lam : ℕ → ℝ) (c : Cyl) : MemLp (fun z : ℕ → ℝ => crossH1 lam c (fun j => z j)) 2 γ := by
  have := hγ.1
  obtain ⟨A, hA⟩ := crossH_growth lam c ∅ (fun _ _ => 0) (le_refl c.J)
  have hb : MemLp (fun z : ℕ → ℝ => A * (1 + ∑ j : Fin c.J, |z j|)) 2 γ := by
    have h1 : MemLp (fun z : ℕ → ℝ => ∑ j : Fin c.J, |z j|) 2 γ :=
      memLp_finsetSum (ε' := ℝ) _ fun j _ => (memLp_coord_gamma hγ j).abs
    exact ((memLp_const (1 : ℝ)).add h1).const_mul A
  have hm : Measurable fun z : ℕ → ℝ => crossH1 lam c (fun j => z j) :=
    (continuous_crossH1 lam c).measurable.comp (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  refine hb.of_le hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  have h : |crossH lam c ∅ (fun _ _ => 0) (le_refl c.J) (fun j : Fin c.J => z j)| ≤
      A * (1 + ∑ j : Fin c.J, |z j|) := hA _
  have e : crossH lam c ∅ (fun _ _ => 0) (le_refl c.J) (fun j : Fin c.J => z j) =
      crossH1 lam c (fun j => z j) := by
    unfold crossH crossH2
    rw [Finset.sum_eq_zero (fun i _ => by simp), add_zero]
    rfl
  rw [e] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact h.trans (le_abs_self _)

/-- **The Gaussian `R`-limit.** -/
theorem tendsto_alphaR (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i)) {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR)
    {s : ℕ → Finset ℕ} {a : ℕ → ℕ → ℕ → ℝ}
    (hK : ∀ R x y, KR R x y = ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)
    (c : Cyl) {J' : ℕ → ℕ} (hJ : ∀ R, c.J ≤ J' R) (hsJ : ∀ R, ∀ q ∈ s R, q < J' R) :
    Tendsto (fun R => ∫ z, F z * crossH lam c (s R) (a R) (hJ R) (fun n : Fin (J' R) => z n) ∂γ)
      atTop (𝓝 (∫ z, F z * (-(c.gen (lamShift lam) Y z)) ∂γ)) := by
  have := hγ.1
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  set ψ' : Fin c.J → (ℕ → ℝ) → ℝ := fun i z => lamShift lam i * cylD c i (fun j => z j)
  have hψK : ∀ i : Fin c.J, ∃ K, 0 ≤ K ∧ ∀ w, |cylD c i w| ≤ K := fun i =>
    exists_bound_of_compact (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  choose Kc hKc0 hKc using hψK
  set K : ℝ := ∑ i : Fin c.J, |lamShift lam i| * Kc i
  have hψb : ∀ i z, |ψ' i z| ≤ K := fun i z => by
    simp only [ψ', abs_mul]
    exact (mul_le_mul_of_nonneg_left (hKc i _) (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun i : Fin c.J => |lamShift lam i| * Kc i)
        (fun i _ => mul_nonneg (abs_nonneg _) (hKc0 i)) (Finset.mem_univ i))
  have hψm : ∀ i, Measurable (ψ' i) := fun i =>
    measurable_const.mul ((contDiff_cylD c i).continuous.measurable.comp
      (measurable_pi_iff.2 fun j => measurable_pi_apply _))
  have hrow := tendsto_gauss_row_term hyp hμ he hKR hK h21 hC hγ hY hF ψ' hψm hψb
  set G : ℕ → (ℕ → ℝ) → ℝ := fun R z => ∑ i : Fin c.J, ψ' i z * ∑ p ∈ s R, ∑ q ∈ s R,
    a R p q * z q * (if p = (i : ℕ) then 1 else 0)
  -- pointwise splitting
  have hpt : ∀ R z, crossH lam c (s R) (a R) (hJ R) (fun n : Fin (J' R) => z n) =
      crossH1 lam c (fun j => z j) + G R z := fun R z => by
    unfold crossH crossH2
    rw [projJ_coe]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ψ', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    rw [extN_coe z (hsJ R q hq)]
    split_ifs <;> ring
  have hH1 := memLp_crossH1 hγ lam c
  have hGL : ∀ R, MemLp (G R) 2 γ := fun R =>
    memLp_finsetSum (ε' := ℝ) _ fun i _ => by
      refine MemLp.of_le (g := fun z => K * ∑ p ∈ s R, ∑ q ∈ s R,
          a R p q * z q * (if p = (i : ℕ) then 1 else 0)) ?_
        ((hψm i).aestronglyMeasurable.mul ?_) (Eventually.of_forall fun z => ?_)
      · exact (memLp_finsetSum (ε' := ℝ) _ fun p _ => memLp_finsetSum (ε' := ℝ) _ fun q _ =>
          ((memLp_coord_gamma hγ q).const_mul (a R p q)).mul_const _).const_mul K
      · exact (Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
          ((measurable_pi_apply q).const_mul _).mul_const _).aestronglyMeasurable
      · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul (ψ' i z), abs_mul K]
        exact mul_le_mul_of_nonneg_right ((hψb i z).trans (le_abs_self K)) (abs_nonneg _)
  have hYL : MemLp (fun z => ∑ i : Fin c.J, ψ' i z * Y i z) 2 γ :=
    memLp_finsetSum (ε' := ℝ) _ fun i _ => by
      refine MemLp.of_le ((hY i).1.const_mul K) ((hψm i).aestronglyMeasurable.mul
        (hY i).1.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul (ψ' i z), abs_mul K]
      exact mul_le_mul_of_nonneg_right ((hψb i z).trans (le_abs_self K)) (abs_nonneg _)
  -- the integrals
  have hsplit : ∀ R, ∫ z, F z * crossH lam c (s R) (a R) (hJ R) (fun n : Fin (J' R) => z n) ∂γ =
      ∫ z, F z * crossH1 lam c (fun j => z j) ∂γ + ∫ z, F z * G R z ∂γ := fun R => by
    rw [← integral_add (f := fun z => F z * crossH1 lam c (fun j => z j)) (g := fun z => F z * G R z)
      (hF.integrable_mul hH1) (hF.integrable_mul (hGL R))]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only [hpt, mul_add])
  have hlim : ∫ z, F z * (-(c.gen (lamShift lam) Y z)) ∂γ =
      ∫ z, F z * crossH1 lam c (fun j => z j) ∂γ + ∫ z, F z * ∑ i : Fin c.J, ψ' i z * Y i z ∂γ := by
    rw [← integral_add (f := fun z => F z * crossH1 lam c (fun j => z j))
      (g := fun z => F z * ∑ i : Fin c.J, ψ' i z * Y i z) (hF.integrable_mul hH1)
      (hF.integrable_mul hYL)]
    exact integral_congr_ae (Eventually.of_forall fun z => by
      simp only [neg_gen_eq, mul_add, ψ'])
  simp_rw [hsplit]
  rw [hlim]
  exact tendsto_const_nhds.add hrow

end SharpLSI
