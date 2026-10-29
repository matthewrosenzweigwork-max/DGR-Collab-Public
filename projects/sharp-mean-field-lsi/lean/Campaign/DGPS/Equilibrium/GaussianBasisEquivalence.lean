import DGPS.Equilibrium.GaussianRate
import DGPS.Lipschitz.WeightedSpectrum

/-!
# Gaussian quotient: spectral coordinate equivalence (FOU020)

For the bounded positive reference `μ = P = w m` with coercive density Hessian `H` and `C = H⁻¹`,
the basis-free Gaussian rate `DGPS.gaussianRate` equals the coordinate infimum
`inf ⟨a, Λ a⟩ / ⟨a, C a⟩` over nonzero centered `a ∈ ℓ²` in the form domain of `Λ^{1/2}`, in any real
orthonormal generator eigenbasis (LIP009 `weighted_eigenbasis_and_growth`).  `C` is never assumed
to commute with the generator.

The proof is a bijection between nonzero centered weak-`H¹(μ)` tests and nonzero centered
form-domain sequences: the numerators agree through the energy identity
`E_μ(f) = ∑ λ_j ⟨e_j, f⟩²`, and the converse direction builds the weak gradient of
`∑ a_j e_j` as a limit in the Hilbert space `Kspace` of weak-gradient pairs.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace DGPS.Analysis

open DGPS DGPS.Analysis.CompactResolvent

variable {d : ℕ}

section Bridge

variable (P : BoundedPositiveReference d) (μ : ProbabilityMeasure (Torus d))

theorem fou020_memLp_iff (hμ : (μ : Measure (Torus d)) = P.measure) {E : Type*}
    [NormedAddCommGroup E] {f : Torus d → E} {p : ℝ≥0∞} :
    MemLp f p (μ : Measure (Torus d)) ↔ MemLp f p (haar d) := by
  rw [hμ]; exact P.memLp_measure_iff

theorem fou020_isWeak_iff (hμ : (μ : Measure (Torus d)) = P.measure) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} :
    IsMeasureWeakGradient μ u g ↔ IsWeakGradient u g := by
  constructor
  · intro h
    exact ⟨(fou020_memLp_iff P μ hμ).1 h.memLp, (fou020_memLp_iff P μ hμ).1 h.memLp_grad, h.ibp⟩
  · intro h
    have h1 := (fou020_memLp_iff P μ hμ).2 h.memLp
    have h2 := (fou020_memLp_iff P μ hμ).2 h.memLp_grad
    exact ⟨h1, h2, h.memLp.integrable one_le_two, h.memLp_grad.integrable one_le_two, h.ibp⟩

theorem fou020_dirichlet_eq (hμ : (μ : Measure (Torus d)) = P.measure) (f : WeakH1Test μ) :
    dirichletEnergy μ f = ENNReal.ofReal (weightedForm P.density f.grad f.grad) := by
  have hg : IsWeakGradient f.fn f.grad := (fou020_isWeak_iff P μ hμ).1 f.isWeak
  have hint : Integrable (fun x => ‖f.grad x‖ ^ 2 * P.density x) (haar d) := by
    have := integrable_inner_mul_weight (w := P.density) P.measurable_density
      (c := P.lower) (C := P.upper) (by filter_upwards [P.lower_le, P.le_upper] with x h1 h2
                                        exact ⟨h1, h2⟩) P.lower_pos hg.memLp_grad hg.memLp_grad
    simpa [real_inner_self_eq_norm_sq] using this
  rw [weightedForm_self, ofReal_integral_eq_lintegral_ofReal hint]
  · unfold dirichletEnergy
    rw [hμ, BoundedPositiveReference.measure]
    rw [lintegral_withDensity_eq_lintegral_mul₀ P.measurable_ofReal_density.aemeasurable]
    · refine lintegral_congr fun x => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm, ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
    · exact hg.memLp_grad.aestronglyMeasurable.enorm.pow_const 2
  · filter_upwards [P.ae_pos] with x hx
    positivity

end Bridge


section Core

variable {w : Torus d → ℝ} {c C : ℝ}

theorem fou020_inner_sum (e : HilbertBasis ℕ ℝ (Hw d w)) (a : ℕ → ℝ) (S : Finset ℕ) (i : ℕ) :
    ⟪e i, ∑ j ∈ S, a j • (e j : Hw d w)⟫_ℝ = if i ∈ S then a i else 0 := by
  classical
  rw [inner_sum]
  have h1 : ∀ j ∈ S, ⟪e i, a j • (e j : Hw d w)⟫_ℝ = if j = i then a j else 0 := by
    intro j _
    rw [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal i j]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' S i a]

theorem fou020_core (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (G : ℕ → Torus d → Tangent d)
    (hgrad : ∀ j, IsWeakGradient ((e j : Hw d w) : Torus d → ℝ) (G j))
    (henergy : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm w Y Y))
    (a : lp (fun _ : ℕ => ℝ) 2) (hsum : Summable fun j => lam j * (a j) ^ 2) :
    ∃ Y : Torus d → Tangent d, IsWeakGradient ((e.repr.symm a : Hw d w) : Torus d → ℝ) Y ∧
      weightedForm w Y Y = ∑' j, lam j * (a j) ^ 2 := by
  classical
  have hGm : ∀ j, MemLp (G j) 2 (wMeasure d w) := fun j =>
    (memLp_wMeasure_iff hc hwb).2 (hgrad j).memLp_grad
  let k : ℕ → Kspace hc hwb := fun j =>
    ⟨WithLp.toLp 2 ((e j : Hw d w), (hGm j).toLp (G j)), by
      refine (hgrad j).congr_ae Filter.EventuallyEq.rfl ?_
      exact (ae_eq_haar hc hwb (hGm j).coeFn_toLp).symm⟩
  have hk : ∀ j, formJ hc hwb (k j) = e j := fun j => rfl
  let x : ℕ → Kspace hc hwb := fun j => a j • k j
  have hJ : ∀ S : Finset ℕ, formJ hc hwb (∑ j ∈ S, x j) = ∑ j ∈ S, a j • (e j : Hw d w) := by
    intro S
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, map_smul, hk]
  -- norm of finite sums
  have hnorm : ∀ S : Finset ℕ, ‖∑ j ∈ S, x j‖ ^ 2 = ∑ j ∈ S, (a j ^ 2 + lam j * a j ^ 2) := by
    intro S
    set q : Kspace hc hwb := ∑ j ∈ S, x j with hq
    have hin : ∀ i, ⟪e i, formJ hc hwb q⟫_ℝ = if i ∈ S then a i else 0 := by
      intro i; rw [hq, hJ]; exact fou020_inner_sum e a S i
    rw [norm_sq_Kspace hw hc hwb q]
    have h1 : ∫ u, (formJ hc hwb q : Torus d → ℝ) u ^ 2 * w u ∂haar d = ∑ j ∈ S, a j ^ 2 := by
      rw [← norm_sq_Hw hw hc hwb, ← real_inner_self_eq_norm_sq]
      have hqJ : formJ hc hwb q = ∑ j ∈ S, a j • (e j : Hw d w) := hJ S
      nth_rewrite 1 [hqJ]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [inner_smul_left, hin j]
      simp [hj, sq]
    have h2 : weightedForm w (formGrad hc hwb q) (formGrad hc hwb q) =
        ∑ j ∈ S, lam j * a j ^ 2 := by
      have hen := henergy (formJ hc hwb q) (formGrad hc hwb q) (isWeakGradient_formJ hc hwb q)
      have hfin : HasSum (fun j => lam j * ⟪e j, formJ hc hwb q⟫_ℝ ^ 2)
          (∑ j ∈ S, lam j * a j ^ 2) := by
        have : HasSum (fun j => lam j * ⟪e j, formJ hc hwb q⟫_ℝ ^ 2)
            (∑ j ∈ S, lam j * ⟪e j, formJ hc hwb q⟫_ℝ ^ 2) :=
          hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hin j, hj])
        convert this using 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hin j]
        simp [hj]
      exact hen.unique hfin
    rw [h1, h2, ← Finset.sum_add_distrib]
  have hsq : Summable fun j => a j ^ 2 := by
    have := (memℓp_gen_iff (p := 2) (by norm_num)).1 a.2
    simpa using this
  have hs : Summable fun j => a j ^ 2 + lam j * a j ^ 2 := hsq.add hsum
  set p : ℕ → Kspace hc hwb := fun N => ∑ j ∈ Finset.range N, x j with hp
  set S : ℕ → ℝ := fun N => ∑ j ∈ Finset.range N, (a j ^ 2 + lam j * a j ^ 2) with hS
  have hdist : ∀ m n, m ≤ n → dist (p n) (p m) ^ 2 = S n - S m := by
    intro m n hmn
    rw [dist_eq_norm, hp, hS]
    simp only
    rw [← Finset.sum_Ico_eq_sub _ hmn, ← Finset.sum_Ico_eq_sub _ hmn, hnorm]
  have hScau : CauchySeq S := hs.hasSum.tendsto_sum_nat.cauchySeq
  have := completeSpace_Kspace hw hc hwb
  have hpcau : CauchySeq p := by
    rw [Metric.cauchySeq_iff] at hScau ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hScau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have key : ∀ m n, N ≤ m → m ≤ n → dist (p n) (p m) < ε := by
      intro m n hm hmn
      have h1 := hN n (hm.trans hmn) m hm
      rw [Real.dist_eq] at h1
      have h2 := hdist m n hmn
      have h3 : dist (p n) (p m) ^ 2 < ε ^ 2 := by
        rw [h2]; exact (le_abs_self _).trans_lt h1
      exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
    rcases le_total m n with h | h
    · rw [dist_comm]; exact key m n hm h
    · exact key n m hn h
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hpcau
  have hv : formJ hc hwb q = e.repr.symm a := by
    have h1 : Tendsto (fun N => formJ hc hwb (p N)) atTop (𝓝 (formJ hc hwb q)) :=
      ((formJ hc hwb).continuous.tendsto q).comp hq
    have h2 : Tendsto (fun N => formJ hc hwb (p N)) atTop (𝓝 (e.repr.symm a)) := by
      have := (HilbertBasis.hasSum_repr_symm e a).tendsto_sum_nat
      refine this.congr fun N => ?_
      rw [hp]; simp only
      rw [hJ]
    exact tendsto_nhds_unique h1 h2
  refine ⟨formGrad hc hwb q, ?_, ?_⟩
  · have := isWeakGradient_formJ hc hwb q
    rwa [hv] at this
  · have hweak : IsWeakGradient ((e.repr.symm a : Hw d w) : Torus d → ℝ) (formGrad hc hwb q) := by
      have := isWeakGradient_formJ hc hwb q
      rwa [hv] at this
    have hen := henergy _ _ hweak
    have hco : ∀ j, ⟪e j, e.repr.symm a⟫_ℝ = a j := by
      intro j
      rw [← HilbertBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    simp_rw [hco] at hen
    exact hen.tsum_eq.symm

end Core

section Main

variable (P : BoundedPositiveReference d)

/-- The probability measure `P = w m` of a bounded positive reference. -/
noncomputable def fou020_prob : ProbabilityMeasure (Torus d) :=
  ⟨P.measure, P.isProbabilityMeasure⟩

theorem fou020_hwb : ∀ᵐ x ∂haar d, P.lower ≤ P.density x ∧ P.density x ≤ P.upper := by
  filter_upwards [P.lower_le, P.le_upper] with x h1 h2
  exact ⟨h1, h2⟩

theorem fou020_inner_e0 {w : Torus d → ℝ} (e : HilbertBasis ℕ ℝ (Hw d w))
    (he0 : ((e 0 : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] fun _ => 1) (f : Hw d w) :
    ⟪e 0, f⟫_ℝ = ∫ x, f x ∂(wMeasure d w) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [he0] with x hx
  rw [hx]
  simp

theorem fou020_coord (e : HilbertBasis ℕ ℝ (Hw d P.density)) (a : lp (fun _ : ℕ => ℝ) 2) (j : ℕ) :
    ⟪e j, e.repr.symm a⟫_ℝ = a j := by
  rw [← HilbertBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Reinterpret an element of the weighted `L²` space as an element of `L²(P)`
(the two are definitionally the same space). -/
def fou020_toL (u : Hw d P.density) : Lp ℝ 2 ((fou020_prob P : ProbabilityMeasure (Torus d)) : Measure (Torus d)) := u

theorem fou020_mem_centered (e : HilbertBasis ℕ ℝ (Hw d P.density))
    (he0 : ((e 0 : Hw d P.density) : Torus d → ℝ) =ᵐ[wMeasure d P.density] fun _ => 1)
    (a : lp (fun _ : ℕ => ℝ) 2) (ha0 : a 0 = 0) :
    fou020_toL P (e.repr.symm a) ∈ centeredL2 (fou020_prob P) := by
  rw [mem_centeredL2]
  have h := fou020_inner_e0 e he0 (e.repr.symm a)
  rw [fou020_coord P e a 0, ha0] at h
  exact h.symm

/-- The form domain of `Λ^{1/2}` in the centered sequence space: weighted-square-summable
sequences (in `ℓ²`) with vanishing zeroth coordinate (centeredness). -/
def fou020_FormDomain (lam : ℕ → ℝ) (a : lp (fun _ : ℕ => ℝ) 2) : Prop :=
  Summable (fun j => lam j * (a j) ^ 2) ∧ a 0 = 0

/-- The covariance form `⟨a, C a⟩` of a centered coordinate sequence: the bounded inverse Hessian
`C` applied to the vector with coordinates `a` in the eigenbasis `e`. -/
noncomputable def fou020_covForm (A : InteractionData d)
    (hH : IsCoerciveDensityHessian A (fou020_prob P))
    (e : HilbertBasis ℕ ℝ (Hw d P.density))
    (he0 : ((e 0 : Hw d P.density) : Torus d → ℝ) =ᵐ[wMeasure d P.density] fun _ => 1)
    (a : lp (fun _ : ℕ => ℝ) 2) (ha0 : a 0 = 0) : ℝ :=
  inner ℝ (⟨fou020_toL P (e.repr.symm a), fou020_mem_centered P e he0 a ha0⟩ :
      centeredL2 (fou020_prob P))
    (densityCovariance A (fou020_prob P) hH
      (⟨fou020_toL P (e.repr.symm a), fou020_mem_centered P e he0 a ha0⟩ :
        centeredL2 (fou020_prob P)))

/-- The spectral coordinate quotient `⟨a, Λ a⟩ / ⟨a, C a⟩`. -/
noncomputable def fou020_coordQuotient (A : InteractionData d)
    (hH : IsCoerciveDensityHessian A (fou020_prob P))
    (e : HilbertBasis ℕ ℝ (Hw d P.density)) (lam : ℕ → ℝ)
    (he0 : ((e 0 : Hw d P.density) : Torus d → ℝ) =ᵐ[wMeasure d P.density] fun _ => 1)
    (a : lp (fun _ : ℕ => ℝ) 2) (ha0 : a 0 = 0) : ℝ≥0∞ :=
  ENNReal.ofReal (∑' j, lam j * (a j) ^ 2) / ENNReal.ofReal (fou020_covForm P A hH e he0 a ha0)

end Main

section Assembly

variable (P : BoundedPositiveReference d) (A : InteractionData d)
  (hH : IsCoerciveDensityHessian A (fou020_prob P))
  (e : HilbertBasis ℕ ℝ (Hw d P.density)) (lam : ℕ → ℝ)
  (he0 : ((e 0 : Hw d P.density) : Torus d → ℝ) =ᵐ[wMeasure d P.density] fun _ => 1)
  (henergy : ∀ (f : Hw d P.density) (Y : Torus d → Tangent d),
    IsWeakGradient (f : Torus d → ℝ) Y →
      HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm P.density Y Y))

include he0 henergy in
theorem fou020_forward (f : WeakH1Test (fou020_prob P)) (hf : IsNonzeroCentered (fou020_prob P) f) :
    ∃ (a : lp (fun _ : ℕ => ℝ) 2) (h : fou020_FormDomain lam a ∧ a ≠ 0),
      fou020_coordQuotient P A hH e lam he0 a h.1.2 =
        gaussianQuotient A (fou020_prob P) hH f hf.1 := by
  have hg : IsWeakGradient f.fn f.grad := (fou020_isWeak_iff P (fou020_prob P) rfl).1 f.isWeak
  let u : Hw d P.density := f.isWeak.memLp.toLp f.fn
  have hu : (u : Torus d → ℝ) =ᵐ[haar d] f.fn :=
    (haar_ac_wMeasure P.lower_pos (fou020_hwb P)).ae_le f.isWeak.memLp.coeFn_toLp
  have hweak : IsWeakGradient (u : Torus d → ℝ) f.grad :=
    hg.congr_ae hu.symm Filter.EventuallyEq.rfl
  have hen := henergy u f.grad hweak
  obtain ⟨a, ha⟩ : ∃ a : lp (fun _ : ℕ => ℝ) 2, a = e.repr u := ⟨_, rfl⟩
  have hco : ∀ j, a j = ⟪e j, u⟫_ℝ := fun j => by
    rw [ha]; exact HilbertBasis.repr_apply_apply e u j
  have hsymm : e.repr.symm a = u := by rw [ha]; exact e.repr.symm_apply_apply u
  have hen' : HasSum (fun j => lam j * (a j) ^ 2) (weightedForm P.density f.grad f.grad) := by
    simpa only [hco] using hen
  have ha0 : a 0 = 0 := by
    rw [hco, fou020_inner_e0 e he0 u, ← hf.1]
    exact integral_congr_ae f.isWeak.memLp.coeFn_toLp
  have hne : a ≠ 0 := by
    intro h0
    apply hf.2
    have h1 : e.repr u = 0 := ha ▸ h0
    have hu0 : u = 0 := (LinearIsometryEquiv.map_eq_zero_iff e.repr).1 h1
    have := Lp.eq_zero_iff_ae_eq_zero.1 hu0
    exact f.isWeak.memLp.coeFn_toLp.symm.trans this
  refine ⟨a, ⟨⟨hen'.summable, ha0⟩, hne⟩, ?_⟩
  have hv : (⟨fou020_toL P (e.repr.symm a), fou020_mem_centered P e he0 a ha0⟩ :
      centeredL2 (fou020_prob P)) = f.toCentered (fou020_prob P) hf.1 := by
    apply Subtype.ext
    exact congrArg (fou020_toL P) hsymm
  have hden : fou020_covForm P A hH e he0 a ha0 = gaussianDenominator A (fou020_prob P) hH f hf.1 := by
    unfold fou020_covForm gaussianDenominator
    rw [hv]
  unfold fou020_coordQuotient gaussianQuotient
  rw [hden, fou020_dirichlet_eq P (fou020_prob P) rfl f, hen'.tsum_eq]

include he0 henergy in
theorem fou020_backward (G : ℕ → Torus d → Tangent d)
    (hgrad : ∀ j, IsWeakGradient ((e j : Hw d P.density) : Torus d → ℝ) (G j))
    (a : lp (fun _ : ℕ => ℝ) 2) (h : fou020_FormDomain lam a ∧ a ≠ 0) :
    ∃ (f : WeakH1Test (fou020_prob P)) (hf : IsNonzeroCentered (fou020_prob P) f),
      gaussianQuotient A (fou020_prob P) hH f hf.1 =
        fou020_coordQuotient P A hH e lam he0 a h.1.2 := by
  obtain ⟨Y, hY, hE⟩ := fou020_core P.measurable_density P.lower_pos (fou020_hwb P) e lam G hgrad
    henergy a h.1.1
  let f : WeakH1Test (fou020_prob P) :=
    ⟨((e.repr.symm a : Hw d P.density) : Torus d → ℝ), Y,
      (fou020_isWeak_iff P (fou020_prob P) rfl).2 hY⟩
  have hc : ∫ x, f.fn x ∂((fou020_prob P : ProbabilityMeasure (Torus d)) : Measure (Torus d)) = 0 :=
    fou020_mem_centered P e he0 a h.1.2
  have hnz : ¬ f.fn =ᵐ[((fou020_prob P : ProbabilityMeasure (Torus d)) : Measure (Torus d))] 0 := by
    intro h0
    apply h.2
    have h1 : e.repr.symm a = 0 := Lp.eq_zero_iff_ae_eq_zero.2 h0
    have h2 : a = e.repr (e.repr.symm a) := (e.repr.apply_symm_apply a).symm
    rw [h2, h1, map_zero]
  refine ⟨f, ⟨hc, hnz⟩, ?_⟩
  have hv : (⟨fou020_toL P (e.repr.symm a), fou020_mem_centered P e he0 a h.1.2⟩ :
      centeredL2 (fou020_prob P)) = f.toCentered (fou020_prob P) hc := by
    apply Subtype.ext
    exact (Lp.toLp_coeFn (fou020_toL P (e.repr.symm a)) (Lp.memLp _)).symm
  have hden : fou020_covForm P A hH e he0 a h.1.2 = gaussianDenominator A (fou020_prob P) hH f hc := by
    unfold fou020_covForm gaussianDenominator
    rw [hv]
  unfold fou020_coordQuotient gaussianQuotient
  rw [hden, fou020_dirichlet_eq P (fou020_prob P) rfl f, hE]

end Assembly

/-- **FOU020.** Spectral coordinate equivalence of the Gaussian quotient.  For the bounded positive
reference `μ = P = w m` with coercive density Hessian `H` and `C = H⁻¹` (`densityCovariance`), and
any real orthonormal generator eigenbasis `e` of `L²(μ)` with `e₀ = 1`, eigenvalues `lam` and weak
gradients `G` satisfying the energy identity `E_μ(f) = ∑ λ_j ⟨e_j, f⟩²` on the weak `H¹(μ)`, the
basis-free Gaussian rate `inf E_μ(g)/⟨g, C g⟩` over nonzero centered `H¹` functions equals the
coordinate infimum `inf ⟨a, Λ a⟩ / ⟨a, C a⟩` over nonzero centered sequences `a ∈ ℓ²` in the form
domain of `Λ^{1/2}` (`∑ λ_j a_j² < ∞`).  No commutation of `C` with `Λ` is used. -/
theorem gaussian_quotient_spectral_coordinate_equivalence
    (P : BoundedPositiveReference d) (A : InteractionData d)
    (hH : IsCoerciveDensityHessian A (fou020_prob P))
    (e : HilbertBasis ℕ ℝ (Hw d P.density)) (lam : ℕ → ℝ) (G : ℕ → Torus d → Tangent d)
    (he0 : ((e 0 : Hw d P.density) : Torus d → ℝ) =ᵐ[wMeasure d P.density] fun _ => 1)
    (hgrad : ∀ j, IsWeakGradient ((e j : Hw d P.density) : Torus d → ℝ) (G j))
    (henergy : ∀ (f : Hw d P.density) (Y : Torus d → Tangent d),
      IsWeakGradient (f : Torus d → ℝ) Y →
        HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm P.density Y Y)) :
    gaussianRate A (fou020_prob P) hH =
      ⨅ a : {a : lp (fun _ : ℕ => ℝ) 2 // fou020_FormDomain lam a ∧ a ≠ 0},
        fou020_coordQuotient P A hH e lam he0 a.1 a.2.1.2 := by
  apply le_antisymm
  · refine le_iInf fun a => ?_
    obtain ⟨f, hf, hq⟩ := fou020_backward P A hH e lam he0 henergy G hgrad a.1 a.2
    rw [← hq]
    exact gaussianRate_le_quotient A (fou020_prob P) hH f hf
  · unfold gaussianRate
    refine le_iInf fun f => ?_
    obtain ⟨a, h, hq⟩ := fou020_forward P A hH e lam he0 henergy f.1 f.2
    rw [← hq]
    exact iInf_le (fun a : {a : lp (fun _ : ℕ => ℝ) 2 // fou020_FormDomain lam a ∧ a ≠ 0} =>
      fou020_coordQuotient P A hH e lam he0 a.1 a.2.1.2) ⟨a, h⟩

end DGPS.Analysis
