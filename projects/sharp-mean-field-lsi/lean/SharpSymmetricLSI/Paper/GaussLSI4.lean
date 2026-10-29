import SharpSymmetricLSI.Paper.GaussLSI3
import SharpSymmetricLSI.Paper.ForceApprox8
import SharpSymmetricLSI.Paper.Prop21Assembly1

/-!
# (8.13) (lane s42), step 2: the test perturbation and its gap

For finitely supported `v`, with `C¹` representatives `eC` of the reference basis, let
`v_fn = ∑_{i<n} v_i eC_{i+1}` and `u = (I+T)^{-1} v_fn ∈ L²_0(μ)`. The function
`h = v_fn - T u` is continuous, `μ(h) = 0`, `h = u` `μ`-a.e., hence `h + T h = v_fn` everywhere,
and `⟨h,(I+T)h⟩_{L²(μ)} = ⟨v, C v⟩` (`exists_test_pert`). With Proposition 2.1 (R02,
`tendsto_gap_pert`), `G(μ(1+th))/t² → ½⟨v,Cv⟩` (`tendsto_gap_test`).
-/

noncomputable section
open MeasureTheory Filter Topology Finset

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

theorem coeFn_finsetSum_ae {α : Type*} [MeasurableSpace α] {ν : Measure α} {ι : Type*}
    (s : Finset ι) (f : ι → Lp ℝ 2 ν) :
    (⇑(∑ i ∈ s, f i) : α → ℝ) =ᵐ[ν] fun x => ∑ i ∈ s, (f i : α → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

/-- **The test perturbation** `h = v_fn - T u`. -/
theorem exists_test_pert (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) {eC : ℕ → Torus d → ℝ}
    (heC : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[(μ : Measure (Torus d))] e j)
    (n : ℕ) (v : ℕ → ℝ) :
    ∃ h : Torus d → ℝ, Continuous h ∧ ∫ x, h x ∂(μ : Measure (Torus d)) = 0 ∧
      (∀ x, h x + Top W (μ : Measure (Torus d)) h x = ∑ i ∈ range n, v i * eC (i + 1) x) ∧
      secondVar W (μ : Measure (Torus d)) h = ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨u, hu0, hu, hq⟩ := inner_solve_eq_quad hd hyp hr hμ he hC n v
  set EL : ℕ → Lp ℝ 2 μm := fun n => (he.memH1 n).2.1.toLp (e n)
  set vL := ∑ i ∈ range n, v i • EL (i + 1)
  set vfn : Torus d → ℝ := fun x => ∑ i ∈ range n, v i * eC (i + 1) x with hvfn
  have hvc : Continuous vfn := continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_of_contDiff_lift' (heC (i + 1)).1)
  -- `vL = v_fn` a.e.
  have hEL : ∀ᵐ x ∂μm, ∀ j, (EL j : Torus d → ℝ) x = eC j x := by
    rw [ae_all_iff]; intro j
    filter_upwards [MemLp.coeFn_toLp (he.memH1 j).2.1, (heC j).2] with x h1 h2
    rw [h1, h2]
  have hvL : (vL : Torus d → ℝ) =ᵐ[μm] vfn := by
    filter_upwards [coeFn_finsetSum_ae (range n) (fun i => v i • EL (i + 1)),
      ae_all_iff.2 fun i => Lp.coeFn_smul (v i) (EL (i + 1)), hEL] with x h1 h2 h3
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 i, Pi.smul_apply, smul_eq_mul, h3]
  -- `u` as a function
  have hu0' : ∫ x, u x ∂μm = 0 := by rw [← inner_oneL]; exact hu0
  have huL : MemL20 μm u := ⟨Lp.memLp u, hu0'⟩
  obtain ⟨CT, hCT⟩ := Top_W1inf hyp μm
  obtain ⟨-, hTL⟩ := hCT _ huL
  set h : Torus d → ℝ := fun x => vfn x - Top W μm u x with hh
  have hc : Continuous h := hvc.sub hTL.continuous
  -- `h = u` a.e.
  have hhu : h =ᵐ[μm] u := by
    filter_upwards [Lp.coeFn_add u (T2op hyp μ u), T2op_ae hyp μ u, hvL] with x h1 h2 h3
    have e1 : ((u + T2op hyp μ u : Lp ℝ 2 μm) : Torus d → ℝ) x = (vL : Torus d → ℝ) x := by
      rw [hu]
    have hx : u x + ∫ y, centeredKernel W μm x y * u y ∂μm = vfn x := by
      rw [← h3, ← e1, h1, Pi.add_apply, h2]
    show vfn x - Top W μm u x = u x
    rw [Top_eq_integral hyp μm huL x]
    linarith
  have hT : ∀ x, Top W μm h x = Top W μm u x := fun x => by
    unfold Top
    have e : ∀ x', ∫ y, W x' y * h y ∂μm = ∫ y, W x' y * u y ∂μm := fun x' =>
      integral_congr_ae (by filter_upwards [hhu] with y hy; rw [hy])
    simp only [e]
  have hsum : ∀ x, h x + Top W μm h x = vfn x := fun x => by rw [hT]; simp [hh]
  have hh0 : ∫ x, h x ∂μm = 0 := by rw [integral_congr_ae hhu]; exact hu0'
  refine ⟨h, hc, hh0, hsum, ?_⟩
  unfold secondVar
  simp_rw [hsum]
  rw [← hq, L2_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hhu, hvL] with x h1 h2
  rw [h1, h2, mul_comm]

/-- **The gap along the test perturbation**: `G(μ(1+th))/t² → ½⟨v,Cv⟩`. -/
theorem tendsto_gap_test (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {h : Torus d → ℝ} (hc : Continuous h)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) {Q : ℝ}
    (hQ : secondVar W (μ : Measure (Torus d)) h = Q) :
    Tendsto (fun t : ℝ => (gap V W (densMeasure fun x =>
        elDens V W (μ : Measure (Torus d)) x * (1 + t * h x))).toReal / t ^ 2)
      (𝓝[≠] 0) (𝓝 (Q / 2)) := by
  rw [← hQ]
  exact tendsto_gap_pert hyp hμ hc.measurable (exists_bound_of_continuous hc) hh0

end SharpLSI
