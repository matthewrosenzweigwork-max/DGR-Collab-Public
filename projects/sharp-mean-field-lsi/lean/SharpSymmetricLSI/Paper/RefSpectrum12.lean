import SharpSymmetricLSI.Paper.RefSpectrum11
import SharpSymmetricLSI.Paper.AscoliSeq
import SharpSymmetricLSI.Paper.TorusLipschitz
import SharpSymmetricLSI.Infra.SobolevTorus

/-!
# R23 (6.1), part 12: `C¹` limits of smooth functions with uniform `C^{1,β}` bounds

A sequence of `C¹` torus functions with `|uₙ| ≤ B`, `|∂ₖuₙ| ≤ M` and
`|∂ₖuₙ(x) - ∂ₖuₙ(y)| ≤ M dist(x,y)^β` has a subsequence converging uniformly together with its
first derivatives (Arzelà–Ascoli twice); the limit `E` is `C¹` with `∂ₖE = lim ∂ₖuₙ`
(`c1_limit`).
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

/-- Arzelà–Ascoli for `ℝ^κ`-valued functions with a uniform Hölder modulus. -/
theorem exists_subseq_unif_holder {X : Type*} [MetricSpace X] [CompactSpace X] {κ : Type*}
    [Fintype κ] (u : ℕ → X → κ → ℝ) {C M β : ℝ} (hβ : 0 < β) (hM : 0 ≤ M)
    (hb : ∀ n x k, |u n x k| ≤ C) (hH : ∀ n x y k, |u n x k - u n y k| ≤ M * dist x y ^ β) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X → κ → ℝ, Continuous v ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x k, |u (φ n) x k - v x k| ≤ ε := by
  have hcont : ∀ n, Continuous (u n) := by
    intro n
    refine continuous_pi fun k => Metric.continuous_iff.mpr fun x ε hε => ?_
    refine ⟨(ε / (M + 1)) ^ (1 / β), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq]
    calc |u n y k - u n x k| ≤ M * dist y x ^ β := hH n y x k
      _ ≤ M * ((ε / (M + 1)) ^ (1 / β)) ^ β := by
          gcongr
      _ = M * (ε / (M + 1)) := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one]
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  set f : ℕ → X →ᵇ (κ → ℝ) := fun n => mkOfCompact ⟨u n, hcont n⟩
  set A : Set (X →ᵇ (κ → ℝ)) := Set.range f
  set K : Set (κ → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-C) C
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hin : ∀ (g : X →ᵇ (κ → ℝ)) (x : X), g ∈ A → g x ∈ K := by
    rintro g x ⟨n, rfl⟩ k -
    exact abs_le.mp (hb n x k)
  have heq : Equicontinuous ((↑) : A → X → κ → ℝ) := by
    refine (Metric.uniformEquicontinuous_iff.mpr fun ε hε => ?_).equicontinuous
    refine ⟨(ε / 2 / (M + 1)) ^ (1 / β), by positivity, fun x y hxy g => ?_⟩
    obtain ⟨n, hn⟩ := g.2
    rw [← hn]
    simp only [f, mkOfCompact_apply, ContinuousMap.coe_mk]
    refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).mpr fun k => ?_) (half_lt_self hε)
    rw [Real.dist_eq]
    calc |u n x k - u n y k| ≤ M * dist x y ^ β := hH n x y k
      _ ≤ M * ((ε / 2 / (M + 1)) ^ (1 / β)) ^ β := by gcongr
      _ = M * (ε / 2 / (M + 1)) := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one]
      _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hKA := arzela_ascoli K hK A hin heq
  obtain ⟨a, -, φ, hφ, hlim⟩ := hKA.tendsto_subseq (x := f) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, hφ, a, a.continuous, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
  refine eventually_atTop.mpr ⟨N, fun n hn x k => ?_⟩
  have h1 := hN n hn
  have h2 : |f (φ n) x k - a x k| ≤ dist (f (φ n)) a := by
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist (f (φ n) x) (a x) k).trans (dist_coe_le_dist x)
  exact h2.trans h1.le

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem lipschitz_of_dpart_bound {u : UnitAddTorus ι → ℝ} (hu : ContDiff ℝ 1 (u ∘ liftT)) {M : ℝ}
    (hM : 0 ≤ M) (hD : ∀ k x, |dpart u k x| ≤ M) :
    LipschitzWith (Real.toNNReal (Fintype.card ι * M)) u := by
  refine lipschitzWith_of_liftT (lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable one_ne_zero)
    fun x => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  refine (opNorm_le_sum_single _).trans ?_
  calc ∑ k, |fderiv ℝ (u ∘ liftT) x (Pi.single k 1)| = ∑ k, |dpart u k (liftT x)| := by
        simp_rw [dpart_liftT]
    _ ≤ ∑ _k : ι, M := Finset.sum_le_sum fun k _ => hD k _
    _ = Fintype.card ι * M := by simp

/-- **`C¹` limits.** -/
theorem c1_limit {u : ℕ → UnitAddTorus ι → ℝ} (hu : ∀ n, ContDiff ℝ 1 (u n ∘ liftT))
    {B M β : ℝ} (hβ : 0 < β) (hM : 0 ≤ M) (hB : ∀ n x, |u n x| ≤ B)
    (hD : ∀ n k x, |dpart (u n) k x| ≤ M)
    (hH : ∀ n x y k, |dpart (u n) k x - dpart (u n) k y| ≤ M * dist x y ^ β) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : UnitAddTorus ι → ℝ, ContDiff ℝ 1 (E ∘ liftT) ∧
      (∀ x, Tendsto (fun n => u (φ n) x) atTop (𝓝 (E x))) ∧
      (∀ k x, Tendsto (fun n => dpart (u (φ n)) k x) atTop (𝓝 (cpartial E k x))) := by
  obtain ⟨φ₁, hφ₁, E, hEc, hE⟩ := exists_subseq_unif u hB
    (fun n => lipschitz_of_dpart_bound (hu n) hM (hD n))
  obtain ⟨φ₂, hφ₂, W, hWc, hW⟩ := exists_subseq_unif_holder
    (fun n x k => dpart (u (φ₁ n)) k x) hβ hM (fun n x k => hD _ k x)
    (fun n x y k => hH _ x y k)
  set φ := φ₁ ∘ φ₂
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  -- uniform convergence along `φ`
  have hEu : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |u (φ n) x - E x| ≤ ε := fun ε hε =>
    (hφ₂.tendsto_atTop.eventually (hE ε hε)).mono fun n hn => hn
  have hWu : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x k, |dpart (u (φ n)) k x - W x k| ≤ ε := hW
  have hEp : ∀ x, Tendsto (fun n => u (φ n) x) atTop (𝓝 (E x)) := fun x =>
    Metric.tendsto_atTop.mpr fun ε hε => by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hEu (ε / 2) (half_pos hε))
      exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact (hN n hn x).trans_lt (half_lt_self hε)⟩
  -- the derivative of the limit
  set g' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ := fun x => ∑ k, W (liftT x) k • ContinuousLinearMap.proj k
  have hg'k : ∀ x k, g' x (Pi.single k 1) = W (liftT x) k := by
    intro x k
    simp [g', Pi.single_apply]
  have hTU : TendstoUniformly (fun n x => fderiv ℝ (u (φ n) ∘ liftT) x) g' atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε' : 0 < ε / (2 * (Fintype.card ι + 1)) := by positivity
    filter_upwards [hWu _ hε'] with n hn x
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt (opNorm_le_sum_single _) ?_
    calc ∑ k, |(fderiv ℝ (u (φ n) ∘ liftT) x - g' x) (Pi.single k 1)|
        = ∑ k, |dpart (u (φ n)) k (liftT x) - W (liftT x) k| := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ContinuousLinearMap.sub_apply, hg'k, dpart_liftT]
      _ ≤ ∑ _k : ι, ε / (2 * (Fintype.card ι + 1)) := Finset.sum_le_sum fun k _ => hn _ k
      _ = Fintype.card ι * (ε / (2 * (Fintype.card ι + 1))) := by simp
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hderiv : ∀ x, HasFDerivAt (E ∘ liftT) (g' x) x := fun x =>
    hasFDerivAt_of_tendstoUniformly hTU
      (fun n x => ((hu (φ n)).differentiable one_ne_zero x).hasFDerivAt)
      (fun x => by simpa [Function.comp] using hEp (liftT x)) x
  have hg'c : Continuous g' :=
    continuous_finset_sum _ fun k _ =>
      ((continuous_apply k).comp (hWc.comp continuous_liftT)).smul continuous_const
  have hC1 : ContDiff ℝ 1 (E ∘ liftT) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have : fderiv ℝ (E ∘ liftT) = g' := funext fun x => (hderiv x).fderiv
    rw [this]; exact hg'c
  have hcp : ∀ k x, cpartial E k x = W x k := by
    intro k x
    rw [cpartial, (hderiv _).fderiv, hg'k, liftT_repTorus]
  refine ⟨φ, hφ, E, hC1, hEp, fun k x => ?_⟩
  rw [hcp]
  exact Metric.tendsto_atTop.mpr fun ε hε => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hWu (ε / 2) (half_pos hε))
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact (hN n hn x k).trans_lt (half_lt_self hε)⟩

end SharpLSI
