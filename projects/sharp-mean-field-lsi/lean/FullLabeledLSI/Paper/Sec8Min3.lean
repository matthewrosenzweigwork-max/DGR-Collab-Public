import FullLabeledLSI.Paper.Sec8Min2

/-!
# Section 8.3 (linearization), part 10: `D₁ ≥ m G₁` for the mean field part

For a bounded Lipschitz mean-zero `g` and `m ≥ 0` with `m ⟨v, C v⟩_n ≤ ∑_{i<n} λ_{i+1} v_i²` for all
finite `v`, `m ⟨g,(I+T)g⟩ ≤ ∫|∇(g + T g)|² dμ`. The finite blocks are the test perturbations of
`exists_test_pert` for the coefficients `v_i = ⟨(I+T)g, e_{i+1}⟩`; the second variations of the test
perturbations converge to `⟨g,(I+T)g⟩` by `quad_conv`, and the energies are bounded by Parseval.
-/

open MeasureTheory InformationTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem coercive (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ x : Torus d → ℝ, MemL20 (μ : Measure (Torus d)) x →
      σ * ∫ y, x y ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W (μ : Measure (Torus d)) x := by
  obtain ⟨-, hall⟩ := prop_equilibrium hd hyp hr
  obtain ⟨p, hp, hvar, σ, hσ, c, hc, hc1, hsig, hcoer⟩ := hall μ hμ
  exact ⟨σ, hσ, hsig⟩

theorem D1_ge (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) {mr : ℝ}
    (hmr : ∀ (n : ℕ) (v : ℕ → ℝ), mr * ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j ≤
      ∑ i ∈ range n, lamShift lam i * v i ^ 2)
    {g : Torus d → ℝ} (hg : ∃ L : ℝ≥0, LipschitzWith L g)
    (hg0 : ∫ x, g x ∂(μ : Measure (Torus d)) = 0) :
    mr * secondVar W (μ : Measure (Torus d)) g ≤
      (dirichlet (μ : Measure (Torus d))
        (fun x => g x + Top W (μ : Measure (Torus d)) g x)).toReal := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨Chl, hlow⟩ := haar_le_smul_minimizer hyp hμ
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  obtain ⟨σ, hσ0, hσ⟩ := coercive hd hyp hr hμ
  have hgB : BM g := BM.of_lip hg
  have hTg : BM (Top W (μ : Measure (Torus d)) g) := hgB.top hyp hg0
  have hFB : BM (fun x => g x + Top W (μ : Measure (Torus d)) g x) := hgB.add hTg
  have hFL : ∃ L : ℝ≥0, LipschitzWith L (fun x => g x + Top W (μ : Measure (Torus d)) g x) :=
    lip_add hg (top_lip_bdd hyp hgB.1 hgB.2.choose_spec hg0).1
  obtain ⟨hfc, hfw, ⟨Kf, hKf⟩, hfgm⟩ := lip_data hFL
  obtain ⟨hFm, Bf, hBf⟩ := hFB
  set f : Torus d → ℝ := fun x => g x + Top W (μ : Measure (Torus d)) g x with hf
  have hf0 : ∫ x, f x ∂(μ : Measure (Torus d)) = 0 := by
    simp only [hf]
    rw [integral_add hgB.integrable hTg.integrable, hg0,
      integral_Top hyp (μ : Measure (Torus d)) hgB.integrable, add_zero]
  have hfH1 : MemH1 (μ : Measure (Torus d)) f := memH1_of_wg hac hfw hFm hBf hKf
  set c : ℕ → ℝ := fun i => ∫ x, f x * e i x ∂(μ : Measure (Torus d)) with hc
  have hc0' : ∫ x, f x * e 0 x ∂(μ : Measure (Torus d)) = 0 := by
    rw [he.zero]; simpa using hf0
  have hc0 : c 0 = 0 := hc0'
  have hpar := energy_parseval hac hlow he hfH1
  rw [dirPair_eq hac hfw] at hpar
  rw [dirichlet_toReal_of_wg hac hfw hKf hfgm]
  set v : ℕ → ℝ := fun i => c (i + 1) with hv
  have hN : ∀ n, ∑ i ∈ range n, lamShift lam i * v i ^ 2 ≤
      ∫ x, ∑ k, lipGrad f x k ^ 2 ∂(μ : Measure (Torus d)) := by
    intro n
    have h1 := sum_le_hasSum (range (n + 1))
      (fun i _ => mul_nonneg (lam_nonneg hac he i) (sq_nonneg _)) hpar
    rw [Finset.sum_range_succ', hc0'] at h1
    simpa [lamShift, hv, hc] using h1
  have heC' : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧
      eC j =ᵐ[(μ : Measure (Torus d))] e j := fun j => ⟨(heC j).1, (heC j).2.2⟩
  choose hh hhc hh0 hhsum hhQ using
    fun n => exists_test_pert hd hyp hr hμ he hC heC' n v
  have hδ : Tendsto (fun n => ∫ x, ((hh n x + Top W (μ : Measure (Torus d)) (hh n) x) -
      (g x + Top W (μ : Measure (Torus d)) g x)) ^ 2 ∂(μ : Measure (Torus d))) atTop (𝓝 0) := by
    have hconv := (tendsto_partial_sum he hfH1.2.1).comp (tendsto_add_atTop_nat 1)
    refine hconv.congr (fun n => ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun i => (heC' (i + 1)).2] with x hx
    have hS : ∑ i ∈ range n, v i * eC (i + 1) x = ∑ i ∈ range n, c (i + 1) * e (i + 1) x :=
      Finset.sum_congr rfl fun i _ => by rw [hx i]
    rw [hhsum n x, hS, Finset.sum_range_succ', hc0', zero_mul, add_zero]
    show (f x - ∑ i ∈ range n, c (i + 1) * e (i + 1) x) ^ 2 =
      (∑ i ∈ range n, c (i + 1) * e (i + 1) x - f x) ^ 2
    ring
  have hQ := quad_conv hyp hσ0 hσ hgB hg0 (fun n => BM.of_cont (hhc n)) hh0 hδ
  have hfin : ∀ n, mr * secondVar W (μ : Measure (Torus d)) (hh n) ≤
      ∫ x, ∑ k, lipGrad f x k ^ 2 ∂(μ : Measure (Torus d)) := fun n => by
    rw [hhQ n]; exact (hmr n v).trans (hN n)
  exact le_of_tendsto (tendsto_const_nhds.mul hQ) (Eventually.of_forall hfin)

end Sec8
end SharpLSI.FL
