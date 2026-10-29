import SharpSymmetricLSI.Paper.R29UI

/-!
# The occupation rest data along the infinite product (Phase 3, lane D; R29 joint law)

Standalone versions of the measurability and almost-sure convergence of `restN` used in
`tendsto_occBasis_joint`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology MvPolynomial Finset.HasAntidiagonal
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

section rest
variable {ν : Measure (Torus d)} [IsProbabilityMeasure ν] {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis ν e lam) (A : Finset (ℕ →₀ ℕ)) (K D : ℕ)
include he

theorem measurable_restN_emod (N : ℕ) :
    Measurable (restN A (D := D) (fun k : Fin K => emod he (k + 1)) N) := by
  set f : Fin K → Torus d → ℝ := fun k => emod he (k + 1)
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_emod he _
  -- measurability of the rest data
  have hmeasA : ∀ N, Measurable fun ω : ℕ → Torus d => fun (i : Fin N) (k : Fin K) => f k (ω i) :=
    fun N => measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k =>
      (hfm k).comp (measurable_pi_apply _)
  refine Measurable.prodMk (measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun γ => ?_)
    measurable_const
  by_cases h : hatΓ γ = 0
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false, qN]
    exact ((continuous_newtonCoeff j _).measurable.comp (hmeasA N)).const_mul _

theorem restN_tendsto_ae_emod :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), Tendsto
      (fun N => restN A (D := D) (fun k : Fin K => emod he (k + 1)) N ω) atTop
      (𝓝 (restInf A (K := K) (D := D))) := by
  set f : Fin K → Torus d → ℝ := fun k => emod he (k + 1)
  set P := Measure.infinitePi fun _ : ℕ => ν
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_emod he _
  have hfL : ∀ k, MemLp (f k) 2 ν := fun k => memLp_emod he _
  -- the strong laws
  set gs : Torus d → ℝ := fun x => ∑ k, |f k x|
  have hgsL : MemLp gs 2 ν := memLp_finsetSum _ fun k _ => (hfL k).abs
  have hgsm : Measurable gs := Finset.measurable_sum _ fun k _ => (hfm k).abs
  have hE1 : ∀ᵐ ω ∂P, ∀ jk : Fin K × Fin K, Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, f jk.1 (ω i) * f jk.2 (ω i)) / N) atTop
        (𝓝 (∫ x, f jk.1 x * f jk.2 x ∂ν)) := by
    rw [ae_all_iff]; intro jk
    exact slln_infinitePi ((hfm _).mul (hfm _)) ((hfL _).integrable_mul (hfL _))
  have hE2 : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, gs (ω i) ^ 2) / N) atTop
      (𝓝 (∫ x, gs x ^ 2 ∂ν)) :=
    slln_infinitePi (hgsm.pow_const 2) hgsL.integrable_sq
  filter_upwards [hE1, hE2] with ω h1 h2
  refine Tendsto.prodMk_nhds (tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun γ => ?_)
    (tendsto_pi_nhds.mpr fun α => tendsto_kappa _)
  show Tendsto (fun N => (if hatΓ γ = 0 then (0 : ℝ) else qN f N ω j (hatΓ γ))) atTop
    (𝓝 (if hatΓ γ = 0 then 0 else qLim 0 j (hatΓ γ)))
  by_cases h0 : hatΓ γ = 0
  · simp only [h0, ite_true]; exact tendsto_const_nhds
  simp only [h0, ite_false]
  set γ' := hatΓ γ
  have hdeg0 : γ'.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
  rcases Nat.lt_or_ge γ'.degree 2 with hlt | hge
  · obtain ⟨k, hk⟩ := eq_single_of_degree_eq_one (show γ'.degree = 1 by omega)
    rw [hk]
    have hlim := (h1 (j, k)).neg
    have hq : ∀ N : ℕ, 1 ≤ N → qN f N ω j (Finsupp.single k 1) =
        -((∑ i ∈ Finset.range N, f j (ω i) * f k (ω i)) / N) := fun N hN => by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [qN, Finsupp.degree_single, newtonCoeff_single]
      rw [Fin.sum_univ_eq_sum_range (fun i => f j (ω i) * f k (ω i)), inv_pow,
        Real.sq_sqrt hNpos.le]
      ring
    have hval : qLim 0 j (Finsupp.single k 1) = -∫ x, f j x * f k x ∂ν := by
      simp only [f]
      rw [integral_emod_mul]
      by_cases hjk : j = k
      · subst hjk; simp [qLim]
      · have h'' : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
        have hs : Finsupp.single k 1 ≠ Finsupp.single j 1 := fun hs =>
          hjk ((Finsupp.single_left_inj one_ne_zero).mp hs).symm
        simp [qLim, hs, h'']
    rw [hval]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hq N hN]
  · have hval : qLim 0 j γ' = 0 := by
      have hs : γ' ≠ Finsupp.single j 1 := fun hs => by
        rw [hs, Finsupp.degree_single] at hge; omega
      simp [qLim, h0, hs]
    rw [hval]
    have hsum := tendsto_sum_pow_of_mean_sq (v := fun i => gs (ω i))
      (fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _) h2 (p := γ'.degree + 1) (by omega)
    refine squeeze_zero_norm' ?_ hsum
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    simp only [qN]
    rw [abs_mul, abs_pow, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    calc (Real.sqrt N)⁻¹ ^ (γ'.degree + 1) *
          |newtonCoeff (fun (i : Fin N) k => f k (ω i)) j γ'|
        ≤ (Real.sqrt N)⁻¹ ^ (γ'.degree + 1) *
          ∑ i : Fin N, (∑ k, |f k (ω i)|) ^ (γ'.degree + 1) :=
          mul_le_mul_of_nonneg_left (abs_newtonCoeff_le _ _ _) (by positivity)
      _ = ∑ i ∈ Finset.range N, ((Real.sqrt N)⁻¹ * gs (ω i)) ^ (γ'.degree + 1) := by
          rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range
            (fun i => (Real.sqrt N)⁻¹ ^ (γ'.degree + 1) * (∑ k, |f k (ω i)|) ^ (γ'.degree + 1))]
          simp only [mul_pow, gs]

end rest

end SharpLSI
