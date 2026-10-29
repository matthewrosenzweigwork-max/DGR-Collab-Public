import FullLabeledLSI.Paper.Sec5LNC

/-!
# Large-N assembly D: L2, Young + conditional Jensen
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 4. L2: Young + conditional Jensen + weight identity -/

/-- Monotonicity of `avg1R`. -/
theorem avg1R_mono_aux {N j : ℕ} {F G : Finset (Fin N) → Fin N → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ, F S i ≤ G S i) :
    avg1R N j F ≤ avg1R N j G := by
  unfold avg1R
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S hS => ?_) (by positivity)
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => h S hS i hi) (by positivity)

/-- Pointwise Young. -/
theorem young_pt {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 := by
  have h : (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 - (a + b) ^ 2 = (ε * a - b) ^ 2 / ε := by
    field_simp; ring
  have : 0 ≤ (ε * a - b) ^ 2 / ε := by positivity
  linarith

/-- The per-`(S,i)` Young estimate. -/
theorem young_term {μ : Measure (Torus d)} {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ}
    {c C : ℝ} {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → Config N d → ℝ}
    {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    [IsProbabilityMeasure ν]
    (hS : ScoreData V W μ ν Q c C GQ s bF bΔ Bb) {ε : ℝ} (hε : 0 < ε)
    (S : Finset (Fin N)) (hS1 : 1 ≤ Sᶜ.card) (i : Fin N) :
    ∫ X, ∑ k : Fin d,
      (condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X +
        BS bF ν S X (X i) k) ^ 2 ∂ν ≤
    (1 + ε) * ∑ k : Fin d, ∫ X, s i k X ^ 2 ∂ν +
      (1 + 1 / ε) * ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k - Gpart bF bΔ N X i k) ^ 2 ∂ν := by
  classical
  have hB := hS.force
  have hm : revSigma (d := d) S i ≤ (inferInstance : MeasurableSpace (Config N d)) :=
    ((measurable_restrictS S).prodMk (measurable_pi_apply i)).comap_le
  have hBm : ∀ k, Measurable[revSigma (d := d) S i] fun X : Config N d => BS bF ν S X (X i) k :=
    fun k => by
    have h := (measurable_BSA hB ν S k).comp
      (comap_measurable (fun X : Config N d => (restrictS S X, X i)))
    exact h
  have key := fun k : Fin d => sq_sub_condExp_le ν hm (hBm k)
    (C := max Bb ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)))
    (fun X => (abs_BS_le hB ν S hS1 X (X i) k).trans (le_max_left _ _)) (measurable_Gpart hB i k)
    (fun X => (abs_Gpart_le hB X i k).trans (le_max_right _ _))
  have hGi : ∀ k, Integrable (fun Y => Gpart bF bΔ N Y i k) ν := fun k =>
    Integrable.of_bound (measurable_Gpart hB i k).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_Gpart_le hB x i k)
  have hsL : ∀ k, MemLp (s i k) 2 ν := fun k =>
    (memLp_two_iff_integrable_sq (hS.sM i k).aestronglyMeasurable).2 (hS.sL2 i k)
  have hsi : ∀ k, Integrable (s i k) ν := fun k => (hsL k).integrable (by norm_num)
  have hacond : ∀ k, MemLp (ν[s i k | revSigma (d := d) S i]) 2 ν := fun k => (hsL k).condExp (by norm_num)
  have hasq : ∀ k, Integrable (fun X => (ν[s i k | revSigma (d := d) S i] X) ^ 2) ν :=
    fun k => (hacond k).integrable_sq
  have hae : ∀ k, ∀ᵐ X ∂ν, condExp (revSigma (d := d) S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X
      + BS bF ν S X (X i) k =
      ν[s i k | revSigma (d := d) S i] X +
        (BS bF ν S X (X i) k - ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) := by
    intro k
    filter_upwards [condExp_sub (m := revSigma (d := d) S i) (hsi k) (hGi k)] with X hX
    have : condExp (revSigma (d := d) S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X =
        ν[s i k | revSigma (d := d) S i] X - ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X :=
      hX
    rw [this]; ring
  have hae' : ∀ᵐ X ∂ν, ∀ k, condExp (revSigma (d := d) S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X
      + BS bF ν S X (X i) k =
      ν[s i k | revSigma (d := d) S i] X +
        (BS bF ν S X (X i) k - ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) :=
    ae_all_iff.2 hae
  have hRint : Integrable (fun X => ∑ k : Fin d,
      ((1 + ε) * (ν[s i k | revSigma (d := d) S i] X) ^ 2 +
        (1 + 1 / ε) * (BS bF ν S X (X i) k - ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2)) ν :=
    integrable_finsetSum _ fun k _ => ((hasq k).const_mul _).add ((key k).1.const_mul _)
  have h1 : ∫ X, ∑ k : Fin d,
      (condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X +
        BS bF ν S X (X i) k) ^ 2 ∂ν ≤
      ∫ X, ∑ k : Fin d,
      ((1 + ε) * (ν[s i k | revSigma (d := d) S i] X) ^ 2 +
        (1 + 1 / ε) * (BS bF ν S X (X i) k - ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2) ∂ν := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X =>
      Finset.sum_nonneg fun k _ => sq_nonneg _) hRint ?_
    filter_upwards [hae'] with X hX
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hX k]; exact young_pt hε _ _
  refine h1.trans ?_
  have hexp : ∫ X, ∑ k : Fin d,
      ((1 + ε) * (ν[s i k | revSigma (d := d) S i] X) ^ 2 +
        (1 + 1 / ε) * (BS bF ν S X (X i) k - ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2) ∂ν =
      (1 + ε) * ∑ k : Fin d, ∫ X, (ν[s i k | revSigma (d := d) S i] X) ^ 2 ∂ν +
      (1 + 1 / ε) * ∑ k : Fin d, ∫ X, (BS bF ν S X (X i) k -
        ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2 ∂ν := by
    have hfs : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun X =>
        (1 + ε) * (ν[s i k | revSigma (d := d) S i] X) ^ 2 +
        (1 + 1 / ε) * (BS bF ν S X (X i) k -
          ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2) ν :=
      fun k _ => ((hasq k).const_mul (1 + ε)).add ((key k).1.const_mul (1 + 1 / ε))
    rw [integral_finsetSum _ hfs]
    have : ∀ k : Fin d, ∫ X, ((1 + ε) * (ν[s i k | revSigma (d := d) S i] X) ^ 2 +
        (1 + 1 / ε) * (BS bF ν S X (X i) k -
          ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2) ∂ν =
        (1 + ε) * ∫ X, (ν[s i k | revSigma (d := d) S i] X) ^ 2 ∂ν +
        (1 + 1 / ε) * ∫ X, (BS bF ν S X (X i) k -
          ν[fun Y => Gpart bF bΔ N Y i k | revSigma (d := d) S i] X) ^ 2 ∂ν := fun k => by
      rw [integral_add ((hasq k).const_mul _) ((key k).1.const_mul _), integral_const_mul,
        integral_const_mul]
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp]
  have hJ := jensen_force hB ν S hS1 i
  rw [integral_finsetSum _ fun k _ => (key k).1] at hJ
  have hA : ∑ k : Fin d, ∫ X, (ν[s i k | revSigma (d := d) S i] X) ^ 2 ∂ν ≤
      ∑ k : Fin d, ∫ X, s i k X ^ 2 ∂ν :=
    Finset.sum_le_sum fun k _ => SharpLSI.integral_sq_condExp_le hm (hsL k)
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hε2 : 0 ≤ 1 + 1 / ε := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hA hε1) (mul_le_mul_of_nonneg_left hJ hε2)


section L2
variable {μ : Measure (Torus d)} {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- **L2.**  For `ε > 0`, `j < N`:
`mfDiss j ≤ (1+ε) (1/N) Σ_i E_ν|s_i|² + (1+1/ε) forceDelta bF bΔ ν j`.
Proof, for each `(S, i)`: with `a = E[s_i|𝒢]`, `b = B_S(X_i) - E[G_i|𝒢]`, `condExp_sub` gives
`E[s_i - G_i|𝒢] + B_S = a + b`; pointwise `|a+b|² ≤ (1+ε)|a|² + (1+1/ε)|b|²`; then
`SharpLSI.integral_sq_condExp_le` (`∫|E[s|𝒢]|² ≤ ∫|s|²`, `s_i ∈ L²` by `hS.sL2`) and `jensen_force`
(Sec5ForceJensen: `∫|B - E[G|𝒢]|² ≤ ∫|B - G|²`, needs `1 ≤ |Sᶜ|`); finally average over `(S,i)` with
`avg1R_const_S` (Sec5ForceT3) applied to the `S`-independent `i ↦ ∫|s_i|²`.  NO symmetry is used.
~100 lines. -/
theorem level_young [IsProbabilityMeasure ν]
    (hS : ScoreData V W μ ν Q c C GQ s bF bΔ Bb) {ε : ℝ} (hε : 0 < ε)
    {j : ℕ} (hj : j < N) :
    mfDiss bF bΔ ν s j ≤ (1 + ε) * ((N : ℝ)⁻¹ * fisherS ν s) +
      (1 + 1 / ε) * forceDelta bF bΔ ν j := by
  have h1 : mfDiss bF bΔ ν s j ≤ avg1R N j (fun S i =>
      (1 + ε) * (∑ k : Fin d, ∫ X, s i k X ^ 2 ∂ν) +
      (1 + 1 / ε) * ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k - Gpart bF bΔ N X i k) ^ 2 ∂ν) := by
    refine avg1R_mono_aux fun S hS0 i _ => ?_
    have hcard : Sᶜ.card = N - j := by
      rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hS0).2]
    exact young_term hS hε S (by omega) i
  refine h1.trans (le_of_eq ?_)
  rw [avg1R_add', avg1R_const_mul', avg1R_const_mul']
  have := avg1R_const_S N j hj (fun i => ∑ k : Fin d, ∫ X, s i k X ^ 2 ∂ν)
  rw [this]
  rfl

end L2

section L2b
variable {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- **Level bound** (L1 + L2): `2 r₀ (h_j + cps_j) ≤ (1+ε)(1/N) I + (1+1/ε) forceDelta_j`.
Immediate: `(level_meanfield …).trans (level_young …)`.  -/
theorem level_bound (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {r₀ ε : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W) (hε : 0 < ε) {j : ℕ} (hj : j < N) :
    2 * r₀ * ((hRev ν (μ : Measure (Torus d)) j).toReal +
        condMeanS ν 2 (Bk W (μ : Measure (Torus d))) j) ≤
      (1 + ε) * ((N : ℝ)⁻¹ * fisherS ν s) + (1 + 1 / ε) * forceDelta bF bΔ ν j :=
  (level_meanfield hyp hμ hS hr₀ hrr hj).trans (level_young hS hε hj)

end L2b


end SharpLSI.FL
