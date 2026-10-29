import SharpSymmetricLSI.Paper.FormLiminf8
import SharpSymmetricLSI.Paper.ForceApprox5

/-!
# (8.20) (lane s42): the force-error bridge to R31

`forceD_approx_sq`: with `u_{lk} = ∇_{lk}(U_N - U_N^{(R)})` (weak gradient; a.e. equal to
`gsG - N⁻¹ ∑_b ∂₁K_R(X_l, X_b)`, `weakGradC_diff_ae`), the force term `D_i` and its finite-rank
counterpart `∑_{p,q} a_{pq} Z_q A_{pi}` differ by `N^{-1/2} ∑_{l,k} u_{lk} ∂_k e_{i+1}(X_l)`;
Cauchy–Schwarz gives the bound `d C_i² |∇(U_N - U_N^{(R)})|²`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- **Cauchy–Schwarz** for `N^{-1/2} ∑_{l,k} u_{lk} c_{lk}` with `|c| ≤ C`. -/
theorem sq_scaled_sum_le {N : ℕ} (hN : 1 ≤ N) (u c : Fin N → Fin d → ℝ) {Ci : ℝ}
    (hc : ∀ l k, |c l k| ≤ Ci) :
    ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k, u l k * c l k) ^ 2 ≤
      d * Ci ^ 2 * ∑ l, ∑ k, u l k ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcs : (∑ l, ∑ k, u l k * c l k) ^ 2 ≤ (∑ l, ∑ k, u l k ^ 2) * ∑ l, ∑ k, c l k ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N × Fin d))
      (fun p => u p.1 p.2) (fun p => c p.1 p.2)
    simpa only [Fintype.sum_prod_type] using h
  have hc2 : ∑ l, ∑ k, c l k ^ 2 ≤ N * (d * Ci ^ 2) := by
    calc ∑ l, ∑ k, c l k ^ 2 ≤ ∑ _l : Fin N, ∑ _k : Fin d, Ci ^ 2 :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hc l k) 2
      _ = N * (d * Ci ^ 2) := by simp
  have hu0 : 0 ≤ ∑ l, ∑ k, u l k ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_pow, rpow_neg_half_sq]
  calc (N : ℝ)⁻¹ * (∑ l, ∑ k, u l k * c l k) ^ 2
      ≤ (N : ℝ)⁻¹ * ((∑ l, ∑ k, u l k ^ 2) * (N * (d * Ci ^ 2))) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hc2 hu0))
          (inv_nonneg.2 hN0.le)
    _ = d * Ci ^ 2 * ∑ l, ∑ k, u l k ^ 2 := by field_simp

/-- Exchange of two finite double sums. -/
theorem sum4_comm {N : ℕ} (s : Finset ℕ) (f : ℕ → ℕ → Fin N → Fin d → ℝ) :
    ∑ p ∈ s, ∑ q ∈ s, ∑ l, ∑ k, f p q l k = ∑ l, ∑ k, ∑ p ∈ s, ∑ q ∈ s, f p q l k := by
  calc ∑ p ∈ s, ∑ q ∈ s, ∑ l, ∑ k, f p q l k = ∑ p ∈ s, ∑ l, ∑ q ∈ s, ∑ k, f p q l k :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p ∈ s, ∑ l, ∑ k, ∑ q ∈ s, f p q l k :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l, ∑ p ∈ s, ∑ k, ∑ q ∈ s, f p q l k := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ p ∈ s, ∑ q ∈ s, f p q l k := Finset.sum_congr rfl fun l _ => Finset.sum_comm

/-- The finite-rank algebra `∑_{p,q} a_{pq} (r S_q)(t ∑ G_p c) = r ∑_{l,k} (t ∑_{p,q} a G_p S_q) c`. -/
theorem finRank_force_alg {N : ℕ} (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (G : ℕ → Fin N → Fin d → ℝ)
    (S : ℕ → ℝ) (c : Fin N → Fin d → ℝ) (r t : ℝ) :
    ∑ p ∈ s, ∑ q ∈ s, a p q * (r * S q) * (t * ∑ l, ∑ k, G p l k * c l k) =
      r * ∑ l, ∑ k, (t * ∑ p ∈ s, ∑ q ∈ s, a p q * G p l k * S q) * c l k := by
  have hL : ∑ p ∈ s, ∑ q ∈ s, a p q * (r * S q) * (t * ∑ l, ∑ k, G p l k * c l k) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ l, ∑ k, r * t * a p q * S q * G p l k * c l k := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  have hR : r * ∑ l, ∑ k, (t * ∑ p ∈ s, ∑ q ∈ s, a p q * G p l k * S q) * c l k =
      ∑ l, ∑ k, ∑ p ∈ s, ∑ q ∈ s, r * t * a p q * S q * G p l k * c l k := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hL, hR, sum4_comm]

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The weak gradient of `U_N - U_N^{(R)}` in the form `gsG - N⁻¹ ∑_b ∂₁K_R(X_l, X_b)`, a.e.
under the Gibbs measure. -/
theorem weakGradC_diff_gibbs (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j) {KR : Torus d → Torus d → ℝ} (s : Finset ℕ)
    {a : ℕ → ℕ → ℝ} (ha : ∀ i j, a i j = a j i)
    (hK : ∀ x y, KR x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y)
    {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ X ∂gibbs V W N, ∀ l k,
      weakGradC (fun Y => Ucentered W μ N Y - UkernelF KR N Y) X l k =
        gsG W μ N (flat X) (l, k) -
          (N : ℝ)⁻¹ * ∑ b, finKerD (fun i => eC (i + 1)) s a (X l) (X b) k := by
  have h1 : gibbs V W N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  have hd := weakGradC_diff_ae hyp hμ (fun i => hφ (i + 1)) s ha hN
    (Ukernel_ae_finKer heC s a hK N)
  filter_upwards [h1.ae_le hd] with X hX l k
  rw [hX l k]
  simp only [gsG, cOff, cDiag]
  rw [show unflat (flat X) = X from rfl,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ l)]
  simp only [Finset.sum_sub_distrib]
  ring

/-- **The force-error bridge**: `(D_i - ∑_{p,q} a_{pq} Z_q A_{pi})² ≤ d C_i² |∇(U_N - U_N^{(R)})|²`
a.e. under the Gibbs measure. -/
theorem forceD_approx_sq (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ)
    {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {KR : Torus d → Torus d → ℝ} (s : Finset ℕ) {a : ℕ → ℕ → ℝ} (ha : ∀ i j, a i j = a j i)
    (hK : ∀ x y, KR x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y)
    {N : ℕ} (hN : 1 ≤ N) (i : ℕ) {Ci : ℝ} (hCi : ∀ y k, |cgrad (eC (i + 1)) y k| ≤ Ci) :
    ∀ᵐ X ∂gibbs V W N,
      (forceD W (μ : Measure (Torus d)) eC N i X -
        ∑ p ∈ s, ∑ q ∈ s, a p q * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
          mobA eC N X p i) ^ 2 ≤
      d * Ci ^ 2 * gradSqC (fun Y => Ucentered W μ N Y - UkernelF KR N Y) X := by
  filter_upwards [weakGradC_diff_gibbs hyp hμ hφ heC s ha hK hN] with X hX
  set u : Fin N → Fin d → ℝ := fun l k =>
    weakGradC (fun Y => Ucentered W μ N Y - UkernelF KR N Y) X l k
  set c : Fin N → Fin d → ℝ := fun l k => cgrad (eC (i + 1)) (X l) k
  have key : forceD W (μ : Measure (Torus d)) eC N i X -
      ∑ p ∈ s, ∑ q ∈ s, a p q * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
        mobA eC N X p i = (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k, u l k * c l k := by
    have h1 : ∀ (l : Fin N) (k : Fin d), ∑ b, finKerD (fun i => eC (i + 1)) s a (X l) (X b) k =
        ∑ p ∈ s, ∑ q ∈ s, a p q * cgrad (eC (p + 1)) (X l) k * ∑ b, eC (q + 1) (X b) := by
      intro l k
      simp only [finKerD]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
    have hR : ∑ p ∈ s, ∑ q ∈ s, a p q * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
        mobA eC N X p i = (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k,
          ((N : ℝ)⁻¹ * ∑ b, finKerD (fun i => eC (i + 1)) s a (X l) (X b) k) * c l k := by
      simp only [h1]
      exact finRank_force_alg s a (fun p l k => cgrad (eC (p + 1)) (X l) k)
        (fun q => ∑ b, eC (q + 1) (X b)) c _ _
    rw [hR]
    simp only [forceD, u, c, hX]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [key]
  exact sq_scaled_sum_le hN u c fun l k => hCi _ _

end SharpLSI
