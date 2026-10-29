import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CosineTest
import SharpSymmetricLSI.Paper.CosineHyp
import SharpSymmetricLSI.Paper.CosineMarginal
import SharpSymmetricLSI.Paper.CosineTagged

/-!
# R9: Section 3.2, the one-coordinate upper bound (3.7)–(3.9)

Manuscript Section 3.2:
* (3.7) `D²W_κ ≥ -2aκ I_2`; hence (1.2) holds (`cosine_hyp`, with `K_V = 0`, `K_W = 2aκ`).
* (3.8) `H_{N,κ} = (1/N) ∑_{i<j} W_κ(xᵢ,xⱼ) = (κ/(2N)) |∑ⱼ e^{2πixⱼ}|² - κN/2`.
* translation invariance: every one-particle marginal of `P_{N,κ}` is `m`.
* (3.9) for `f(X) = h(x_1)`: `Ent_{P_{N,κ}}(f²) = Ent_m(h²)`, `∫ ∑ᵢ |∂ᵢf|² dP_{N,κ} = ∫ |h'|² dm`.
* (unnumbered display after (3.9)) with `h_ε = 1 + ε cos(2πx)`: `2∫|h_ε'|²/Ent_m(h_ε²) → a`; hence `r^all_{N,κ} ≤ a`.
The particle index `1` is `⟨0, _⟩ : Fin N`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- (3.7) and (1.2) for the cosine model. -/
theorem cosine_hyp {κ : ℝ} (hκ : 0 < κ) : Hyp cosV (cosW κ) 0 (2 * aCos * κ) := by
  exact cosine_hyp_aux hκ

/-- (3.8): the Hamiltonian of the cosine model. -/
theorem cosine_hamiltonian (κ : ℝ) {N : ℕ} (hN : 1 ≤ N) (X : Config N 1) :
    hamiltonian cosV (cosW κ) N X =
        1 / (N : ℝ) * ∑ i, ∑ j, (if i < j then cosW κ (X i) (X j) else 0) ∧
      hamiltonian cosV (cosW κ) N X =
        κ / (2 * (N : ℝ)) * Complex.normSq (∑ j, expT (X j)) - κ * N / 2 := by
  have hexp : ∀ x y : Torus 1, expT (x - y) = expT x * starRingEnd ℂ (expT y) := by
    intro x y
    simp only [expT, fourier_apply, one_smul, Pi.sub_apply, sub_eq_add_neg,
      AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul, Circle.coe_inv_eq_conj]
  have hg : ∀ x y : Torus 1, gCos (x - y) = (expT x * starRingEnd ℂ (expT y)).re := by
    intro x y; rw [gCos, hexp]
  have hsymm : ∀ x y : Torus 1, cosW κ x y = cosW κ y x := by
    intro x y
    simp only [cosW, hg]
    congr 2
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  have hdiag : ∀ x : Torus 1, cosW κ x x = 0 := by
    intro x
    simp only [cosW, hg, Complex.mul_conj, Complex.ofReal_re]
    have : Complex.normSq (expT x) = 1 := by
      simp [expT, fourier_apply, Complex.normSq_eq_norm_sq]
    rw [this]; ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH : hamiltonian cosV (cosW κ) N X =
      1 / (2 * (N : ℝ)) * ∑ i, ∑ j, cosW κ (X i) (X j) := by
    simp [hamiltonian, cosV]
  constructor
  · rw [hH]
    have hsplit : ∀ i j, cosW κ (X i) (X j) =
        (if i < j then cosW κ (X i) (X j) else 0) + (if j < i then cosW κ (X j) (X i) else 0) := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · simp [h, not_lt.mpr h.le]
      · subst h; simp [hdiag]
      · simp only [h, not_lt.mpr h.le, ↓reduceIte, zero_add]; exact hsymm _ _
    have : ∑ i, ∑ j, cosW κ (X i) (X j) =
        2 * ∑ i, ∑ j, (if i < j then cosW κ (X i) (X j) else 0) := by
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hsplit i j))]
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => if j < i then cosW κ (X j) (X i) else 0)]
      ring
    rw [this]; field_simp
  · rw [hH]
    have : ∑ i, ∑ j, cosW κ (X i) (X j) =
        κ * Complex.normSq (∑ j, expT (X j)) - κ * N ^ 2 := by
      have hn : Complex.normSq (∑ j, expT (X j)) =
          ∑ i, ∑ j, (expT (X i) * starRingEnd ℂ (expT (X j))).re := by
        have h1 : (Complex.normSq (∑ j, expT (X j)) : ℂ).re = Complex.normSq (∑ j, expT (X j)) :=
          Complex.ofReal_re _
        rw [← h1, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
        simp only [Complex.re_sum]
      simp only [cosW, hg]
      rw [hn]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_one, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [this]; field_simp

/-- Translation invariance: every one-particle marginal of `P_{N,κ}` is `m`. -/
theorem cosine_marginal (κ : ℝ) {N : ℕ} (i : Fin N) :
    (gibbs cosV (cosW κ) N).map (fun X => X i) = haar 1 := by
  exact cosine_marginal_aux κ i

/-- (3.9): one-coordinate tests `f(X) = h(x_1)`. -/
theorem cosine_tagged (κ : ℝ) {N : ℕ} (hN : 1 ≤ N) {h : Torus 1 → ℝ}
    (hh : MemH1 (haar 1) h) :
    MemH1C (gibbs cosV (cosW κ) N) (fun X => h (X ⟨0, hN⟩)) ∧
    ent (gibbs cosV (cosW κ) N) (fun X => h (X ⟨0, hN⟩) ^ 2) =
      ent (haar 1) (fun x => h x ^ 2) ∧
    energy cosV (cosW κ) N (fun X => h (X ⟨0, hN⟩)) =
      ∫⁻ x, ENNReal.ofReal (weakGrad h x 0 ^ 2) ∂haar 1 := by
  exact cosine_tagged_aux κ hN hh

/-- Unnumbered display after (3.9): `h_ε = 1 + ε cos(2πx)` gives the quotient `2∫|h_ε'|²/Ent_m(h_ε²) → a`. -/
theorem cosine_test_quotient :
    Tendsto (fun ε : ℝ => 2 * dirichlet (haar 1) (fun x => 1 + ε * gCos x) /
        ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2)) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal aCos)) := by
  exact cosine_test_quotient_aux

/-- Section 3.2: `r^all_{N,κ} ≤ a` for every `N ≥ 1`. -/
theorem cosine_rAll_le {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    rAll cosV (cosW κ) N ≤ ENNReal.ofReal aCos := by
  exact cosine_rAll_le_aux hN

end SharpLSI
