import DGPS.Variational.PositiveRankOne
import DGPS.Equilibrium.GaussianRate

/-!
# Local positive-rank-one Gaussian endpoint lower limit (EX061)

If `ρₙ → q` uniformly in square root, `G(ρₙ) > 0` and `D/(2G)` stays bounded, then
`liminf D/(2G) ≥ λ_G(q, Id + η φ ⊗ φ)`.  The proof is direct (no compactness): a test function
built from the normalized square root of `ρₙ` is inserted into the Gaussian Rayleigh quotient.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open DGPS.PositiveRankOne

namespace DGPS.LocalGaussianEndpoint

theorem psi_poly (x R : ℝ) (hx : |x| ≤ 1 / 2) (hR : |R| ≤ 2 * x ^ 4) :
    (1 + x) ^ 2 * (2 * (x - x ^ 2 / 2 + x ^ 3 / 3 + R)) - (1 + x) ^ 2 + 1 ≤
      2 * x ^ 2 + 6 * (x ^ 2 * |x|) := by
  have ha0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h4 : x ^ 4 = |x| ^ 4 := by rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm
  have hlin : (1 + x) ^ 2 ≤ 9 / 4 := by
    have := abs_le.1 hx; nlinarith
  have hR2 := (abs_le.1 hR).2
  have hRabs : 2 * (1 + x) ^ 2 * R ≤ 9 * |x| ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_left hR2 (by positivity : (0:ℝ) ≤ 2 * (1 + x) ^ 2)
    have h2 := mul_le_mul_of_nonneg_right hlin (by positivity : (0:ℝ) ≤ 2 * x ^ 4)
    rw [h4] at h1 h2
    nlinarith
  have key : (1 + x) ^ 2 * (2 * (x - x ^ 2 / 2 + x ^ 3 / 3 + R)) - (1 + x) ^ 2 + 1 =
      2 * x ^ 2 + (2 / 3) * x ^ 3 + x ^ 4 / 3 + (2 / 3) * x ^ 5 + 2 * (1 + x) ^ 2 * R := by ring
  rw [key]
  have c3 : x ^ 3 ≤ |x| ^ 3 := by
    have := le_abs_self (x ^ 3); rwa [abs_pow] at this
  have c5 : x ^ 5 ≤ |x| ^ 5 := by
    have := le_abs_self (x ^ 5); rwa [abs_pow] at this
  have h5 : |x| ^ 5 ≤ |x| ^ 3 / 4 := by
    have h2 : |x| ^ 2 ≤ 1 / 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 (pow_nonneg ha0 3)
    nlinarith
  have c4 : |x| ^ 4 ≤ |x| ^ 3 / 2 := by
    have := mul_le_mul_of_nonneg_left hx (pow_nonneg ha0 3)
    nlinarith
  have hxa : x ^ 2 * |x| = |x| ^ 3 := by rw [hx2]; ring
  rw [hxa, h4]
  have := pow_nonneg ha0 3
  linarith

/-- Third-order entropy bound for `t = (1+x)²`. -/
theorem psi_bound (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 + x) ^ 2 * Real.log ((1 + x) ^ 2) - (1 + x) ^ 2 + 1 ≤ 2 * x ^ 2 + 6 * (x ^ 2 * |x|) := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 3
  have hden : 0 < 1 - |x| := by linarith
  have hlog : Real.log ((1 + x) ^ 2) = 2 * Real.log (1 + x) := by
    rw [Real.log_pow]; push_cast; ring
  rw [show (1 : ℝ) - -x = 1 + x by ring] at h
  have e : (∑ i ∈ Finset.range 3, (-x) ^ (i + 1) / ((i : ℝ) + 1)) =
      (-x) + x ^ 2 / 2 - x ^ 3 / 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  rw [e, abs_neg] at h
  have hR : |(-x) + x ^ 2 / 2 - x ^ 3 / 3 + Real.log (1 + x)| ≤ 2 * x ^ 4 := by
    refine h.trans ?_
    rw [div_le_iff₀ hden]
    have h4 : |x| ^ (3 + 1) = x ^ 4 := by
      show |x| ^ 4 = x ^ 4
      rw [pow_abs]; exact abs_of_nonneg (by positivity)
    rw [h4]
    have : 0 ≤ x ^ 4 := by positivity
    nlinarith
  rw [hlog]
  have := psi_poly x ((-x) + x ^ 2 / 2 - x ^ 3 / 3 + Real.log (1 + x)) hx hR
  have e2 : x - x ^ 2 / 2 + x ^ 3 / 3 + ((-x) + x ^ 2 / 2 - x ^ 3 / 3 + Real.log (1 + x)) =
      Real.log (1 + x) := by ring
  rwa [e2] at this

end DGPS.LocalGaussianEndpoint

namespace DGPS.LocalGaussianEndpoint

theorem xb_bound (η Φ C S a b N X : ℝ) (hS : 0 ≤ S) (hN0 : 0 ≤ N) (hN1 : N ≤ 1)
    (ha : a ^ 2 ≤ Φ * N) (hb : |b| ≤ C * N)
    (hX : X ≤ η ^ 2 / 2 * (b ^ 2 * S + (2 * a + b) ^ 2 * S * N)) :
    X ≤ η ^ 2 * S / 2 * (3 * C ^ 2 + 8 * Φ) * N ^ 2 := by
  have hb2 : b ^ 2 ≤ C ^ 2 * N ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rw [sq_abs, mul_pow] at h
    exact h
  have hNN : N ^ 2 ≤ N := by nlinarith
  have hm2 : (2 * a + b) ^ 2 ≤ (8 * Φ + 2 * C ^ 2) * N := by
    have h1 : (2 * a + b) ^ 2 ≤ 2 * (4 * a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (2 * a - b)]
    have h2 : C ^ 2 * N ^ 2 ≤ C ^ 2 * N := mul_le_mul_of_nonneg_left hNN (sq_nonneg C)
    linarith
  have h1 : (2 * a + b) ^ 2 * S * N ≤ (8 * Φ + 2 * C ^ 2) * N * S * N := by
    have := mul_le_mul_of_nonneg_right hm2 (mul_nonneg hS hN0)
    linarith
  have h2 : b ^ 2 * S ≤ C ^ 2 * N ^ 2 * S := mul_le_mul_of_nonneg_right hb2 hS
  have h3 : η ^ 2 / 2 * (b ^ 2 * S + (2 * a + b) ^ 2 * S * N) ≤
      η ^ 2 / 2 * (C ^ 2 * N ^ 2 * S + (8 * Φ + 2 * C ^ 2) * N * S * N) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : η ^ 2 / 2 * (C ^ 2 * N ^ 2 * S + (8 * Φ + 2 * C ^ 2) * N * S * N) =
      η ^ 2 * S / 2 * (3 * C ^ 2 + 8 * Φ) * N ^ 2 := by ring
  linarith

theorem xdel_bound (C3 X N δ : ℝ) (hC3n : 0 ≤ C3) (hδ0 : 0 < δ) (hN0 : 0 ≤ N)
    (hNδ : N ≤ δ ^ 2) (hX : X ≤ C3 * N ^ 2) : X / δ ≤ C3 * δ * N := by
  rw [div_le_iff₀ hδ0]
  have h : N ^ 2 ≤ δ ^ 2 * N := by
    have := mul_le_mul_of_nonneg_right hNδ hN0
    linarith
  have := mul_le_mul_of_nonneg_left h hC3n
  linarith

theorem tlow_bound (r C3 c1 δ N E T X : ℝ) (hr : 0 < r) (hδ0 : 0 < δ) (hC3n : 0 ≤ C3)
    (hc1 : c1 = 1 + 2 * C3 / r) (hXd : X / δ ≤ C3 * δ * N) (hE : r * N ≤ 2 * E)
    (hT : (1 - δ) * E - X / δ ≤ T) : E * (1 - c1 * δ) ≤ T := by
  have hNE : N ≤ 2 * E / r := by rw [le_div_iff₀ hr]; linarith
  have h1 : C3 * δ * N ≤ C3 * δ * (2 * E / r) :=
    mul_le_mul_of_nonneg_left hNE (by positivity)
  have h2 : C3 * δ * (2 * E / r) = (2 * C3 / r) * δ * E := by field_simp
  have h3 : E * (1 - c1 * δ) = (1 - δ) * E - (2 * C3 / r) * δ * E := by rw [hc1]; ring
  linarith

theorem gup_bound (η C δ N a b G Hr c2 : ℝ) (hη : 0 ≤ η) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hN0 : 0 ≤ N) (hNδ : N ≤ δ ^ 2) (hHr : Hr ≤ (2 + 6 * δ) * N) (hb : |b| ≤ C * N)
    (hG : G = Hr + η / 2 * (2 * a + b) ^ 2) (hc2 : c2 = 16 + 2 * η * C ^ 2) :
    2 * G ≤ (4 + c2 * δ) * (N + η * a ^ 2) := by
  have hab : (2 * a + b) ^ 2 ≤ 4 * (1 + δ) * a ^ 2 + b ^ 2 * (1 + 1 / δ) := by
    have h1 : 4 * a * b ≤ 4 * δ * a ^ 2 + b ^ 2 / δ := by
      have := sq_nonneg (2 * δ * a - b)
      have h2 : 0 ≤ (2 * δ * a - b) ^ 2 / δ := by positivity
      have h3 : (2 * δ * a - b) ^ 2 / δ = 4 * δ * a ^ 2 - 4 * a * b + b ^ 2 / δ := by
        field_simp; ring
      linarith
    have h4 : b ^ 2 * (1 + 1 / δ) = b ^ 2 + b ^ 2 / δ := by ring
    nlinarith
  have hb2 : b ^ 2 ≤ C ^ 2 * N ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rw [sq_abs, mul_pow] at h
    exact h
  have hNd : N ^ 2 ≤ δ ^ 2 * N := by
    have := mul_le_mul_of_nonneg_right hNδ hN0
    linarith
  have hb2δ : b ^ 2 * (1 + 1 / δ) ≤ 2 * C ^ 2 * δ * N := by
    have h1 : b ^ 2 ≤ C ^ 2 * δ ^ 2 * N := by
      have := mul_le_mul_of_nonneg_left hNd (sq_nonneg C)
      linarith
    have h2 : b ^ 2 * (1 + 1 / δ) ≤ C ^ 2 * δ ^ 2 * N * (1 + 1 / δ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : C ^ 2 * δ ^ 2 * N * (1 + 1 / δ) = C ^ 2 * N * (δ ^ 2 + δ) := by
      field_simp
    have h4 : δ ^ 2 ≤ δ := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left (add_le_add_left h4 δ) (mul_nonneg (sq_nonneg C) hN0)
    nlinarith
  have h0 : (2 * a + b) ^ 2 ≤ 4 * (1 + δ) * a ^ 2 + 2 * C ^ 2 * δ * N := by linarith
  have h1 := mul_le_mul_of_nonneg_left h0 hη
  have h2 : 2 * G ≤ (4 + 12 * δ) * N + η * (2 * a + b) ^ 2 := by
    rw [hG]; linarith
  have h3 : 0 ≤ η * a ^ 2 := by positivity
  have h4 : 0 ≤ δ * N := mul_nonneg hδ0.le hN0
  have h5 : 0 ≤ δ * (η * a ^ 2) := mul_nonneg hδ0.le h3
  have h6 : 0 ≤ η * C ^ 2 * δ * (η * a ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hη (sq_nonneg C)) hδ0.le) h3
  rw [hc2]
  linarith

theorem gB_bound (η c2 c5 δ N a B G : ℝ) (hη : 0 ≤ η) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hN0 : 0 ≤ N) (hNδ : N ≤ δ ^ 2) (hc2n : 0 ≤ c2) (hc5 : c5 = 4 + 3 / 2 * c2)
    (hB : B = N - N ^ 2 / 4 + η * a ^ 2) (hG : 2 * G ≤ (4 + c2 * δ) * (N + η * a ^ 2)) :
    2 * G ≤ (4 + c5 * δ) * B ∧ 0 ≤ B := by
  have hN1 : N ≤ 1 / 4 := by nlinarith
  have h3 : 0 ≤ η * a ^ 2 := by positivity
  have hB0 : 0 ≤ B := by rw [hB]; nlinarith
  refine ⟨?_, hB0⟩
  have hNB : N + η * a ^ 2 ≤ (1 + δ) * B := by
    have h1 : N + η * a ^ 2 = B + N ^ 2 / 4 := by rw [hB]; ring
    have hNd : N ^ 2 ≤ δ ^ 2 * N := by
      have := mul_le_mul_of_nonneg_right hNδ hN0
      linarith
    have h2 : N ^ 2 / 4 ≤ δ * B := by
      have hB1 : 15 / 16 * N ≤ B := by rw [hB]; nlinarith
      have : δ ^ 2 * N ≤ δ * (δ * N) := by ring_nf; exact le_refl _
      have h4 : δ * N ≤ δ * (16 / 15 * B) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
      have h5 : δ * (δ * N) ≤ δ * (δ * (16 / 15 * B)) := mul_le_mul_of_nonneg_left h4 hδ0.le
      have h6 : δ * (δ * (16 / 15 * B)) ≤ 1 / 2 * (δ * (16 / 15 * B)) :=
        mul_le_mul_of_nonneg_right hδ2 (by positivity)
      have h7 : 0 ≤ δ * B := mul_nonneg hδ0.le hB0
      nlinarith
    linarith
  have h1 : (4 + c2 * δ) * (N + η * a ^ 2) ≤ (4 + c2 * δ) * ((1 + δ) * B) :=
    mul_le_mul_of_nonneg_left hNB (by positivity)
  have h2 : (4 + c2 * δ) * ((1 + δ) * B) ≤ (4 + c5 * δ) * B := by
    have h : (4 + c2 * δ) * (1 + δ) ≤ 4 + c5 * δ := by
      have : c2 * δ * δ ≤ c2 * δ * (1 / 2) := mul_le_mul_of_nonneg_left hδ2 (by positivity)
      rw [hc5]; nlinarith
    have := mul_le_mul_of_nonneg_right h hB0
    linarith
  linarith

theorem final_real (r η Φ C S : ℝ) (hr : 0 < r) (hη : 0 ≤ η) (hΦ : 0 ≤ Φ)
    (hS : 0 ≤ S) :
    ∃ c δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧ 0 ≤ c ∧
      ∀ δ N a b E B Hr T X G D : ℝ, 0 < δ → δ ≤ δ0 → 0 ≤ N → N ≤ δ ^ 2 → 0 ≤ Hr →
        Hr ≤ (2 + 6 * δ) * N → a ^ 2 ≤ Φ * N → |b| ≤ C * N →
        G = Hr + η / 2 * (2 * a + b) ^ 2 → B = N - N ^ 2 / 4 + η * a ^ 2 →
        X ≤ η ^ 2 / 2 * (b ^ 2 * S + (2 * a + b) ^ 2 * S * N) →
        (1 - δ) * E - X / δ ≤ T → r * B ≤ E → D = 4 * T →
        r * (1 - c * δ) * (2 * G) ≤ (1 + c * δ) * D := by
  obtain ⟨C3, hC3⟩ : ∃ C3 : ℝ, C3 = η ^ 2 * S / 2 * (3 * C ^ 2 + 8 * Φ) := ⟨_, rfl⟩
  have hC3n : 0 ≤ C3 := by rw [hC3]; positivity
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = 1 + 2 * C3 / r := ⟨_, rfl⟩
  have hc1n : 0 ≤ c1 := by rw [hc1]; positivity
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ, c2 = 16 + 2 * η * C ^ 2 := ⟨_, rfl⟩
  have hc2n : 0 ≤ c2 := by rw [hc2]; positivity
  obtain ⟨c5, hc5⟩ : ∃ c5 : ℝ, c5 = 4 + 3 / 2 * c2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = c1 + c5 / 4 := ⟨_, rfl⟩
  have hc5n : 0 ≤ c5 := by rw [hc5]; positivity
  have hcn : 0 ≤ c := by rw [hc]; positivity
  refine ⟨c, min (1 / 2) (1 / (c + 1)), lt_min (by norm_num) (by positivity), min_le_left _ _,
    hcn, ?_⟩
  intro δ N a b E B Hr T X G D hδ0 hδ hN0 hNδ hHr0 hHr ha hb hG hB hX hT hE hD
  have hδ2 : δ ≤ 1 / 2 := hδ.trans (min_le_left _ _)
  have hδc : c * δ ≤ 1 := by
    have h1 : δ ≤ 1 / (c + 1) := hδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hc1δ : c1 * δ ≤ c * δ := by
    have : c1 ≤ c := by rw [hc]; linarith
    exact mul_le_mul_of_nonneg_right this hδ0.le
  have hδsq : δ ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ hδ0.le hδ2 2
    norm_num at this
    linarith
  have hN14 : N ≤ 1 / 4 := le_trans hNδ hδsq
  have hXb := xb_bound η Φ C S a b N X hS hN0 (by linarith) ha hb hX
  rw [← hC3] at hXb
  have hXd := xdel_bound C3 X N δ hC3n hδ0 hN0 hNδ hXb
  have hBN : 15 / 16 * N ≤ B := by
    have h1 : 0 ≤ η * a ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hN14 hN0
    rw [hB]; linarith
  have hB0 : 0 ≤ B := by linarith
  have hrN : r * (15 / 16 * N) ≤ r * B := mul_le_mul_of_nonneg_left hBN hr.le
  have hE0 : 0 ≤ E := le_trans (mul_nonneg hr.le hB0) hE
  have hTlow := tlow_bound r C3 c1 δ N E T X hr hδ0 hC3n hc1 hXd (by linarith) hT
  have hfac : 0 ≤ 1 - c1 * δ := by linarith
  have hTB : r * B * (1 - c1 * δ) ≤ T :=
    le_trans (mul_le_mul_of_nonneg_right hE hfac) hTlow
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (mul_nonneg hr.le hB0) hfac) hTB
  have h2G := gup_bound η C δ N a b G Hr c2 hη hδ0 hδ2 hN0 hNδ hHr hb hG hc2
  obtain ⟨h2G', -⟩ := gB_bound η c2 c5 δ N a B G hη hδ0 hδ2 hN0 hNδ hc2n hc5 hB h2G
  have hD0 : 0 ≤ D := by rw [hD]; linarith
  have hrf : 0 ≤ r * (1 - c1 * δ) := by positivity
  have hstep : r * (1 - c1 * δ) * (2 * G) ≤ (1 + c5 / 4 * δ) * D := by
    have h1 : r * (1 - c1 * δ) * (2 * G) ≤ r * (1 - c1 * δ) * ((4 + c5 * δ) * B) :=
      mul_le_mul_of_nonneg_left h2G' hrf
    have h2 : (1 + c5 / 4 * δ) * (4 * (r * B * (1 - c1 * δ))) ≤ (1 + c5 / 4 * δ) * (4 * T) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : (1 + c5 / 4 * δ) * (4 * (r * B * (1 - c1 * δ))) =
        r * (1 - c1 * δ) * ((4 + c5 * δ) * B) := by ring
    rw [hD]; linarith
  have hG0 : 0 ≤ G := by
    rw [hG]; positivity
  have e1 : r * (1 - c * δ) * (2 * G) ≤ r * (1 - c1 * δ) * (2 * G) := by
    have : 1 - c * δ ≤ 1 - c1 * δ := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hr.le) (by linarith)
  have e2 : (1 + c5 / 4 * δ) * D ≤ (1 + c * δ) * D := by
    have : c5 / 4 * δ ≤ c * δ := by
      have : c5 / 4 ≤ c := by rw [hc]; linarith
      exact mul_le_mul_of_nonneg_right this hδ0.le
    exact mul_le_mul_of_nonneg_right (by linarith) hD0
  linarith

end DGPS.LocalGaussianEndpoint

namespace DGPS.LocalGaussianEndpoint

section hess

variable {d : ℕ} (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem hessian_symm (a b : centeredL2 μ) :
    inner ℝ (densityHessian A μ a) b = inner ℝ a (densityHessian A μ b) := by
  have h1 : inner ℝ (densityHessian A μ a) b =
      inner ℝ a b + inner ℝ (centeredInteraction A μ a) b := by
    rw [← inner_add_left]; rfl
  have h2 : inner ℝ a (densityHessian A μ b) =
      inner ℝ a b + inner ℝ a (centeredInteraction A μ b) := by
    rw [← inner_add_right]; rfl
  rw [h1, h2, centeredInteraction_symmetric]

/-- Variational lower bound for the covariance form. -/
theorem denom_lower (hH : IsCoerciveDensityHessian A μ) (h f : centeredL2 μ) :
    2 * inner ℝ h f - inner ℝ h (densityHessian A μ h) ≤
      inner ℝ f (densityCovariance A μ hH f) := by
  set k := densityCovariance A μ hH f with hk
  have hHk : densityHessian A μ k = f := densityHessian_densityCovariance A μ hH f
  have hpos : 0 ≤ inner ℝ (h - k) (densityHessian A μ (h - k)) := by
    obtain ⟨c, hc, hcoer⟩ := hH
    exact le_trans (by positivity) (hcoer (h - k))
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hHk] at hpos
  have e1 : inner ℝ k (densityHessian A μ h) = inner ℝ h f := by
    rw [← hessian_symm A μ k h, hHk, real_inner_comm]
  have e2 : inner ℝ k f = inner ℝ f k := real_inner_comm _ _
  linarith

end hess

end DGPS.LocalGaussianEndpoint

namespace DGPS.LocalGaussianEndpoint

theorem integrable_cont_mul' {μ : Measure (Torus 1)} {c f : Torus 1 → ℝ} (hc : Continuous c)
    (hf : Integrable f μ) : Integrable (fun x => c x * f x) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact hf.bdd_mul (c := C) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

end DGPS.LocalGaussianEndpoint

namespace DGPS.PositiveRankOne.RankOneModel

/-- The reference probability as a `ProbabilityMeasure`. -/
noncomputable def lgeMu (M : RankOneModel) : ProbabilityMeasure (Torus 1) :=
  ⟨M.ref.measure, M.ref.isProbabilityMeasure⟩

theorem lgeMu_coe (M : RankOneModel) : (M.lgeMu : Measure (Torus 1)) = M.ref.measure := rfl

end DGPS.PositiveRankOne.RankOneModel

namespace DGPS.LocalGaussianEndpoint


section hessrank

variable (M : RankOneModel)

theorem w_split (F : Torus 1 → ℝ) (p : Torus 1 × Torus 1) :
    M.W p.1 p.2 * (F p.1 * F p.2) =
      M.η * ((M.φ p.1 * F p.1) * (M.φ p.2 * F p.2)
        - (1 / 2) * ((M.φ p.1 ^ 2 * F p.1) * F p.2)
        - (1 / 2) * (F p.1 * (M.φ p.2 ^ 2 * F p.2))) := by
  unfold RankOneModel.W; ring

theorem integral_W_form (F : Torus 1 → ℝ) (hF : Integrable F (M.lgeMu : Measure (Torus 1)))
    (h0 : ∫ x, F x ∂(M.lgeMu : Measure (Torus 1)) = 0) :
    ∫ p, M.W p.1 p.2 * (F p.1 * F p.2) ∂((M.lgeMu : Measure (Torus 1)).prod M.lgeMu) =
      M.η * (∫ x, M.φ x * F x ∂(M.lgeMu : Measure (Torus 1))) ^ 2 := by
  have i1 : Integrable (fun x => M.φ x * F x) (M.lgeMu : Measure (Torus 1)) :=
    integrable_cont_mul' M.φ_cont hF
  have i2 : Integrable (fun x => M.φ x ^ 2 * F x) (M.lgeMu : Measure (Torus 1)) :=
    integrable_cont_mul' (M.φ_cont.pow 2) hF
  have j1 := i1.mul_prod i1
  have j2 := i2.mul_prod hF
  have j3 := hF.mul_prod i2
  simp_rw [w_split M F]
  rw [integral_const_mul]
  congr 1
  have k2 : Integrable (fun z : Torus 1 × Torus 1 => (1 / 2 : ℝ) * (M.φ z.1 ^ 2 * F z.1 * F z.2))
      ((M.lgeMu : Measure (Torus 1)).prod M.lgeMu) := j2.const_mul _
  have k3 : Integrable (fun z : Torus 1 × Torus 1 => (1 / 2 : ℝ) * (F z.1 * (M.φ z.2 ^ 2 * F z.2)))
      ((M.lgeMu : Measure (Torus 1)).prod M.lgeMu) := j3.const_mul _
  have k12 : Integrable (fun z : Torus 1 × Torus 1 => M.φ z.1 * F z.1 * (M.φ z.2 * F z.2) -
      (1 / 2 : ℝ) * (M.φ z.1 ^ 2 * F z.1 * F z.2)) ((M.lgeMu : Measure (Torus 1)).prod M.lgeMu) :=
    j1.sub k2
  rw [integral_sub k12 k3, integral_sub j1 k2, integral_const_mul, integral_const_mul]
  rw [integral_prod_mul (fun x => M.φ x * F x) (fun x => M.φ x * F x),
    integral_prod_mul (fun x => M.φ x ^ 2 * F x) F, integral_prod_mul F (fun x => M.φ x ^ 2 * F x), h0]
  ring

theorem inner_hessian_rankOne (f : centeredL2 M.lgeMu) :
    inner ℝ f (densityHessian M.data M.lgeMu f) = ‖f‖ ^ 2 +
      M.η * (∫ x, M.φ x * ((f : Lp ℝ 2 (M.lgeMu : Measure (Torus 1))) : Torus 1 → ℝ) x
        ∂(M.lgeMu : Measure (Torus 1))) ^ 2 := by
  rw [inner_densityHessian]
  congr 1
  exact integral_W_form M _ (integrable_lp M.lgeMu _) f.2

theorem coercive : IsCoerciveDensityHessian M.data M.lgeMu := by
  refine ⟨1, one_pos, fun f => ?_⟩
  rw [inner_hessian_rankOne, one_mul]
  have := mul_nonneg M.η_nonneg (sq_nonneg (∫ x, M.φ x * ((f : Lp ℝ 2 (M.lgeMu : Measure (Torus 1))) : Torus 1 → ℝ) x
        ∂(M.lgeMu : Measure (Torus 1))))
  linarith

end hessrank


section stage1

variable (M : RankOneModel)

theorem mul_smooth_H1 {v w : Torus 1 → ℝ} {h : Torus 1 → Tangent 1}
    (hv : IsSmoothPeriodic v) (hw : IsWeakGradient w h) :
    IsWeakGradient (fun x => v x * w x) (fun x => w x • smoothGrad v x + v x • h x) where
  memLp := by
    have := memLp_mul_top (a := v) hv.memLp_top hw.memLp
    simpa [mul_comm] using this
  memLp_grad := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      hv.continuous_smoothGrad.continuousOn
    have h1 : MemLp (fun x => w x • smoothGrad v x) 2 (haar 1) := by
      refine hw.memLp.of_le_mul (c := C) (hw.memLp.aestronglyMeasurable.smul
        hv.continuous_smoothGrad.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC x (Set.mem_univ _)) (norm_nonneg _)
    exact h1.add (memLp_smul_top hv.memLp_top hw.memLp_grad)
  ibp φ hφ j := by
    have hvφ : IsSmoothPeriodic (fun x => v x * φ x) := hv.mul hφ
    have e1 := hw.ibp _ hvφ j
    have hwt := hw.memLp
    have hhj : MemLp (fun x => h x j) 2 (haar 1) := memLp_coord hw.memLp_grad j
    have s1 : IsSmoothPeriodic (fun x => v x * coordPartial j φ x) :=
      hv.mul (hφ.isSmoothPeriodic_coordPartial j)
    have s2 : IsSmoothPeriodic (fun x => coordPartial j v x * φ x) :=
      (hv.isSmoothPeriodic_coordPartial j).mul hφ
    have i1 := integrable_mul_of_memLp_two hwt s1.memLp_top
    have i2 := integrable_mul_of_memLp_two hwt s2.memLp_top
    have i3 := integrable_mul_of_memLp_two hhj hvφ.memLp_top
    simp_rw [coordPartial_mul hv hφ, mul_add] at e1
    rw [integral_add i1 i2] at e1
    have eL : (fun x => v x * w x * coordPartial j φ x)
        = fun x => w x * (v x * coordPartial j φ x) := by funext x; ring
    have eR : (fun x => (w x • smoothGrad v x + v x • h x) j * φ x)
        = fun x => w x * (coordPartial j v x * φ x) + h x j * (v x * φ x) := by
      funext x; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, smoothGrad_apply]; ring
    rw [eL, eR, integral_add i2 i3]
    linarith

/-- The weight `w = q^{-1/2}`. -/
noncomputable def wf (x : Torus 1) : ℝ := Real.exp (-(1 / 2) * Real.log (M.q x))

theorem wf_pos (x : Torus 1) : 0 < wf M x := Real.exp_pos _

theorem wf_sq_mul (x : Torus 1) : wf M x ^ 2 * M.q x = 1 := by
  unfold wf
  rw [← Real.exp_nat_mul]
  have : ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log (M.q x)) = - Real.log (M.q x) := by push_cast; ring
  rw [this, Real.exp_neg, Real.exp_log (M.q_pos x)]
  exact inv_mul_cancel₀ (M.q_pos x).ne'

theorem wf_smooth : IsSmoothPeriodic (wf M) := by
  have : ContDiffOn ℝ ∞ (fun t : ℝ => Real.exp (-(1 / 2) * Real.log t)) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => -(1 / 2) * Real.log t) (Set.Ioi 0) :=
      contDiffOn_const.mul (Real.contDiffOn_log.mono fun _ ht => (Set.mem_Ioi.mp ht).ne')
    exact Real.contDiff_exp.comp_contDiffOn h1
  exact RelativeFisher.isSmoothPeriodic_comp M.q_smooth this M.q_pos

theorem dlogq_eq (x : Torus 1) : M.dlogq x = (M.q x)⁻¹ * coordPartial 0 M.q x := by
  unfold RankOneModel.dlogq
  exact RelativeFisher.coordPartial_comp M.q_smooth (φ := Real.log) (D := fun t => t⁻¹)
    (fun t ht => Real.hasDerivAt_log ht.ne') M.q_pos 0 x

theorem wf_deriv (x : Torus 1) : coordPartial 0 (wf M) x = -(1 / 2) * wf M x * M.dlogq x := by
  have h := RelativeFisher.coordPartial_comp M.q_smooth
    (φ := fun t : ℝ => Real.exp (-(1 / 2) * Real.log t))
    (D := fun t => Real.exp (-(1 / 2) * Real.log t) * (-(1 / 2) * t⁻¹))
    (fun t ht => by
      have h1 := (Real.hasDerivAt_log ht.ne').const_mul (-(1 / 2) : ℝ)
      exact h1.exp) M.q_pos 0 x
  show coordPartial 0 (fun y => Real.exp (-(1 / 2) * Real.log (M.q y))) x = _
  rw [h, dlogq_eq]
  unfold wf
  ring

end stage1

section moments

variable {α : Type*} [MeasurableSpace α] (ν : Measure α)

theorem memLp_bdd_mul {f g : α → ℝ} {C : ℝ} (hf : MemLp f 2 ν) (hg : AEStronglyMeasurable g ν)
    (hb : ∀ x, |g x| ≤ C) : MemLp (fun x => g x * f x) 2 ν := by
  refine hf.of_le_mul (c := C) (hg.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)

theorem memLp_bdd [IsFiniteMeasure ν] {g : α → ℝ} {C : ℝ} (hg : AEStronglyMeasurable g ν)
    (hb : ∀ x, |g x| ≤ C) : MemLp g 2 ν :=
  memLp_of_bounded (a := -C) (b := C) (Eventually.of_forall fun x => abs_le.1 (hb x)) hg 2

theorem sq_integral_le [IsProbabilityMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  have h := ProbabilityTheory.variance_nonneg f ν
  rw [ProbabilityTheory.variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

theorem moment_facts [IsProbabilityMeasure ν] (V W φ ψ : α → ℝ) (η Cφ Cψ δ : ℝ)
    (hδ : 0 < δ)
    (hV : MemLp V 2 ν) (hW : MemLp W 2 ν) (hφm : AEStronglyMeasurable φ ν)
    (hψm : AEStronglyMeasurable ψ ν) (hφ : ∀ x, |φ x| ≤ Cφ) (hψ : ∀ x, |ψ x| ≤ Cψ)
    (hVδ : ∀ x, |V x| ≤ δ) (N a b E T X : ℝ)
    (hN : N = ∫ x, V x ^ 2 ∂ν) (ha : a = ∫ x, V x * φ x ∂ν) (hb : b = ∫ x, V x ^ 2 * φ x ∂ν)
    (hE : E = ∫ x, (W x + η * a * ψ x) ^ 2 ∂ν)
    (hT : T = ∫ x, (W x + η * (2 * a + b) / 2 * (1 + V x) * ψ x) ^ 2 ∂ν)
    (hX : X = ∫ x, (η * b / 2 * ψ x + η * (2 * a + b) / 2 * V x * ψ x) ^ 2 ∂ν) :
    0 ≤ N ∧ N ≤ δ ^ 2 ∧ a ^ 2 ≤ Cφ ^ 2 * N ∧ |b| ≤ Cφ * N ∧
      X ≤ η ^ 2 / 2 * (b ^ 2 * Cψ ^ 2 + (2 * a + b) ^ 2 * Cψ ^ 2 * N) ∧
      (1 - δ) * E - X / δ ≤ T := by
  have hV2 : Integrable (fun x => V x ^ 2) ν := hV.integrable_sq
  have hVφ : MemLp (fun x => φ x * V x) 2 ν := memLp_bdd_mul ν hV hφm hφ
  have hVφ' : MemLp (fun x => V x * φ x) 2 ν := by
    simpa only [mul_comm] using hVφ
  have hVψ : MemLp (fun x => ψ x * V x) 2 ν := memLp_bdd_mul ν hV hψm hψ
  have hψ2 : MemLp ψ 2 ν := memLp_bdd ν hψm hψ
  have hCφ : 0 ≤ Cφ := by
    have : Nonempty α := nonempty_of_isProbabilityMeasure ν
    exact le_trans (abs_nonneg _) (hφ (Classical.arbitrary _))
  have h1 : 0 ≤ N := by rw [hN]; exact integral_nonneg fun x => sq_nonneg _
  have h2 : N ≤ δ ^ 2 := by
    rw [hN]
    calc ∫ x, V x ^ 2 ∂ν ≤ ∫ _x, δ ^ 2 ∂ν :=
          integral_mono hV2 (integrable_const _) fun x => by
            have := hVδ x
            have h0 := abs_nonneg (V x)
            calc V x ^ 2 = |V x| ^ 2 := (sq_abs _).symm
              _ ≤ δ ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = δ ^ 2 := by simp
  have h3 : a ^ 2 ≤ Cφ ^ 2 * N := by
    have c1 := sq_integral_le ν hVφ'
    rw [← ha] at c1
    refine c1.trans ?_
    rw [hN, ← integral_const_mul]
    refine integral_mono hVφ'.integrable_sq (hV2.const_mul _) fun x => ?_
    have := hφ x
    calc (V x * φ x) ^ 2 = V x ^ 2 * φ x ^ 2 := by ring
      _ ≤ V x ^ 2 * Cφ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc φ x ^ 2 = |φ x| ^ 2 := (sq_abs _).symm
            _ ≤ Cφ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = Cφ ^ 2 * V x ^ 2 := by ring
  have h4 : |b| ≤ Cφ * N := by
    rw [hb, hN, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hV2.const_mul _) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hφ x) (sq_nonneg _)
  have hZ : MemLp (fun x => η * b / 2 * ψ x + η * (2 * a + b) / 2 * V x * ψ x) 2 ν := by
    have := (hψ2.const_mul (η * b / 2)).add (hVψ.const_mul (η * (2 * a + b) / 2))
    refine this.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  have hxL : MemLp (fun x => W x + η * a * ψ x) 2 ν := hW.add (hψ2.const_mul (η * a))
  have h5 : X ≤ η ^ 2 / 2 * (b ^ 2 * Cψ ^ 2 + (2 * a + b) ^ 2 * Cψ ^ 2 * N) := by
    have hrhs : ∫ x, η ^ 2 / 2 * (b ^ 2 * Cψ ^ 2 + (2 * a + b) ^ 2 * Cψ ^ 2 * V x ^ 2) ∂ν =
        η ^ 2 / 2 * (b ^ 2 * Cψ ^ 2 + (2 * a + b) ^ 2 * Cψ ^ 2 * N) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hV2.const_mul _), integral_const,
        integral_const_mul, ← hN]
      simp
    rw [hX, ← hrhs]
    refine integral_mono hZ.integrable_sq
      (((integrable_const _).add (hV2.const_mul _)).const_mul _) fun x => ?_
    have hp : ψ x ^ 2 ≤ Cψ ^ 2 :=
      calc ψ x ^ 2 = |ψ x| ^ 2 := (sq_abs _).symm
        _ ≤ Cψ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hψ x) 2
    set P := η * b / 2 * ψ x with hP
    set Q := η * (2 * a + b) / 2 * V x * ψ x with hQ
    have h6 : (P + Q) ^ 2 ≤ 2 * P ^ 2 + 2 * Q ^ 2 := by nlinarith [sq_nonneg (P - Q)]
    have h7 : 2 * P ^ 2 + 2 * Q ^ 2 =
        η ^ 2 / 2 * (b ^ 2 * ψ x ^ 2 + (2 * a + b) ^ 2 * ψ x ^ 2 * V x ^ 2) := by
      rw [hP, hQ]; ring
    have h8 : b ^ 2 * ψ x ^ 2 + (2 * a + b) ^ 2 * ψ x ^ 2 * V x ^ 2 ≤
        b ^ 2 * Cψ ^ 2 + (2 * a + b) ^ 2 * Cψ ^ 2 * V x ^ 2 := by
      have i1 := mul_le_mul_of_nonneg_left hp (sq_nonneg b)
      have i2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (sq_nonneg (2 * a + b))) (sq_nonneg (V x))
      linarith
    have h9 := mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ η ^ 2 / 2)
    linarith
  have hTint : Integrable (fun x => (W x + η * (2 * a + b) / 2 * (1 + V x) * ψ x) ^ 2) ν := by
    have := (hxL.add hZ).integrable_sq
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    congr 1; ring
  have h10 : (1 - δ) * E - X / δ ≤ T := by
    have e1 : (1 - δ) * E - X / δ =
        ∫ x, ((1 - δ) * (W x + η * a * ψ x) ^ 2 -
          (η * b / 2 * ψ x + η * (2 * a + b) / 2 * V x * ψ x) ^ 2 / δ) ∂ν := by
      rw [integral_sub (hxL.integrable_sq.const_mul _) (hZ.integrable_sq.div_const _),
        integral_const_mul, integral_div, hE, hX]
    rw [e1, hT]
    refine integral_mono ((hxL.integrable_sq.const_mul _).sub (hZ.integrable_sq.div_const _))
      hTint fun x => ?_
    set p := W x + η * a * ψ x with hp
    set q := η * b / 2 * ψ x + η * (2 * a + b) / 2 * V x * ψ x with hq
    have hpq : W x + η * (2 * a + b) / 2 * (1 + V x) * ψ x = p + q := by rw [hp, hq]; ring
    simp only []
    rw [hpq]
    have i1 : 0 ≤ (δ * p + q) ^ 2 / δ := by positivity
    have i2 : (δ * p + q) ^ 2 / δ = δ * p ^ 2 + 2 * p * q + q ^ 2 / δ := by
      field_simp
      ring
    nlinarith
  exact ⟨h1, h2, h3, h4, h5, h10⟩

end moments

end DGPS.LocalGaussianEndpoint

namespace DGPS.LocalGaussianEndpoint

section bridge

variable (M : RankOneModel)

theorem integral_ref_eq (f : Torus 1 → ℝ) :
    ∫ x, f x ∂M.ref.measure = ∫ x, M.q x * f x ∂haar 1 := by
  show ∫ x, f x ∂(haar 1).withDensity (fun x => ENNReal.ofReal (M.q x)) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (M.q_pos x).le]
  · exact M.q_cont.measurable.ennreal_ofReal.aemeasurable
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem wf_mul_sqrt (x : Torus 1) : wf M x * Real.sqrt (M.q x) = 1 := by
  have h1 := wf_sq_mul M x
  have h2 : Real.sqrt (M.q x) ^ 2 = M.q x := Real.sq_sqrt (M.q_pos x).le
  have h3 : (wf M x * Real.sqrt (M.q x)) ^ 2 = 1 := by rw [mul_pow, h2, h1]
  have h4 : 0 < wf M x * Real.sqrt (M.q x) := mul_pos (wf_pos M x) (Real.sqrt_pos.2 (M.q_pos x))
  nlinarith

/-- The relative square root minus one. -/
noncomputable def Vf (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ := wf M x * ρ.sqrt x - 1

/-- The weak gradient of `√ρ` (first coordinate). -/
noncomputable def ug (ρ : AbsoluteDensity 1) : Torus 1 → Tangent 1 := weakGradient ρ.sqrt ρ.sqrt_mem

/-- First coordinate of the gradient of `wf * √ρ`. -/
noncomputable def Wf (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  ρ.sqrt x * coordPartial 0 (wf M) x + wf M x * ug ρ x 0

theorem hwp (ρ : AbsoluteDensity 1) :
    IsWeakGradient (fun x => wf M x * ρ.sqrt x)
      (fun x => ρ.sqrt x • smoothGrad (wf M) x + wf M x • ug ρ x) :=
  mul_smooth_H1 (wf_smooth M) (isWeakGradient_weakGradient ρ.sqrt_mem)

theorem hwp_coord (ρ : AbsoluteDensity 1) (x : Torus 1) :
    (ρ.sqrt x • smoothGrad (wf M) x + wf M x • ug ρ x) 0 = Wf M ρ x := by
  simp [Wf, smoothGrad_apply]

theorem sqrt_sq_eq (ρ : AbsoluteDensity 1) (x : Torus 1) :
    ρ.sqrt x ^ 2 = M.q x * (1 + Vf M ρ x) ^ 2 := by
  unfold Vf
  linear_combination (-(ρ.sqrt x ^ 2)) * wf_sq_mul M x

theorem memLp_wu (ρ : AbsoluteDensity 1) :
    MemLp (fun x => wf M x * ρ.sqrt x) 2 (M.lgeMu : Measure (Torus 1)) :=
  M.ref.memLp_measure_iff.2 (hwp M ρ).memLp

theorem memLp_Vf (ρ : AbsoluteDensity 1) :
    MemLp (Vf M ρ) 2 (M.lgeMu : Measure (Torus 1)) :=
  (memLp_wu M ρ).sub (memLp_const 1)

theorem memLp_Wf (ρ : AbsoluteDensity 1) :
    MemLp (Wf M ρ) 2 (M.lgeMu : Measure (Torus 1)) := by
  have h := M.ref.memLp_measure_iff.2 (memLp_coord (hwp M ρ).memLp_grad 0)
  exact h.ae_eq (Eventually.of_forall fun x => hwp_coord M ρ x)

theorem mass_V (ρ : AbsoluteDensity 1) :
    ∫ x, (1 + Vf M ρ x) ^ 2 ∂(M.lgeMu : Measure (Torus 1)) = 1 := by
  rw [M.lgeMu_coe, integral_ref_eq]
  have : ∀ x, M.q x * (1 + Vf M ρ x) ^ 2 = ρ.sqrt x ^ 2 := fun x => (sqrt_sq_eq M ρ x).symm
  simp_rw [this]
  exact ρ.mass_one

theorem integral_V (ρ : AbsoluteDensity 1) :
    ∫ x, Vf M ρ x ∂(M.lgeMu : Measure (Torus 1)) =
      -(∫ x, Vf M ρ x ^ 2 ∂(M.lgeMu : Measure (Torus 1))) / 2 := by
  have h := mass_V M ρ
  have hV : Integrable (Vf M ρ) (M.lgeMu : Measure (Torus 1)) :=
    (memLp_Vf M ρ).integrable one_le_two
  have hV2 : Integrable (fun x => Vf M ρ x ^ 2) (M.lgeMu : Measure (Torus 1)) :=
    (memLp_Vf M ρ).integrable_sq
  have e : ∀ x, (1 + Vf M ρ x) ^ 2 = 1 + 2 * Vf M ρ x + Vf M ρ x ^ 2 := fun x => by ring
  simp_rw [e] at h
  have i1 : Integrable (fun x => (1 : ℝ) + 2 * Vf M ρ x) (M.lgeMu : Measure (Torus 1)) :=
    (integrable_const _).add (hV.const_mul 2)
  have s1 := integral_add i1 hV2
  have s2 := integral_add (integrable_const (1 : ℝ)) (hV.const_mul 2)
  rw [integral_const_mul] at s2
  simp only [integral_const] at s2
  have hp : (M.lgeMu : Measure (Torus 1)).real Set.univ = 1 := by simp
  simp only [hp, smul_eq_mul, one_mul] at s2
  have hh : ∫ x, (1 + 2 * Vf M ρ x + Vf M ρ x ^ 2) ∂(M.lgeMu : Measure (Torus 1)) =
      1 + 2 * ∫ x, Vf M ρ x ∂(M.lgeMu : Measure (Torus 1)) +
        ∫ x, Vf M ρ x ^ 2 ∂(M.lgeMu : Measure (Torus 1)) := by
    rw [s1, s2]
  linarith

theorem bdd_cont {f : Torus 1 → ℝ} (hf : Continuous f) : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have := hC x (Set.mem_univ x)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem integrable_Vphi (ρ : AbsoluteDensity 1) :
    Integrable (fun x => Vf M ρ x * M.φ x) (M.lgeMu : Measure (Torus 1)) :=
  (integrable_cont_mul' M.φ_cont ((memLp_Vf M ρ).integrable one_le_two)).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

theorem integrable_V2phi (ρ : AbsoluteDensity 1) :
    Integrable (fun x => Vf M ρ x ^ 2 * M.φ x) (M.lgeMu : Measure (Torus 1)) :=
  (integrable_cont_mul' M.φ_cont (memLp_Vf M ρ).integrable_sq).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

theorem integral_phi_lge : ∫ x, M.φ x ∂(M.lgeMu : Measure (Torus 1)) = 0 := by
  rw [M.lgeMu_coe, integral_ref_eq]
  simp_rw [mul_comm (M.q _)]
  exact M.φ_centered

theorem m_eq (ρ : AbsoluteDensity 1) :
    ∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1)) =
      2 * ∫ x, Vf M ρ x * M.φ x ∂(M.lgeMu : Measure (Torus 1)) +
        ∫ x, Vf M ρ x ^ 2 * M.φ x ∂(M.lgeMu : Measure (Torus 1)) := by
  rw [RankOneModel.integral_densityMeasure]
  have h1 : ∀ x, ρ.density x * M.φ x = M.q x * ((1 + Vf M ρ x) ^ 2 * M.φ x) := fun x => by
    simp only [AbsoluteDensity.density]; rw [sqrt_sq_eq M ρ x]; ring
  simp_rw [h1]
  rw [← integral_ref_eq M (fun x => (1 + Vf M ρ x) ^ 2 * M.φ x), ← M.lgeMu_coe]
  have e : ∀ x, (1 + Vf M ρ x) ^ 2 * M.φ x =
      M.φ x + (2 * (Vf M ρ x * M.φ x)) + Vf M ρ x ^ 2 * M.φ x := fun x => by ring
  simp_rw [e]
  have i1 : Integrable M.φ (M.lgeMu : Measure (Torus 1)) :=
    M.φ_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 := (integrable_Vphi M ρ).const_mul 2
  have i12 : Integrable (fun x => M.φ x + 2 * (Vf M ρ x * M.φ x))
      (M.lgeMu : Measure (Torus 1)) := i1.add i2
  have s1 := integral_add i12 (integrable_V2phi M ρ)
  have s2 := integral_add i1 i2
  rw [s1, s2, integral_const_mul, integral_phi_lge]
  ring

theorem q_V2_eq (ρ : AbsoluteDensity 1) (x : Torus 1) :
    M.q x * Vf M ρ x ^ 2 = (ρ.sqrt x - Real.sqrt (M.q x)) ^ 2 := by
  have e1 : Real.sqrt (M.q x) * Vf M ρ x = ρ.sqrt x - Real.sqrt (M.q x) := by
    unfold Vf; linear_combination (ρ.sqrt x) * wf_mul_sqrt M x
  have h2 : Real.sqrt (M.q x) ^ 2 = M.q x := Real.sq_sqrt (M.q_pos x).le
  rw [← e1, mul_pow, h2]

theorem integrable_q_V2 (ρ : AbsoluteDensity 1) :
    Integrable (fun x => M.q x * Vf M ρ x ^ 2) (haar 1) := by
  have h := (ρ.memLp_sqrt.sub M.sqrt_smooth.isWeakGradient.memLp).integrable_sq
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  exact (q_V2_eq M ρ x).symm

theorem entropy_bounds (ρ : AbsoluteDensity 1) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hV : ∀ x, |Vf M ρ x| ≤ δ) :
    0 ≤ (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal ∧
    (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal ≤
      (2 + 6 * δ) * ∫ x, Vf M ρ x ^ 2 ∂(M.lgeMu : Measure (Torus 1)) := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  obtain ⟨hA1, -, hA3, hA4⟩ := absoluteDensity_entropy_finite ρ
  rw [M.entropy_ref_eq _ hA3, hA4, RankOneModel.integral_densityMeasure]
  have iB : Integrable (fun x => ρ.density x * Real.log (M.q x)) (haar 1) :=
    (integrable_cont_mul' M.log_smooth.continuous_torus ρ.integrable_density).congr
      (Eventually.of_forall fun x => mul_comm _ _)
  rw [← integral_sub hA1 iB]
  have iq : Integrable M.q (haar 1) := M.q_cont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have iR : Integrable (fun x => M.q x * ((2 + 6 * δ) * Vf M ρ x ^ 2) + ρ.density x - M.q x)
      (haar 1) :=
    (((integrable_q_V2 M ρ).const_mul (2 + 6 * δ)).congr
      (Eventually.of_forall fun x => by simp only []; ring)).add ρ.integrable_density |>.sub iq
  have hmono := integral_mono (hA1.sub iB) iR (fun x => by
    have hv := hV x
    have hv2 : |Vf M ρ x| ≤ 1 / 2 := hv.trans hδ2
    have hq := M.q_pos x
    have hs : 0 < 1 + Vf M ρ x := by linarith [(abs_le.1 hv2).1]
    have hpsi := psi_bound (Vf M ρ x) hv2
    have hV2 : 0 ≤ Vf M ρ x ^ 2 := sq_nonneg _
    have hb : Vf M ρ x ^ 2 * |Vf M ρ x| ≤ Vf M ρ x ^ 2 * δ := mul_le_mul_of_nonneg_left hv hV2
    have hd : ρ.density x = M.q x * (1 + Vf M ρ x) ^ 2 := by
      simp only [AbsoluteDensity.density]; exact sqrt_sq_eq M ρ x
    have hlog : Real.log (ρ.density x) = Real.log (M.q x) + Real.log ((1 + Vf M ρ x) ^ 2) := by
      rw [hd, Real.log_mul hq.ne' (pow_pos hs 2).ne']
    have key : ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (M.q x) =
        M.q x * ((1 + Vf M ρ x) ^ 2 * Real.log ((1 + Vf M ρ x) ^ 2)) := by
      rw [hlog, hd]; ring
    show ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (M.q x) ≤ _
    rw [key]
    have : (1 + Vf M ρ x) ^ 2 * Real.log ((1 + Vf M ρ x) ^ 2) ≤
        (2 + 6 * δ) * Vf M ρ x ^ 2 + (1 + Vf M ρ x) ^ 2 - 1 := by nlinarith
    rw [hd]
    nlinarith [mul_le_mul_of_nonneg_left this hq.le])
  refine hmono.trans (le_of_eq ?_)
  have e : ∫ x, (M.q x * ((2 + 6 * δ) * Vf M ρ x ^ 2) + ρ.density x - M.q x) ∂haar 1 =
      (2 + 6 * δ) * ∫ x, M.q x * Vf M ρ x ^ 2 ∂haar 1 + ∫ x, ρ.density x ∂haar 1 -
        ∫ x, M.q x ∂haar 1 := by
    have i1 : Integrable (fun x => M.q x * ((2 + 6 * δ) * Vf M ρ x ^ 2)) (haar 1) :=
      ((integrable_q_V2 M ρ).const_mul (2 + 6 * δ)).congr
        (Eventually.of_forall fun x => by simp only []; ring)
    have i1' : Integrable (fun x => M.q x * ((2 + 6 * δ) * Vf M ρ x ^ 2) + ρ.density x)
        (haar 1) := i1.add ρ.integrable_density
    have s1 := integral_sub i1' iq
    have s2 := integral_add i1 ρ.integrable_density
    rw [s1, s2]
    congr 2
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only []; ring)
  rw [e, ρ.integral_density, M.q_mass, M.lgeMu_coe, integral_ref_eq]
  ring


theorem pt_dissip (ρ : AbsoluteDensity 1) (K : ℝ) (x : Torus 1) :
    (2 * ug ρ x 0 + ρ.sqrt x * (-M.dlogq x + K * M.dφ x)) ^ 2 =
      4 * M.q x * (Wf M ρ x + K / 2 * (1 + Vf M ρ x) * M.dφ x) ^ 2 := by
  have hw := wf_sq_mul M x
  unfold Wf Vf
  rw [wf_deriv]
  linear_combination (-(2 * ug ρ x 0 - ρ.sqrt x * M.dlogq x + K * ρ.sqrt x * M.dφ x) ^ 2) * hw

theorem integral_dissip (ρ : AbsoluteDensity 1) (K : ℝ) :
    ∫ x, (2 * ug ρ x 0 + ρ.sqrt x * (-M.dlogq x + K * M.dφ x)) ^ 2 ∂haar 1 =
      4 * ∫ x, (Wf M ρ x + K / 2 * (1 + Vf M ρ x) * M.dφ x) ^ 2
        ∂(M.lgeMu : Measure (Torus 1)) := by
  rw [M.lgeMu_coe, integral_ref_eq, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only []
  rw [pt_dissip]; ring

/-- Moments. -/
noncomputable def Nf (ρ : AbsoluteDensity 1) : ℝ :=
  ∫ x, Vf M ρ x ^ 2 ∂(M.lgeMu : Measure (Torus 1))
noncomputable def af (ρ : AbsoluteDensity 1) : ℝ :=
  ∫ x, Vf M ρ x * M.φ x ∂(M.lgeMu : Measure (Torus 1))
noncomputable def bf (ρ : AbsoluteDensity 1) : ℝ :=
  ∫ x, Vf M ρ x ^ 2 * M.φ x ∂(M.lgeMu : Measure (Torus 1))

theorem dissip_eq (b : AbsoluteDrift M.data) (ρ : AbsoluteDensity 1) :
    (speciesDissipation M.data b (SpeciesFamily.single ρ)).toReal =
      4 * ∫ x, (Wf M ρ x + M.η * (2 * af M ρ + bf M ρ) / 2 * (1 + Vf M ρ x) * M.dφ x) ^ 2
        ∂(M.lgeMu : Measure (Torus 1)) := by
  obtain ⟨-, -, -, h4⟩ := DGPS.Examples.positive_rank_one_scalar_case M b ρ
  have hm := m_eq M ρ
  have hd := (M.dissipation_integral (isWeakGradient_weakGradient ρ.sqrt_mem)
    (M.η * (2 * af M ρ + bf M ρ))).2.2
  rw [← integral_dissip M ρ (M.η * (2 * af M ρ + bf M ρ))]
  unfold af bf
  rw [h4, RankOneModel.fisher_eq M ρ, ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _),
    hm, RankOneModel.integral_densityMeasure, RankOneModel.integral_densityMeasure]
  unfold af bf at hd
  have hρ : ∀ x, ρ.density x = ρ.sqrt x ^ 2 := fun x => rfl
  simp only [hρ]
  refine Eq.trans ?_ hd.symm
  ring

end bridge

section cm

variable {α : Type*} [MeasurableSpace α] (ν : Measure α)

theorem centered_moments [IsProbabilityMeasure ν] (V φ : α → ℝ) (C : ℝ) (hV : MemLp V 2 ν)
    (hφm : AEStronglyMeasurable φ ν) (hφ : ∀ x, |φ x| ≤ C) (N a c : ℝ)
    (hN : N = ∫ x, V x ^ 2 ∂ν) (hVi : ∫ x, V x ∂ν = -N / 2) (hφ0 : ∫ x, φ x ∂ν = 0)
    (ha : a = ∫ x, V x * φ x ∂ν) :
    (∫ x, (V x + N / 2 + c * φ x) ∂ν = 0) ∧
    (∫ x, (V x + N / 2) * (V x + N / 2 + c * φ x) ∂ν = N - N ^ 2 / 4 + c * a) ∧
    (∫ x, (V x + N / 2) ^ 2 ∂ν = N - N ^ 2 / 4) ∧
    (∫ x, φ x * (V x + N / 2) ∂ν = a) := by
  have h2 : Integrable (fun x => V x ^ 2) ν := hV.integrable_sq
  have h1 : Integrable V ν := hV.integrable one_le_two
  have h4 : Integrable φ ν := (memLp_bdd ν hφm hφ).integrable one_le_two
  have h3 : Integrable (fun x => V x * φ x) ν := by
    have := (memLp_bdd_mul ν hV hφm hφ).integrable one_le_two
    exact this.congr (Eventually.of_forall fun x => mul_comm _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_add (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop)]
    simp [integral_const_mul, hVi, hφ0]
    ring
  · have e : ∀ x, (V x + N / 2) * (V x + N / 2 + c * φ x) =
        V x ^ 2 + N * V x + N ^ 2 / 4 + c * (V x * φ x) + (c * N / 2) * φ x := fun x => by ring
    simp_rw [e]
    rw [integral_add (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop),
      integral_add (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop)]
    simp [integral_const_mul, ← hN, hVi, ← ha, hφ0]
    ring
  · have e : ∀ x, (V x + N / 2) ^ 2 = V x ^ 2 + N * V x + N ^ 2 / 4 := fun x => by ring
    simp_rw [e]
    rw [integral_add (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop)]
    simp [integral_const_mul, ← hN, hVi]
    ring
  · have e : ∀ x, φ x * (V x + N / 2) = V x * φ x + (N / 2) * φ x := fun x => by ring
    simp_rw [e]
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [integral_const_mul, ← ha, hφ0]

end cm

section part3

variable (M : RankOneModel)

/-- Test function value. -/
noncomputable def tfn (ρ : AbsoluteDensity 1) (c k : ℝ) (x : Torus 1) : ℝ :=
  wf M x * ρ.sqrt x + c * M.φ x - k

/-- Test function gradient. -/
noncomputable def tgrad (ρ : AbsoluteDensity 1) (c : ℝ) (x : Torus 1) : Tangent 1 :=
  (ρ.sqrt x • smoothGrad (wf M) x + wf M x • ug ρ x) + c • smoothGrad M.φ x

theorem tweak (ρ : AbsoluteDensity 1) (c k : ℝ) :
    IsWeakGradient (tfn M ρ c k) (tgrad M ρ c) :=
  ((hwp M ρ).add (M.φ_smooth.isWeakGradient.smul c)).sub_const k

/-- The test function in the weighted weak form domain. -/
noncomputable def ftest (ρ : AbsoluteDensity 1) (c k : ℝ) : WeakH1Test M.lgeMu where
  fn := tfn M ρ c k
  grad := tgrad M ρ c
  isWeak := (isMeasureWeakGradient_iff M.ref).2
    ((isWeightedWeakGradient_iff M.ref).2 (tweak M ρ c k))

theorem tgrad_coord (ρ : AbsoluteDensity 1) (c : ℝ) (x : Torus 1) :
    tgrad M ρ c x 0 = Wf M ρ x + c * M.dφ x := by
  simp [tgrad, Wf, smoothGrad_apply, RankOneModel.dφ]

theorem tfn_eq (ρ : AbsoluteDensity 1) (c : ℝ) (x : Torus 1) :
    tfn M ρ c (1 - Nf M ρ / 2) x = Vf M ρ x + Nf M ρ / 2 + c * M.φ x := by
  unfold tfn Vf; ring

theorem phi_bound : ∃ C, 0 ≤ C ∧ ∀ x, |M.φ x| ≤ C := bdd_cont M.φ_cont

theorem memLp_dφ : MemLp M.dφ 2 (M.lgeMu : Measure (Torus 1)) :=
  memLp_bdd _ M.dφ_cont.aestronglyMeasurable (bdd_cont M.dφ_cont).choose_spec.2

theorem memLp_grad0 (ρ : AbsoluteDensity 1) (c : ℝ) :
    MemLp (fun x => Wf M ρ x + c * M.dφ x) 2 (M.lgeMu : Measure (Torus 1)) :=
  (memLp_Wf M ρ).add ((memLp_dφ M).const_mul c)

theorem energy_test (ρ : AbsoluteDensity 1) (c k : ℝ) :
    dirichletEnergy M.lgeMu (ftest M ρ c k) =
      ENNReal.ofReal (∫ x, (Wf M ρ x + c * M.dφ x) ^ 2 ∂(M.lgeMu : Measure (Torus 1))) := by
  unfold dirichletEnergy
  simp only [ftest, RankOneModel.enorm_sq_tangent, tgrad_coord]
  rw [ofReal_integral_eq_lintegral_ofReal (memLp_grad0 M ρ c).integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]

theorem inner_toCentered (g f : WeakH1Test M.lgeMu)
    (hg : ∫ x, g.fn x ∂(M.lgeMu : Measure (Torus 1)) = 0)
    (hf : ∫ x, f.fn x ∂(M.lgeMu : Measure (Torus 1)) = 0) :
    inner ℝ (g.toCentered M.lgeMu hg) (f.toCentered M.lgeMu hf) =
      ∫ x, g.fn x * f.fn x ∂(M.lgeMu : Measure (Torus 1)) := by
  show inner ℝ (g.isWeak.memLp.toLp g.fn) (f.isWeak.memLp.toLp f.fn) = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [g.isWeak.memLp.coeFn_toLp, f.isWeak.memLp.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem test_facts (ρ : AbsoluteDensity 1) :
    ∃ hf0 : ∫ x, (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)).fn x
        ∂(M.lgeMu : Measure (Torus 1)) = 0,
      Nf M ρ - Nf M ρ ^ 2 / 4 + M.η * af M ρ ^ 2 ≤
        gaussianDenominator M.data M.lgeMu (coercive M)
          (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)) hf0 ∧
      ∫ x, (Vf M ρ x + Nf M ρ / 2) * (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)).fn x
        ∂(M.lgeMu : Measure (Torus 1)) = Nf M ρ - Nf M ρ ^ 2 / 4 + M.η * af M ρ ^ 2 := by
  obtain ⟨C, -, hC⟩ := phi_bound M
  have cm := fun c => centered_moments (M.lgeMu : Measure (Torus 1)) (Vf M ρ) M.φ C
    (memLp_Vf M ρ) M.φ_cont.aestronglyMeasurable hC (Nf M ρ) (af M ρ) c rfl
    (integral_V M ρ) (integral_phi_lge M) rfl
  have hfn : ∀ c x, (ftest M ρ c (1 - Nf M ρ / 2)).fn x = Vf M ρ x + Nf M ρ / 2 + c * M.φ x :=
    fun c x => tfn_eq M ρ c x
  have hf0 : ∫ x, (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)).fn x
      ∂(M.lgeMu : Measure (Torus 1)) = 0 := by
    simp_rw [hfn]; exact (cm _).1
  have hg0 : ∫ x, (ftest M ρ 0 (1 - Nf M ρ / 2)).fn x
      ∂(M.lgeMu : Measure (Torus 1)) = 0 := by
    simp_rw [hfn]; exact (cm _).1
  have hgf : ∫ x, (ftest M ρ 0 (1 - Nf M ρ / 2)).fn x *
      (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)).fn x ∂(M.lgeMu : Measure (Torus 1)) =
      Nf M ρ - Nf M ρ ^ 2 / 4 + M.η * af M ρ ^ 2 := by
    have := (cm (M.η * af M ρ)).2.1
    simp_rw [hfn, zero_mul, add_zero]
    rw [this]; ring
  have hgg : ∫ x, (ftest M ρ 0 (1 - Nf M ρ / 2)).fn x *
      (ftest M ρ 0 (1 - Nf M ρ / 2)).fn x ∂(M.lgeMu : Measure (Torus 1)) =
      Nf M ρ - Nf M ρ ^ 2 / 4 := by
    have := (cm 0).2.2.1
    simp_rw [hfn, zero_mul, add_zero]
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only []; ring)
  have hφg : ∫ x, M.φ x * (ftest M ρ 0 (1 - Nf M ρ / 2)).fn x
      ∂(M.lgeMu : Measure (Torus 1)) = af M ρ := by
    have := (cm 0).2.2.2
    simp_rw [hfn, zero_mul, add_zero]
    exact this
  refine ⟨hf0, ?_, ?_⟩
  · have hl := denom_lower M.data M.lgeMu (coercive M)
      ((ftest M ρ 0 (1 - Nf M ρ / 2)).toCentered M.lgeMu hg0)
      ((ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)).toCentered M.lgeMu hf0)
    rw [inner_hessian_rankOne, inner_toCentered, ← real_inner_self_eq_norm_sq,
      inner_toCentered, hgf, hgg] at hl
    have hφ' : ∫ x, M.φ x * (((ftest M ρ 0 (1 - Nf M ρ / 2)).toCentered M.lgeMu hg0 :
        centeredL2 M.lgeMu) : Lp ℝ 2 (M.lgeMu : Measure (Torus 1))) x
        ∂(M.lgeMu : Measure (Torus 1)) = af M ρ := by
      rw [← hφg]
      refine integral_congr_ae ?_
      filter_upwards [(ftest M ρ 0 (1 - Nf M ρ / 2)).isWeak.memLp.coeFn_toLp] with x hx
      exact congrArg _ hx
    rw [hφ'] at hl
    unfold gaussianDenominator
    nlinarith [hl]
  · have := (cm (M.η * af M ρ)).2.1
    simp_rw [hfn]
    rw [this]; ring

end part3

section localsec

variable (M : RankOneModel)

theorem local_ineq (b : AbsoluteDrift M.data) (r : ℝ) (hr : 0 < r) :
    ∃ c δ0 : ℝ, 0 < δ0 ∧ 0 ≤ c ∧ ∀ (ρ : AbsoluteDensity 1) (δ : ℝ), 0 < δ → δ ≤ δ0 →
      (∀ x, |Vf M ρ x| ≤ δ) → 0 < (speciesGap M.data (SpeciesFamily.single ρ) : ℝ) →
      ENNReal.ofReal r ≤ gaussianRate M.data M.lgeMu (coercive M) →
      r * (1 - c * δ) * (2 * (speciesGap M.data (SpeciesFamily.single ρ) : ℝ)) ≤
        (1 + c * δ) * (speciesDissipation M.data b (SpeciesFamily.single ρ)).toReal := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := phi_bound M
  obtain ⟨Cψ, hCψ0, hCψ⟩ := bdd_cont M.dφ_cont
  obtain ⟨c, δ0, hδ0, hδ0', hc, hfin⟩ := final_real r M.η (Cφ ^ 2) Cφ (Cψ ^ 2) hr M.η_nonneg
    (sq_nonneg _) (sq_nonneg _)
  refine ⟨c, δ0, hδ0, hc, fun ρ δ hδ hδδ0 hV hG hrate => ?_⟩
  have hδ2 : δ ≤ 1 / 2 := hδδ0.trans hδ0'
  set E := ∫ x, (Wf M ρ x + M.η * af M ρ * M.dφ x) ^ 2 ∂(M.lgeMu : Measure (Torus 1)) with hE
  set T := ∫ x, (Wf M ρ x + M.η * (2 * af M ρ + bf M ρ) / 2 * (1 + Vf M ρ x) * M.dφ x) ^ 2
    ∂(M.lgeMu : Measure (Torus 1)) with hT
  set X := ∫ x, (M.η * bf M ρ / 2 * M.dφ x +
    M.η * (2 * af M ρ + bf M ρ) / 2 * Vf M ρ x * M.dφ x) ^ 2
    ∂(M.lgeMu : Measure (Torus 1)) with hX
  obtain ⟨hN0, hNδ, ha2, hb2, hX2, hTE⟩ := moment_facts (M.lgeMu : Measure (Torus 1)) (Vf M ρ)
    (Wf M ρ) M.φ M.dφ M.η Cφ Cψ δ hδ (memLp_Vf M ρ) (memLp_Wf M ρ)
    M.φ_cont.aestronglyMeasurable M.dφ_cont.aestronglyMeasurable hCφ hCψ hV (Nf M ρ) (af M ρ)
    (bf M ρ) E T X rfl rfl rfl hE hT hX
  obtain ⟨hH0, hH1⟩ := entropy_bounds M ρ δ hδ hδ2 hV
  have hH1' : (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal ≤
      (2 + 6 * δ) * Nf M ρ := hH1
  obtain ⟨hgap, -, -, -⟩ := DGPS.Examples.positive_rank_one_scalar_case M b ρ
  have hm := m_eq M ρ
  have hgap' : (speciesGap M.data (SpeciesFamily.single ρ) : ℝ) =
      (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal +
        M.η / 2 * (2 * af M ρ + bf M ρ) ^ 2 := by
    rw [hgap, hm]; rfl
  have hNpos : 0 < Nf M ρ := by
    rcases hN0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Nf M ρ = 0 := h.symm
      have hHr : (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal
          = 0 := le_antisymm (by rw [h0, mul_zero] at hH1'; exact hH1') hH0
      have ha0 : af M ρ = 0 := by
        have : af M ρ ^ 2 ≤ 0 := by rw [h0, mul_zero] at ha2; exact ha2
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
      have hb0 : bf M ρ = 0 := by
        have : |bf M ρ| ≤ 0 := by rw [h0, mul_zero] at hb2; exact hb2
        exact abs_nonpos_iff.1 this
      rw [hgap', hHr, ha0, hb0] at hG
      simp at hG
  obtain ⟨hf0, hBle, hinner⟩ := test_facts M ρ
  have hBpos : 0 < Nf M ρ - Nf M ρ ^ 2 / 4 + M.η * af M ρ ^ 2 := by
    have h1 : Nf M ρ ≤ 1 / 4 := by nlinarith
    have h2 := mul_nonneg M.η_nonneg (sq_nonneg (af M ρ))
    nlinarith
  have hnz : IsNonzeroCentered M.lgeMu
      (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)) := by
    refine ⟨hf0, fun h => ?_⟩
    have : ∫ x, (Vf M ρ x + Nf M ρ / 2) * (ftest M ρ (M.η * af M ρ) (1 - Nf M ρ / 2)).fn x
        ∂(M.lgeMu : Measure (Torus 1)) = 0 := by
      rw [← integral_zero (μ := (M.lgeMu : Measure (Torus 1))) (G := ℝ)]
      refine integral_congr_ae ?_
      filter_upwards [h] with x hx
      rw [hx]; simp
    rw [hinner] at this
    linarith
  have hr' := ((le_gaussianRate_iff_forall M.data M.lgeMu (coercive M) _).1 hrate) _ hnz
  rw [energy_test, ← ENNReal.ofReal_mul hr.le,
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => sq_nonneg _)] at hr'
  have hden : r * (Nf M ρ - Nf M ρ ^ 2 / 4 + M.η * af M ρ ^ 2) ≤ E :=
    le_trans (mul_le_mul_of_nonneg_left hBle hr.le) hr'
  exact hfin δ (Nf M ρ) (af M ρ) (bf M ρ) E _ _ T X _ _ hδ hδδ0 hN0 hNδ hH0 hH1' ha2 hb2 hgap' rfl
    hX2 hTE hden (dissip_eq M b ρ)

end localsec

section uniform

variable (M : RankOneModel)

theorem wf_bound : ∃ Cw : ℝ, 0 < Cw ∧ ∀ x, |wf M x| ≤ Cw := by
  obtain ⟨C, -, hC⟩ := bdd_cont (wf_smooth M).continuous_torus
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun x => (hC x).trans (le_max_left _ _)⟩

theorem eventually_Vf_le (ρ : ℕ → AbsoluteDensity 1)
    (hρ : TendstoUniformly (fun n x => (ρ n).sqrt x) (fun x => Real.sqrt (M.q x)) atTop)
    (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n in atTop, ∀ x, |Vf M (ρ n) x| ≤ δ := by
  obtain ⟨Cw, hCw, hC⟩ := wf_bound M
  have := (Metric.tendstoUniformly_iff.1 hρ) (δ / Cw) (div_pos hδ hCw)
  filter_upwards [this] with n hn x
  have h1 := hn x
  rw [Real.dist_eq] at h1
  have e : Vf M (ρ n) x = wf M x * ((ρ n).sqrt x - Real.sqrt (M.q x)) := by
    unfold Vf; linear_combination (1 : ℝ) * wf_mul_sqrt M x
  rw [e, abs_mul]
  have h2 : |(ρ n).sqrt x - Real.sqrt (M.q x)| ≤ δ / Cw := by
    rw [abs_sub_comm]; exact h1.le
  calc |wf M x| * |(ρ n).sqrt x - Real.sqrt (M.q x)| ≤ Cw * (δ / Cw) :=
        mul_le_mul (hC x) h2 (abs_nonneg _) hCw.le
    _ = δ := by field_simp

end uniform

end DGPS.LocalGaussianEndpoint

namespace DGPS.Examples

open DGPS.LocalGaussianEndpoint

theorem local_endpoint_rate_lower_bound (M : RankOneModel) (b : AbsoluteDrift M.data) (ρ : ℕ → AbsoluteDensity 1)
    (hρ : TendstoUniformly (fun n x => (ρ n).sqrt x) (fun x => Real.sqrt (M.q x)) atTop)
    (hG : ∀ n, 0 < speciesGap M.data (SpeciesFamily.single (ρ n))) (r : ℝ) (hr : 0 < r)
    (hrL : ENNReal.ofReal r ≤ gaussianRate M.data M.lgeMu (coercive M)) :
    ENNReal.ofReal r ≤ liminf (fun n => speciesQuotient M.data b (SpeciesFamily.single (ρ n)))
      atTop := by
  obtain ⟨c, δ0, hδ0, hc, hloc⟩ := local_ineq M b r hr
  refine le_of_forall_lt fun cc hcc => ?_
  obtain ⟨s, hs0, hcs, hsr⟩ := (ENNReal.lt_iff_exists_real_btwn).1 hcc
  have hsr' : s < r := (ENNReal.ofReal_lt_ofReal_iff hr).1 hsr
  have hspos : 0 < s := by
    by_contra h
    have : s = 0 := le_antisymm (not_lt.1 h) hs0
    rw [this] at hcs
    simp at hcs
  refine lt_of_lt_of_le hcs ?_
  set δ := min δ0 ((r - s) / ((c + 1) * (r + s))) with hδdef
  have hδpos : 0 < δ := lt_min hδ0 (div_pos (by linarith) (mul_pos (by linarith) (by linarith)))
  have hδ1 : δ ≤ δ0 := min_le_left _ _
  have hδ2 : δ ≤ (r - s) / ((c + 1) * (r + s)) := min_le_right _ _
  have hcδ : c * δ * (r + s) ≤ r - s := by
    have h1 : δ * ((c + 1) * (r + s)) ≤ r - s := (le_div_iff₀ (mul_pos (by linarith)
      (by linarith))).1 hδ2
    nlinarith [mul_nonneg hδpos.le (mul_nonneg (by linarith : (0:ℝ) ≤ r + s) (zero_le_one (α := ℝ)))]
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_Vf_le M ρ hρ δ hδpos] with n hn
  have hgn : 0 < ((speciesGap M.data (SpeciesFamily.single (ρ n)) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.2 (hG n)
  obtain ⟨-, -, hDne, hDeq⟩ := positive_rank_one_scalar_case M b (ρ n)
  have key := hloc (ρ n) δ hδpos hδ1 hn hgn hrL
  set g : ℝ := ((speciesGap M.data (SpeciesFamily.single (ρ n)) : ℝ≥0) : ℝ) with hgdef
  set Dr : ℝ := (speciesDissipation M.data b (SpeciesFamily.single (ρ n))).toReal with hDr
  have hcd : 0 < 1 + c * δ := by positivity
  have hreal : s * (2 * g) ≤ Dr := by
    have h1 : s * (1 + c * δ) ≤ r * (1 - c * δ) := by nlinarith
    have h2 : s * (1 + c * δ) * (2 * g) ≤ r * (1 - c * δ) * (2 * g) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (1 + c * δ) * (s * (2 * g)) ≤ (1 + c * δ) * Dr := by nlinarith
    exact le_of_mul_le_mul_left h3 hcd
  unfold speciesQuotient
  have hgE : ((speciesGap M.data (SpeciesFamily.single (ρ n)) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal g := (ENNReal.ofReal_coe_nnreal).symm
  rw [hgE, ENNReal.le_div_iff_mul_le (Or.inl (by simp [hgn])) (Or.inl (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul hs0]
  calc ENNReal.ofReal (s * (2 * g)) ≤ ENNReal.ofReal Dr := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal hDne

/-- Local positive-rank-one Gaussian endpoint lower limit. -/
theorem local_positive_rank_one_gaussian_endpoint_lower_limit (M : RankOneModel)
    (b : AbsoluteDrift M.data) (ρ : ℕ → AbsoluteDensity 1)
    (hρ : TendstoUniformly (fun n x => (ρ n).sqrt x) (fun x => Real.sqrt (M.q x)) atTop)
    (hG : ∀ n, 0 < speciesGap M.data (SpeciesFamily.single (ρ n)))
    (_hbdd : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ n, speciesQuotient M.data b (SpeciesFamily.single (ρ n)) ≤ C) :
    gaussianRate M.data M.lgeMu (coercive M) ≤
      liminf (fun n => speciesQuotient M.data b (SpeciesFamily.single (ρ n))) atTop := by
  refine le_of_forall_lt fun cc hcc => ?_
  obtain ⟨r, hr0, hcr, hrL⟩ := (ENNReal.lt_iff_exists_real_btwn).1 hcc
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := le_antisymm (not_lt.1 h) hr0
    rw [this] at hcr
    simp at hcr
  exact lt_of_lt_of_le hcr (local_endpoint_rate_lower_bound M b ρ hρ hG r hrpos hrL.le)

end DGPS.Examples
