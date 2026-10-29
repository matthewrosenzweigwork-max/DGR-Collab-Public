import SharpSymmetricLSI.Paper.FormLiminfS16a
import SharpSymmetricLSI.Paper.FormLiminfS7
import SharpSymmetricLSI.Statements.R19_Lemma_5_2
import SharpSymmetricLSI.Statements.R25_Lemma_A_2

/-!
# R33 (Q2): the force-error bound

`∫ |f_k ψ_k (D_i - ∑_{p,q} a_{pq} Z_q A_{pi})| dP_{N_k} ≤ ε_R` eventually in `k`, with `ε_R → 0`
(`force_err_bound`): the a.e. bridge `forceD_approx_sq` (FormLiminfS7), the arithmetic-geometric
mean inequality with weight `√M_R`, and the finite majorant `force_limsup_majorant` of (7.12).
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `|x y| ≤ (t x² + y²/t)/2` for `t > 0`. -/
theorem abs_mul_le_amgm {x y t : ℝ} (ht : 0 < t) : |x * y| ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  rw [abs_mul]
  have h : 0 ≤ (t * |x| - |y|) ^ 2 := sq_nonneg _
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  have hy : |y| ^ 2 = y ^ 2 := sq_abs y
  rw [show (t * x ^ 2 + y ^ 2 / t) / 2 = (t ^ 2 * x ^ 2 + y ^ 2) / (2 * t) by
    field_simp, le_div_iff₀ (by positivity)]
  nlinarith [abs_nonneg x, abs_nonneg y]

theorem force_err_bound (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR) {s : ℕ → Finset ℕ} {a : ℕ → ℕ → ℕ → ℝ}
    (ha : ∀ R i j, a R i j = a R j i) (hK : ∀ R x y, KR R x y = ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)
    {Ns : ℕ → ℕ} (hNs : Tendsto Ns atTop atTop) {f : (k : ℕ) → Config (Ns k) d → ℝ}
    (hfL : ∀ k, MemLp (f k) 2 (gibbs V W (Ns k))) {B : ℝ} (hf2 : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ B)
    (i : ℕ) {ψ : (k : ℕ) → Config (Ns k) d → ℝ} (hψm : ∀ k, AEStronglyMeasurable (ψ k) (gibbs V W (Ns k)))
    {K : ℝ} (hψ : ∀ k X, |ψ k X| ≤ K) :
    ∃ εR : ℕ → ℝ, Tendsto εR atTop (𝓝 0) ∧ ∀ R, ∀ᶠ k in atTop,
      ∫ X, |f k X * ψ k X * (forceD W (μ : Measure (Torus d)) eC (Ns k) i X -
        ∑ p ∈ s R, ∑ q ∈ s R, a R p q * ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
          mobA eC (Ns k) X p i)| ∂gibbs V W (Ns k) ≤ εR R := by
  -- the finite majorant of (7.12)
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  obtain ⟨eC', heC'⟩ := exists_c1_reps hd hyp hr hμ he
  choose s' a' ha' hK' using hKR.1
  obtain ⟨H, hHf, hHls, hH0⟩ := force_limsup_majorant hyp hμ heC' ha' hK' hd hKR he
    ⟨Cp, p, hp, fun N hN => (hCp N hN).2.2⟩
  -- constants
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hψ 0 0)
  have hB0 : 0 ≤ B := (integral_nonneg fun X => sq_nonneg (f 0 X)).trans (hf2 0)
  set c0 : ℝ := d * Ci ^ 2
  have hc0 : 0 ≤ c0 := by positivity
  set M : ℕ → ℝ := fun R => (H R).toReal + 1 / ((R : ℝ) + 1)
  have hMpos : ∀ R, 0 < M R := fun R => by
    have : (0 : ℝ) < 1 / ((R : ℝ) + 1) := by positivity
    simp only [M]; linarith [ENNReal.toReal_nonneg (a := H R)]
  refine ⟨fun R => K / 2 * (B + c0) * √(M R), ?_, fun R => ?_⟩
  · have hM : Tendsto M atTop (𝓝 0) := by
      have h1 : Tendsto (fun R => (H R).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hH0
        rw [ENNReal.toReal_zero] at this; exact this
      simpa [M] using h1.add tendsto_one_div_add_atTop_nhds_zero_nat
    have := ((continuous_sqrt.tendsto 0).comp hM).const_mul (K / 2 * (B + c0))
    simpa [Function.comp_def] using this
  -- eventually the Gibbs force error is below `M R`
  have hlt : limsup (fun N => ∫⁻ X, ENNReal.ofReal
      (gradSqC (fun Y => Ucentered W μ N Y - UkernelF (KR R) N Y) X) ∂gibbs V W N) atTop <
      ENNReal.ofReal (M R) := by
    refine (hHls R).trans_lt ?_
    simp only [M]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal (hHf R)]
    exact ENNReal.lt_add_right (hHf R) (by simp; positivity)
  have hev := hNs.eventually ((eventually_lt_of_limsup_lt hlt).and (eventually_ge_atTop 1))
  filter_upwards [hev] with k ⟨hk, hN⟩
  set N := Ns k
  set Δ : Config N d → ℝ := fun X => forceD W (μ : Measure (Torus d)) eC N i X -
    ∑ p ∈ s R, ∑ q ∈ s R, a R p q * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
      mobA eC N X p i
  set G : Config N d → ℝ := fun X =>
    gradSqC (fun Y => Ucentered W μ N Y - UkernelF (KR R) N Y) X
  have hG0 : ∀ X, 0 ≤ G X := fun X =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hΔ : ∀ᵐ X ∂gibbs V W N, Δ X ^ 2 ≤ c0 * G X :=
    forceD_approx_sq hyp hμ hφ heC (s R) (ha R) (hK R) hN i hCi
  set t := √(M R)
  have ht : 0 < t := sqrt_pos.2 (hMpos R)
  have hεnn : 0 ≤ K / 2 * (B + c0) * t := by positivity
  by_cases hint : Integrable (fun X => |f k X * ψ k X * Δ X|) (gibbs V W N)
  swap
  · rw [integral_undef hint]; exact hεnn
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => abs_nonneg _)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hεnn ?_
  -- pointwise bound
  have hpt : ∀ᵐ X ∂gibbs V W N, ENNReal.ofReal |f k X * ψ k X * Δ X| ≤
      ENNReal.ofReal (K / 2 * t * f k X ^ 2) + ENNReal.ofReal (K / 2 / t * c0) *
        ENNReal.ofReal (G X) := by
    filter_upwards [hΔ] with X hX
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (hG0 X))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : |f k X * ψ k X * Δ X| ≤ K * |f k X * Δ X| := by
      rw [show f k X * ψ k X * Δ X = ψ k X * (f k X * Δ X) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right (hψ k X) (abs_nonneg _)
    have h2 := abs_mul_le_amgm (x := f k X) (y := Δ X) ht
    have h3 : Δ X ^ 2 / t ≤ c0 * G X / t := div_le_div_of_nonneg_right hX ht.le
    calc |f k X * ψ k X * Δ X| ≤ K * ((t * f k X ^ 2 + Δ X ^ 2 / t) / 2) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
      _ ≤ K * ((t * f k X ^ 2 + c0 * G X / t) / 2) := by gcongr
      _ = K / 2 * t * f k X ^ 2 + K / 2 / t * c0 * G X := by ring
  refine (lintegral_mono_ae hpt).trans ?_
  have hfm : AEMeasurable (fun X => ENNReal.ofReal (K / 2 * t * f k X ^ 2)) (gibbs V W N) :=
    ((hfL k).aestronglyMeasurable.aemeasurable.pow_const 2 |>.const_mul _).ennreal_ofReal
  rw [lintegral_add_left' hfm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hP : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hf2' : ∫⁻ X, ENNReal.ofReal (K / 2 * t * f k X ^ 2) ∂gibbs V W N ≤
      ENNReal.ofReal (K / 2 * t * B) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((hfL k).integrable_sq.const_mul _)
      (Eventually.of_forall fun X => by positivity), integral_const_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hf2 k) (by positivity))
  have hG' : ENNReal.ofReal (K / 2 / t * c0) * ∫⁻ X, ENNReal.ofReal (G X) ∂gibbs V W N ≤
      ENNReal.ofReal (K / 2 / t * c0 * M R) := by
    calc _ ≤ ENNReal.ofReal (K / 2 / t * c0) * ENNReal.ofReal (M R) := mul_le_mul_right hk.le _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  refine (add_le_add hf2' hG').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have htt : t * t = M R := mul_self_sqrt (hMpos R).le
  field_simp
  rw [← htt]
  ring

end SharpLSI
