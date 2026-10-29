import FullLabeledLSI.Paper.Hybrid63AltN
import FullLabeledLSI.Paper.Hybrid63AltA
import FullLabeledLSI.Paper.Sec6Rank3

/-!
# Proposition 6.3: assembly of `spectral_comparison`
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

theorem integral_sq_le_of_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {B : ℝ}
    (h : eLpNorm f 2 P ≤ ENNReal.ofReal B) : ∫ ω, f ω ^ 2 ∂P ≤ B ^ 2 := by
  have hlt : eLpNorm f 2 P < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hmem : MemLp f 2 P := hlt
  have h1 := hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)
  have hX : ∫ ω, ‖f ω‖ ^ (ENNReal.toReal 2) ∂P = ∫ ω, f ω ^ 2 ∂P := by
    simp [sq_abs]
  rw [h1, hX] at h
  have hX0 : 0 ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  set X := ∫ ω, f ω ^ 2 ∂P
  set Y : ℝ := X ^ ((ENNReal.toReal 2)⁻¹) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hX0 _
  have hYX : Y ^ 2 = X := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
  have hB : ENNReal.ofReal B = ENNReal.ofReal (max B 0) := by
    rcases le_total 0 B with hB | hB
    · rw [max_eq_left hB]
    · rw [max_eq_right hB, ENNReal.ofReal_of_nonpos hB, ENNReal.ofReal_zero]
  rw [hB, ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)] at h
  rw [← hYX]
  have : Y ^ 2 ≤ (max B 0) ^ 2 := pow_le_pow_left₀ hY0 h 2
  refine this.trans ?_
  rcases le_total 0 B with hB | hB
  · rw [max_eq_left hB]
  · rw [max_eq_right hB]; nlinarith [sq_nonneg B]

section
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem spectral_comparison_alt
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, IsInverseOfIPlus (A.a R) (CR R)) :
    ∃ R₀ : ℕ, ∀ R, R₀ ≤ R → ∀ L : ℝ, ∀ F : (N : ℕ) → Config N d → ℝ,
      (∀ N, InSpectralRange e lam L (F N)) →
      (∃ B : ℝ, ∀ N, eLpNorm (F N) 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, -ε ≤ Jexpr A lam (CR R) R (F N) := by
  obtain ⟨σ, hσ, R0, hR0⟩ := positivity_export hd hyp hr μ hμ e lam he A
  obtain ⟨R1, hR1⟩ := eventually_atTop.1 hCR
  refine ⟨max R0 R1, fun R hR L F hFr hBex ε hε => ?_⟩
  have hpos : PosIPlus A R σ := hR0 R ((le_max_left _ _).trans hR)
  have hC : IsInverseOfIPlus (A.a R) (CR R) := hR1 R ((le_max_right _ _).trans hR)
  obtain ⟨B, hB⟩ := hBex
  obtain ⟨eC, a, hac, hca, hC1, haeC, -, -, hlam0, hlamnn, hlam1, -, ⟨cW, hcW, hweyl⟩⟩ :=
    Gross.torus_standing hd hyp hr μ hμ e lam he
  obtain ⟨-, -, hmono, hlam1pos⟩ := lam_facts hd hyp hr hμ he
  obtain ⟨e', hG, hae0⟩ := exists_goodBasis hd hyp hr hμ he
  have hae : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j := fun j => (hae0 j).symm
  obtain ⟨JL, hJL⟩ := exists_JL lam hmono hd hcW hweyl L
  set JR : ℕ := (A.s R).sup id + 1 with hJR
  set J : ℕ := max JR JL with hJdef
  have hsJR : ∀ i ∈ A.s R, i < JR := fun i hi => by
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    omega
  have hJ : ∀ i ∈ A.s R, i < J := fun i hi =>
    lt_of_lt_of_le (hsJR i hi) (le_max_left _ _)
  set Λ : ℝ := lam 1 with hΛ
  set K0 : ℝ := |Real.log (kappaR A R)| with hK0
  have hΛ0 : 0 < Λ := hlam1pos
  have hτ : 0 < ε / (3 + 3 * Λ) := by positivity
  set τ : ℝ := ε / (3 + 3 * Λ) with hτdef
  obtain ⟨δ₀, hδ₀, H26⟩ := errS26_small hd hyp hr μ hμ e lam he A R e' hae J JR
    (le_max_left _ _) hsJR L B τ K0 hτ (abs_nonneg _)
  have hδ : 0 < δ₀ / 2 := by positivity
  have H15 := errT15_small hd hyp hr μ hμ e lam he A R e' hG hae J hJ L B τ hτ hδ
  have hρ0 : 0 ≤ (bRate (μ : Measure (Torus d)) lam (CR R)).toReal := ENNReal.toReal_nonneg
  have hρΛ : (bRate (μ : Measure (Torus d)) lam (CR R)).toReal ≤ Λ :=
    rho_le_lam_one he (rLS_le_lam_one hyp hμ he)
  filter_upwards [H26 (δ₀ / 2) hδ (by linarith), H15] with N h26 h15
  obtain ⟨T, cc, hT, hFe⟩ := hFr N
  have hTJ : ∀ k ∈ T, ∀ i, k i ≤ J := fun k hk i => by
    have h1 : lam (k i) ≤ ∑ i, lam (k i) :=
      Finset.single_le_sum (f := fun i => lam (k i)) (fun i _ => hlamnn _) (Finset.mem_univ i)
    exact (hJL _ (h1.trans (hT k hk))).trans (le_max_right _ _)
  set c : (Fin N → Fin (J + 1)) → ℝ := coefArr (J := J) T cc with hc
  have hcspec : SpectralCoeff lam L c := spectralCoeff_coefArr lam L T hT cc
  have hint : ∫ X, F N X ^ 2 ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ B ^ 2 :=
    integral_sq_le_of_eLpNorm_two (hB N)
  have hsum : ∑ j, c j ^ 2 ≤ B ^ 2 := by
    have := (Gross.torus_energy_formula hac hca he hC1 haeC T cc (F := F N) hFe).1
    rw [hc, sum_sq_coefArr T hTJ cc, ← this]
    exact hint
  have hFpoly : ∀ X, F N X = polyEval e c X := fun X => by
    rw [hFe X, hc, polyEval_coefArr e T hTJ cc X]
  have hint' : ∫ X, polyEval e' c X ^ 2
      ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ B ^ 2 := by
    refine le_trans (le_of_eq ?_) hint
    refine integral_congr_ae ?_
    filter_upwards [ae_pi_eq hae N] with X hX
    rw [hFpoly X, polyEval_congr c X hX]
  obtain ⟨h2, h3, h4, h6, h7⟩ := h26 c hcspec hsum hint'
  obtain ⟨hn, h1', h5⟩ := h15 c hcspec hsum
  have hmain := per_N hd hyp hr μ hμ e lam he A CR R hσ hpos hC e' hG hae J hJ L T cc hT hTJ
    (F N) hFe (δ₀ / 2) hn
  set ρ := (bRate (μ : Measure (Torus d)) lam (CR R)).toReal with hρ
  have hτΛ : (3 + 3 * Λ) * τ = ε := by
    rw [hτdef]; field_simp
  have hτ0 := hτ.le
  have hmul : ρ / 2 * (errT3 (μ : Measure (Torus d)) e' c (δ₀ / 2) +
      errT4 (μ : Measure (Torus d)) e' c (δ₀ / 2) + errT5 (μ : Measure (Torus d)) A R e' c (δ₀ / 2)
      + errT6 (μ : Measure (Torus d)) A R e' c (δ₀ / 2) +
      K0 * errT7 (μ : Measure (Torus d)) e' c (δ₀ / 2)) ≤ Λ / 2 * (5 * τ) := by
    apply mul_le_mul (by linarith) (by linarith) _ (by linarith)
    have := abs_nonneg (Real.log (kappaR A R))
    have e3 : 0 ≤ errT3 (μ : Measure (Torus d)) e' c (δ₀ / 2) := abs_nonneg _
    have e4 : 0 ≤ errT4 (μ : Measure (Torus d)) e' c (δ₀ / 2) := abs_nonneg _
    have e5 : 0 ≤ errT5 (μ : Measure (Torus d)) A R e' c (δ₀ / 2) := abs_nonneg _
    have e6 : 0 ≤ errT6 (μ : Measure (Torus d)) A R e' c (δ₀ / 2) := abs_nonneg _
    have e7 : 0 ≤ K0 * errT7 (μ : Measure (Torus d)) e' c (δ₀ / 2) :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith
  have hfin : errT1 (μ : Measure (Torus d)) A lam R e' c (δ₀ / 2) +
      errT2 (μ : Measure (Torus d)) A lam R e' c (δ₀ / 2) +
      ρ / 2 * (errT3 (μ : Measure (Torus d)) e' c (δ₀ / 2) +
      errT4 (μ : Measure (Torus d)) e' c (δ₀ / 2) + errT5 (μ : Measure (Torus d)) A R e' c (δ₀ / 2)
      + errT6 (μ : Measure (Torus d)) A R e' c (δ₀ / 2) +
      K0 * errT7 (μ : Measure (Torus d)) e' c (δ₀ / 2)) ≤ ε := by
    nlinarith
  have hmain' : -(errT1 (μ : Measure (Torus d)) A lam R e' c (δ₀ / 2) +
      errT2 (μ : Measure (Torus d)) A lam R e' c (δ₀ / 2) +
      ρ / 2 * (errT3 (μ : Measure (Torus d)) e' c (δ₀ / 2) +
      errT4 (μ : Measure (Torus d)) e' c (δ₀ / 2) + errT5 (μ : Measure (Torus d)) A R e' c (δ₀ / 2)
      + errT6 (μ : Measure (Torus d)) A R e' c (δ₀ / 2) +
      K0 * errT7 (μ : Measure (Torus d)) e' c (δ₀ / 2))) ≤ Jexpr A lam (CR R) R (F N) := hmain
  linarith

end

end SharpLSI.FL

end
