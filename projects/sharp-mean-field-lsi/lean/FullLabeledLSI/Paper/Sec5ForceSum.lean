import FullLabeledLSI.Paper.Sec5ForceT1
import FullLabeledLSI.Paper.Sec5ForceT2a
import FullLabeledLSI.Paper.Sec5ForceT2b
import FullLabeledLSI.Paper.Sec5ForceT3
import FullLabeledLSI.Paper.Sec5ForceJensen
import FullLabeledLSI.Paper.Sec5Products2

/-!
# Lemma 5.5: assembly of the abstract force estimate
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- `∑_{j<N-M} √(2 d_{j,k}) ≤ C √H₀` (Cauchy–Schwarz and (5.11)). -/
theorem sum_sqrt_dRev_le (k : ℕ) (hk : 1 ≤ k) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (N M : ℕ), k ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
        (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
        klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
        ∑ j ∈ Finset.range (N - M), Real.sqrt (2 * (dRev ν j k).toReal) ≤
          C * Real.sqrt (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal := by
  have hk1 : 1 ≤ k := hk
  set K : ℝ := (k : ℝ) * ((k : ℝ) - 1) with hK
  have hK0 : 0 ≤ K := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    rw [hK]; nlinarith
  refine ⟨Real.sqrt (2 * K * k / τ), ?_⟩
  intro N M hkM hMN hτM μ _ ν _ hH
  have hM1 : 1 ≤ M := le_trans hk1 hkM
  have hN1 : 1 ≤ N := le_trans hM1 hMN
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set Hr : ℝ := (klDiv ν (Measure.pi fun _ => μ)).toReal with hHr
  have hHr0 : 0 ≤ Hr := ENNReal.toReal_nonneg
  set ℓ : ℕ := N - M with hℓ
  have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
  set x : ℕ → ℝ := fun j => (dRev ν j k).toReal with hx
  have hx0 : ∀ j, 0 ≤ x j := fun j => ENNReal.toReal_nonneg
  have hchain : ∑ j ∈ Finset.range ℓ, x j ≤ K * Hr / ((M - k + 2 : ℕ) : ℝ) := by
    have hc := chain_sum_d ν μ k M hkM hMN
    have h1 : ((k : ℝ≥0∞) - 1).toReal = (k : ℝ) - 1 := by
      rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hk1) (ENNReal.natCast_ne_top k)]
      simp
    have hRne : (k * (k - 1) : ℝ≥0∞) * klDiv ν (Measure.pi fun _ : Fin N => μ) /
        ((M - k + 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
      rw [div_eq_mul_inv]
      refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top k) (ENNReal.sub_ne_top (ENNReal.natCast_ne_top k))) hH)
        (ENNReal.inv_ne_top.2 ?_)
      exact_mod_cast (by omega : M - k + 2 ≠ 0)
    have hfin : ∀ j ∈ Finset.range ℓ, dRev ν j k ≠ ⊤ := by
      intro j hjm
      refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hRne hc) ?_
      exact Finset.single_le_sum (f := fun j => dRev ν j k) (fun _ _ => bot_le) hjm
    have := ENNReal.toReal_mono hRne hc
    rw [ENNReal.toReal_sum hfin] at this
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul, h1,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hm : ((M - k + 2 : ℕ) : ℝ) = (M : ℝ) - k + 2 := by
    rw [Nat.cast_add, Nat.cast_sub hkM]; push_cast; ring
  have hm0 : (0 : ℝ) < ((M - k + 2 : ℕ) : ℝ) := by rw [hm]; linarith
  have hratio : (ℓ : ℝ) * τ ≤ k * ((M - k + 2 : ℕ) : ℝ) := by
    have := (le_div_iff₀ hN0).1 hτM
    rw [hm]
    have h3 : (ℓ : ℝ) * τ ≤ M := by nlinarith
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range ℓ) (fun _ => (1 : ℝ))
    (fun j => Real.sqrt (2 * x j))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  have hsq : ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * x j) ^ 2 = 2 * ∑ j ∈ Finset.range ℓ, x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Real.sq_sqrt (by linarith [hx0 j])
  rw [hsq] at hcs
  have hb : (ℓ : ℝ) * (2 * ∑ j ∈ Finset.range ℓ, x j) ≤ 2 * K * k / τ * Hr := by
    have h4 : ∑ j ∈ Finset.range ℓ, x j ≤ K * Hr / ((M - k + 2 : ℕ) : ℝ) := hchain
    have h5 : (ℓ : ℝ) * (K * Hr / ((M - k + 2 : ℕ) : ℝ)) ≤ K * k / τ * Hr := by
      rw [mul_div_assoc', div_le_iff₀ hm0, show K * k / τ * Hr = (K * Hr * k) / τ by ring,
        div_mul_eq_mul_div, le_div_iff₀ hτ]
      have : 0 ≤ K * Hr := mul_nonneg hK0 hHr0
      nlinarith
    have h6 : (ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, x j ≤
        (ℓ : ℝ) * (K * Hr / ((M - k + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    calc (ℓ : ℝ) * (2 * ∑ j ∈ Finset.range ℓ, x j)
        = 2 * ((ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, x j) := by ring
      _ ≤ 2 * (K * k / τ * Hr) := by linarith
      _ = 2 * K * k / τ * Hr := by ring
  rw [← Real.sqrt_mul (by positivity)]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (hcs.trans hb))

section Delta

variable {N : ℕ} {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

theorem avg1R_congr' (N j : ℕ) {F G : Finset (Fin N) → Fin N → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ, F S i = G S i) :
    avg1R N j F = avg1R N j G := by
  unfold avg1R
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  congr 1
  exact Finset.sum_congr rfl (h S hS)

theorem avg1R_add' (N j : ℕ) (F G : Finset (Fin N) → Fin N → ℝ) :
    avg1R N j (fun S i => F S i + G S i) = avg1R N j F + avg1R N j G := by
  unfold avg1R
  simp only [Finset.sum_add_distrib, mul_add]

theorem avg1R_sub' (N j : ℕ) (F G : Finset (Fin N) → Fin N → ℝ) :
    avg1R N j (fun S i => F S i - G S i) = avg1R N j F - avg1R N j G := by
  unfold avg1R
  simp only [Finset.sum_sub_distrib, mul_sub]

theorem avg1R_const_mul' (N j : ℕ) (a : ℝ) (F : Finset (Fin N) → Fin N → ℝ) :
    avg1R N j (fun S i => a * F S i) = a * avg1R N j F := by
  unfold avg1R
  have : ∀ S : Finset (Fin N), ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, a * F S i =
      a * (((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, F S i) := fun S => by
    rw [← Finset.mul_sum]; ring
  simp_rw [this]
  rw [← Finset.mul_sum]
  ring

theorem avg1R_comb (N j : ℕ) (F E1 E2a E2b E2c E3 : Finset (Fin N) → Fin N → ℝ)
    (h : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ,
      F S i = E1 S i - 2 * (E2a S i + E2b S i + E2c S i) + E3 S i) :
    avg1R N j F = avg1R N j E1 - 2 * (avg1R N j E2a + avg1R N j E2b + avg1R N j E2c) +
      avg1R N j E3 := by
  rw [avg1R_congr' N j h, avg1R_add', avg1R_sub', avg1R_const_mul', avg1R_add', avg1R_add']

theorem avg1R_abs_le {N j : ℕ} (hj : j < N) (F : Finset (Fin N) → Fin N → ℝ) {c : ℝ}
    (hc : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ, |F S i| ≤ c) :
    |avg1R N j F| ≤ c := by
  have hCj : (0 : ℝ) < (Nat.choose N j : ℝ) := by exact_mod_cast Nat.choose_pos hj.le
  unfold avg1R
  rw [abs_mul, abs_of_pos (inv_pos.2 hCj)]
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      |((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, F S i| ≤ c := by
    intro S hS
    have hcard : Sᶜ.card = N - j := by
      rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hS).2]
    have hpos : (0 : ℝ) < Sᶜ.card := by
      rw [hcard]; exact_mod_cast (by omega : 0 < N - j)
    rw [abs_mul, abs_of_pos (inv_pos.2 hpos)]
    calc _ ≤ (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, c :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i hi => hc S hS i hi)) (inv_nonneg.2 hpos.le)
      _ = c := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  calc _ ≤ (Nat.choose N j : ℝ)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, c :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum hS)) (inv_nonneg.2 hCj.le)
    _ = c := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hCj.ne', one_mul]

theorem abs_sum_sq_le' {B : ℝ} (p : Fin d → ℝ) (hp : ∀ k, |p k| ≤ B) :
    |∑ k, (p k) ^ 2| ≤ (d : ℝ) * B ^ 2 := by
  have := abs_sum_mul_le (Bb := B) p p hp hp
  simpa [sq] using this

theorem abs_globTupleMean_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hN : 3 ≤ N) :
    |globTupleMean ν 3 (A3 bF)| ≤ (d : ℝ) * Bb ^ 2 := by
  have hdn : (0 : ℝ) < ((N.descFactorial 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hN
  unfold globTupleMean
  rw [abs_mul, abs_of_pos (inv_pos.2 hdn)]
  calc _ ≤ ((N.descFactorial 3 : ℕ) : ℝ)⁻¹ * ∑ J ∈ injTuples N 3, (d : ℝ) * Bb ^ 2 :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun J _ =>
            abs_integral_le_of_prob ν _ (fun X => abs_A3_le hB _))) (inv_nonneg.2 hdn.le)
    _ = _ := by
        rw [Finset.sum_const, card_injTuples, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hdn.ne', one_mul]


theorem sum_ne_split (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) (f : Fin N → ℝ) :
    (∑ l, if l ≠ i then f l else 0) = ∑ l ∈ S, f l + ∑ l ∈ Sᶜ.erase i, f l := by
  classical
  have hu : (Finset.univ.filter fun l : Fin N => l ≠ i) = S ∪ Sᶜ.erase i := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_erase,
      Finset.mem_compl]
    constructor
    · intro h
      by_cases hl : l ∈ S
      · exact Or.inl hl
      · exact Or.inr ⟨h, hl⟩
    · rintro (h | h)
      · rintro rfl; exact hi h
      · exact h.1
  have hd : Disjoint S (Sᶜ.erase i) := by
    rw [Finset.disjoint_left]
    intro l hl hl'
    exact (Finset.mem_compl.1 (Finset.mem_of_mem_erase hl')) hl
  rw [← Finset.sum_filter, hu, Finset.sum_union hd]

/-- Pointwise (in `S, i`) expansion of `E|B_S - G_i|²`. -/
theorem force_expand (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (i : Fin N) (hi : i ∈ Sᶜ) :
    ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k - Gpart bF bΔ N X i k) ^ 2 ∂ν =
      (∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k) ^ 2 ∂ν) -
        2 * ((N : ℝ)⁻¹ * ∑ l ∈ S, ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν +
          (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν +
          (N : ℝ)⁻¹ * ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bΔ (X i) k ∂ν) +
        ∫ X, ∑ k : Fin d, (Gpart bF bΔ N X i k) ^ 2 ∂ν := by
  have hiS : i ∉ S := Finset.mem_compl.1 hi
  set b : Fin d → Config N d → ℝ := fun k X => BS bF ν S X (X i) k with hb
  set g : Fin d → Config N d → ℝ := fun k X => Gpart bF bΔ N X i k with hg
  set u : Fin N → Config N d → ℝ := fun l X => ∑ k : Fin d, b k X * bF (X i) (X l) k with hu
  set w : Config N d → ℝ := fun X => ∑ k : Fin d, b k X * bΔ (X i) k with hw
  have hbm : ∀ k, Measurable (b k) := fun k => measurable_BS_comp hB ν S i k
  have hgm : ∀ k, Measurable (g k) := fun k => measurable_Gpart_T3 hB N i k
  have hbb : ∀ k X, |b k X| ≤ Bb := fun k X => abs_BS_le hB ν S hS X (X i) k
  have hgb : ∀ k X, |g k X| ≤ (N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb) := fun k X => abs_Gpart_le hB X i k
  have hFm : ∀ (l : Fin N) k, Measurable fun X : Config N d => bF (X i) (X l) k := fun l k =>
    (hB.meas k).comp (f := fun X : Config N d => (X i, X l))
      ((measurable_pi_apply i).prodMk (measurable_pi_apply l))
  have hum : ∀ l, Measurable (u l) := fun l =>
    Finset.measurable_sum _ fun k _ => (hbm k).mul (hFm l k)
  have hub : ∀ l X, |u l X| ≤ (d : ℝ) * Bb ^ 2 := fun l X =>
    abs_sum_mul_le _ _ (fun k => hbb k X) (fun k => hB.bound _ _ k)
  have hwm : Measurable w := Finset.measurable_sum _ fun k _ =>
    (hbm k).mul ((hB.measΔ k).comp (measurable_pi_apply i))
  have hwb : ∀ X, |w X| ≤ (d : ℝ) * Bb ^ 2 := fun X =>
    abs_sum_mul_le _ _ (fun k => hbb k X) (fun k => hB.boundΔ _ k)
  have hI1 : Integrable (fun X => ∑ k, (b k X) ^ 2) ν :=
    integrable_of_bdd ν (Finset.measurable_sum _ fun k _ => (hbm k).pow_const 2)
      (fun X => abs_sum_sq_le' (fun k => b k X) (fun k => hbb k X))
  have hI3 : Integrable (fun X => ∑ k, (g k X) ^ 2) ν :=
    integrable_of_bdd ν (Finset.measurable_sum _ fun k _ => (hgm k).pow_const 2)
      (fun X => abs_sum_sq_le' (fun k => g k X) (fun k => hgb k X))
  have hIu : ∀ l, Integrable (u l) ν := fun l => integrable_of_bdd ν (hum l) (hub l)
  have hIw : Integrable w ν := integrable_of_bdd ν hwm hwb
  have hpt : ∀ X, ∑ k : Fin d, (b k X - g k X) ^ 2 =
      (∑ k, (b k X) ^ 2) - 2 * ((N : ℝ)⁻¹ * ∑ l ∈ S, u l X + (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X +
        (N : ℝ)⁻¹ * w X) + ∑ k, (g k X) ^ 2 := by
    intro X
    have e1 : ∑ k : Fin d, (b k X - g k X) ^ 2 =
        (∑ k, (b k X) ^ 2) - 2 * ∑ k, b k X * g k X + ∑ k, (g k X) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∀ k, b k X * g k X = (N : ℝ)⁻¹ * (b k X * ∑ l ∈ S, bF (X i) (X l) k +
        b k X * ∑ l ∈ Sᶜ.erase i, bF (X i) (X l) k + b k X * bΔ (X i) k) := by
      intro k
      simp only [hg, Gpart]
      rw [sum_ne_split S i hiS (fun l => bF (X i) (X l) k)]
      ring
    have e3 : ∑ k, b k X * g k X = (N : ℝ)⁻¹ * (∑ l ∈ S, u l X + ∑ l ∈ Sᶜ.erase i, u l X + w X) := by
      rw [Finset.sum_congr rfl fun k _ => e2 k, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      congr 1
      have c1 : ∀ T : Finset (Fin N), ∑ k, b k X * ∑ l ∈ T, bF (X i) (X l) k = ∑ l ∈ T, u l X := by
        intro T
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      rw [c1, c1]
    rw [e1, e3]
    ring
  have hfun : (fun X : Config N d => ∑ k : Fin d, (BS bF ν S X (X i) k - Gpart bF bΔ N X i k) ^ 2) =
      fun X => (∑ k, (b k X) ^ 2) - 2 * ((N : ℝ)⁻¹ * ∑ l ∈ S, u l X +
        (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X + (N : ℝ)⁻¹ * w X) + ∑ k, (g k X) ^ 2 := funext hpt
  have hS1 : Integrable (fun X => (N : ℝ)⁻¹ * ∑ l ∈ S, u l X) ν :=
    (integrable_finsetSum _ fun l _ => hIu l).const_mul _
  have hS2 : Integrable (fun X => (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X) ν :=
    (integrable_finsetSum _ fun l _ => hIu l).const_mul _
  have hS3 : Integrable (fun X => (N : ℝ)⁻¹ * w X) ν := hIw.const_mul _
  have hS12 : Integrable (fun X => (N : ℝ)⁻¹ * ∑ l ∈ S, u l X +
      (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X) ν := hS1.add hS2
  have hS123 : Integrable (fun X => (N : ℝ)⁻¹ * ∑ l ∈ S, u l X +
      (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X + (N : ℝ)⁻¹ * w X) ν := hS12.add hS3
  have hT : Integrable (fun X => 2 * ((N : ℝ)⁻¹ * ∑ l ∈ S, u l X +
      (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X + (N : ℝ)⁻¹ * w X)) ν := hS123.const_mul 2
  have hD : Integrable (fun X => (∑ k, (b k X) ^ 2) - 2 * ((N : ℝ)⁻¹ * ∑ l ∈ S, u l X +
      (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, u l X + (N : ℝ)⁻¹ * w X)) ν := hI1.sub hT
  rw [hfun, integral_add hD hI3, integral_sub hI1 hT, integral_const_mul,
    integral_add hS12 hS3, integral_add hS1 hS2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun l _ => hIu l),
    integral_finsetSum _ (fun l _ => hIu l)]

/-- Purely algebraic final step of `forceDelta_le`. -/
theorem force_alg (fD A1 A2a A2b A2c A3' g j N n C1 C2a C2b C3 c s2 s3 : ℝ)
    (hN : 0 < N) (hn0 : 0 < n) (hn : n = N - j) (hc : 0 ≤ c) (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3)
    (hfD : fD = A1 - 2 * (A2a + A2b + A2c) + A3')
    (h1 : |A1 - g| ≤ C1 * (1 / n + s3))
    (h2a : |A2a - j / N * g| ≤ C2a * (1 / n + s2))
    (h2b : |A2b - (n - 1) / N * g| ≤ C2b * (1 / n + s2 + s3))
    (h3 : |A3' - g| ≤ C3 / N)
    (h2c : |A2c| ≤ N⁻¹ * c) (hg : |g| ≤ c) :
    fD ≤ (|C1| + 2 * |C2a| + 2 * |C2b| + |C3| + 4 * c) * (1 / N + 1 / n + s2 + s3) := by
  have ha : 0 ≤ 1 / N := by positivity
  have hb : 0 ≤ 1 / n := by positivity
  have hcoef : 2 - 2 * (j / N) - 2 * ((n - 1) / N) = 2 / N := by
    rw [hn]; field_simp; ring
  have hFD : fD = (A1 - g) - 2 * (A2a - j / N * g) - 2 * (A2b - ((n - 1) / N) * g)
      - 2 * A2c + (A3' - g) + (2 / N) * g := by
    rw [hfD]; linear_combination g * hcoef
  have e1 := abs_le.1 h1
  have e2a := abs_le.1 h2a
  have e2b := abs_le.1 h2b
  have e3 := abs_le.1 h3
  have e2c := abs_le.1 h2c
  have egl := abs_le.1 hg
  have m1 : C1 * (1 / n + s3) ≤ |C1| * (1 / n + s3) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have m2 : C2a * (1 / n + s2) ≤ |C2a| * (1 / n + s2) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have m3 : C2b * (1 / n + s2 + s3) ≤ |C2b| * (1 / n + s2 + s3) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have m4 : C3 * (1 / N) ≤ |C3| * (1 / N) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) ha
  have g1 : 2 * (1 / N) * g ≤ 2 * (1 / N) * c :=
    mul_le_mul_of_nonneg_left egl.2 (by positivity)
  have p1 : 0 ≤ |C1| * (1 / N + s2) := by positivity
  have p2 : 0 ≤ |C2a| * (1 / N + s3) := by positivity
  have p3 : 0 ≤ |C2b| * (1 / N) := by positivity
  have p4 : 0 ≤ |C3| * (1 / n + s2 + s3) := by positivity
  have p5 : 0 ≤ c * (1 / n + s2 + s3) := by positivity
  have q : C3 / N = C3 * (1 / N) := by ring
  have q2 : N⁻¹ = 1 / N := by ring
  have q3 : 2 / N = 2 * (1 / N) := by ring
  rw [q] at e3
  rw [q2] at e2c
  rw [hFD, q3]
  linarith [e1.1, e1.2, e2a.1, e2a.2, e2b.1, e2b.2, e3.1, e3.2, e2c.1, e2c.2]

theorem force_exp (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    {j : ℕ} (hj : j + 1 ≤ N) :
    forceDelta bF bΔ ν j =
      avg1R N j (fun S i => ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k) ^ 2 ∂ν) -
        2 * (avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ S,
            ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) +
          avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i,
            ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) +
          avg1R N j (fun S i => (N : ℝ)⁻¹ *
            ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bΔ (X i) k ∂ν)) +
        avg1R N j (fun S i => ∫ X, ∑ k : Fin d, (Gpart bF bΔ N X i k) ^ 2 ∂ν) := by
  unfold forceDelta
  refine avg1R_comb N j _ _ _ _ _ _ ?_
  intro S hS i hi
  have hcard : Sᶜ.card = N - j := by
    rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hS).2]
  exact force_expand hB ν S (by omega) i hi

theorem force_c_bound (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] {j : ℕ} (hjN : j < N) :
    |avg1R N j (fun S i => (N : ℝ)⁻¹ *
      ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bΔ (X i) k ∂ν)| ≤
      (N : ℝ)⁻¹ * ((d : ℝ) * Bb ^ 2) := by
  refine avg1R_abs_le hjN _ (fun S hS i hi => ?_)
  have hcard : Sᶜ.card = N - j := by
    rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hS).2]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact abs_integral_le_of_prob ν _ (fun X =>
    abs_sum_mul_le _ _ (fun k => abs_BS_le hB ν S (by omega) X (X i) k)
      (fun k => hB.boundΔ _ k))

end Delta

/-- The level-`j` estimate: `forceDelta` is within `K (1/N + 1/n + √(2d_{j,2}) + √(2d_{j,3}))`
of `0` (it equals `T₁ − 2T₂ + T₃`, all three within the stated errors of `C₃`, the coefficients
`j/N + (n-1)/N = (N-1)/N`). -/
theorem forceDelta_le {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) :
    ∃ K : ℝ, ∀ (N : ℕ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
      (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ → ∀ j, j + 3 ≤ N →
      forceDelta bF bΔ ν j ≤
        K * (1 / (N : ℝ) + 1 / ((N - j : ℕ) : ℝ) + Real.sqrt (2 * (dRev ν j 2).toReal) +
          Real.sqrt (2 * (dRev ν j 3).toReal)) := by
  obtain ⟨C1, hC1⟩ := T1_close hB
  obtain ⟨C2a, hC2a⟩ := T2a_close hB
  obtain ⟨C2b, hC2b⟩ := T2b_close hB
  obtain ⟨C3, hC3⟩ := T3_close hB
  have hc0 : 0 ≤ (d : ℝ) * Bb ^ 2 := by positivity
  refine ⟨|C1| + 2 * |C2a| + 2 * |C2b| + |C3| + 4 * ((d : ℝ) * Bb ^ 2), ?_⟩
  intro N μ _ ν _ hH j hj
  have hjN : j < N := by omega
  have hN3 : 3 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < ((N - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - j)
  have hnN : (((N - j : ℕ) : ℝ)) = (N : ℝ) - j := by
    rw [Nat.cast_sub (by omega)]
  exact force_alg _ _ _ _ _ _ _ (j : ℝ) (N : ℝ) _ C1 C2a C2b C3 _ _ _ hN0 hn0 hnN hc0
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (force_exp hB ν (by omega))
    (hC1 N μ ν hH j hj) (hC2a N μ ν hH j hj) (hC2b N μ ν hH j hj) (hC3 N ν hN3 j hjN)
    (force_c_bound hB ν hjN) (abs_globTupleMean_le hB ν hN3)

/-- Lemma 5.5, abstract form: `∑_{j<N-M} forceDelta ≤ C (1 + √H₀)`. -/
theorem abstract_force_sum {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ}
    {Bb : ℝ} (hB : ForceRep bF bΔ Bb) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (N M : ℕ), 3 ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
        (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
        klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
        ∑ j ∈ Finset.range (N - M), forceDelta bF bΔ ν j ≤
          C * (1 + Real.sqrt (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal) := by
  obtain ⟨K, hK⟩ := forceDelta_le hB
  obtain ⟨C2, hC2⟩ := sum_sqrt_dRev_le 2 (by norm_num) τ hτ
  obtain ⟨C3, hC3⟩ := sum_sqrt_dRev_le 3 (by norm_num) τ hτ
  refine ⟨|K| * (1 + |Real.log (1 / τ)| + |C2| + |C3|), ?_⟩
  intro N M hM3 hMN hτM μ _ ν _ hH
  have hM1 : 1 ≤ M := by omega
  have hN1 : 1 ≤ N := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  set Hr : ℝ := (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal with hHr
  have hHr0 : 0 ≤ Real.sqrt Hr := Real.sqrt_nonneg _
  have hterm : ∀ j ∈ Finset.range (N - M), forceDelta bF bΔ ν j ≤
      |K| * (1 / (N : ℝ) + 1 / ((N - j : ℕ) : ℝ) + Real.sqrt (2 * (dRev ν j 2).toReal) +
        Real.sqrt (2 * (dRev ν j 3).toReal)) := by
    intro j hj
    have hjl := Finset.mem_range.1 hj
    exact (hK N μ ν hH j (by omega)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hS0 : ∑ j ∈ Finset.range (N - M), (1 : ℝ) / (N : ℝ) ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((N - M : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
    rw [mul_one_div, div_le_one hN0]; exact this
  have hS1 : ∑ j ∈ Finset.range (N - M), (1 : ℝ) / ((N - j : ℕ) : ℝ) ≤ |Real.log (1 / τ)| := by
    refine (sum_inv_sub_le_log hM1 hMN).trans ?_
    refine le_trans ?_ (le_abs_self _)
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hM0 hτ]
    have := (le_div_iff₀ hN0).1 hτM
    linarith
  have hS2 := hC2 N M (by omega) hMN hτM μ ν hH
  have hS3 := hC3 N M hM3 hMN hτM μ ν hH
  have hm2 : C2 * Real.sqrt Hr ≤ |C2| * Real.sqrt Hr :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hHr0
  have hm3 : C3 * Real.sqrt Hr ≤ |C3| * Real.sqrt Hr :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hHr0
  have hsum : ∑ j ∈ Finset.range (N - M), (1 : ℝ) / (N : ℝ) +
      ∑ j ∈ Finset.range (N - M), (1 : ℝ) / ((N - j : ℕ) : ℝ) +
      ∑ j ∈ Finset.range (N - M), Real.sqrt (2 * (dRev ν j 2).toReal) +
      ∑ j ∈ Finset.range (N - M), Real.sqrt (2 * (dRev ν j 3).toReal) ≤
      1 + |Real.log (1 / τ)| + |C2| * Real.sqrt Hr + |C3| * Real.sqrt Hr := by
    linarith
  have hK0 : 0 ≤ |K| := abs_nonneg _
  have hL0 : 0 ≤ |Real.log (1 / τ)| := abs_nonneg _
  refine (mul_le_mul_of_nonneg_left hsum hK0).trans ?_
  have : 0 ≤ |K| * ((|C2| + |C3|) + (1 + |Real.log (1 / τ)|) * Real.sqrt Hr) := by positivity
  nlinarith [this]

end SharpLSI.FL
