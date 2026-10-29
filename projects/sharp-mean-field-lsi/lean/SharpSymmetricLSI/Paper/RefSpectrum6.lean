import SharpSymmetricLSI.Paper.RefSpectrum5

/-!
# R23 (6.1), part 6: completeness of the successive minimizers

* `rayleigh_le`: `λ_{n+1} ∫u² ≤ D(u)` for `u ∈ H¹(P)` orthogonal to `e₀, …, eₙ`.
* `tendsto_lam`: `λ_n → ∞` (otherwise Rellich gives an `L²`-Cauchy subsequence of an orthonormal
  sequence).
* `eSeq_complete`: if `f ⊥ eₙ` for all `n` then `f ⊥ φ` for every `φ ∈ H¹(P)` (the remainders
  `φ - ∑_{i≤n}⟨φ,eᵢ⟩eᵢ` have energy `≤ D(φ)`, so their `L²` norms tend to `0`); testing with
  `cos`, `sin` kills all Fourier coefficients of `fρ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ} {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
include hρ

/-- The Rayleigh bound from the minimality of `e_{n+1}`. -/
theorem rayleigh_le (hd : 1 ≤ d) {n : ℕ} {u : Torus d → ℝ} (hu : MemH1 (densMeasure ρ) u)
    (huo : ∀ i ≤ n, ∫ x, u x * eSeq (densMeasure ρ) i x ∂densMeasure ρ = 0) :
    dirE (densMeasure ρ) (eSeq (densMeasure ρ) (n + 1)) * ∫ x, u x ^ 2 ∂densMeasure ρ ≤
      dirE (densMeasure ρ) u := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  have hmem := (eSeq_spec hρ hd (n + 1)).2.2.2.1 n (Nat.lt_succ_self n)
  set N := ∫ x, u x ^ 2 ∂P
  have hN0 : 0 ≤ N := integral_nonneg fun x => sq_nonneg _
  rcases hN0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact dirE_nonneg hρ u
  set sc := 1 / Real.sqrt N
  obtain ⟨hwH, -⟩ := memH1_lin hρ hu hu sc 0
  have hsc : sc ^ 2 * N = 1 := by
    rw [div_pow, Real.sq_sqrt hpos.le, one_pow, one_div_mul_cancel hpos.ne']
  have hwA : (fun x => sc * u x + 0 * u x) ∈ Adm P (eSeq P) n := by
    refine ⟨hwH, ?_, fun i hi => ?_⟩
    · have : ∫ x, (sc * u x + 0 * u x) ^ 2 ∂P = sc ^ 2 * N := by
        rw [← integral_const_mul]; congr 1; funext x; ring
      rw [this, hsc]
    · have hiH := (eSeq_spec hρ hd n).1 i hi
      rw [integral_lin_mul hρ hu.2.1 hu.2.1 hiH.2.1, huo i hi]; ring
  have h := hmem.2 _ hwA
  rw [dirE_lin hρ hu hu sc 0] at h
  calc dirE P (eSeq P (n + 1)) * N ≤ (sc ^ 2 * dirE P u + 2 * sc * 0 * dirB P u u +
        0 ^ 2 * dirE P u) * N := mul_le_mul_of_nonneg_right h hN0
    _ = dirE P u := by
        rw [show (sc ^ 2 * dirE P u + 2 * sc * 0 * dirB P u u + 0 ^ 2 * dirE P u) * N =
          dirE P u * (sc ^ 2 * N) by ring, hsc, mul_one]

theorem integral_sub_sq_eSeq (hd : 1 ≤ d) {i j : ℕ} (hij : i ≠ j) :
    ∫ x, (eSeq (densMeasure ρ) i x - eSeq (densMeasure ρ) j x) ^ 2 ∂densMeasure ρ = 2 := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  obtain ⟨hH, hon, -⟩ := eSeq_spec hρ hd (max i j)
  have hi := hH i (le_max_left _ _)
  have hj := hH j (le_max_right _ _)
  have e : ∫ x, (eSeq P i x - eSeq P j x) ^ 2 ∂P =
      ∫ x, (1 * eSeq P i x + (-1) * eSeq P j x) * (1 * eSeq P i x + (-1) * eSeq P j x) ∂P := by
    congr 1; funext x; ring
  obtain ⟨hl, -⟩ := memH1_lin hρ hi hj 1 (-1)
  rw [e, integral_lin_mul hρ hi.2.1 hj.2.1 hl.2.1]
  have e1 : ∫ x, eSeq P i x * (1 * eSeq P i x + (-1) * eSeq P j x) ∂P =
      ∫ x, (1 * eSeq P i x + (-1) * eSeq P j x) * eSeq P i x ∂P := by congr 1; funext x; ring
  have e2 : ∫ x, eSeq P j x * (1 * eSeq P i x + (-1) * eSeq P j x) ∂P =
      ∫ x, (1 * eSeq P i x + (-1) * eSeq P j x) * eSeq P j x ∂P := by congr 1; funext x; ring
  rw [e1, e2, integral_lin_mul hρ hi.2.1 hj.2.1 hi.2.1, integral_lin_mul hρ hi.2.1 hj.2.1 hj.2.1,
    hon i (le_max_left _ _) i (le_max_left _ _), hon i (le_max_left _ _) j (le_max_right _ _),
    hon j (le_max_right _ _) i (le_max_left _ _), hon j (le_max_right _ _) j (le_max_right _ _)]
  simp [hij, Ne.symm hij]
  norm_num

/-- **`λₙ → ∞`.** -/
theorem tendsto_lam (hd : 1 ≤ d) :
    Tendsto (fun n => dirE (densMeasure ρ) (eSeq (densMeasure ρ) n)) atTop atTop := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  have hmono : Monotone fun n => dirE P (eSeq P n) :=
    monotone_nat_of_le_succ fun n => (eSeq_spec hρ hd (n + 1)).2.2.2.2 n (Nat.lt_succ_self n)
  refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
  by_contra hb
  push Not at hb
  have hH : ∀ n, MemH1 P (eSeq P n) := fun n => (eSeq_spec hρ hd n).1 n le_rfl
  have ha := hρ.haar_le_smul
  have hb' := hρ.le_smul
  have hc0 : 0 ≤ 1 / c := by have := hρ.pos; positivity
  have hB : ∀ n, (∫ y, eSeq P n y ^ 2) + ∑ j, ∫ y, weakGrad (eSeq P n) y j ^ 2 ≤
      1 / c + 1 / c * b := by
    intro n
    have h1 : ∫ y, eSeq P n y ^ 2 ≤ 1 / c * ∫ y, eSeq P n y ^ 2 ∂P :=
      integral_le_smul_of_le hc0 ha (fun _ => sq_nonneg _) (hH n).2.1.integrable_sq
    have h2 : ∑ j, ∫ y, weakGrad (eSeq P n) y j ^ 2 ≤ 1 / c * dirE P (eSeq P n) := by
      rw [dirE, integral_finsetSum _ fun j _ => (gradP hρ (hH n) j).integrable_sq, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ =>
        integral_le_smul_of_le hc0 ha (fun _ => sq_nonneg _) (gradP hρ (hH n) j).integrable_sq
    have hn1 : ∫ y, eSeq P n y ^ 2 ∂P = 1 := by
      have := (eSeq_spec hρ hd n).2.1 n le_rfl n le_rfl
      simp only [if_true] at this; simp_rw [sq]; exact this
    rw [hn1] at h1
    nlinarith [mul_le_mul_of_nonneg_left (hb n).le hc0]
  obtain ⟨φ, hφ, f, G, hf2, -, -, hconv, -⟩ := rellich_torus
    (fun n => isWeakGrad_weakGrad (hH n).1) (fun n => memLp_vol ha (hH n))
    (fun n j => memLp_grad_vol ha hb' (hH n) j) hB
  have hCpos := hρ.C_pos
  have hε : (0 : ℝ) < 1 / (8 * C) := by positivity
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hconv) _ hε
  have hk1 := hK K le_rfl
  have hk2 := hK (K + 1) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hk1 hk2
  have hne : φ K ≠ φ (K + 1) := (hφ (Nat.lt_succ_self K)).ne
  have h2 := integral_sub_sq_eSeq hρ hd hne
  have hle : ∫ x, (eSeq P (φ K) x - eSeq P (φ (K + 1)) x) ^ 2 ∂P ≤
      C * ∫ x, (eSeq P (φ K) x - eSeq P (φ (K + 1)) x) ^ 2 :=
    integral_le_smul_of_le hCpos.le hb' (fun _ => sq_nonneg _)
      ((memLp_vol ha (hH _)).sub (memLp_vol ha (hH _))).integrable_sq
  have htri : ∫ x, (eSeq P (φ K) x - eSeq P (φ (K + 1)) x) ^ 2 ≤
      2 * (∫ x, (eSeq P (φ K) x - f x) ^ 2) + 2 * ∫ x, (eSeq P (φ (K + 1)) x - f x) ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · refine integral_mono (((memLp_vol ha (hH _)).sub (memLp_vol ha (hH _))).integrable_sq)
        ?_ fun x => ?_
      · exact (((memLp_vol ha (hH _)).sub hf2).integrable_sq.const_mul 2).add
          (((memLp_vol ha (hH _)).sub hf2).integrable_sq.const_mul 2)
      · nlinarith [sq_nonneg (eSeq P (φ K) x + eSeq P (φ (K + 1)) x - 2 * f x)]
    · exact ((memLp_vol ha (hH _)).sub hf2).integrable_sq.const_mul 2
    · exact ((memLp_vol ha (hH _)).sub hf2).integrable_sq.const_mul 2
  have : (2 : ℝ) < 2 := by
    calc (2 : ℝ) = _ := h2.symm
      _ ≤ _ := hle
      _ ≤ C * (2 * (1 / (8 * C)) + 2 * (1 / (8 * C))) := by
          refine mul_le_mul_of_nonneg_left (htri.trans ?_) hCpos.le
          linarith
      _ = 1 / 2 := by field_simp; ring
      _ < 2 := by norm_num
  exact lt_irrefl _ this

theorem integral_mul_sq_le {f g : Torus d → ℝ} (hf : MemLp f 2 (densMeasure ρ))
    (hg : MemLp g 2 (densMeasure ρ)) :
    (∫ x, f x * g x ∂densMeasure ρ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂densMeasure ρ) * ∫ x, g x ^ 2 ∂densMeasure ρ := by
  haveI := hρ.isProb
  have h := real_inner_mul_inner_self_le hf.toLp hg.toLp
  rw [inner_toLp, inner_toLp, inner_toLp] at h
  simp_rw [← sq] at h
  exact h

/-- Orthogonality to all `eₙ` gives orthogonality to `H¹(P)`. -/
theorem orth_H1 (hd : 1 ≤ d) {f : Torus d → ℝ} (hf : MemLp f 2 (densMeasure ρ))
    (hfo : ∀ j, ∫ x, f x * eSeq (densMeasure ρ) j x ∂densMeasure ρ = 0)
    {φ : Torus d → ℝ} (hφ : MemH1 (densMeasure ρ) φ) :
    ∫ x, f x * φ x ∂densMeasure ρ = 0 := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  set lam := fun n => dirE P (eSeq P n)
  have hlam0 : ∀ n, 0 ≤ lam n := fun n => dirE_nonneg hρ _
  set cφ : ℕ → ℝ := fun i => ∫ x, φ x * eSeq P i x ∂P
  -- the remainders
  have hrem : ∀ n, (∫ x, (φ x - ∑ i ∈ Finset.range (n + 1), cφ i * eSeq P i x) ^ 2 ∂P) * lam (n + 1)
      ≤ dirE P φ ∧ ∫ x, f x * φ x ∂P =
        ∫ x, f x * (φ x - ∑ i ∈ Finset.range (n + 1), cφ i * eSeq P i x) ∂P := by
    intro n
    obtain ⟨hH, hon, heig, -⟩ := eSeq_spec hρ hd n
    have hH' : ∀ i ∈ Finset.range (n + 1), MemH1 P (eSeq P i) := fun i hi =>
      hH i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    obtain ⟨h1, h2, h3⟩ := memH1_sub_sum hρ hφ (Finset.range (n + 1)) hH' cφ
    set ψ := fun x => φ x - ∑ i ∈ Finset.range (n + 1), cφ i * eSeq P i x
    have hψo : ∀ j ≤ n, ∫ x, ψ x * eSeq P j x ∂P = 0 := by
      intro j hj
      rw [h3 _ (hH j hj).2.1, Finset.sum_eq_single j]
      · rw [hon j hj j hj, if_pos rfl, mul_one]; simp only [cφ]; ring
      · intro i hi hij
        rw [hon i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) j hj, if_neg hij, mul_zero]
      · intro hj'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj'
    have hEψ : dirE P ψ ≤ dirE P φ := by
      have e1 : dirE P ψ = dirB P φ ψ := by
        rw [dirE_eq_dirB hρ, h2 ψ h1]
        rw [Finset.sum_eq_zero fun i hi => by
          rw [heig i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) ψ h1]
          rw [show ∫ x, eSeq P i x * ψ x ∂P = ∫ x, ψ x * eSeq P i x ∂P by
            congr 1; funext x; ring, hψo i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
          ring]
        ring
      have e2 : dirB P φ ψ = dirE P φ - ∑ i ∈ Finset.range (n + 1), lam i * cφ i ^ 2 := by
        rw [dirB_comm hρ, h2 φ hφ, dirE_eq_dirB hρ φ]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [heig i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) φ hφ]
        simp only [lam, cφ]
        rw [show ∫ x, eSeq P i x * φ x ∂P = ∫ x, φ x * eSeq P i x ∂P by
          congr 1; funext x; ring]
        ring
      rw [e1, e2]
      have : 0 ≤ ∑ i ∈ Finset.range (n + 1), lam i * cφ i ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hlam0 i) (sq_nonneg _)
      linarith
    refine ⟨?_, ?_⟩
    · have := rayleigh_le hρ hd h1 hψo
      rw [mul_comm]; exact this.trans hEψ
    · have e : ∫ x, f x * ψ x ∂P = ∫ x, ψ x * f x ∂P := by congr 1; funext x; ring
      rw [e, h3 f hf, Finset.sum_eq_zero fun i hi => by
        rw [show ∫ x, eSeq P i x * f x ∂P = ∫ x, f x * eSeq P i x ∂P by
          congr 1; funext x; ring, hfo i]; ring, sub_zero]
      congr 1; funext x; ring
  -- the remainders tend to zero
  have hlam := tendsto_lam hρ hd
  set A := dirE P φ
  have hA0 : 0 ≤ A := dirE_nonneg hρ φ
  have key : ∀ ε > 0, |∫ x, f x * φ x ∂P| ≤ ε := by
    intro ε hε
    set F2 := ∫ x, f x ^ 2 ∂P
    have hF2 : 0 ≤ F2 := integral_nonneg fun _ => sq_nonneg _
    set B := (F2 + 1) * (A + 1) / ε ^ 2
    have hB : 0 < B := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp hlam) B)
    obtain ⟨hr1, hr2⟩ := hrem N
    have hlN := hN (N + 1) (by omega)
    set ψ := fun x => φ x - ∑ i ∈ Finset.range (N + 1), cφ i * eSeq P i x
    have hψ2 : MemLp ψ 2 P := by
      have hH := (eSeq_spec hρ hd N).1
      exact (memH1_sub_sum hρ hφ (Finset.range (N + 1)) (fun i hi =>
        hH i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) cφ).1.2.1
    set Ψ := ∫ x, ψ x ^ 2 ∂P
    have hΨ0 : 0 ≤ Ψ := integral_nonneg fun _ => sq_nonneg _
    have hΨ : Ψ ≤ A / B := by
      rw [le_div_iff₀ hB]
      calc Ψ * B ≤ Ψ * lam (N + 1) := mul_le_mul_of_nonneg_left hlN hΨ0
        _ ≤ A := hr1
    have hCS := integral_mul_sq_le hρ hf hψ2
    rw [← hr2] at hCS
    have hsq : (∫ x, f x * φ x ∂P) ^ 2 ≤ ε ^ 2 := by
      calc (∫ x, f x * φ x ∂P) ^ 2 ≤ F2 * Ψ := hCS
        _ ≤ F2 * (A / B) := mul_le_mul_of_nonneg_left hΨ hF2
        _ = ε ^ 2 * (F2 * A / ((F2 + 1) * (A + 1))) := by
            simp only [B]; field_simp
        _ ≤ ε ^ 2 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_one (by positivity)]
            nlinarith
        _ = ε ^ 2 := mul_one _
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hε.le] at this
  by_contra hne
  have hpos : 0 < |∫ x, f x * φ x ∂P| := abs_pos.mpr hne
  have := key _ (half_pos hpos)
  linarith

theorem memH1_theta {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    MemH1 (densMeasure ρ) (fun y => Θ (secT y)) := by
  refine memH1_of_vol hρ (memH1_of_contDiff ?_)
  have : (fun y => Θ (secT y)) ∘ liftT = Θ := by funext x; exact hp.secT_liftT x
  rw [this]; exact hΘ

/-- **Completeness.** -/
theorem eSeq_complete (hd : 1 ≤ d) {f : Torus d → ℝ} (hf : MemLp f 2 (densMeasure ρ))
    (hfo : ∀ j, ∫ x, f x * eSeq (densMeasure ρ) j x ∂densMeasure ρ = 0) :
    f =ᵐ[densMeasure ρ] 0 := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  have hfv : MemLp f 2 volume := hf.of_measure_le_smul ENNReal.ofReal_ne_top hρ.haar_le_smul
  set g := fun x => ρ x * f x
  have hg : MemLp g 2 volume := by
    refine (hfv.const_mul C).of_le (hρ.meas.aestronglyMeasurable.mul hfv.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hρ.nonneg x),
      abs_of_nonneg hρ.C_pos.le]
    exact mul_le_mul_of_nonneg_right (hρ.upper x) (abs_nonneg _)
  have hgi : Integrable g volume := hg.integrable one_le_two
  have hθ : ∀ (Θ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, g y * Θ (secT y) = 0 := by
    intro Θ hΘ hp
    have h := orth_H1 hρ hd hf hfo (memH1_theta hρ hΘ hp)
    rw [hρ.integral_eq] at h
    rw [← h]; congr 1; funext y; simp only [g]; ring
  have hcf : ∀ k, mFourierCoeff (fun y => (g y : ℂ)) k = 0 := by
    intro k
    rw [mFourierCoeff_eq_theta hgi, hθ _ (contDiff_thC k) (isPer_thC k),
      hθ _ (contDiff_thS k) (isPer_thS k)]
    simp
  have hP := hasSum_sq_mFourierCoeff_real hg
  simp only [hcf, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hP
  have h0 : ∫ y, g y ^ 2 = 0 := (hasSum_zero.unique hP).symm
  have hg0 : g =ᵐ[volume] 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (g y)) hg.integrable_sq).mp h0
    filter_upwards [this] with y hy
    simpa using hy
  refine hρ.ac.ae_le ?_
  filter_upwards [hg0] with y hy
  simp only [g, Pi.zero_apply, mul_eq_zero] at hy ⊢
  exact hy.resolve_left (hρ.pos.trans_le (hρ.lower y)).ne'

/-- **The successive minimizers form a reference eigenbasis.** -/
theorem isRefEigenbasis_eSeq (hd : 1 ≤ d) :
    IsRefEigenbasis (densMeasure ρ) (eSeq (densMeasure ρ))
      (fun n => dirE (densMeasure ρ) (eSeq (densMeasure ρ) n)) where
  zero := eSeq_zero _
  memH1 j := (eSeq_spec hρ hd j).1 j le_rfl
  orthonormal i j := (eSeq_spec hρ hd (max i j)).2.1 i (le_max_left _ _) j (le_max_right _ _)
  complete f hf hfo := eSeq_complete hρ hd hf hfo
  eigen j φ hφ := (eSeq_spec hρ hd j).2.2.1 j le_rfl φ hφ
  mono := monotone_nat_of_le_succ fun n =>
    (eSeq_spec hρ hd (n + 1)).2.2.2.2 n (Nat.lt_succ_self n)

end SharpLSI
