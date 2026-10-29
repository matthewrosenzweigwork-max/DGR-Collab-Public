import SharpSymmetricLSI.Paper.Occ15
import SharpSymmetricLSI.Paper.FourierSynth

/-!
# Spectral facts for the reference eigenbasis (Phase 3, lane D; R29 groundwork)

`λ_j ≥ 4π²/(ab) > 0` for `j ≥ 1` (Poincaré on `𝕋^d` and density comparison), `λ_j → ∞`
(Rellich and orthonormality), hence `{α : Λ_α ≤ L}` is finite.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section spec
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

omit hyp hμ in
theorem lam_eq_dirichlet (j : ℕ) :
    lam j = ∫ x, sqNorm (weakGrad (e j) x) ∂(μ : Measure (Torus d)) := by
  have h := he.eigen j (e j) (he.memH1 j)
  simp only [he.orthonormal j j, ↓reduceIte, mul_one] at h
  rw [← h]
  simp only [sqNorm, sq]

/-- `λ_j ≥ 4π²/(ab)` for `j ≥ 1`. -/
theorem exists_lam_lower : ∃ c : ℝ, 0 < c ∧ ∀ j, 1 ≤ j → c ≤ lam j := by
  obtain ⟨a, ha⟩ := haar_le_smul_minimizer hyp hμ (d := d)
  obtain ⟨b, hb0, hb⟩ := minimizer_le_smul_haar hyp hμ
  have ha0 : 0 < a := by
    by_contra h
    push Not at h
    have h1 := ha.trans (le_of_eq (by rw [ENNReal.ofReal_of_nonpos h, zero_smul]))
    have h2 : haar d Set.univ ≤ 0 := by simpa using h1 Set.univ
    rw [measure_univ] at h2
    exact absurd h2 (by norm_num)
  refine ⟨4 * π ^ 2 / (a * b), by positivity, fun j hj => ?_⟩
  set μm := (μ : Measure (Torus d))
  have hH := he.memH1 j
  have hw := isWeakGrad_weakGrad hH.1
  have hL := memLp_vol ha hH
  have hg : ∀ k, MemLp (fun y => weakGrad (e j) y k) 2 volume := memLp_grad_vol ha hb hH
  have hP := poincare_torus hw hL hg
  -- `Var_vol(e) ≥ 1/b`
  have hmean : ∫ x, e j x ∂μm = 0 := by
    have h := he.orthonormal j 0
    simp only [he.zero, mul_one, show j ≠ 0 by omega, ↓reduceIte] at h
    exact h
  have hvar : 1 / b ≤ ProbabilityTheory.variance (e j) volume := by
    rw [ProbabilityTheory.variance_eq_integral hL.aestronglyMeasurable.aemeasurable]
    set c := ∫ x, e j x ∂(volume : Measure (Torus d))
    have h1 : ∫ x, (e j x - c) ^ 2 ∂μm ≤ b * ∫ x, (e j x - c) ^ 2 :=
      integral_le_smul_of_le hb0.le hb (fun x => sq_nonneg _)
        ((hL.sub (memLp_const c)).integrable_sq)
    have h2 : ∫ x, (e j x - c) ^ 2 ∂μm = 1 + c ^ 2 := by
      have hi : Integrable (fun x => e j x ^ 2) μm := (he.memLp j).integrable_sq
      have hi1 : Integrable (e j) μm := (he.memLp j).integrable one_le_two
      have : (fun x => (e j x - c) ^ 2) = fun x => e j x ^ 2 - 2 * c * e j x + c ^ 2 := by
        funext x; ring
      rw [this, integral_add (f := fun x => e j x ^ 2 - 2 * c * e j x) (g := fun _ => c ^ 2)
        (hi.sub (hi1.const_mul _)) (integrable_const _),
        integral_sub (f := fun x => e j x ^ 2) (g := fun x => 2 * c * e j x) hi (hi1.const_mul _),
        integral_const_mul, hmean]
      have h3 := he.orthonormal j j
      simp only [↓reduceIte, ← sq] at h3
      rw [h3]; simp
    rw [h2] at h1
    rw [div_le_iff₀ hb0]
    nlinarith [sq_nonneg c]
  have hlam : ∫ x, sqNorm (weakGrad (e j) x) ≤ a * lam j := by
    rw [lam_eq_dirichlet he j]
    exact integral_le_smul_of_le ha0.le ha (fun x => sqNorm_nonneg _)
      (integrable_sqNorm_P hb hH)
  have hsum : ∑ k, ∫ y, weakGrad (e j) y k ^ 2 = ∫ x, sqNorm (weakGrad (e j) x) := by
    unfold sqNorm
    exact (integral_finsetSum _ fun k _ => (hg k).integrable_sq).symm
  rw [hsum] at hP
  rw [div_le_iff₀ (by positivity)]
  have : 4 * π ^ 2 * (1 / b) ≤ a * lam j := by
    calc 4 * π ^ 2 * (1 / b) ≤ 4 * π ^ 2 * ProbabilityTheory.variance (e j) volume := by gcongr
      _ ≤ _ := hP.trans hlam
  rw [mul_one_div, div_le_iff₀ hb0] at this
  linarith

/-- **`λ_j → ∞`.** -/
theorem tendsto_lam_ref : Tendsto lam atTop atTop := by
  obtain ⟨a, ha⟩ := haar_le_smul_minimizer hyp hμ (d := d)
  obtain ⟨b, hb0, hb⟩ := minimizer_le_smul_haar hyp hμ
  have ha0 : 0 < a := by
    by_contra h
    push Not at h
    have h1 := ha.trans (le_of_eq (by rw [ENNReal.ofReal_of_nonpos h, zero_smul]))
    have h2 : haar d Set.univ ≤ 0 := by simpa using h1 Set.univ
    rw [measure_univ] at h2
    exact absurd h2 (by norm_num)
  set μm := (μ : Measure (Torus d))
  refine tendsto_atTop_atTop_of_monotone he.mono fun L => ?_
  by_contra hcon
  push Not at hcon
  -- the `e_{n+1}` are bounded in `H¹(m)`
  set u : ℕ → Torus d → ℝ := fun n => e (n + 1)
  have hH : ∀ n, MemH1 μm (u n) := fun n => he.memH1 _
  have hw : ∀ n, IsWeakGrad (u n) (weakGrad (u n)) := fun n => isWeakGrad_weakGrad (hH n).1
  have hu : ∀ n, MemLp (u n) 2 volume := fun n => memLp_vol ha (hH n)
  have hg : ∀ n k, MemLp (fun y => weakGrad (u n) y k) 2 volume := fun n =>
    memLp_grad_vol ha hb (hH n)
  have hB : ∀ n, (∫ y, u n y ^ 2) + ∑ k, ∫ y, weakGrad (u n) y k ^ 2 ≤ a + a * L := by
    intro n
    have h1 : ∫ y, u n y ^ 2 ≤ a * ∫ y, u n y ^ 2 ∂μm :=
      integral_le_smul_of_le ha0.le ha (fun y => sq_nonneg _) (he.memLp _).integrable_sq
    have h1' : ∫ y, u n y ^ 2 ∂μm = 1 := by
      have := he.orthonormal (n + 1) (n + 1)
      simp only [↓reduceIte, ← sq] at this
      exact this
    have h2 : ∑ k, ∫ y, weakGrad (u n) y k ^ 2 ≤ a * lam (n + 1) := by
      have hsum : ∑ k, ∫ y, weakGrad (u n) y k ^ 2 = ∫ x, sqNorm (weakGrad (u n) x) := by
        unfold sqNorm
        exact (integral_finsetSum _ fun k _ => (hg n k).integrable_sq).symm
      rw [hsum, lam_eq_dirichlet he]
      exact integral_le_smul_of_le ha0.le ha (fun x => sqNorm_nonneg _)
        (integrable_sqNorm_P hb (hH n))
    have h3 : lam (n + 1) ≤ L := (hcon (n + 1)).le
    rw [h1', mul_one] at h1
    nlinarith
  obtain ⟨φ, hφ, f, -, hf, -, -, hconv, -⟩ := rellich_torus hw hu hg hB
  -- orthonormality: `∫(u_i - u_j)² dμ = 2`
  have horth : ∀ i j, i ≠ j → 2 / b ≤ ∫ y, (u i y - u j y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) := by
    intro i j hij
    have hint : Integrable (fun y => (u i y - u j y) ^ 2) volume := ((hu i).sub (hu j)).integrable_sq
    have h1 : ∫ y, (u i y - u j y) ^ 2 ∂μm ≤ b * ∫ y, (u i y - u j y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) :=
      integral_le_smul_of_le hb0.le hb (fun y => sq_nonneg _) hint
    have h2 : ∫ y, (u i y - u j y) ^ 2 ∂μm = 2 := by
      have hi := (he.memLp (i + 1)).integrable_sq
      have hj := (he.memLp (j + 1)).integrable_sq
      have hij' := (he.memLp (i + 1)).integrable_mul (he.memLp (j + 1))
      have : (fun y => (u i y - u j y) ^ 2) =
          fun y => (u i y ^ 2 + u j y ^ 2) - 2 * (u i y * u j y) := by funext y; ring
      rw [this, integral_sub (f := fun y => u i y ^ 2 + u j y ^ 2)
        (g := fun y => 2 * (u i y * u j y)) (hi.add hj) (hij'.const_mul 2),
        integral_add (f := fun y => u i y ^ 2) (g := fun y => u j y ^ 2) hi hj,
        integral_const_mul]
      have e1 := he.orthonormal (i + 1) (i + 1)
      have e2 := he.orthonormal (j + 1) (j + 1)
      have e3 := he.orthonormal (i + 1) (j + 1)
      simp only [↓reduceIte, ← sq] at e1 e2
      simp only [show i + 1 ≠ j + 1 by omega, ↓reduceIte] at e3
      simp only [u]
      rw [e1, e2, e3]; ring
    rw [div_le_iff₀ hb0]; linarith
  have hε : (0 : ℝ) < 1 / (4 * b) := by positivity
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hconv) _ hε
  have hle : ∀ n ≥ N0, ∫ y, (u (φ n) y - f y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) < 1 / (4 * b) := fun n hn => by
    have := hN0 n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hne : φ N0 ≠ φ (N0 + 1) := (hφ (Nat.lt_succ_self N0)).ne
  have h1 := horth _ _ hne
  have h2 : ∫ y, (u (φ N0) y - u (φ (N0 + 1)) y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) ≤
      2 * ∫ y, (u (φ N0) y - f y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) + 2 * ∫ y, (u (φ (N0 + 1)) y - f y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) := by
    have hX : Integrable (fun y => 2 * (u (φ N0) y - f y) ^ 2) volume :=
      ((hu (φ N0)).sub hf).integrable_sq.const_mul 2
    have hY : Integrable (fun y => 2 * (u (φ (N0 + 1)) y - f y) ^ 2) volume :=
      ((hu (φ (N0 + 1))).sub hf).integrable_sq.const_mul 2
    have key : ∫ y, (2 * (u (φ N0) y - f y) ^ 2 + 2 * (u (φ (N0 + 1)) y - f y) ^ 2) ∂(volume : Measure (UnitAddTorus (Fin d))) =
        2 * ∫ y, (u (φ N0) y - f y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) + 2 * ∫ y, (u (φ (N0 + 1)) y - f y) ^ 2 ∂(volume : Measure (UnitAddTorus (Fin d))) := by
      rw [integral_add hX hY, integral_const_mul, integral_const_mul]
    rw [← key]
    exact integral_mono (((hu _).sub (hu _)).integrable_sq) (hX.add hY) fun y => by
      nlinarith [sq_nonneg (u (φ N0) y + u (φ (N0 + 1)) y - 2 * f y)]
  have h3 := hle N0 le_rfl
  have h4 := hle (N0 + 1) (Nat.le_succ N0)
  have : 2 / b < 1 / b := by
    calc 2 / b ≤ _ := h1
      _ ≤ _ := h2
      _ < 2 * (1 / (4 * b)) + 2 * (1 / (4 * b)) := by linarith
      _ = 1 / b := by field_simp; ring
  have : (1 : ℝ) / b < 2 / b := div_lt_div_of_pos_right (by norm_num) hb0
  linarith

/-- **`{α : Λ_α ≤ L}` is finite.** -/
theorem finite_occEnergy_le (L : ℝ) : {α : ℕ →₀ ℕ | occEnergy lam α ≤ L}.Finite := by
  obtain ⟨c, hc0, hc⟩ := exists_lam_lower hyp hμ he
  obtain ⟨n0, hn0⟩ := (tendsto_atTop.mp (tendsto_lam_ref hyp hμ he)) (L + 1) |>.exists_forall_of_atTop
  set M := ⌈L / c⌉₊
  refine ((Finset.range n0).finsupp fun _ => Finset.range (M + 1)).finite_toSet.subset fun α hα => ?_
  simp only [Set.mem_ofPred_eq] at hα
  have hterm : ∀ n ∈ α.support, lam (n + 1) * α n ≤ L := fun n hn => by
    refine le_trans ?_ hα
    unfold occEnergy Finsupp.sum
    exact Finset.single_le_sum (f := fun n => lam (n + 1) * (α n : ℝ))
      (fun m _ => mul_nonneg (hc0.le.trans (hc _ (by omega))) (Nat.cast_nonneg _)) hn
  have hlam1 : ∀ n, 0 < lam (n + 1) := fun n => lt_of_lt_of_le hc0 (hc _ (by omega))
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  refine ⟨fun n hn => Finset.mem_range.mpr ?_, fun n _ => Finset.mem_range.mpr ?_⟩
  · by_contra h
    have h1 := hterm n hn
    have h2 := hn0 (n + 1) (by omega)
    have h3 : (1 : ℝ) ≤ α n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hn)
    nlinarith [hlam1 n]
  · by_cases hn : n ∈ α.support
    · have h1 := hterm n hn
      have h2 : c * α n ≤ L := le_trans (mul_le_mul_of_nonneg_right (hc _ (by omega))
        (Nat.cast_nonneg _)) h1
      have h3 : (α n : ℝ) ≤ L / c := by rw [le_div_iff₀ hc0]; linarith
      have h4 : α n ≤ M := by exact_mod_cast h3.trans (Nat.le_ceil _)
      omega
    · rw [Finsupp.notMem_support_iff.mp hn]; omega

end spec

end SharpLSI
