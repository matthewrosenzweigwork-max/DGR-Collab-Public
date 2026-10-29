import SharpSymmetricLSI.Paper.RefSpectrum15

/-!
# R23 (6.1), part 16: the `C^{1,α}` representative with polynomial `C¹` bounds

`∫∂ₖe_t = 0` turns the Hölder bound into `|∂ₖe_t| ≤ K(1+λ)^q`; with `|e_t| ≤ K_B(1+λ)^d`, the
`C¹` limit along `t → 0` (`c1_limit`) is a representative of `e` (`e_t → e` in `L¹`), with
`|E| + |∇E| ≤ C(1+λ)^q`, and its partials are `α`-Hölder for every `α < 1` (Hölder bounds at
every level `N = 2^{m+1}` pass to the limit) (`c1rep`).
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ} {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
  {Lσ : ℝ≥0} (hσ : LipschitzWith Lσ (recipD ρ ∘ liftT))
include hρ hρc hσ

omit hρ hρc hσ in
theorem integral_dpart_eq_zero {u : Torus d → ℝ} (hu : ContDiff ℝ 1 (u ∘ liftT)) (k : Fin d) :
    ∫ y, dpart u k y = 0 :=
  integral_fderiv_torus_eq_zero hu (Pi.single k 1)

omit hρ hρc hσ in
/-- A mean-zero function with a Hölder modulus `≤ M` (and `dist ≤ 1/2`) is bounded by `M`. -/
theorem abs_le_of_mean_zero {V : Torus d → ℝ} (hV : Continuous V) (h0 : ∫ y, V y = 0) {M β : ℝ}
    (hM : 0 ≤ M) (hβ : 0 ≤ β) (hH : ∀ x y, |V x - V y| ≤ M * dist x y ^ β) (x : Torus d) :
    |V x| ≤ M := by
  have hint : Integrable (fun y => V x - V y) :=
    integrable_of_continuous_torus (continuous_const.sub hV)
  have e : V x = ∫ y, (V x - V y) := by
    rw [integral_sub (integrable_const _) (integrable_of_continuous_torus hV), h0]; simp
  rw [e]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |V x - V y| ≤ ∫ _y : Torus d, M := by
        refine integral_mono hint.abs (integrable_const _) fun y => (hH x y).trans ?_
        have hd1 : dist x y ≤ 1 := (dist_torus_le_half x y).trans (by norm_num)
        have : dist x y ^ β ≤ 1 := Real.rpow_le_one dist_nonneg hd1 hβ
        nlinarith
    _ = M := by simp

omit hρ hρc hσ in
theorem sqrt_sqNorm_le_sum (v : Fin d → ℝ) : Real.sqrt (sqNorm v) ≤ ∑ k, |v k| := by
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  unfold sqNorm
  calc ∑ k, v k ^ 2 = ∑ k, |v k| ^ 2 := by simp_rw [sq_abs]
    _ ≤ (∑ k, |v k|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _

omit hρ hρc hσ in
theorem holderWith_of_le {f : Torus d → ℝ} {H : ℝ} (hH : 0 ≤ H) {α : ℝ≥0}
    (h : ∀ x y, |f x - f y| ≤ H * dist x y ^ (α : ℝ)) : HolderWith (Real.toNNReal H) α f := by
  intro x y
  have e1 : edist (f x) (f y) = ENNReal.ofReal |f x - f y| := by rw [edist_dist, Real.dist_eq]
  have e2 : (edist x y) ^ (α : ℝ) = ENNReal.ofReal (dist x y ^ (α : ℝ)) := by
    rw [edist_dist]; exact ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg
  rw [e1, e2, show ((Real.toNNReal H : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal H from rfl,
    ← ENNReal.ofReal_mul hH]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- **The `C^{1,α}` representative.** -/
theorem c1rep (hd : 1 ≤ d) : ∃ Cc : ℝ, ∃ q : ℕ, ∀ e lam, IsEig (densMeasure ρ) e lam →
    ∃ eC : Torus d → ℝ, ContDiff ℝ 1 (eC ∘ liftT) ∧ eC =ᵐ[densMeasure ρ] e ∧
      (∀ x, |eC x| + Real.sqrt (sqNorm fun k => cpartial eC k x) ≤ Cc * (1 + lam) ^ q) ∧
      ∀ α : ℝ≥0, α < 1 → ∃ H : ℝ≥0, ∀ k, HolderWith H α (fun x => cpartial eC k x) := by
  haveI := hρ.isProb
  obtain ⟨KB, hKB, hBnd⟩ := moser_bound hρ
  have hd0 : (d : ℝ) < (2 : ℝ) ^ (d + 1) := by
    have : d < 2 ^ (d + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num)
      (Nat.lt_succ_self d))
    exact_mod_cast this
  obtain ⟨K0, q0, hK0, hH0⟩ := holder_bound hρ hρc hσ hd d hd0
  refine ⟨KB + d * K0, max d q0, fun e lam h => ?_⟩
  have hlam := h.lam_nonneg hρ
  have h1l : (1 : ℝ) ≤ 1 + lam := by linarith
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul h.1
  have hei : Integrable e := hev.integrable one_le_two
  set ts : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hts : ∀ n, 0 < ts n := fun n => by positivity
  set u : ℕ → Torus d → ℝ := fun n => heatT (ts n) e
  set B := KB * (1 + lam) ^ d
  set M := K0 * (1 + lam) ^ q0
  have hM0 : 0 ≤ M := by positivity
  set β : ℝ := 1 - (d : ℝ) / (2 : ℝ) ^ (d + 1)
  have hβ : 0 < β := by
    have : (d : ℝ) / (2 : ℝ) ^ (d + 1) < 1 := by rw [div_lt_one (by positivity)]; exact hd0
    simp only [β]; linarith
  have hu1 : ∀ n, ContDiff ℝ 1 (u n ∘ liftT) := fun n =>
    (heat_smooth hev (hts n)).of_le (by norm_cast)
  have huB : ∀ n x, |u n x| ≤ B := fun n x =>
    abs_heatT_le (hts n) hei.aestronglyMeasurable (hBnd e lam h) x
  have huH : ∀ n x y k, |dpart (u n) k x - dpart (u n) k y| ≤ M * dist x y ^ β := fun n x y k =>
    hH0 e lam h (ts n) (hts n) k x y
  have huD : ∀ n k x, |dpart (u n) k x| ≤ M := fun n k x =>
    abs_le_of_mean_zero (continuous_of_liftT' (contDiff_dpart (n := 0) (hu1 n) k).continuous)
      (integral_dpart_eq_zero (hu1 n) k) hM0 hβ.le (fun x y => huH n x y k) x
  obtain ⟨φ, hφ, E, hE1, hEp, hDp⟩ := c1_limit hu1 hβ hM0 huB huD huH
  refine ⟨E, hE1, ?_, fun x => ?_, fun α hα => ?_⟩
  · -- `E = e` a.e.
    have hts0 : Tendsto (fun n => ts (φ n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop,
        Eventually.of_forall fun n => hts _⟩
    have hL1 := (tendsto_heatT_L1 hei).comp hts0
    obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
      (fun n => (continuous_heatT (hts _) hei).aestronglyMeasurable) hei.aestronglyMeasurable hL1
    have hEe : E =ᵐ[volume] e := by
      filter_upwards [hae] with y hy
      exact tendsto_nhds_unique ((hEp y).comp hns.tendsto_atTop) hy
    exact hρ.ac.ae_le hEe
  · have hE : |E x| ≤ B := le_of_tendsto ((continuous_abs.tendsto _).comp (hEp x))
      (Eventually.of_forall fun n => huB _ x)
    have hD : ∀ k, |cpartial E k x| ≤ M := fun k =>
      le_of_tendsto ((continuous_abs.tendsto _).comp (hDp k x))
        (Eventually.of_forall fun n => huD _ k x)
    calc |E x| + Real.sqrt (sqNorm fun k => cpartial E k x)
        ≤ B + ∑ k, |cpartial E k x| := add_le_add hE (sqrt_sqNorm_le_sum _)
      _ ≤ B + ∑ _k : Fin d, M := by gcongr with k; exact hD k
      _ = KB * (1 + lam) ^ d + d * (K0 * (1 + lam) ^ q0) := by simp [B, M]
      _ ≤ (KB + d * K0) * (1 + lam) ^ (max d q0) := by
          have e1 : (1 + lam) ^ d ≤ (1 + lam) ^ (max d q0) :=
            pow_le_pow_of_one_le h1l (le_max_left _ _)
          have e2 : (1 + lam) ^ q0 ≤ (1 + lam) ^ (max d q0) :=
            pow_le_pow_of_one_le h1l (le_max_right _ _)
          have : (0 : ℝ) ≤ d * K0 := by positivity
          nlinarith
  · -- Hölder continuity of the partials for `α < 1`
    have hα1 : (α : ℝ) < 1 := by exact_mod_cast hα
    obtain ⟨m, hm⟩ := exists_nat_gt ((d : ℝ) / (1 - α) + d)
    have hdα : (0 : ℝ) ≤ (d : ℝ) / (1 - α) := div_nonneg (Nat.cast_nonneg _) (by linarith)
    have hm2 : (m : ℝ) < (2 : ℝ) ^ (m + 1) := by
      have : m < 2 ^ (m + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num)
        (Nat.lt_succ_self m))
      exact_mod_cast this
    have hdm : (d : ℝ) < (2 : ℝ) ^ (m + 1) := by linarith
    have hβm : (α : ℝ) ≤ 1 - (d : ℝ) / (2 : ℝ) ^ (m + 1) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
      have h1 : (d : ℝ) / (1 - α) < (2 : ℝ) ^ (m + 1) := by linarith
      rw [div_lt_iff₀ (by linarith)] at h1
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hpos]
      nlinarith
    obtain ⟨Km, qm, hKm, hHm⟩ := holder_bound hρ hρc hσ hd m hdm
    set Hm := Km * (1 + lam) ^ qm
    refine ⟨Real.toNNReal Hm, fun k => holderWith_of_le (by positivity) fun x y => ?_⟩
    have hlim : |cpartial E k x - cpartial E k y| ≤
        Hm * dist x y ^ (1 - (d : ℝ) / (2 : ℝ) ^ (m + 1)) :=
      le_of_tendsto ((continuous_abs.tendsto _).comp ((hDp k x).sub (hDp k y)))
        (Eventually.of_forall fun n => hHm e lam h _ (hts _) k x y)
    refine hlim.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_exponent_ge' dist_nonneg
      ((dist_torus_le_half x y).trans (by norm_num)) α.2 hβm

end SharpLSI
