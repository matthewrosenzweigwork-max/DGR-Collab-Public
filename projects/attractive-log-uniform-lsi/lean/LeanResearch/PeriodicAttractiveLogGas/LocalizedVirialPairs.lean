import LeanResearch.PeriodicAttractiveLogGas.CollectiveSecondMoment
import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialInsidePairs
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialFarPairs
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialLaplacian
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialScalar

/-! Actual near-shell pair sum in the supplied localized virial proof.
The global physical Lipschitz estimate cancels the Green singularity before
summation, including coincident particle positions. -/

noncomputable section
open scoped BigOperators

namespace PeriodicAttractiveLogGas.LocalizedVirialPairs

open CollectiveSecondMoment SeparatedRadius ConditionalLawEstimates

def pairTerm {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (i j : Fin N) : ℝ :=
  inner ℝ (greenGradient (X i - X j)) (G ξ s X (X i) - G ξ s X (X j))

theorem pairTerm_self {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (i : Fin N) : pairTerm ξ s X i i = 0 := by
  simp [pairTerm]

theorem abs_pairTerm_le {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (X : Configuration N) (i j : Fin N) :
    |pairTerm ξ s X i j| ≤ 162 * kernelConstant * mass ξ s X / N := by
  have hM := mass_nonneg ξ s X
  have hC := kernelConstant_pos.le
  by_cases hij : X i = X j
  · simp only [pairTerm, hij, sub_self, inner_zero_right, abs_zero]
    positivity
  · have hz : X i - X j ≠ 0 := sub_ne_zero.mpr hij
    have hr := (torusEuclideanNorm_pos_iff _).mpr hz
    calc
      _ ≤ ‖greenGradient (X i - X j)‖ * ‖G ξ s X (X i) - G ξ s X (X j)‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (kernelConstant / torusEuclideanNorm (X i - X j)) *
          ((162 * mass ξ s X / N) * torusEuclideanNorm (X i - X j)) :=
        mul_le_mul (kernel_gradient_bound _ hz) (G_lipschitz hs hsmall ξ X (X i) (X j))
          (norm_nonneg _) (by positivity)
      _ = _ := by field_simp [hr.ne']

def nearPair {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N)
    (i j : Fin N) : Prop :=
  (torusEuclideanDist (X i) ξ < 4 * s ∧
    4 * s ≤ torusEuclideanDist (X j) ξ ∧ torusEuclideanDist (X j) ξ < K * s) ∨
  (torusEuclideanDist (X j) ξ < 4 * s ∧
    4 * s ≤ torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < K * s)

def nearPairSum {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) : ℝ := by
  classical
  exact ∑ i : Fin N, ∑ j : Fin N, if nearPair ξ s K X i j then pairTerm ξ s X i j else 0

theorem abs_nearPairSum_le {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (K : ℝ) (X : Configuration N) :
    |nearPairSum ξ s K X| ≤ 2 * (162 * kernelConstant * mass ξ s X / N) *
      ballCount ξ (4 * s) X * nearShellCount ξ s K X := by
  classical
  let A := 162 * kernelConstant * mass ξ s X / N
  let b (i : Fin N) : ℝ := if torusEuclideanDist (X i) ξ < 4 * s then 1 else 0
  let n (i : Fin N) : ℝ := if 4 * s ≤ torusEuclideanDist (X i) ξ ∧
      torusEuclideanDist (X i) ξ < K * s then 1 else 0
  have hA : 0 ≤ A := by dsimp [A]; positivity [kernelConstant_pos, mass_nonneg ξ s X]
  have hb (i : Fin N) : 0 ≤ b i := by dsimp [b]; split_ifs <;> norm_num
  have hn (i : Fin N) : 0 ≤ n i := by dsimp [n]; split_ifs <;> norm_num
  have hp (i j : Fin N) :
      |if nearPair ξ s K X i j then pairTerm ξ s X i j else 0| ≤
        A * (b i * n j + b j * n i) := by
    by_cases h : nearPair ξ s K X i j
    · rw [ite_eq_left h]
      apply (abs_pairTerm_le hs hsmall ξ X i j).trans
      change A ≤ A * (b i * n j + b j * n i)
      rcases h with h | h
      · have hbi : b i = 1 := by simp only [b, ite_eq_left h.1]
        have hnj : n j = 1 := by simp only [n, ite_eq_left h.2]
        rw [hbi, hnj, mul_one]
        nlinarith [mul_nonneg (hb j) (hn i)]
      · have hbj : b j = 1 := by simp only [b, ite_eq_left h.1]
        have hni : n i = 1 := by simp only [n, ite_eq_left h.2]
        rw [hbj, hni, mul_one]
        nlinarith [mul_nonneg (hb i) (hn j)]
    · rw [ite_eq_right h, abs_zero]
      exact mul_nonneg hA (add_nonneg (mul_nonneg (hb i) (hn j)) (mul_nonneg (hb j) (hn i)))
  have hbs : (∑ i : Fin N, b i) = (ballCount ξ (4 * s) X : ℝ) :=
    (ballCount_real_eq ξ (4 * s) X).symm
  have hns : (∑ i : Fin N, n i) = (nearShellCount ξ s K X : ℝ) :=
    (nearShellCount_real_eq ξ s K X).symm
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N,
        |if nearPair ξ s K X i j then pairTerm ξ s X i j else 0| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, A * (b i * n j + b j * n i) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hp i j
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hbs, hns]
      rw [← Finset.mul_sum, hns]
      dsimp [A]
      ring

theorem nearPairSum_drift_lower {N : ℕ} (hN : 0 < N) {s β : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hβ : 0 ≤ β)
    (ξ : Torus) (K : ℝ) (X : Configuration N) :
    -(162 * β * kernelConstant * (mass ξ s X / N) * nearShellCount ξ s K X) ≤
      β / (2 * (N : ℝ)) * nearPairSum ξ s K X := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hM := mass_nonneg ξ s X
  have hC := kernelConstant_pos.le
  have hcount : (ballCount ξ (4 * s) X : ℝ) ≤ N := by exact_mod_cast ballCount_le_N ξ (4 * s) X
  have habs := abs_nearPairSum_le hs hsmall ξ K X
  have hbound : |nearPairSum ξ s K X| ≤
      2 * (162 * kernelConstant * mass ξ s X / N) * N * nearShellCount ξ s K X := by
    exact habs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcount (by positivity)) (Nat.cast_nonneg _))
  have hlow := (neg_le_abs (nearPairSum ξ s K X)).trans hbound
  have hm := mul_le_mul_of_nonneg_left hlow (show 0 ≤ β / (2 * (N : ℝ)) by positivity)
  have he : β / (2 * (N : ℝ)) *
      (2 * (162 * kernelConstant * mass ξ s X / N) * N * nearShellCount ξ s K X) =
      162 * β * kernelConstant * (mass ξ s X / N) * nearShellCount ξ s K X := by
    field_simp
  rw [he] at hm
  nlinarith

open CollectiveIntegrationByParts LocalizedVirialInsidePairs LocalizedVirialFarPairs
  LocalizedVirialLaplacian LocalizedVirialScalar HeavyScales

/-- Literal decomposition of the source ordered interaction into the three
classes; pairs outside the support ball contribute exactly zero. -/
theorem ordered_pair_sum_split {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 4 < K)
    (ξ : Torus) (X : Configuration N) :
    (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else pairTerm ξ s X i j) =
      insidePairSum ξ s X + nearPairSum ξ s K X + orderedFarSum ξ s K X := by
  classical
  have hKs : 4 * s < K * s := mul_lt_mul_of_pos_right hK hs
  unfold insidePairSum nearPairSum orderedFarSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp [pairTerm]
  · by_cases hi : torusEuclideanDist (X i) ξ < 4 * s
    · have hni : ¬4 * s ≤ torusEuclideanDist (X i) ξ := not_le.mpr hi
      have hfi : ¬K * s ≤ torusEuclideanDist (X i) ξ := not_le.mpr (hi.trans hKs)
      by_cases hj : torusEuclideanDist (X j) ξ < 4 * s
      · have hnj : ¬4 * s ≤ torusEuclideanDist (X j) ξ := not_le.mpr hj
        have hfj : ¬K * s ≤ torusEuclideanDist (X j) ξ := not_le.mpr (hj.trans hKs)
        simp [hij, hi, hj, hni, hnj, hfi, hfj, nearPair, pairTerm]
      · have hnj : 4 * s ≤ torusEuclideanDist (X j) ξ := le_of_not_gt hj
        by_cases hjk : torusEuclideanDist (X j) ξ < K * s
        · have hfj : ¬K * s ≤ torusEuclideanDist (X j) ξ := not_le.mpr hjk
          simp [hij, hi, hj, hni, hnj, hfi, hfj, hjk, nearPair, pairTerm]
        · have hfj : K * s ≤ torusEuclideanDist (X j) ξ := le_of_not_gt hjk
          simp [hij, hi, hj, hni, hnj, hfi, hfj, hjk, nearPair, pairTerm]
    · have hni : 4 * s ≤ torusEuclideanDist (X i) ξ := le_of_not_gt hi
      by_cases hj : torusEuclideanDist (X j) ξ < 4 * s
      · have hnj : ¬4 * s ≤ torusEuclideanDist (X j) ξ := not_le.mpr hj
        have hfj : ¬K * s ≤ torusEuclideanDist (X j) ξ := not_le.mpr (hj.trans hKs)
        by_cases hik : torusEuclideanDist (X i) ξ < K * s
        · have hfi : ¬K * s ≤ torusEuclideanDist (X i) ξ := not_le.mpr hik
          simp [hij, hi, hj, hni, hnj, hfi, hfj, hik, nearPair, pairTerm]
        · have hfi : K * s ≤ torusEuclideanDist (X i) ξ := le_of_not_gt hik
          simp [hij, hi, hj, hni, hnj, hfi, hfj, hik, nearPair, pairTerm]
      · have hnj : 4 * s ≤ torusEuclideanDist (X j) ξ := le_of_not_gt hj
        simp [hij, hi, hj, nearPair, pairTerm, G_eq_zero_outer hs ξ X hni,
          G_eq_zero_outer hs ξ X hnj]

theorem QFunction_pairDrift_split {N : ℕ} (hN : 0 < N) {s K : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hK : 4 < K) (ξ : Torus) (β : ℝ)
    {X : Configuration N} (hX : X ∉ collisionSet N) :
    (QFunction ξ hs hsmall).pairDrift greenGradient β X =
      β / (2 * (N : ℝ)) * (insidePairSum ξ s X + nearPairSum ξ s K X + orderedFarSum ξ s K X) := by
  rw [C2Function.pairDrift_eq_symmetrized _ hN greenGradient
    (fun _ hz ↦ greenGradient_odd_off_origin hz) β hX]
  simp only [QFunction_particleGradient hN ξ hs hsmall X]
  rw [← ordered_pair_sum_split hs hK ξ X]
  rfl

theorem outerCount_one_le_of_mass_pos {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (hM : 0 < mass ξ s X) :
    (1 : ℝ) ≤ ballCount ξ (4 * s) X := by
  have hc : 0 < ballCount ξ (4 * s) X := by
    exact_mod_cast hM.trans_le (mass_le_outerCount hs ξ X)
  exact_mod_cast Nat.succ_le_of_lt hc

/-- The negative main term permits M/N <= 1 only after proving N2>=1.
This step is common to both later mass branches. -/
theorem insidePairSum_drift_lower_linear {N : ℕ} (hN : 0 < N) {s β : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hβ : 0 ≤ β)
    (ξ : Torus) (X : Configuration N) (hM : 0 < mass ξ s X) (hX : Function.Injective X) :
    mass ξ s X / N * (-(insideCoefficient β s * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
      160 * β * kernelConstant * annulusCount ξ s X) ≤
      β / (2 * (N : ℝ)) * insidePairSum ξ s X := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ mass ξ s X / N := div_nonneg hM.le hn.le
  have hr1 : mass ξ s X / N ≤ 1 := (div_le_one hn).mpr (mass_le_N ξ s X)
  have hrs : (mass ξ s X / N) ^ 2 ≤ mass ξ s X / N := by nlinarith
  have hc := outerCount_one_le_of_mass_pos hs ξ X hM
  have hb := insideCoefficient_nonneg hβ hs.le
  have hmain := mul_le_mul_of_nonneg_right hrs
    (mul_nonneg hb (sub_nonneg.mpr hc))
  have hraw := insidePairSum_drift_lower hN hs hsmall hβ ξ X hM hX
  have he : β * mass ξ s X ^ 2 / (N : ℝ) ^ 2 *
        (1 + 8 * remainderGradientBound * s) * ((ballCount ξ (4 * s) X : ℝ) - 1) =
      (mass ξ s X / N) ^ 2 * (insideCoefficient β s * ((ballCount ξ (4 * s) X : ℝ) - 1)) := by
    simp only [insideCoefficient, div_pow]
    ring
  rw [he] at hraw
  nlinarith only [hraw, hmain]

/-- Combining the proved pair contributions with the exact attractive
generator sign leaves no pair or cancellation hypothesis. -/
theorem QFunction_pairDrift_lower {N : ℕ} (hN : 0 < N) {s β K : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hβ : 0 ≤ β) (hK : 4 < K)
    (ξ : Torus) {X : Configuration N} (hM : 0 < mass ξ s X) (hX : X ∉ collisionSet N) :
    mass ξ s X / N * (-(insideCoefficient β s * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
      (160 * β * kernelConstant + 64 * β * kernelConstant / K) * annulusCount ξ s X -
      162 * β * kernelConstant * nearShellCount ξ s K X -
      farCoefficient β K * ballCount ξ (4 * s) X) ≤
      (QFunction ξ hs hsmall).pairDrift greenGradient β X := by
  have hinj : Function.Injective X := by
    intro i j he
    by_contra hij
    exact hX ⟨i, j, hij, he⟩
  have hi := insidePairSum_drift_lower_linear hN hs hsmall hβ ξ X hM hinj
  have hn := nearPairSum_drift_lower hN hs hsmall hβ ξ K X
  have hf := orderedFarSum_lower_constants hN hβ hs hK ξ X
  rw [QFunction_pairDrift_split hN hs hsmall hK ξ β hX]
  have hh := add_le_add (add_le_add hi hn) hf
  convert hh using 1 <;> simp only [farCoefficient, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- The source estimate before splitting on the sign of M−1. -/
theorem QFunction_generator_before_split {N : ℕ} (hN : 0 < N) {s β K : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hβ : 0 ≤ β) (hK : 4 < K)
    (ξ : Torus) {X : Configuration N} (hM : 0 < mass ξ s X) (hX : X ∉ collisionSet N) :
    mass ξ s X / N * (4 * (mass ξ s X - 1) -
      insideCoefficient β s * ((ballCount ξ (4 * s) X : ℝ) - 1) -
      annulusCoefficient β K * annulusCount ξ s X -
      162 * β * kernelConstant * nearShellCount ξ s K X -
      farCoefficient β K * ballCount ξ (4 * s) X) ≤
      (QFunction ξ hs hsmall).generator β X := by
  have hl := QFunction_laplacian_lower hN hs hsmall ξ X
  have hd := QFunction_pairDrift_lower hN hs hsmall hβ hK ξ hM hX
  change _ ≤ (QFunction ξ hs hsmall).laplacian X +
    (QFunction ξ hs hsmall).pairDrift greenGradient β X
  convert add_le_add hl hd using 1
  simp only [annulusCoefficient]
  ring

/-- Retain the actual nonnegative first Laplacian sum, as required when
the smoothed mass is less than one. -/
theorem QFunction_generator_nonnegative_first {N : ℕ} (hN : 0 < N) {s β K : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hβ : 0 ≤ β) (hK : 4 < K)
    (ξ : Torus) {X : Configuration N} (hM : 0 < mass ξ s X) (hX : X ∉ collisionSet N) :
    mass ξ s X / N * (-(insideCoefficient β s * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
      annulusCoefficient β K * annulusCount ξ s X -
      162 * β * kernelConstant * nearShellCount ξ s K X -
      farCoefficient β K * ballCount ξ (4 * s) X) ≤
      (QFunction ξ hs hsmall).generator β X := by
  have hl := QFunction_laplacian_lower_nonnegative_first hN hs hsmall ξ X
  have hd := QFunction_pairDrift_lower hN hs hsmall hβ hK ξ hM hX
  change _ ≤ (QFunction ξ hs hsmall).laplacian X +
    (QFunction ξ hs hsmall).pairDrift greenGradient β X
  convert add_le_add hl hd using 1
  simp only [annulusCoefficient]
  ring

theorem outerCount_eq_annulus_of_mass_lt_one {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (hM : mass ξ s X < 1) :
    ballCount ξ (4 * s) X = annulusCount ξ s X := by
  have hi : innerCount ξ s X < 1 := by
    exact_mod_cast (innerCount_le_mass hs ξ X).trans_lt hM
  have hz : innerCount ξ s X = 0 := by omega
  rw [outerCount_eq_inner_add_annulus hs, hz, zero_add]

/-- The actual localized virial proposition, with every differential and
pair-class estimate proved for the literal Q and original Gibbs generator.
The two mass cases are separate, including beta0=0. -/
theorem QFunction_generator_lower {N : ℕ} (hN : 0 < N) {s β β₀ K : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hK : 8 ≤ K)
    (hscale : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀)
    (ξ : Torus) {X : Configuration N} (hM : 0 < mass ξ s X) (hX : X ∉ collisionSet N) :
    mass ξ s X / N * ((4 - β₀) / 2 * (mass ξ s X - 1) -
      virialConstant β₀ * shellCount ξ s K X -
      farCoefficient β₀ K * ballCount ξ (4 * s) X) ≤
      (QFunction ξ hs hsmall).generator β X := by
  have hK4 : 4 < K := by linarith
  have hfactor : 0 ≤ mass ξ s X / (N : ℝ) := div_nonneg hM.le (Nat.cast_nonneg N)
  by_cases hM1 : 1 ≤ mass ξ s X
  · have hscalar := large_mass_bracket hβ hβ₀ hβ4 hs.le hK hscale hM1
      (Nat.cast_nonneg (ballCount ξ (4 * s) X)) (Nat.cast_nonneg (annulusCount ξ s X))
      (Nat.cast_nonneg (nearShellCount ξ s K X)) (outerCount_le_mass_add_annulus hs ξ X)
    have h := (mul_le_mul_of_nonneg_left hscalar hfactor).trans
      (QFunction_generator_before_split hN hs hsmall hβ hK4 ξ hM hX)
    simpa only [shellCount, Nat.cast_add] using h
  · have hM1' : mass ξ s X < 1 := lt_of_not_ge hM1
    have hc := outerCount_eq_annulus_of_mass_lt_one hs ξ X hM1'
    have hscalar := small_mass_bracket (K := K) (n₂ := (ballCount ξ (4 * s) X : ℝ))
      hβ hβ₀ hβ4 hs.le hK hscale hM1'
      (Nat.cast_nonneg (ballCount ξ (4 * s) X)) (Nat.cast_nonneg (annulusCount ξ s X))
      (Nat.cast_nonneg (nearShellCount ξ s K X))
    have h := mul_le_mul_of_nonneg_left hscalar hfactor
    have hraw := QFunction_generator_nonnegative_first hN hs hsmall hβ hK4 ξ hM hX
    rw [hc] at hraw
    simp only [shellCount, Nat.cast_add]
    rw [hc] at h
    calc
      _ ≤ mass ξ s X / N * (insideCoefficient β s -
          (annulusCoefficient β K + insideCoefficient β s) * annulusCount ξ s X -
          162 * β * kernelConstant * nearShellCount ξ s K X -
          farCoefficient β K * annulusCount ξ s X) := by simpa only [hc] using h
      _ ≤ _ := by nlinarith only [hraw]

/-- Source corollary: the constructed second moment has positive actual
generator whenever the literal shell count is small. -/
theorem QFunction_generator_separated_lower {N : ℕ} (hN : 0 < N) {s β β₀ K : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hK : separationRadius β₀ ≤ K)
    (hscale : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀)
    (ξ : Torus) {X : Configuration N} (hM : 4 ≤ mass ξ s X)
    (hsh : (shellCount ξ s K X : ℝ) <
      2 * separationConstant β₀ * (4 - β₀) * mass ξ s X)
    (hX : X ∉ collisionSet N) :
    (4 - β₀) / (4 * (N : ℝ)) * mass ξ s X ^ 2 ≤
      (QFunction ξ hs hsmall).generator β X := by
  have hc : (ballCount ξ (4 * s) X : ℝ) ≤ mass ξ s X + shellCount ξ s K X := by
    have h := outerCount_le_mass_add_annulus hs ξ X
    simp only [shellCount, Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) (nearShellCount ξ s K X)]
  exact separated_positive_scalar hN (hβ.trans hβ₀) hβ4 hK hM
    (Nat.cast_nonneg (ballCount ξ (4 * s) X)) hc hsh
    (QFunction_generator_lower hN hβ hβ₀ hβ4 hs hsmall
      ((separationRadius_ge_eight β₀).trans hK) hscale ξ (by linarith) hX)

end PeriodicAttractiveLogGas.LocalizedVirialPairs
