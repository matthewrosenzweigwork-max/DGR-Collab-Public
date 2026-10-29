import FullLabeledLSI.Examples.E01a_Common
import FullLabeledLSI.Paper.Sec8Fourier2

/-!
# Lane D, helper E01g0: Fourier toolkit on the circle for the `λ_G` formula (Task A, H4)

Generic Fourier facts on `𝕋^ι` used to classify reference eigenbases of Haar measure on the circle:
convolution with a mode, evenness and reality of Fourier coefficients, and a function with
Fourier support in `{k, -k}` is a.e. `2 Re (α e_k)`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

section generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mFourier_pt_zero (k : ι → ℤ) : mFourier k (0 : UnitAddTorus ι) = 1 := by
  simp [mFourier]

theorem mFourier_neg_pt (k : ι → ℤ) (t : UnitAddTorus ι) : mFourier k (-t) = mFourier (-k) t := by
  have := Sec8.mFourier_sub_eq k 0 t
  rw [zero_sub, mFourier_pt_zero, one_mul] at this
  exact this

/-- Convolution with a mode: `∫ C(x-y) e_k(y) dy = Ĉ(k) e_k(x)`. -/
theorem conv_mFourier (C : UnitAddTorus ι → ℝ) (k : ι → ℤ) (x : UnitAddTorus ι) :
    ∫ y, (C (x - y) : ℂ) * mFourier k y = cf C k * mFourier k x := by
  have h := integral_sub_left_eq_self
    (fun z : UnitAddTorus ι => (C z : ℂ) * mFourier k (x - z)) (volume : Measure (UnitAddTorus ι)) x
  simp only [sub_sub_cancel] at h
  rw [h]
  have e : ∀ z : UnitAddTorus ι, (C z : ℂ) * mFourier k (x - z) =
      mFourier k x * (mFourier (-k) z * (C z : ℂ)) := by
    intro z
    rw [Sec8.mFourier_sub_eq]; ring
  simp_rw [e]
  rw [integral_const_mul]
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul]
  rw [mul_comm]

/-- Even real kernels have even Fourier coefficients. -/
theorem cf_even (C : UnitAddTorus ι → ℝ) (hev : ∀ x, C (-x) = C x) (k : ι → ℤ) :
    cf C (-k) = cf C k := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul, neg_neg]
  have h := integral_sub_left_eq_self
    (fun z : UnitAddTorus ι => mFourier (-k) z * (C z : ℂ)) (volume : Measure (UnitAddTorus ι)) 0
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [zero_sub, hev, mFourier_neg_pt, neg_neg]

/-- Even real kernels have real Fourier coefficients. -/
theorem cf_im_eq_zero (C : UnitAddTorus ι → ℝ) (hev : ∀ x, C (-x) = C x) (k : ι → ℤ) :
    (cf C k).im = 0 := by
  have h1 := cf_neg C k
  rw [cf_even C hev k] at h1
  have := congrArg Complex.im h1
  simp at this
  linarith

theorem cf_real_eq (C : UnitAddTorus ι → ℝ) (hev : ∀ x, C (-x) = C x) (k : ι → ℤ) :
    cf C k = ((cf C k).re : ℂ) := by
  apply Complex.ext <;> simp [cf_im_eq_zero C hev k]


omit [Fintype ι] [DecidableEq ι] in
theorem ne_neg_self {k : ι → ℤ} (hk : k ≠ 0) : k ≠ -k := fun h => hk (by
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  have : k i = 0 := by omega
  simpa using this)

/-- `∫ mFourier m = 1_{m = 0}`. -/
theorem integral_mFourier' (m : ι → ℤ) :
    ∫ y : UnitAddTorus ι, mFourier m y = if m = 0 then 1 else 0 := integral_mFourier m

/-- The Fourier coefficients of `y ↦ 2 Re (α e_k(y))`. -/
theorem cf_two_re (α : ℂ) (k : ι → ℤ) (hk : k ≠ 0) (m : ι → ℤ) :
    cf (fun y => 2 * (α * mFourier k y).re) m =
      (if m = k then α else 0) + (if m = -k then conj α else 0) := by
  have hy : ∀ y : UnitAddTorus ι, (((2 * (α * mFourier k y).re : ℝ)) : ℂ) =
      α * mFourier k y + conj α * mFourier (-k) y := by
    intro y
    rw [mFourier_neg]
    have h := Complex.add_conj (α * mFourier k y)
    rw [map_mul] at h
    exact h.symm
  have hc : Continuous fun y : UnitAddTorus ι => (α * mFourier k y) := continuous_const.mul (mFourier k).continuous
  have hi1 : Integrable (fun y : UnitAddTorus ι => mFourier (-m) y * (α * mFourier k y)) volume :=
    ((mFourier (-m)).continuous.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun y : UnitAddTorus ι => mFourier (-m) y * (conj α * mFourier (-k) y)) volume :=
    ((mFourier (-m)).continuous.mul (continuous_const.mul (mFourier (-k)).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul, hy, mul_add]
  rw [integral_add hi1 hi2]
  have e1 : ∀ y : UnitAddTorus ι, mFourier (-m) y * (α * mFourier k y) = α * mFourier (k - m) y := by
    intro y
    have : mFourier (k - m) y = mFourier k y * mFourier (-m) y := by
      rw [sub_eq_add_neg, add_comm, mFourier_add]; ring
    rw [this]; ring
  have e2 : ∀ y : UnitAddTorus ι, mFourier (-m) y * (conj α * mFourier (-k) y) =
      conj α * mFourier (-k - m) y := by
    intro y
    have : mFourier (-k - m) y = mFourier (-k) y * mFourier (-m) y := by
      rw [sub_eq_add_neg, add_comm, mFourier_add]; ring
    rw [this]; ring
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul, integral_mFourier', integral_mFourier']
  have c1 : (k - m = 0) ↔ (m = k) := by
    constructor
    · intro h; exact (sub_eq_zero.mp h).symm
    · intro h; rw [h]; simp
  have c2 : (-k - m = 0) ↔ (m = -k) := by
    constructor
    · intro h; exact (sub_eq_zero.mp h).symm
    · intro h; rw [h]; simp
  simp only [c1, c2]
  by_cases h1 : m = k
  · have h2 : ¬ m = -k := fun h => ne_neg_self hk (h1.symm.trans h)
    simp only [if_pos h1, if_neg h2]; ring
  · by_cases h2 : m = -k
    · simp only [if_neg h1, if_pos h2]; ring
    · simp only [if_neg h1, if_neg h2]; ring

/-- A real `L²` function with Fourier support in `{k, -k}` (`k ≠ 0`) is a.e. `2 Re (α e_k)`,
`α = û(k)`. -/
theorem ae_eq_two_re (u : UnitAddTorus ι → ℝ) (hu : MemLp u 2 volume) (k : ι → ℤ) (hk : k ≠ 0)
    (hsupp : ∀ m, cf u m ≠ 0 → m = k ∨ m = -k) :
    u =ᵐ[volume] fun y => 2 * (cf u k * mFourier k y).re := by
  set w : UnitAddTorus ι → ℝ := fun y => 2 * (cf u k * mFourier k y).re with hw
  have hwc : Continuous w := by
    simp only [hw]
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul (mFourier k).continuous))
  have hwL : MemLp w 2 volume := hwc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd : MemLp (fun y => u y - w y) 2 volume := hu.sub hwL
  have hcf : ∀ m, cf (fun y => u y - w y) m = 0 := by
    intro m
    rw [cf_sub (hu.integrable one_le_two) (hwL.integrable one_le_two), hw, cf_two_re _ k hk m]
    by_cases h1 : m = k
    · subst h1
      have hneg : m ≠ -m := ne_neg_self hk
      simp [hneg]
    · by_cases h2 : m = -k
      · subst h2
        rw [cf_neg]
        have : -k ≠ k := (ne_neg_self hk).symm
        simp [this]
      · have : cf u m = 0 := by
          by_contra hne
          rcases hsupp m hne with h | h
          · exact h1 h
          · exact h2 h
        simp [h1, h2, this]
  have hP := hasSum_sq_mFourierCoeff_real hd
  simp only [hcf, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hP
  have h0 : ∫ y, (u y - w y) ^ 2 = 0 := (hasSum_zero.unique hP).symm
  have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (u y - w y)) hd.integrable_sq).mp h0
  filter_upwards [this] with y hy
  simp only [Pi.zero_apply] at hy
  have : u y - w y = 0 := by nlinarith [sq_nonneg (u y - w y)]
  linarith


/-- Convolution of `C` with `2 Re (α e_k)` is `Re Ĉ(k)` times the same function. -/
theorem conv_two_re (C : UnitAddTorus ι → ℝ) (hev : ∀ x, C (-x) = C x)
    (hc : Continuous C) (α : ℂ) (k : ι → ℤ) (x : UnitAddTorus ι) :
    ∫ y, C (x - y) * (2 * (α * mFourier k y).re) =
      (cf C k).re * (2 * (α * mFourier k x).re) := by
  have hy : ∀ y : UnitAddTorus ι, (((2 * (α * mFourier k y).re : ℝ)) : ℂ) =
      α * mFourier k y + conj α * mFourier (-k) y := by
    intro y
    rw [mFourier_neg]
    have h := Complex.add_conj (α * mFourier k y)
    rw [map_mul] at h
    exact h.symm
  have hcont : ∀ m : ι → ℤ, Continuous fun y : UnitAddTorus ι => (C (x - y) : ℂ) * mFourier m y :=
    fun m => (Complex.continuous_ofReal.comp (hc.comp (continuous_const.sub continuous_id))).mul
      (mFourier m).continuous
  have hi : ∀ m : ι → ℤ, Integrable (fun y : UnitAddTorus ι => (C (x - y) : ℂ) * mFourier m y) volume :=
    fun m => (hcont m).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Complex.ofReal_injective
  have hk := cf_real_eq C hev k
  generalize hcc : (cf C k).re = c at hk ⊢
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_mul, hy]
  have e1 : ∀ y : UnitAddTorus ι, (C (x - y) : ℂ) * (α * mFourier k y + conj α * mFourier (-k) y) =
      α * ((C (x - y) : ℂ) * mFourier k y) + conj α * ((C (x - y) : ℂ) * mFourier (-k) y) := by
    intro y; ring
  simp_rw [e1]
  rw [integral_add ((hi k).const_mul α) ((hi (-k)).const_mul (conj α)), integral_const_mul,
    integral_const_mul, conv_mFourier, conv_mFourier, cf_even C hev k]
  rw [hk, show mFourier (-k) x = conj (mFourier k x) from mFourier_neg]
  ring

end generic

end SharpLSI.FL.Ex.LaneD
