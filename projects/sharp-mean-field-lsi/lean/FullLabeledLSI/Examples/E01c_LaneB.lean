import FullLabeledLSI.Examples.E01b_LaneA
import SharpSymmetricLSI.Paper.CircleLSI
import SharpSymmetricLSI.Paper.CircleLSIExt

/-!
# E01c: Lane B proofs for Section 9 (Lemma 9.3, Proposition 9.4)

Work in progress; see `Audit/FLX/route_plan_20261008.md`, T3 and T4.
-/

open MeasureTheory InformationTheory Filter Topology Complex UnitAddTorus Set
open scoped ENNReal Real ComplexConjugate ContDiff

namespace SharpLSI.FL
namespace Ex

/-- Fourier coefficients of a function on `𝕋¹`, indexed by `ℤ`. -/
noncomputable def A1 (u : Torus 1 → ℝ) (m : ℤ) : ℂ := cf u (fun _ => m)

theorem A1_neg (u : Torus 1 → ℝ) (m : ℤ) : A1 u (-m) = conj (A1 u m) :=
  cf_neg u (fun _ : Fin 1 => m)

theorem memLp2_smooth {u : Torus 1 → ℝ} (hu : IsSmoothT u) : MemLp u 2 volume :=
  memLp_of_continuous (continuous_of_isSmoothT hu) 2

theorem reindex_hasSum {f : (Fin 1 → ℤ) → ℝ} {c : ℝ} (h : HasSum f c) :
    HasSum (fun m : ℤ => f (fun _ => m)) c :=
  ((Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff).mpr h

theorem parseval_u {u : Torus 1 → ℝ} (hu : IsSmoothT u) :
    HasSum (fun m : ℤ => ‖A1 u m‖ ^ 2) (∫ y, u y ^ 2) :=
  reindex_hasSum (hasSum_sq_mFourierCoeff_real (memLp2_smooth hu))

theorem parseval_du {u : Torus 1 → ℝ} (hu : IsSmoothT u) :
    HasSum (fun m : ℤ => (2 * π * m) ^ 2 * ‖A1 u m‖ ^ 2) (∫ y, dpart u 0 y ^ 2) := by
  have hd := Sec8.isSmoothT_dpart hu 0
  have h := reindex_hasSum (hasSum_sq_mFourierCoeff_real (memLp2_smooth hd))
  convert h using 1
  funext m
  have e : cf (dpart u 0) (fun _ => m) = 2 * π * Complex.I * m * A1 u m := by
    have := cf_dpart (u := u) (hu.of_le (by exact_mod_cast le_top)) 0 (fun _ => m)
    simpa [A1, cf] using this
  show _ = ‖cf (dpart u 0) (fun _ => m)‖ ^ 2
  rw [e, norm_mul, mul_pow]
  have : ‖2 * (π : ℂ) * Complex.I * (m : ℂ)‖ = 2 * π * |(m : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [this]; simp only [mul_pow, sq_abs]

theorem parseval_ddu {u : Torus 1 → ℝ} (hu : IsSmoothT u) :
    HasSum (fun m : ℤ => (2 * π * m) ^ 4 * ‖A1 u m‖ ^ 2) (∫ y, dpart (dpart u 0) 0 y ^ 2) := by
  have hd := Sec8.isSmoothT_dpart (Sec8.isSmoothT_dpart hu 0) 0
  have h := reindex_hasSum (hasSum_sq_mFourierCoeff_real (memLp2_smooth hd))
  convert h using 1
  funext m
  have e := Sec8.cf_dpart2 hu 0 (fun _ => m)
  show _ = ‖cf (dpart (dpart u 0) 0) (fun _ => m)‖ ^ 2
  rw [e, norm_mul, norm_neg, mul_pow]
  have : ‖(4 * (π : ℂ) ^ 2 * (m : ℂ) ^ 2)‖ = 4 * π ^ 2 * (m : ℝ) ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]; simp [abs_of_pos Real.pi_pos]
  rw [this]
  have e2 : cf u (fun _ => m) = A1 u m := rfl
  rw [e2]; ring


theorem hasSum_prod_cplx {ι : Type} [Fintype ι] [DecidableEq ι] {a b : UnitAddTorus ι → ℂ}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    HasSum (fun k => conj (mFourierCoeff a k) * mFourierCoeff b k) (∫ t, conj (a t) * b t) := by
  set μ' : Measure (UnitAddTorus ι) := Measure.pi fun _ => AddCircle.haarAddCircle with hμ'
  have ha' : MemLp a 2 μ' := by rw [hμ', ← volume_eq_haarPi]; exact ha
  have hb' : MemLp b 2 μ' := by rw [hμ', ← volume_eq_haarPi]; exact hb
  have hP := hasSum_prod_mFourierCoeff (ha'.toLp _) (hb'.toLp _)
  have hca : ∀ k, mFourierCoeff (ha'.toLp _ : UnitAddTorus ι → ℂ) k = mFourierCoeff a k := fun k =>
    integral_congr_ae (ha'.coeFn_toLp.mono fun t ht => by simp only [ht])
  have hcb : ∀ k, mFourierCoeff (hb'.toLp _ : UnitAddTorus ι → ℂ) k = mFourierCoeff b k := fun k =>
    integral_congr_ae (hb'.coeFn_toLp.mono fun t ht => by simp only [ht])
  have hi : ∫ t, conj ((ha'.toLp _ : UnitAddTorus ι → ℂ) t) * (hb'.toLp _ : UnitAddTorus ι → ℂ) t ∂μ' =
      ∫ t, conj (a t) * b t := by
    have e : ∫ t, conj ((ha'.toLp _ : UnitAddTorus ι → ℂ) t) *
        (hb'.toLp _ : UnitAddTorus ι → ℂ) t ∂μ' = ∫ t, conj (a t) * b t ∂μ' :=
      integral_congr_ae ((ha'.coeFn_toLp.and hb'.coeFn_toLp).mono fun t ht => by
        simp only [ht.1, ht.2])
    rw [e, hμ', ← volume_eq_haarPi]
  simp only [hca, hcb] at hP
  rw [← hi]
  exact hP


/-- `Z u = ∫ e^{4πi x} u(x)² dm`. -/
noncomputable def Zmode (u : Torus 1 → ℝ) : ℂ :=
  ∫ y : Torus 1, fourier (2 : ℤ) (y 0) * ((u y ^ 2 : ℝ) : ℂ) ∂haar 1

theorem mFourierCoeff_mode_mul (f : Torus 1 → ℂ) (k : Fin 1 → ℤ) :
    mFourierCoeff (fun y => fourier (2 : ℤ) (y 0) * f y) k = mFourierCoeff f (fun i => k i - 2) := by
  simp only [mFourierCoeff]
  congr 1; funext y
  simp only [smul_eq_mul]
  have e1 : mFourier (-k) y = fourier (-(k 0)) (y 0) := by simp [mFourier]
  have e2 : mFourier (-(fun i => k i - 2)) y = fourier (2 - k 0) (y 0) := by
    simp [mFourier]
  rw [e1, e2, ← mul_assoc, ← fourier_add]
  congr 3; ring

theorem hasSum_Z {u : Torus 1 → ℝ} (hu : IsSmoothT u) :
    HasSum (fun m : ℤ => A1 u m * A1 u (-m - 2)) (Zmode u) := by
  have hfc : Continuous (fun y : Torus 1 => fourier (2 : ℤ) (y 0)) :=
    (fourier (2 : ℤ)).continuous.comp (continuous_apply (0 : Fin 1))
  have huc : Continuous (fun y : Torus 1 => (u y : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_of_isSmoothT hu)
  have hf : MemLp (fun y : Torus 1 => (u y : ℂ)) 2 volume :=
    huc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : MemLp (fun y : Torus 1 => fourier (2 : ℤ) (y 0) * (u y : ℂ)) 2 volume :=
    (hfc.mul huc).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP := hasSum_prod_cplx hf hg
  have hint : ∫ t, conj ((u t : ℂ)) * (fourier (2 : ℤ) (t 0) * (u t : ℂ)) = Zmode u := by
    unfold Zmode
    congr 1; funext t
    simp only [Complex.conj_ofReal]
    push_cast; ring
  rw [hint] at hP
  have hr := ((Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff).mpr hP
  have e : ∀ m : ℤ, conj (mFourierCoeff (fun y : Torus 1 => (u y : ℂ)) (fun _ => m)) *
      mFourierCoeff (fun y : Torus 1 => fourier (2 : ℤ) (y 0) * (u y : ℂ)) (fun _ => m) =
      A1 u (-m) * A1 u (m - 2) := fun m => by
    have hA : A1 u (-m) = conj (mFourierCoeff (fun y : Torus 1 => (u y : ℂ)) (fun _ => m)) := A1_neg u m
    rw [mFourierCoeff_mode_mul, ← hA]
    rfl
  have hr' : HasSum (fun m : ℤ => A1 u (-m) * A1 u (m - 2)) (Zmode u) := by
    refine HasSum.congr_fun (f := fun m : ℤ => _) hr (fun m => ?_)
    exact (e m).symm
  have hfun : (fun m : ℤ => A1 u m * A1 u (-m - 2)) =
      (fun m : ℤ => A1 u (-m) * A1 u (m - 2)) ∘ (Equiv.neg ℤ) := by
    funext m; simp [Function.comp_def]
  rw [hfun]
  exact ((Equiv.neg ℤ).hasSum_iff).mpr hr'


theorem tsum_int_sym {g : ℤ → ℝ} (hg : Summable g) (hsym : ∀ m, g (-m) = g m) :
    ∑' m, g m = g 0 + 2 * ∑' n : ℕ, g ((n : ℤ) + 1) := by
  have h1 : Summable fun n : ℕ => g (n : ℤ) := hg.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => g (-((n : ℤ) + 1)) := by
    have : (fun n : ℕ => g (-((n : ℤ) + 1))) = fun n : ℕ => g ((n : ℤ) + 1) := by
      funext n; exact hsym _
    rw [this]
    exact hg.comp_injective (fun a b h => by exact_mod_cast (add_right_cancel h))
  rw [tsum_of_nat_of_neg_add_one h1 h2, Summable.tsum_eq_zero_add h1]
  have : (fun n : ℕ => g (-((n : ℤ) + 1))) = fun n : ℕ => g (((n : ℕ) : ℤ) + 1) := by
    funext n; exact hsym _
  rw [this]
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  ring


section SeqIneq
open scoped BigOperators
theorem tsum_cs {x y : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxs : Summable fun i => x i ^ 2) (hys : Summable fun i => y i ^ 2) :
    ∑' i, x i * y i ≤ Real.sqrt ((∑' i, x i ^ 2) * (∑' i, y i ^ 2)) := by
  have hsum : Summable fun i => x i * y i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hx i) (hy i))
      (fun i => by nlinarith [sq_nonneg (x i - y i)]) ((hxs.add hys).div_const 2)
  set A := ∑' i, x i ^ 2 with hAdef
  set B := ∑' i, y i ^ 2 with hBdef
  set S := ∑' i, x i * y i with hSdef
  have hA : 0 ≤ A := tsum_nonneg fun i => sq_nonneg _
  have hB : 0 ≤ B := tsum_nonneg fun i => sq_nonneg _
  have key : ∀ l : ℝ, 0 < l → 2 * S ≤ l * A + B / l := fun l hl => by
    have h : ∀ i, 2 * (x i * y i) ≤ l * x i ^ 2 + y i ^ 2 / l := fun i => by
      have : 0 ≤ (l * x i - y i) ^ 2 / l := by positivity
      have e : (l * x i - y i) ^ 2 / l = l * x i ^ 2 - 2 * (x i * y i) + y i ^ 2 / l := by
        field_simp; ring
      linarith
    have h2 := Summable.tsum_le_tsum h (hsum.mul_left 2) ((hxs.mul_left l).add (hys.div_const l))
    rw [tsum_mul_left, Summable.tsum_add (hxs.mul_left l) (hys.div_const l), tsum_mul_left, tsum_div_const] at h2
    linarith
  have hS : S ≤ Real.sqrt (A * B) := by
    by_cases hS0 : S ≤ 0
    · exact hS0.trans (Real.sqrt_nonneg _)
    · rw [not_le] at hS0
      rcases hA.eq_or_lt with hA0 | hApos
      · exfalso
        have := key (B / S + 1) (by positivity)
        rw [← hA0] at this
        have h3 : 2 * S ≤ B / (B / S + 1) := by simpa using this
        have h4 : B / (B / S + 1) < S := by
          rw [div_lt_iff₀ (by positivity)]
          have : B / S * S = B := by field_simp
          nlinarith
        linarith
      · have := key (S / A) (by positivity)
        have e : S / A * A + B / (S / A) = S + B * A / S := by field_simp
        rw [e] at this
        have h5 : S ≤ B * A / S := by linarith
        have h6 : S * S ≤ B * A := by
          rw [le_div_iff₀ hS0] at h5; exact h5
        exact Real.le_sqrt_of_sq_le (by nlinarith)
  exact hS


/-- The pure Fourier-sequence inequality behind Lemma 9.3.  `α j = ‖a_j‖`, `j ≥ 0`. -/
theorem seq_ineq (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j)
    (hs0 : Summable fun j => α j ^ 2)
    (hs2 : Summable fun j : ℕ => ((j : ℝ) + 1) ^ 2 * α (j + 1) ^ 2)
    (hs4 : Summable fun j : ℕ => (((j : ℝ) + 2) ^ 4 - ((j : ℝ) + 2) ^ 2) * α (j + 2) ^ 2)
    (hn : α 0 ^ 2 + 2 * ∑' j, α (j + 1) ^ 2 = 1) :
    (α 1 ^ 2 + 2 * ∑' s, α (s + 2) * α s) ^ 2 ≤
      11 / 36 * (2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * α (j + 1) ^ 2) ^ 2 +
        11 / 12 * (2 * ∑' j : ℕ, (((j : ℝ) + 2) ^ 4 - ((j : ℝ) + 2) ^ 2) * α (j + 2) ^ 2) := by
  set D := 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * α (j + 1) ^ 2 with hD
  set K := 2 * ∑' j : ℕ, (((j : ℝ) + 2) ^ 4 - ((j : ℝ) + 2) ^ 2) * α (j + 2) ^ 2 with hK
  have hs0' : Summable fun j => α (j + 1) ^ 2 := (summable_nat_add_iff 1).mpr hs0
  have hs0'' : Summable fun j => α (j + 2) ^ 2 := (summable_nat_add_iff 2).mpr hs0
  have hDnn : 0 ≤ D := by
    rw [hD]; exact mul_nonneg (by norm_num) (tsum_nonneg fun j => by positivity)
  have hKnn : 0 ≤ K := by
    rw [hK]; refine mul_nonneg (by norm_num) (tsum_nonneg fun j => ?_)
    refine mul_nonneg ?_ (sq_nonneg _)
    have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [sq_nonneg ((j:ℝ)+2), sq_nonneg ((j:ℝ) + 2 - 1)]
  -- (4) α₁² ≤ D/2
  have h4 : α 1 ^ 2 ≤ D / 2 := by
    have := hs2.le_tsum 0 (fun j _ => by positivity)
    simp only [Nat.cast_zero, zero_add, one_pow, one_mul] at this
    rw [hD]; linarith
  -- (2) X ≤ K/24
  set X := ∑' s : ℕ, α (s + 2) ^ 2 with hX
  have h2 : 24 * X ≤ K := by
    have hle : ∀ s : ℕ, 12 * α (s + 2) ^ 2 ≤ (((s : ℝ) + 2) ^ 4 - ((s : ℝ) + 2) ^ 2) * α (s + 2) ^ 2 := fun s => by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have : (0:ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      nlinarith [sq_nonneg ((s:ℝ)+2), mul_nonneg this this]
    have := Summable.tsum_le_tsum hle (hs0''.mul_left 12) hs4
    rw [tsum_mul_left] at this
    rw [hK]; linarith
  -- (3) Y ≤ 1
  set Y := ∑' s : ℕ, α s ^ 2 with hY
  have h3 : Y ≤ 1 := by
    have : Y = α 0 ^ 2 + ∑' j, α (j + 1) ^ 2 := by
      rw [hY, Summable.tsum_eq_zero_add hs0]
    have hT : 0 ≤ ∑' j, α (j + 1) ^ 2 := tsum_nonneg fun j => sq_nonneg _
    have h0 : α 0 ^ 2 ≤ 1 := by linarith
    rw [this]; linarith
  -- (1) the cross sum
  have hcs := tsum_cs (x := fun s => α (s + 2)) (y := fun s => α s) (fun s => hα _) (fun s => hα _) hs0'' hs0
  have hXY : (∑' s, α (s + 2) * α s) ≤ Real.sqrt (K / 24) := by
    refine hcs.trans (Real.sqrt_le_sqrt ?_)
    have hX0 : 0 ≤ X := tsum_nonneg fun j => sq_nonneg _
    calc X * Y ≤ X * 1 := mul_le_mul_of_nonneg_left h3 hX0
      _ = X := mul_one X
      _ ≤ K / 24 := by linarith
  have hsum_nn : 0 ≤ ∑' s, α (s + 2) * α s := tsum_nonneg fun s => mul_nonneg (hα _) (hα _)
  -- assemble
  have hkey : α 1 ^ 2 + 2 * ∑' s, α (s + 2) * α s ≤ D / 2 + Real.sqrt (K / 6) := by
    have : 2 * Real.sqrt (K / 24) = Real.sqrt (K / 6) := by
      rw [show K / 6 = 4 * (K / 24) by ring, Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
    linarith
  have hL : 0 ≤ α 1 ^ 2 + 2 * ∑' s, α (s + 2) * α s := by positivity
  have hsq : (D / 2 + Real.sqrt (K / 6)) ^ 2 ≤ 11 / 36 * D ^ 2 + 11 / 12 * K := by
    set r := Real.sqrt (K / 6) with hr
    have hr2 : r ^ 2 = K / 6 := Real.sq_sqrt (by positivity)
    have hK6 : K = 6 * r ^ 2 := by rw [hr2]; ring
    rw [hK6]
    nlinarith [sq_nonneg (D - 9 * r)]
  calc (α 1 ^ 2 + 2 * ∑' s, α (s + 2) * α s) ^ 2 ≤ (D / 2 + Real.sqrt (K / 6)) ^ 2 :=
        pow_le_pow_left₀ hL hkey 2
    _ ≤ _ := hsq


end SeqIneq

theorem seq_to_ineq (A : ℤ → ℂ) (hsym : ∀ m, ‖A (-m)‖ = ‖A m‖) {P R : ℝ} {z : ℂ}
    (hP1 : HasSum (fun m : ℤ => ‖A m‖ ^ 2) 1)
    (hP2 : HasSum (fun m : ℤ => (2 * π * m) ^ 2 * ‖A m‖ ^ 2) P)
    (hP3 : HasSum (fun m : ℤ => (2 * π * m) ^ 4 * ‖A m‖ ^ 2) R)
    (hZ : HasSum (fun m : ℤ => A m * A (-m - 2)) z) :
    ‖z‖ ^ 2 ≤ 11 / 36 * (P / (4 * π ^ 2)) ^ 2 + 11 / 12 * ((R - 4 * π ^ 2 * P) / (16 * π ^ 4)) := by
  have hπ : 0 < π := Real.pi_pos
  set α : ℕ → ℝ := fun n => ‖A (n : ℤ)‖ with hα
  have hαnn : ∀ n, 0 ≤ α n := fun n => norm_nonneg _
  -- symmetric reductions
  have e1 : 1 = ‖A 0‖ ^ 2 + 2 * ∑' n : ℕ, α (n + 1) ^ 2 := by
    rw [← hP1.tsum_eq, tsum_int_sym hP1.summable (fun m => by rw [hsym])]
    simp [hα]
  have e2 : P = 2 * ∑' n : ℕ, (2 * π) ^ 2 * (((n : ℝ) + 1) ^ 2 * α (n + 1) ^ 2) := by
    rw [← hP2.tsum_eq, tsum_int_sym hP2.summable (fun m => by rw [hsym]; push_cast; ring)]
    simp [hα]
    congr 1; congr 1; funext n; ring
  -- the fourth-order combination
  have hg4 : HasSum (fun m : ℤ => (((m : ℝ)) ^ 4 - (m : ℝ) ^ 2) * ‖A m‖ ^ 2)
      ((R - 4 * π ^ 2 * P) / (16 * π ^ 4)) := by
    have := (hP3.sub (hP2.mul_left (4 * π ^ 2))).div_const (16 * π ^ 4)
    convert this using 1
    funext m
    field_simp
    ring
  have e3 : (R - 4 * π ^ 2 * P) / (16 * π ^ 4) =
      2 * ∑' n : ℕ, ((((n : ℝ) + 2) ^ 4 - ((n : ℝ) + 2) ^ 2) * α (n + 2) ^ 2) := by
    rw [← hg4.tsum_eq, tsum_int_sym hg4.summable (fun m => by rw [hsym]; push_cast; ring)]
    simp only [Int.cast_zero, zero_pow (by norm_num : (4:ℕ) ≠ 0), zero_pow (by norm_num : (2:ℕ) ≠ 0),
      sub_self, zero_mul, zero_add]
    have hk : Summable fun n : ℕ => ((((n : ℤ) + 1 : ℤ) : ℝ) ^ 4 - (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2) *
        ‖A ((n : ℤ) + 1)‖ ^ 2 := by
      have inj : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := fun a b h => by
        simpa using h
      exact hg4.summable.comp_injective inj
    rw [Summable.tsum_eq_zero_add hk]
    simp [hα]
    congr 1; congr 1
    funext n
    push_cast; ring
  -- the cross term
  set G : ℤ → ℝ := fun m => ‖A m‖ * ‖A (-m - 2)‖ with hG
  have hGs : Summable G := by
    have := (summable_norm_iff.mpr hZ.summable)
    refine this.congr (fun m => ?_)
    simp [hG, norm_mul]
  have hzb : ‖z‖ ≤ ∑' m, G m := by
    rw [← hZ.tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · exact (summable_norm_iff.mpr hZ.summable)
    · congr 1; funext m; simp [hG, norm_mul]
  have hn1 : Summable fun n : ℕ => G (n : ℤ) := hGs.comp_injective Nat.cast_injective
  have hn2 : Summable fun n : ℕ => G (-((n : ℤ) + 1)) :=
    hGs.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun a b h => by
      have : (a : ℤ) + 1 = (b : ℤ) + 1 := by linarith
      exact_mod_cast (add_right_cancel this))
  have hsplit := tsum_of_nat_of_neg_add_one hn1 hn2
  have hG1 : ∀ n : ℕ, G (n : ℤ) = α n * α (n + 2) := fun n => by
    simp only [hG, hα]
    congr 1
    have : (-(n : ℤ) - 2) = -((n + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [this, hsym]
  have hG2 : ∀ n : ℕ, G (-(((n + 1 : ℕ) : ℤ) + 1)) = α (n + 2) * α n := fun n => by
    simp only [hG, hα]
    have e1 : (-(((n + 1 : ℕ) : ℤ) + 1)) = -((n + 2 : ℕ) : ℤ) := by omega
    have e2 : (-(-(((n + 1 : ℕ) : ℤ) + 1)) - 2) = (n : ℤ) := by omega
    rw [e2, e1, hsym]
  have hG20 : G (-(((0 : ℕ) : ℤ) + 1)) = α 1 ^ 2 := by
    simp only [hG, hα]
    have e1 : (-(((0 : ℕ) : ℤ) + 1)) = -((1 : ℕ) : ℤ) := by omega
    have e2 : (-(-(((0 : ℕ) : ℤ) + 1)) - 2) = -((1 : ℕ) : ℤ) := by omega
    rw [e2, e1, hsym]; ring
  have hsum2 : ∑' n : ℕ, G (-((n : ℤ) + 1)) = α 1 ^ 2 + ∑' n : ℕ, α (n + 2) * α n := by
    rw [Summable.tsum_eq_zero_add hn2, hG20]
    congr 1
    exact tsum_congr hG2
  have hzb2 : ‖z‖ ≤ α 1 ^ 2 + 2 * ∑' n : ℕ, α (n + 2) * α n := by
    rw [hsplit, hsum2] at hzb
    have : ∑' n : ℕ, G (n : ℤ) = ∑' n : ℕ, α (n + 2) * α n := by
      rw [tsum_congr hG1]
      congr 1; funext n; ring
    rw [this] at hzb
    linarith
  -- apply the sequence inequality
  have hs0 : Summable fun j : ℕ => α j ^ 2 := hP1.summable.comp_injective Nat.cast_injective
  have injS : ∀ c : ℕ, Function.Injective (fun n : ℕ => (n : ℤ) + c) := fun c a b h => by
    simpa using h
  have hs2 : Summable fun j : ℕ => ((j : ℝ) + 1) ^ 2 * α (j + 1) ^ 2 := by
    have := (hP2.summable.comp_injective (injS 1)).div_const ((2 * π) ^ 2)
    refine this.congr (fun n => ?_)
    simp only [Function.comp_def, hα]
    push_cast
    field_simp
  have hs4 : Summable fun j : ℕ => (((j : ℝ) + 2) ^ 4 - ((j : ℝ) + 2) ^ 2) * α (j + 2) ^ 2 := by
    have := hg4.summable.comp_injective (injS 2)
    refine this.congr (fun n => ?_)
    simp only [Function.comp_def, hα]
    push_cast
    ring
  have hn : α 0 ^ 2 + 2 * ∑' j, α (j + 1) ^ 2 = 1 := by
    have : α 0 = ‖A 0‖ := by simp [hα]
    rw [this]; exact e1.symm
  have hmain := seq_ineq α hαnn hs0 hs2 hs4 hn
  have hD : 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * α (j + 1) ^ 2 = P / (4 * π ^ 2) := by
    rw [e2, tsum_mul_left]
    field_simp
    ring
  have hK : 2 * ∑' j : ℕ, (((j : ℝ) + 2) ^ 4 - ((j : ℝ) + 2) ^ 2) * α (j + 2) ^ 2 =
      (R - 4 * π ^ 2 * P) / (16 * π ^ 4) := e3.symm
  rw [hD, hK] at hmain
  calc ‖z‖ ^ 2 ≤ (α 1 ^ 2 + 2 * ∑' n : ℕ, α (n + 2) * α n) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hzb2 2
    _ ≤ _ := hmain


theorem fourier_second_mode {u : Torus 1 → ℝ} (hu : IsSmoothT u) (h1 : ∫ y, u y ^ 2 = 1) :
    ‖Zmode u‖ ^ 2 ≤ 11 / 36 * ((∫ y, dpart u 0 y ^ 2) / (4 * π ^ 2)) ^ 2 +
      11 / 12 * (((∫ y, dpart (dpart u 0) 0 y ^ 2) - 4 * π ^ 2 * ∫ y, dpart u 0 y ^ 2) / (16 * π ^ 4)) := by
  refine seq_to_ineq (A1 u) (fun m => by rw [A1_neg, Complex.norm_conj]) ?_ (parseval_du hu)
    (parseval_ddu hu) (hasSum_Z hu)
  have := parseval_u hu
  rwa [h1] at this


/-- A smooth 1-periodic function on `ℝ` as a function on the circle. -/
noncomputable def toTorus (f : ℝ → ℝ) (z : Torus 1) : ℝ := f (secT z 0)

theorem toTorus_liftT {f : ℝ → ℝ} (hper : Function.Periodic f 1) (v : Fin 1 → ℝ) :
    toTorus f (liftT v) = f (v 0) := by
  obtain ⟨m, hm⟩ := secT_liftT_eq v
  unfold toTorus
  rw [hm]
  have := (hper.int_mul (m 0)) (v 0)
  simpa [intVec, add_comm] using this

theorem toTorus_lineT {f : ℝ → ℝ} (hper : Function.Periodic f 1) (x : ℝ) :
    toTorus f (lineT x) = f x := toTorus_liftT hper (lineF x)

theorem isSmoothT_toTorus {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) :
    IsSmoothT (toTorus f) := by
  unfold IsSmoothT
  have : (toTorus f ∘ liftT) = fun v : Fin 1 → ℝ => f (v 0) := by
    funext v; exact toTorus_liftT hper v
  rw [this]
  exact hf.comp (contDiff_apply ℝ ℝ 0)

theorem dpart_toTorus_lineT {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (x : ℝ) :
    dpart (toTorus f) 0 (lineT x) = deriv f x := by
  unfold lineT
  rw [dpart_liftT]
  have : (toTorus f ∘ liftT) = fun v : Fin 1 → ℝ => f (v 0) := by
    funext v; exact toTorus_liftT hper v
  rw [this]
  have hd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have h1 : HasFDerivAt (fun v : Fin 1 → ℝ => f (v 0)) 
      ((fderiv ℝ f x).comp (ContinuousLinearMap.proj 0)) (lineF x) := by
    exact hd.hasFDerivAt.comp (lineF x) (hasFDerivAt_apply 0 _)
  rw [h1.fderiv]
  simp [lineF]


theorem periodic_deriv {f : ℝ → ℝ} (hper : Function.Periodic f 1) : Function.Periodic (deriv f) 1 := by
  intro x
  have h := deriv_comp_add_const (f := f) (a := (1 : ℝ)) (x := x)
  have e : (fun x => f (x + 1)) = f := funext hper
  rw [e] at h
  exact h.symm

theorem lineT_secT (z : Torus 1) : lineT (secT z 0) = z := by
  unfold lineT
  rw [← secT_eq_lineF, liftT_secT]

theorem dpart_toTorus {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) :
    dpart (toTorus f) 0 = toTorus (deriv f) := by
  funext z
  rw [← lineT_secT z, dpart_toTorus_lineT hf hper, toTorus_lineT (periodic_deriv hper)]

theorem contDiff_deriv' {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

theorem integral_Ioc_eq_interval (g : ℝ → ℝ) :
    ∫ x in Ioc (0 : ℝ) 1, g x = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_of_le zero_le_one]

theorem integral_Ioc_eq_interval_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x in Ioc (0 : ℝ) 1, g x = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_of_le zero_le_one]


theorem integral_torus_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Torus 1 → E}
    (hg : Continuous g) : ∫ y, g y ∂haar 1 = ∫ x in (0 : ℝ)..1, g (lineT x) := by
  rw [← integral_Ioc_eq_interval_gen (fun x => g (lineT x))]
  exact (integral_lineT hg.aestronglyMeasurable).symm


theorem fourier_second_mode_line {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (h1 : ∫ x in (0 : ℝ)..1, f x ^ 2 = 1) :
    ‖∫ x in (0 : ℝ)..1, cexp (2 * π * I * 2 * x) * ((f x ^ 2 : ℝ) : ℂ)‖ ^ 2 ≤
      11 / 36 * ((∫ x in (0 : ℝ)..1, deriv f x ^ 2) / (4 * π ^ 2)) ^ 2 +
        11 / 12 * (((∫ x in (0 : ℝ)..1, deriv (deriv f) x ^ 2) -
          4 * π ^ 2 * ∫ x in (0 : ℝ)..1, deriv f x ^ 2) / (16 * π ^ 4)) := by
  have hu := isSmoothT_toTorus hf hper
  have hf' := contDiff_deriv' hf
  have hper' := periodic_deriv hper
  have hu' := isSmoothT_toTorus hf' hper'
  have hd1 : dpart (toTorus f) 0 = toTorus (deriv f) := dpart_toTorus hf hper
  have hd2 : dpart (toTorus (deriv f)) 0 = toTorus (deriv (deriv f)) := dpart_toTorus hf' hper'
  have hcont : ∀ {g : ℝ → ℝ}, ContDiff ℝ ∞ g → Function.Periodic g 1 → Continuous (toTorus g) :=
    fun hg hp => continuous_of_isSmoothT (isSmoothT_toTorus hg hp)
  have I0 : ∫ y, toTorus f y ^ 2 ∂haar 1 = ∫ x in (0 : ℝ)..1, f x ^ 2 := by
    rw [integral_torus_line (g := fun y => toTorus f y ^ 2) ((hcont hf hper).pow 2)]
    simp only [toTorus_lineT hper]
  have I1 : ∫ y, toTorus (deriv f) y ^ 2 ∂haar 1 = ∫ x in (0 : ℝ)..1, deriv f x ^ 2 := by
    rw [integral_torus_line (g := fun y => toTorus (deriv f) y ^ 2) ((hcont hf' hper').pow 2)]
    simp only [toTorus_lineT hper']
  have hf'' := contDiff_deriv' hf'
  have hper'' := periodic_deriv hper'
  have I2 : ∫ y, toTorus (deriv (deriv f)) y ^ 2 ∂haar 1 = ∫ x in (0 : ℝ)..1, deriv (deriv f) x ^ 2 := by
    rw [integral_torus_line (g := fun y => toTorus (deriv (deriv f)) y ^ 2) ((hcont hf'' hper'').pow 2)]
    simp only [toTorus_lineT hper'']
  have IZ : Zmode (toTorus f) = ∫ x in (0 : ℝ)..1, cexp (2 * π * I * 2 * x) * ((f x ^ 2 : ℝ) : ℂ) := by
    unfold Zmode
    have hc : Continuous fun y : Torus 1 => fourier (2 : ℤ) (y 0) * ((toTorus f y ^ 2 : ℝ) : ℂ) :=
      ((fourier (2 : ℤ)).continuous.comp (continuous_apply (0 : Fin 1))).mul
        (Complex.continuous_ofReal.comp ((hcont hf hper).pow 2))
    rw [integral_torus_line hc]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have e0 : (lineT x) 0 = (x : UnitAddCircle) := rfl
    rw [e0, fourier_coe_apply, toTorus_lineT hper]
    push_cast
    congr 2
    ring
  have := fourier_second_mode hu (by rw [I0]; exact h1)
  rw [hd1, hd2, I1, I2, IZ] at this
  exact this



theorem hasDerivAt_deriv_of_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    HasDerivAt g (deriv g x) x :=
  ((hg.differentiable (by simp)) x).hasDerivAt


theorem integral_lin4 {a b c d : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hd : Continuous d) {α β γ δ : ℝ} :
    ∫ x in (0 : ℝ)..1, (α * a x + β * b x + γ * c x + δ * d x) =
      α * (∫ x in (0 : ℝ)..1, a x) + β * (∫ x in (0 : ℝ)..1, b x) +
        γ * (∫ x in (0 : ℝ)..1, c x) + δ * ∫ x in (0 : ℝ)..1, d x := by
  rw [intervalIntegral.integral_add (f := fun x => α * a x + β * b x + γ * c x) (g := fun x => δ * d x)
      ((((ha.const_mul α).add (hb.const_mul β)).add (hc.const_mul γ)).intervalIntegrable _ _)
      ((hd.const_mul δ).intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun x => α * a x + β * b x) (g := fun x => γ * c x)
      (((ha.const_mul α).add (hb.const_mul β)).intervalIntegrable _ _) ((hc.const_mul γ).intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun x => α * a x) (g := fun x => β * b x)
      ((ha.const_mul α).intervalIntegrable _ _) ((hb.const_mul β).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The integral identity for the Fisher information production. -/
theorem L_eq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (hpos : ∀ x, 0 < f x) :
    ∫ x in (0 : ℝ)..1, (16 * deriv f x ^ 2 * deriv (deriv f) x / f x +
        8 * deriv f x * deriv (deriv (deriv f)) x - 8 * deriv f x ^ 4 / f x ^ 2) =
      -8 * (∫ x in (0 : ℝ)..1, deriv (deriv f) x ^ 2) -
        8 / 3 * ∫ x in (0 : ℝ)..1, deriv f x ^ 4 / f x ^ 2 := by
  have hf1 := contDiff_deriv' hf
  have hf2 := contDiff_deriv' hf1
  have hf3 := contDiff_deriv' hf2
  have p1 := periodic_deriv hper
  have p2 := periodic_deriv p1
  have c0 := hf.continuous
  have c1 := hf1.continuous
  have c2 := hf2.continuous
  have c3 := hf3.continuous
  have d0 := hasDerivAt_deriv_of_smooth hf
  have d1 := hasDerivAt_deriv_of_smooth hf1
  have d2 := hasDerivAt_deriv_of_smooth hf2
  have e1 : deriv f 1 = deriv f 0 := by simpa using p1 0
  have e2 : deriv (deriv f) 1 = deriv (deriv f) 0 := by simpa using p2 0
  have e0 : f 1 = f 0 := by simpa using hper 0
  -- IBP1
  have ibp1 : ∫ x in (0 : ℝ)..1, (deriv (deriv f) x ^ 2 + deriv f x * deriv (deriv (deriv f)) x) = 0 := by
    refine integral_deriv_periodic (F := fun x => deriv f x * deriv (deriv f) x) (fun x => ?_)
      ((c2.pow 2).add (c1.mul c3)) (by simp only [e1, e2])
    exact ((d1 x).mul (d2 x)).congr_deriv (by ring)
  -- IBP2
  have ibp2 : ∫ x in (0 : ℝ)..1, (3 * deriv f x ^ 2 * deriv (deriv f) x / f x -
      deriv f x ^ 4 / f x ^ 2) = 0 := by
    have hc : Continuous fun x => 3 * deriv f x ^ 2 * deriv (deriv f) x / f x - deriv f x ^ 4 / f x ^ 2 :=
      (((continuous_const.mul (c1.pow 2)).mul c2).div c0 fun x => (hpos x).ne').sub
        ((c1.pow 4).div (c0.pow 2) fun x => (pow_pos (hpos x) 2).ne')
    refine integral_deriv_periodic (F := fun x => deriv f x ^ 3 / f x) (fun x => ?_) hc
      (by simp only [e1, e0])
    have h := ((d1 x).pow 3).div (d0 x) (hpos x).ne'
    refine h.congr_deriv ?_
    have := (hpos x).ne'
    simp only [Pi.pow_apply]
    push_cast
    field_simp
  -- combine
  have hA : Continuous fun x => 3 * deriv f x ^ 2 * deriv (deriv f) x / f x - deriv f x ^ 4 / f x ^ 2 :=
    (((continuous_const.mul (c1.pow 2)).mul c2).div c0 fun x => (hpos x).ne').sub
      ((c1.pow 4).div (c0.pow 2) fun x => (pow_pos (hpos x) 2).ne')
  have hB : Continuous fun x => deriv (deriv f) x ^ 2 + deriv f x * deriv (deriv (deriv f)) x :=
    (c2.pow 2).add (c1.mul c3)
  have hQ : Continuous fun x => deriv f x ^ 4 / f x ^ 2 := (c1.pow 4).div (c0.pow 2) fun x => (pow_pos (hpos x) 2).ne'
  have hb : Continuous fun x => deriv (deriv f) x ^ 2 := c2.pow 2
  have pt : ∀ x, 16 * deriv f x ^ 2 * deriv (deriv f) x / f x +
        8 * deriv f x * deriv (deriv (deriv f)) x - 8 * deriv f x ^ 4 / f x ^ 2 =
      (16 / 3) * (3 * deriv f x ^ 2 * deriv (deriv f) x / f x - deriv f x ^ 4 / f x ^ 2) +
      8 * (deriv (deriv f) x ^ 2 + deriv f x * deriv (deriv (deriv f)) x) +
      (-(8 / 3)) * (deriv f x ^ 4 / f x ^ 2) + (-8) * deriv (deriv f) x ^ 2 := fun x => by ring
  simp_rw [pt]
  rw [integral_lin4 hA hB hQ hb]
  rw [ibp1, ibp2]
  ring


theorem second_mode_f {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (hpos : ∀ x, 0 < f x)
    (h1 : ∫ x in (0 : ℝ)..1, f x ^ 2 = 1) :
    (1536 * π ^ 4 / 11) * ‖∫ x in (0 : ℝ)..1, cexp (2 * π * I * 2 * x) * ((f x ^ 2 : ℝ) : ℂ)‖ ^ 2 ≤
      8 * ((∫ x in (0 : ℝ)..1, deriv (deriv f) x ^ 2) - 4 * π ^ 2 * ∫ x in (0 : ℝ)..1, deriv f x ^ 2) +
        8 / 3 * ∫ x in (0 : ℝ)..1, deriv f x ^ 4 / f x ^ 2 := by
  have hF := fourier_second_mode_line hf hper h1
  have hf1 := contDiff_deriv' hf
  have c0 := hf.continuous
  have c1 := hf1.continuous
  have hQ := sq_integral_le (A := fun x => deriv f x ^ 2) (B := fun x => f x ^ 2) (c1.pow 2) (c0.pow 2)
    (fun x => sq_nonneg _) (fun x => pow_pos (hpos x) 2)
  have hQ' : (∫ x in (0 : ℝ)..1, deriv f x ^ 2) ^ 2 ≤ ∫ x in (0 : ℝ)..1, deriv f x ^ 4 / f x ^ 2 := by
    rw [h1, mul_one] at hQ
    refine hQ.trans (le_of_eq ?_)
    congr 1; funext x; ring
  set a := ∫ x in (0 : ℝ)..1, deriv f x ^ 2 with ha
  set b := ∫ x in (0 : ℝ)..1, deriv (deriv f) x ^ 2 with hb
  set Q := ∫ x in (0 : ℝ)..1, deriv f x ^ 4 / f x ^ 2 with hQdef
  set Zn := ‖∫ x in (0 : ℝ)..1, cexp (2 * π * I * 2 * x) * ((f x ^ 2 : ℝ) : ℂ)‖ ^ 2 with hZn
  have hπ : 0 < π := Real.pi_pos
  have hκ : (1536 * π ^ 4 / 11) * (11 / 36 * (a / (4 * π ^ 2)) ^ 2 + 11 / 12 * ((b - 4 * π ^ 2 * a) / (16 * π ^ 4))) =
      8 / 3 * a ^ 2 + 8 * (b - 4 * π ^ 2 * a) := by
    field_simp
    ring
  have hκpos : 0 ≤ 1536 * π ^ 4 / 11 := by positivity
  calc (1536 * π ^ 4 / 11) * Zn ≤ (1536 * π ^ 4 / 11) * (11 / 36 * (a / (4 * π ^ 2)) ^ 2 +
        11 / 12 * ((b - 4 * π ^ 2 * a) / (16 * π ^ 4))) := mul_le_mul_of_nonneg_left hF hκpos
    _ = 8 / 3 * a ^ 2 + 8 * (b - 4 * π ^ 2 * a) := hκ
    _ ≤ _ := by nlinarith [hQ']


theorem contDiff_heatD (ρ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (j : ℕ) : ContDiff ℝ ∞ (fun x => heatD ρ j t x) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing j with
  | zero => exact contDiff_zero.mpr (continuous_heatD ρ j ht)
  | succ n ih =>
    have hd : deriv (fun x => heatD ρ j t x) = fun x => heatD ρ (j + 1) t x :=
      funext fun x => (hasDerivAt_heatD_x ρ j ht x).deriv
    have h : ContDiff ℝ ((n : ℕ∞ω) + 1) (fun x => heatD ρ j t x) :=
      contDiff_succ_iff_deriv.mpr ⟨fun x => (hasDerivAt_heatD_x ρ j ht x).differentiableAt,
        fun h => absurd h (by simp), by rw [hd]; exact ih (j + 1)⟩
    exact_mod_cast h

theorem periodic_heatD (ρ : ℝ → ℝ) (j : ℕ) (t : ℝ) : Function.Periodic (fun x => heatD ρ j t x) 1 :=
  fun x => heatD_add_one ρ j t x


theorem heat_L_le {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    (∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
      heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)) ≤
      -8 * π ^ 2 * fisherI ρ t -
        (1536 * π ^ 4 / 11) * ‖heatCoeff (heat ρ t) (-2)‖ ^ 2 := by
  have hpos : ∀ x, 0 < heat ρ t x := fun x => heat_pos hρ hρ0 hρ1 ht x
  have hp : ContDiff ℝ ∞ (fun x => heat ρ t x) := contDiff_heatD ρ ht 0
  set f : ℝ → ℝ := fun x => Real.sqrt (heat ρ t x) with hfdef
  have hf : ContDiff ℝ ∞ f := hp.sqrt (fun x => (hpos x).ne')
  have hfper : Function.Periodic f 1 := fun x => by
    simp only [hfdef]; rw [show heat ρ t (x + 1) = heat ρ t x from heatD_add_one ρ 0 t x]
  have hfpos : ∀ x, 0 < f x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hf2 : ∀ x, f x ^ 2 = heat ρ t x := fun x => Real.sq_sqrt (hpos x).le
  have h1 : ∫ x in (0 : ℝ)..1, f x ^ 2 = 1 := by
    simp_rw [hf2]; rw [integral_heat ρ ht, hρ1]
  have hf1 := contDiff_deriv' hf
  have hf2' := contDiff_deriv' hf1
  have hf3' := contDiff_deriv' hf2'
  have d0 := hasDerivAt_deriv_of_smooth hf
  have d1 := hasDerivAt_deriv_of_smooth hf1
  have d2 := hasDerivAt_deriv_of_smooth hf2'
  -- derivative identities
  have q1 : ∀ x, heatD ρ 1 t x = 2 * f x * deriv f x := fun x => by
    have h := hasDerivAt_heatD_x ρ 0 ht x
    have h' : HasDerivAt (fun x => f x ^ 2) (2 * f x * deriv f x) x :=
      ((d0 x).pow 2).congr_deriv (by norm_num)
    have e : (fun x => heatD ρ 0 t x) = fun x => f x ^ 2 := funext fun x => (hf2 x).symm
    rw [e] at h
    exact h.unique h'
  have q2 : ∀ x, heatD ρ 2 t x = 2 * deriv f x ^ 2 + 2 * f x * deriv (deriv f) x := fun x => by
    have h := hasDerivAt_heatD_x ρ 1 ht x
    have h' : HasDerivAt (fun x => 2 * f x * deriv f x) (2 * deriv f x ^ 2 + 2 * f x * deriv (deriv f) x) x :=
      (((d0 x).const_mul 2).mul (d1 x)).congr_deriv (by ring)
    have e : (fun x => heatD ρ 1 t x) = fun x => 2 * f x * deriv f x := funext q1
    rw [e] at h
    exact h.unique h'
  have q3 : ∀ x, heatD ρ 3 t x = 6 * deriv f x * deriv (deriv f) x + 2 * f x * deriv (deriv (deriv f)) x := fun x => by
    have h := hasDerivAt_heatD_x ρ 2 ht x
    have h' : HasDerivAt (fun x => 2 * deriv f x ^ 2 + 2 * f x * deriv (deriv f) x)
        (6 * deriv f x * deriv (deriv f) x + 2 * f x * deriv (deriv (deriv f)) x) x :=
      ((((d1 x).pow 2).const_mul 2).add (((d0 x).const_mul 2).mul (d2 x))).congr_deriv (by norm_num; ring)
    have e : (fun x => heatD ρ 2 t x) = fun x => 2 * deriv f x ^ 2 + 2 * f x * deriv (deriv f) x := funext q2
    rw [e] at h
    exact h.unique h'
  -- the integrand and the Fisher information
  have hI : fisherI ρ t = 4 * ∫ x in (0 : ℝ)..1, deriv f x ^ 2 := by
    unfold fisherI
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [q1]
    have := (hfpos x).ne'
    rw [← hf2 x]
    field_simp
    ring
  have hL : (∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
      heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)) =
      ∫ x in (0 : ℝ)..1, (16 * deriv f x ^ 2 * deriv (deriv f) x / f x +
        8 * deriv f x * deriv (deriv (deriv f)) x - 8 * deriv f x ^ 4 / f x ^ 2) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [q1, q2, q3]
    have := (hfpos x).ne'
    rw [← hf2 x]
    field_simp
    ring
  rw [hL, L_eq hf hfper hfpos, hI]
  -- the second Fourier mode
  have hZ : heatCoeff (fun x => heat ρ t x) (-2) =
      ∫ x in (0 : ℝ)..1, cexp (2 * π * I * 2 * x) * ((f x ^ 2 : ℝ) : ℂ) := by
    unfold heatCoeff
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only
    rw [hf2 x, mul_comm]
    congr 2
    push_cast
    ring
  have hmain := second_mode_f hf hfper hfpos h1
  rw [← hZ] at hmain
  have : heatCoeff (heat ρ t) (-2) = heatCoeff (fun x => heat ρ t x) (-2) := rfl
  rw [this]
  nlinarith [hmain]



theorem norm_sq_heatCoeff_heat (ρ : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ‖heatCoeff (heat ρ s) (-2)‖ ^ 2 = ‖heatCoeff ρ (-2)‖ ^ 2 * Real.exp (-(32 * π ^ 2) * s) := by
  rw [heatCoeff_heat ρ hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hasDerivAt_Zn (ρ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ‖heatCoeff (heat ρ s) (-2)‖ ^ 2) (-(32 * π ^ 2) * ‖heatCoeff (heat ρ t) (-2)‖ ^ 2) t := by
  have h : HasDerivAt (fun s : ℝ => ‖heatCoeff ρ (-2)‖ ^ 2 * Real.exp (-(32 * π ^ 2) * s))
      (‖heatCoeff ρ (-2)‖ ^ 2 * (Real.exp (-(32 * π ^ 2) * t) * (-(32 * π ^ 2)))) t := by
    have := ((hasDerivAt_id t).const_mul (-(32 * π ^ 2))).exp.const_mul (‖heatCoeff ρ (-2)‖ ^ 2)
    simpa using this
  have hev : (fun s => ‖heatCoeff (heat ρ s) (-2)‖ ^ 2) =ᶠ[𝓝 t]
      fun s => ‖heatCoeff ρ (-2)‖ ^ 2 * Real.exp (-(32 * π ^ 2) * s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact norm_sq_heatCoeff_heat ρ hs
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [norm_sq_heatCoeff_heat ρ ht]
  ring


/-- The Lyapunov functional `Φ(t) = I(p_t) - 8π² H(p_t) - (48π²/11)|\hat p_t(-2)|²`. -/
noncomputable def phiL (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  fisherI ρ t - 8 * π ^ 2 * entropyH ρ t - (48 * π ^ 2 / 11) * ‖heatCoeff (heat ρ t) (-2)‖ ^ 2

theorem hasDerivAt_phiL {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (phiL ρ)
      ((∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
        heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)) + 8 * π ^ 2 * fisherI ρ t +
        (1536 * π ^ 4 / 11) * ‖heatCoeff (heat ρ t) (-2)‖ ^ 2) t := by
  have h1 := hasDerivAt_fisherI hρ hρ0 hρ1 ht
  have h2 := (hasDerivAt_entropyH hρ hρ0 hρ1 ht).const_mul (8 * π ^ 2)
  have h3 := (hasDerivAt_Zn ρ ht).const_mul (48 * π ^ 2 / 11)
  refine ((h1.sub h2).sub h3).congr_deriv ?_
  ring

theorem phiL_deriv_nonpos {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    deriv (phiL ρ) t ≤ 0 := by
  rw [(hasDerivAt_phiL hρ hρ0 hρ1 ht).deriv]
  have := heat_L_le hρ hρ0 hρ1 ht
  linarith

theorem phiL_antitone {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) : AntitoneOn (phiL ρ) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · exact fun t ht => (hasDerivAt_phiL hρ hρ0 hρ1 ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact (hasDerivAt_phiL hρ hρ0 hρ1 ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact phiL_deriv_nonpos hρ hρ0 hρ1 ht

theorem phiL_nonneg {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) : 0 ≤ phiL ρ t := by
  set K := ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) 0 1 n with hK
  set Z0 := ‖heatCoeff ρ (-2)‖ ^ 2 with hZ0
  set ε : ℝ → ℝ := fun T => 8 * π ^ 2 * (Real.exp (-(4 * π ^ 2) * (T - 1)) * K) ^ 2 +
    (48 * π ^ 2 / 11) * (Z0 * Real.exp (-(32 * π ^ 2) * T)) with hε
  have hbound : ∀ᶠ T in atTop, -ε T ≤ phiL ρ t := by
    filter_upwards [eventually_ge_atTop (max t 1)] with T hT
    have hT0 : 0 < T := lt_of_lt_of_le ht ((le_max_left _ _).trans hT)
    have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
    have hmono := phiL_antitone hρ hρ0 hρ1 ht hT0 ((le_max_left _ _).trans hT)
    refine le_trans ?_ hmono
    have hI := fisherI_nonneg hρ hρ0 hρ1 hT0
    have hH := entropyH_le_sq_decay (ρ := ρ) hρ1 hT1 (heat_pos hρ hρ0 hρ1 hT0)
    have hZ := norm_sq_heatCoeff_heat ρ hT0
    unfold phiL
    rw [hZ]
    simp only [hε]
    nlinarith [hI, hH, mul_nonneg (by positivity : (0:ℝ) ≤ 8 * π ^ 2) (sq_nonneg (Real.exp (-(4 * π ^ 2) * (T - 1)) * K))]
  have hlim : Tendsto (fun T => -ε T) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => -(4 * π ^ 2) * (T - 1)) atTop atBot := by
      have : Tendsto (fun T : ℝ => (4 * π ^ 2) * (T + -1)) atTop atTop :=
        (tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop (by positivity)
      convert tendsto_neg_atTop_atBot.comp this using 1
      funext T; simp only [Function.comp_apply]; ring
    have h2 : Tendsto (fun T : ℝ => -(32 * π ^ 2) * T) atTop atBot := by
      have : Tendsto (fun T : ℝ => (32 * π ^ 2) * T) atTop atTop :=
        tendsto_id.const_mul_atTop (by positivity)
      convert tendsto_neg_atTop_atBot.comp this using 1
      funext T; simp only [Function.comp_apply]; ring
    have e1 := ((Real.tendsto_exp_atBot.comp h1).mul_const K).pow 2
    have e2 := (Real.tendsto_exp_atBot.comp h2).const_mul Z0
    have := ((e1.const_mul (8 * π ^ 2)).add (e2.const_mul (48 * π ^ 2 / 11))).neg
    simpa [hε] using this
  exact le_of_tendsto hlim hbound


theorem fisherI_flow_le {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) {s : ℝ} (hs : 0 < s) :
    fisherI (fun x => ρ (lineT x)) s ≤ 4 * ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1 := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  set r : ℝ → ℝ := fun x => ρ (lineT x) with hr
  have hi := integrable_of_integral_eq_one hρ1
  have hu2 : MemLp u 2 (haar 1) := hρ.2.1
  have hrI : IntervalIntegrable r volume 0 1 := intervalIntegrable_lineT hi
  have hr0 : ∀ y, 0 ≤ r y := fun y => hρ0 _
  have hr1 : ∫ y in (0 : ℝ)..1, r y = 1 := by
    rw [hr, intervalIntegral_lineT hi.aestronglyMeasurable]; exact hρ1
  have hg2 := memLp_weakGrad_zero hρ
  have huu : Integrable (fun y => 2 * u y * weakGrad u y 0) (haar 1) := by
    refine Integrable.mono' (hu2.integrable_sq.add hg2.integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul hg2.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    show ‖2 * u y * weakGrad u y 0‖ ≤ u y ^ 2 + weakGrad u y 0 ^ 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (u y + weakGrad u y 0), sq_nonneg (u y - weakGrad u y 0)]
  have hI := fisherI_le_of_coeff (r := r) (v := fun y => u (lineT y))
      (w := fun y => weakGrad u (lineT y) 0) hr0 hr1 (fun y => (Real.sq_sqrt (hρ0 _)).symm)
      (integrableOn_lineT hu2.integrable_sq) (integrableOn_lineT hg2.integrable_sq)
      (integrableOn_lineT huu) (heatCoeff_lift_grad hρ0 hρ1 hρ) hs
  rw [intervalIntegral_lineT (g := fun y => weakGrad u y 0 ^ 2)
      hg2.integrable_sq.aestronglyMeasurable] at hI
  exact hI

theorem klDiv_le_of_flow {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)))
    {B S0 : ℝ} (hS0 : 0 < S0)
    (hflow : ∀ s : ℝ, 0 < s → s ≤ S0 → entropyH (fun x => ρ (lineT x)) s ≤ B) :
    klDiv (densMeasure ρ) (haar 1) ≤ ENNReal.ofReal B := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  set r : ℝ → ℝ := fun x => ρ (lineT x) with hr
  have hi := integrable_of_integral_eq_one hρ1
  have hu2 : MemLp u 2 (haar 1) := hρ.2.1
  have hrI : IntervalIntegrable r volume 0 1 := intervalIntegrable_lineT hi
  have hr0 : ∀ y, 0 ≤ r y := fun y => hρ0 _
  have hr1 : ∫ y in (0 : ℝ)..1, r y = 1 := by
    rw [hr, intervalIntegral_lineT hi.aestronglyMeasurable]; exact hρ1
  have hs : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  -- the entropy along the flow as a lintegral
  have hlin : ∀ s > 0, ∫⁻ y, ENNReal.ofReal (klFun (heatLift ρ s y)) ∂haar 1 =
      ENNReal.ofReal (entropyH r s) := by
    intro s hs
    have hpos : ∀ z, 0 < heatLift ρ s z := fun z => heat_pos hrI hr0 hr1 hs _
    set Bd := ∑' n, heatBound (∫ y in (0 : ℝ)..1, |r y|) 0 s n
    have hint : Integrable (fun y => klFun (heatLift ρ s y)) (haar 1) := by
      refine Integrable.of_bound (continuous_klFun.comp_aestronglyMeasurable
        (measurable_heatLift ρ hs).aestronglyMeasurable) ((Bd + 1) ^ 2)
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hpos z).le)]
      refine (klFun_le_sq (hpos z)).trans ?_
      have hb := abs_heatLift_le ρ hs z
      have h1 : |heatLift ρ s z - 1| ≤ Bd + 1 :=
        (abs_sub _ _).trans (by rw [abs_one]; linarith)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z => klFun_nonneg (hpos z).le)]
    congr 1
    rw [← integral_lineT hint.aestronglyMeasurable, entropyH,
      intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [heatLift_lineT, hr]
  -- `L¹` convergence and an a.e. convergent subsequence
  have hρ2 := memLp_two_of_sqrt_memH1 hρ0 hρ1 hρ
  have hL2 := tendsto_heatLift_L2 hρ2
  have hL1 : Tendsto (fun n : ℕ => ∫⁻ y, ‖heatLift ρ (1 / (n + 1)) y - ρ y‖ₑ ∂haar 1) atTop
      (𝓝 0) := by
    have hb : ∀ n : ℕ, ∫⁻ y, ‖heatLift ρ (1 / (n + 1)) y - ρ y‖ₑ ∂haar 1 ≤
        ENNReal.ofReal (Real.sqrt (∫ y, (heatLift ρ (1 / (n + 1)) y - ρ y) ^ 2 ∂haar 1)) := by
      intro n
      have hm := (memLp_heatLift ρ (hs n) 2).sub hρ2
      rw [show (fun y => ‖heatLift ρ (1 / (n + 1)) y - ρ y‖ₑ) =
        fun y => ‖(heatLift ρ (1 / (n + 1)) - ρ) y‖ₑ from rfl,
        ← ofReal_integral_norm_eq_lintegral_enorm (hm.integrable one_le_two)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := integral_abs_le_sqrt hm
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (Real.sqrt (∫ y, (heatLift ρ (1 / (n + 1)) y - ρ y) ^ 2 ∂haar 1))) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp hL2)
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) hb
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (F := fun n : ℕ => heatLift ρ (1 / (n + 1))) (f := ρ)
    (fun n => (measurable_heatLift ρ (hs n)).aestronglyMeasurable) hi.aestronglyMeasurable hL1
  -- Fatou
  have hcont : Continuous fun p : ℝ => ENNReal.ofReal (klFun p) :=
    ENNReal.continuous_ofReal.comp continuous_klFun
  rw [klDiv_densMeasure hρ0 hρ1]
  calc ∫⁻ y, ENNReal.ofReal (klFun (ρ y)) ∂haar 1
      = ∫⁻ y, liminf (fun k => ENNReal.ofReal (klFun (heatLift ρ (1 / (ns k + 1)) y))) atTop
          ∂haar 1 :=
        lintegral_congr_ae (hae.mono fun y hy =>
          ((hcont.tendsto _).comp hy).liminf_eq.symm)
    _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (klFun (heatLift ρ (1 / (ns k + 1)) y)) ∂haar 1)
          atTop :=
        lintegral_liminf_le' fun k => (ENNReal.measurable_ofReal.comp
          (continuous_klFun.measurable.comp (measurable_heatLift ρ (hs _)))).aemeasurable
    _ ≤ ENNReal.ofReal B := by
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hS0
        refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
        filter_upwards [eventually_ge_atTop N] with k hk
        rw [hlin _ (hs _)]
        refine ENNReal.ofReal_le_ofReal (hflow _ (hs _) ?_)
        have h1 : (k : ℝ) ≤ ns k := by exact_mod_cast hns.id_le k
        have h2 : (N : ℝ) ≤ k := by exact_mod_cast hk
        have h3 : 1 / ((ns k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity); linarith
        linarith


theorem entropyH_nonneg (ρ : ℝ → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ : IntervalIntegrable ρ volume 0 1)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {s : ℝ} (hs : 0 < s) : 0 ≤ entropyH ρ s :=
  intervalIntegral.integral_nonneg zero_le_one fun x _ => klFun_nonneg (heat_pos hρ hρ0 hρ1 hs x).le

theorem heatCoeff_lineT (ρ : Torus 1 → ℝ) (hρ : Integrable ρ (haar 1)) :
    heatCoeff (fun x => ρ (lineT x)) (-2) = ∫ x, fourier 2 (x 0) * (ρ x : ℂ) ∂haar 1 := by
  have hc : AEStronglyMeasurable (fun x : Torus 1 => fourier (2 : ℤ) (x 0) * (ρ x : ℂ)) (haar 1) :=
    (((fourier (2 : ℤ)).continuous.comp (continuous_apply (0 : Fin 1))).aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hρ.aestronglyMeasurable)
  rw [← integral_lineT hc, heatCoeff, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  have e0 : (lineT x) 0 = (x : UnitAddCircle) := rfl
  simp only [e0, fourier_coe_apply]
  rw [mul_comm]
  congr 2
  push_cast
  ring


theorem second_mode_remainder_proved (ρ : Torus 1 → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    ENNReal.ofReal (2 * aCos) * klDiv (densMeasure ρ) (haar 1) +
        ENNReal.ofReal (12 / 11 * aCos * Complex.normSq (∫ x, fourier 2 (x 0) * (ρ x : ℂ) ∂haar 1)) ≤
      fisherInfo (densMeasure ρ) (haar 1) := by
  have hπ : 0 < π := Real.pi_pos
  have hi := integrable_of_integral_eq_one hρ1
  set r : ℝ → ℝ := fun x => ρ (lineT x) with hr
  have hrI : IntervalIntegrable r volume 0 1 := intervalIntegrable_lineT hi
  have hr0 : ∀ y, 0 ≤ r y := fun y => hρ0 _
  have hr1 : ∫ y in (0 : ℝ)..1, r y = 1 := by
    rw [hr, intervalIntegral_lineT hi.aestronglyMeasurable]; exact hρ1
  set J := 4 * ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1 with hJ
  set N0 := ‖heatCoeff r (-2)‖ ^ 2 with hN0
  have hN0' : Complex.normSq (∫ x, fourier 2 (x 0) * (ρ x : ℂ) ∂haar 1) = N0 := by
    rw [← heatCoeff_lineT ρ hi, Complex.normSq_eq_norm_sq]
  have hN0nn : 0 ≤ N0 := sq_nonneg _
  have haCos : aCos = 4 * π ^ 2 := rfl
  -- step 1: the flow inequality
  have step1 : ∀ s : ℝ, 0 < s → 8 * π ^ 2 * entropyH r s + 48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * s)) ≤ J := by
    intro s hs
    have h1 := phiL_nonneg hrI hr0 hr1 hs
    have h2 := fisherI_flow_le hρ0 hρ1 hH hs
    unfold phiL at h1
    rw [norm_sq_heatCoeff_heat r hs] at h1
    simp only [hJ] at *
    nlinarith [h1, h2]
  -- step 1b: κ' N0 ≤ J
  have hJN : 48 * π ^ 2 / 11 * N0 ≤ J := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * s)) ≤ J := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have := step1 s hs
      have hH0 := entropyH_nonneg r hr0 hrI hr1 hs
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 8 * π ^ 2) hH0]
    have hlim : Tendsto (fun s : ℝ => 48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * s))) (𝓝[>] 0)
        (𝓝 (48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * 0)))) :=
      ((continuous_const.mul (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).tendsto 0).mono_left nhdsWithin_le_nhds
    have := le_of_tendsto hlim hev
    simpa using this
  -- step 2: entropy bound for `s ≤ S0`
  set c : ℝ → ℝ := fun S0 => (J - 48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * S0))) / (8 * π ^ 2) with hc
  have step2 : ∀ S0 : ℝ, 0 < S0 → klDiv (densMeasure ρ) (haar 1) ≤ ENNReal.ofReal (c S0) := by
    intro S0 hS0
    refine klDiv_le_of_flow hρ0 hρ1 hH hS0 (fun s hs hsS => ?_)
    have := step1 s hs
    have hexp : Real.exp (-(32 * π ^ 2) * S0) ≤ Real.exp (-(32 * π ^ 2) * s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : 48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * S0)) ≤
        48 * π ^ 2 / 11 * (N0 * Real.exp (-(32 * π ^ 2) * s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hN0nn) (by positivity)
    simp only [hc]
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- step 3: S0 → 0
  set c0 := (J - 48 * π ^ 2 / 11 * N0) / (8 * π ^ 2) with hc0
  have hclim : Tendsto (fun S0 : ℝ => ENNReal.ofReal (c S0)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c0)) := by
    have hcont : Continuous c := by simp only [hc]; fun_prop
    have hc00 : c 0 = c0 := by simp [hc, hc0]
    have : Tendsto c (𝓝[>] 0) (𝓝 c0) := by
      rw [← hc00]; exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (ENNReal.continuous_ofReal.tendsto _).comp this
  have hkl : klDiv (densMeasure ρ) (haar 1) ≤ ENNReal.ofReal c0 :=
    ge_of_tendsto hclim (by filter_upwards [self_mem_nhdsWithin] with S0 hS0 using step2 S0 hS0)
  -- step 4: assemble
  have hfi : fisherInfo (densMeasure ρ) (haar 1) = ENNReal.ofReal J :=
    fisherInfo_densMeasure_eq hρ0 hρ1 hH
  have h8 : ENNReal.ofReal (2 * aCos) * klDiv (densMeasure ρ) (haar 1) ≤
      ENNReal.ofReal (J - 48 * π ^ 2 / 11 * N0) := by
    calc ENNReal.ofReal (2 * aCos) * klDiv (densMeasure ρ) (haar 1)
        ≤ ENNReal.ofReal (2 * aCos) * ENNReal.ofReal c0 := mul_le_mul' le_rfl hkl
      _ = ENNReal.ofReal (2 * aCos * c0) := (ENNReal.ofReal_mul (by rw [haCos]; positivity)).symm
      _ = ENNReal.ofReal (J - 48 * π ^ 2 / 11 * N0) := by
        congr 1; rw [haCos, hc0]; field_simp; ring
  rw [hN0', hfi]
  calc ENNReal.ofReal (2 * aCos) * klDiv (densMeasure ρ) (haar 1) +
        ENNReal.ofReal (12 / 11 * aCos * N0)
      ≤ ENNReal.ofReal (J - 48 * π ^ 2 / 11 * N0) + ENNReal.ofReal (12 / 11 * aCos * N0) :=
        add_le_add h8 le_rfl
    _ = ENNReal.ofReal J := by
        rw [← ENNReal.ofReal_add (by linarith) (by rw [haCos]; positivity)]
        congr 1; rw [haCos]; ring


/-! ### Statement-identity checks -/

example : (type_of% @second_mode_remainder) = (type_of% @second_mode_remainder_proved) := rfl

end Ex
end SharpLSI.FL
