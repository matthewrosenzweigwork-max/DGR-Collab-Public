import SharpSymmetricLSI.Paper.RefSpectrum2
import SharpSymmetricLSI.Paper.RefSpectrum3
import SharpSymmetricLSI.Paper.CosineExpansion

/-!
# R23 (6.1), part 4: the admissible sets are nonempty

For `d ≥ 1` the functions `cos(2πm x_{i₀})`, `m = 0, …, n+1`, are smooth, orthogonal in `L²(m)`
with positive norms, hence linearly independent modulo `P`-null functions; some nonzero
combination is orthogonal to `n+1` given functions (`adm_nonempty`).
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ}

theorem kLin_neg {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℤ) (x : ι → ℝ) : kLin (-k) x = -kLin k x := by
  rw [kLin_apply, kLin_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- `cos(2πk·y) = (e_k + e_{-k})/2`. -/
theorem thC_secT_eq {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℤ) (y : UnitAddTorus ι) :
    (thC k (secT y) : ℂ) = (mFourier k y + mFourier (-k) y) / 2 := by
  have h1 := mFourier_neg_secT k y
  have h2 := mFourier_neg_secT (-k) y
  rw [neg_neg] at h2
  have hc : thC (-k) (secT y) = thC k (secT y) := by simp [thC, kLin_neg, Real.cos_neg]
  have hs : thS (-k) (secT y) = -thS k (secT y) := by simp [thS, kLin_neg, Real.sin_neg]
  rw [h1, h2, hc, hs]
  push_cast; ring

theorem integral_mFourier_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℤ) :
    ∫ y : UnitAddTorus ι, mFourier a y * mFourier b y = if a + b = 0 then 1 else 0 := by
  have : (fun y : UnitAddTorus ι => mFourier a y * mFourier b y) = fun y => mFourier (a + b) y := by
    funext y; rw [mFourier_add]
  rw [this, integral_mFourier]

/-- The test functions `cos(2πm y_{i₀})`. -/
noncomputable def cosF (i₀ : Fin d) (m : ℕ) (y : Torus d) : ℝ :=
  thC (Pi.single i₀ (m : ℤ)) (secT y)

theorem integral_cosF_mul (i₀ : Fin d) (m l : ℕ) :
    ∫ y, cosF i₀ m y * cosF i₀ l y =
      if m = l then (if m = 0 then 1 else 1 / 2) else 0 := by
  set k : Fin d → ℤ := Pi.single i₀ (m : ℤ)
  set q : Fin d → ℤ := Pi.single i₀ (l : ℤ)
  have hint : ∀ a b : Fin d → ℤ, Integrable (fun y : Torus d => mFourier a y * mFourier b y) :=
    fun a b => ((map_continuous _).mul (map_continuous _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC : ((∫ y, cosF i₀ m y * cosF i₀ l y : ℝ) : ℂ) =
      ((if k + q = 0 then 1 else 0) + (if k + -q = 0 then 1 else 0) +
        (if -k + q = 0 then 1 else 0) + (if -k + -q = 0 then 1 else 0)) / 4 := by
    rw [← integral_complex_ofReal]
    have e : ∀ y, ((cosF i₀ m y * cosF i₀ l y : ℝ) : ℂ) =
        (mFourier k y * mFourier q y + mFourier k y * mFourier (-q) y +
          mFourier (-k) y * mFourier q y + mFourier (-k) y * mFourier (-q) y) / 4 := by
      intro y
      push_cast
      rw [cosF, cosF, thC_secT_eq, thC_secT_eq]
      ring
    simp_rw [e]
    rw [integral_div]
    have i1 := hint k q
    have i2 := hint k (-q)
    have i3 := hint (-k) q
    have i4 := hint (-k) (-q)
    rw [integral_add (f := fun y => mFourier k y * mFourier q y + mFourier k y * mFourier (-q) y +
        mFourier (-k) y * mFourier q y) (g := fun y => mFourier (-k) y * mFourier (-q) y)
        (by exact (i1.add i2).add i3) i4,
      integral_add (f := fun y => mFourier k y * mFourier q y + mFourier k y * mFourier (-q) y)
        (g := fun y => mFourier (-k) y * mFourier q y) (by exact i1.add i2) i3,
      integral_add (f := fun y => mFourier k y * mFourier q y)
        (g := fun y => mFourier k y * mFourier (-q) y) i1 i2]
    simp only [integral_mFourier_mul']
  have hkq : ∀ a b : ℕ, (Pi.single i₀ (a : ℤ) + Pi.single i₀ (b : ℤ) : Fin d → ℤ) = 0 ↔
      a = 0 ∧ b = 0 := by
    intro a b
    constructor
    · intro h
      have := congrFun h i₀
      simp at this
      omega
    · rintro ⟨rfl, rfl⟩; simp
  have hneg : ∀ a : ℕ, -(Pi.single i₀ (a : ℤ) : Fin d → ℤ) = Pi.single i₀ (-(a : ℤ)) := by
    intro a; simp [Pi.single_neg]
  have hdiff : ∀ a b : ℕ, (Pi.single i₀ (a : ℤ) + Pi.single i₀ (-(b : ℤ)) : Fin d → ℤ) = 0 ↔
      a = b := by
    intro a b
    constructor
    · intro h
      have := congrFun h i₀
      simp at this
      omega
    · rintro rfl
      rw [← Pi.single_add]; simp
  have hdiff' : ∀ a b : ℕ, (Pi.single i₀ (-(a : ℤ)) + Pi.single i₀ (b : ℤ) : Fin d → ℤ) = 0 ↔
      a = b := by
    intro a b; rw [add_comm, hdiff, eq_comm]
  have hnn : ∀ a b : ℕ, (Pi.single i₀ (-(a : ℤ)) + Pi.single i₀ (-(b : ℤ)) : Fin d → ℤ) = 0 ↔
      a = 0 ∧ b = 0 := by
    intro a b
    constructor
    · intro h
      have := congrFun h i₀
      simp at this
      omega
    · rintro ⟨rfl, rfl⟩; simp
  simp only [k, q, hneg, hkq, hdiff, hdiff', hnn] at hC
  have : ((∫ y, cosF i₀ m y * cosF i₀ l y : ℝ) : ℂ) =
      ((if m = l then (if m = 0 then 1 else 1 / 2) else 0 : ℝ) : ℂ) := by
    rw [hC]
    by_cases hml : m = l
    · subst hml
      by_cases hm : m = 0
      · subst hm; simp; norm_num
      · simp [hm]; norm_num
    · have h1 : ¬(m = 0 ∧ l = 0) := fun h => hml (h.1.trans h.2.symm)
      simp [hml, h1, Ne.symm hml]
  exact_mod_cast this

section adm

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
include hρ

theorem memH1_of_vol {f : Torus d → ℝ} (hf : MemH1 volume f) : MemH1 (densMeasure ρ) f :=
  ⟨hf.1, hf.2.1.of_measure_le_smul ENNReal.ofReal_ne_top hρ.le_smul,
    hf.2.2.of_measure_le_smul ENNReal.ofReal_ne_top hρ.le_smul⟩

theorem memH1_cosF (i₀ : Fin d) (m : ℕ) : MemH1 (densMeasure ρ) (cosF i₀ m) := by
  refine memH1_of_vol hρ (memH1_of_contDiff ?_)
  have : cosF i₀ m ∘ liftT = thC (Pi.single i₀ (m : ℤ)) := by
    funext x; exact (isPer_thC _).secT_liftT x
  rw [this]; exact contDiff_thC _

/-- Finite combinations in `H¹(P)`. -/
theorem memH1_finsum {κ : Type*} (s : Finset κ) (f : κ → Torus d → ℝ)
    (hf : ∀ i ∈ s, MemH1 (densMeasure ρ) (f i)) (a : κ → ℝ) :
    MemH1 (densMeasure ρ) (fun x => ∑ i ∈ s, a i * f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := memH1_of_vol hρ (memH1_of_contDiff (f := fun _ : Torus d => (0 : ℝ))
      contDiff_const)
    exact h
  | insert b s hb ih =>
    have h1 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h2 := (memH1_lin hρ h1 (hf b (Finset.mem_insert_self b s)) 1 (a b)).1
    have e : (fun x => ∑ i ∈ insert b s, a i * f i x) =
        fun x => 1 * (∑ i ∈ s, a i * f i x) + a b * f b x := by
      funext x; rw [Finset.sum_insert hb]; ring
    rw [e]; exact h2

/-- **The admissible sets are nonempty** (`d ≥ 1`). -/
theorem adm_nonempty (hd : 1 ≤ d) {e : ℕ → Torus d → ℝ} {n : ℕ}
    (he : ∀ i ≤ n, MemLp (e i) 2 (densMeasure ρ)) : (Adm (densMeasure ρ) e n).Nonempty := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  set i₀ : Fin d := ⟨0, hd⟩
  set F : Fin (n + 2) → Torus d → ℝ := fun m => cosF i₀ m
  have hFH : ∀ m, MemH1 P (F m) := fun m => memH1_cosF hρ i₀ m
  set M : Matrix (Fin (n + 1)) (Fin (n + 2)) ℝ := fun i m => ∫ y, F m y * e i y ∂P
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at ha
  set u : Torus d → ℝ := fun y => ∑ m, a m * F m y
  have huH : MemH1 P u := memH1_finsum hρ Finset.univ F (fun m _ => hFH m) a
  have hint : ∀ m, ∀ w : Torus d → ℝ, MemLp w 2 P → Integrable (fun y => F m y * w y) P :=
    fun m w hw => (hFH m).2.1.integrable_mul hw
  have horth : ∀ i ≤ n, ∫ y, u y * e i y ∂P = 0 := by
    intro i hi
    have := congrFun ha ⟨i, Nat.lt_succ_of_le hi⟩
    simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply] at this
    rw [← this]
    simp only [u, Finset.sum_mul]
    rw [integral_finsetSum _ fun m _ => ((hint m _ (he i hi)).const_mul (a m)).congr
      (Eventually.of_forall fun y => by simp only; ring)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← integral_mul_const]; congr 1; funext y; ring
  -- `u ≠ 0` in `L²(P)`
  set N := ∫ y, u y ^ 2 ∂P
  have hN : 0 < N := by
    rcases (integral_nonneg fun y => sq_nonneg (u y) : 0 ≤ N).eq_or_lt with h0 | h
    · exfalso
      apply ha0
      have hu0 : u =ᵐ[P] 0 := by
        have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (u y))
          huH.2.1.integrable_sq).mp h0.symm
        filter_upwards [this] with y hy
        simpa using hy
      have hu0' : u =ᵐ[volume] 0 := hρ.ac' hu0
      funext l
      have hFc : ∀ m : Fin (n + 2), Continuous (F m) := fun m => by
        refine continuous_of_liftT' ?_
        have : cosF i₀ m ∘ liftT = thC (Pi.single i₀ ((m : ℕ) : ℤ)) := by
          funext x; exact (isPer_thC _).secT_liftT x
        rw [this]; exact (contDiff_thC _).continuous
      have h1 : ∫ y, u y * F l y = 0 := by
        rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hu0'.mono fun y hy => by
          simp only [Pi.zero_apply] at hy; simp [hy])]
        simp
      have h2 : ∫ y, u y * F l y = a l * (if (l : ℕ) = 0 then 1 else 1 / 2) := by
        simp only [u, Finset.sum_mul]
        rw [integral_finsetSum (f := fun m y => a m * F m y * F l y) _ fun m _ =>
          (integrable_of_continuous_torus ((continuous_const.mul (hFc m)).mul (hFc l)))]
        simp_rw [mul_assoc, integral_const_mul]
        simp only [F, integral_cosF_mul, Fin.val_inj, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ l]
        simp
      rw [h1] at h2
      have hc : (if (l : ℕ) = 0 then (1 : ℝ) else 1 / 2) ≠ 0 := by split_ifs <;> norm_num
      exact (mul_eq_zero.mp h2.symm).resolve_right hc
    · exact h
  set sc := 1 / Real.sqrt N
  obtain ⟨hvH, -⟩ := memH1_lin hρ huH huH sc 0
  refine ⟨fun y => sc * u y + 0 * u y, hvH, ?_, fun i hi => ?_⟩
  · have : ∫ y, (sc * u y + 0 * u y) ^ 2 ∂P = sc ^ 2 * N := by
      rw [← integral_const_mul]; congr 1; funext y; ring
    rw [this, div_pow, Real.sq_sqrt hN.le, one_pow, one_div_mul_cancel hN.ne']
  · rw [integral_lin_mul hρ huH.2.1 huH.2.1 (he i hi), horth i hi]; ring

end adm

end SharpLSI
