import FullLabeledLSI.Paper.HybridLSIAltA

/-!
# Hybrid tilted log-Sobolev inequality (alternative route), part B: polynomial bounds and the
# explicit derivative formulas of the test function

`PBu f` : `|f x g| ≤ C (1 + ‖g‖)^k` uniformly in `x` (uniform polynomial growth in the Gaussian variable).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI

section pb
variable {α : Type*} {M : ℕ}

/-- Uniform polynomial growth in the Gaussian variable. -/
def PBu (f : α → (Fin M → ℝ) → ℝ) : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x g, |f x g| ≤ C * (1 + ‖g‖) ^ k

theorem one_add_norm_pow_mono (g : Fin M → ℝ) {k l : ℕ} (h : k ≤ l) :
    (1 + ‖g‖) ^ k ≤ (1 + ‖g‖) ^ l :=
  pow_le_pow_right₀ (by linarith [norm_nonneg g]) h

theorem PBu.mono_exp {f : α → (Fin M → ℝ) → ℝ} {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x g, |f x g| ≤ C * (1 + ‖g‖) ^ k) {l : ℕ} (hl : k ≤ l) :
    ∀ x g, |f x g| ≤ C * (1 + ‖g‖) ^ l := fun x g =>
  (h x g).trans (mul_le_mul_of_nonneg_left (one_add_norm_pow_mono g hl) hC)

theorem PBu.add {f f' : α → (Fin M → ℝ) → ℝ} (hf : PBu f) (hf' : PBu f') :
    PBu (fun x g => f x g + f' x g) := by
  obtain ⟨k, C, hC, h⟩ := hf
  obtain ⟨k', C', hC', h'⟩ := hf'
  refine ⟨max k k', C + C', by positivity, fun x g => ?_⟩
  have h1 := PBu.mono_exp hC h (le_max_left k k') x g
  have h2 := PBu.mono_exp hC' h' (le_max_right k k') x g
  calc |f x g + f' x g| ≤ |f x g| + |f' x g| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem PBu.neg {f : α → (Fin M → ℝ) → ℝ} (hf : PBu f) : PBu (fun x g => -f x g) := by
  obtain ⟨k, C, hC, h⟩ := hf
  exact ⟨k, C, hC, fun x g => by simpa using h x g⟩

theorem PBu.sub {f f' : α → (Fin M → ℝ) → ℝ} (hf : PBu f) (hf' : PBu f') :
    PBu (fun x g => f x g - f' x g) := by
  simpa [sub_eq_add_neg] using hf.add hf'.neg

theorem PBu.mul {f f' : α → (Fin M → ℝ) → ℝ} (hf : PBu f) (hf' : PBu f') :
    PBu (fun x g => f x g * f' x g) := by
  obtain ⟨k, C, hC, h⟩ := hf
  obtain ⟨k', C', hC', h'⟩ := hf'
  refine ⟨k + k', C * C', by positivity, fun x g => ?_⟩
  rw [abs_mul, pow_add]
  calc |f x g| * |f' x g| ≤ (C * (1 + ‖g‖) ^ k) * (C' * (1 + ‖g‖) ^ k') :=
        mul_le_mul (h x g) (h' x g) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem PBu.const_mul {f : α → (Fin M → ℝ) → ℝ} (hf : PBu f) (c : ℝ) :
    PBu (fun x g => c * f x g) := by
  obtain ⟨k, C, hC, h⟩ := hf
  refine ⟨k, |c| * C, by positivity, fun x g => ?_⟩
  rw [abs_mul]
  calc |c| * |f x g| ≤ |c| * (C * (1 + ‖g‖) ^ k) := mul_le_mul_of_nonneg_left (h x g) (abs_nonneg _)
    _ = _ := by ring

theorem PBu.sq {f : α → (Fin M → ℝ) → ℝ} (hf : PBu f) : PBu (fun x g => f x g ^ 2) := by
  have e : (fun x g => f x g ^ 2) = fun x g => f x g * f x g := by funext x g; ring
  rw [e]; exact hf.mul hf

theorem PBu.sum {ι : Type*} (s : Finset ι) {f : ι → α → (Fin M → ℝ) → ℝ}
    (hf : ∀ i ∈ s, PBu (f i)) : PBu (fun x g => ∑ i ∈ s, f i x g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun x g => by simp⟩
  | insert a s ha ih =>
    have := (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem PBu.const (K : ℝ) : PBu (fun (_ : α) (_ : Fin M → ℝ) => K) :=
  ⟨0, |K|, abs_nonneg _, fun x g => by simp⟩

theorem PBu.of_bdd {φ : α → ℝ} (K : ℝ) (hφ : ∀ x, |φ x| ≤ K) :
    PBu (fun (x : α) (_ : Fin M → ℝ) => φ x) :=
  ⟨0, |K|, abs_nonneg _, fun x g => by simpa using (hφ x).trans (le_abs_self K)⟩

theorem PBu.of_tg {f : (Fin M → ℝ) → ℝ} (hf : f.HasTemperateGrowth) :
    PBu (fun (_ : α) (g : Fin M → ℝ) => f g) := by
  obtain ⟨k, C, hC, h, -⟩ := tg_bound hf
  exact ⟨k, C, hC, fun _ g => h g⟩

theorem norm_single_le (k : Fin M) : ‖(Pi.single k (1 : ℝ) : Fin M → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem PBu.of_fderiv {f : (Fin M → ℝ) → ℝ} (hf : f.HasTemperateGrowth) (k : Fin M) :
    PBu (fun (_ : α) (g : Fin M → ℝ) => fderiv ℝ f g (Pi.single k 1)) := by
  obtain ⟨k', C, hC, -, h⟩ := tg_bound hf
  refine ⟨k', C, hC, fun _ g => ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ f g (Pi.single k 1)‖ ≤ ‖fderiv ℝ f g‖ * ‖(Pi.single k (1:ℝ) : Fin M → ℝ)‖ :=
        (fderiv ℝ f g).le_opNorm _
    _ ≤ ‖fderiv ℝ f g‖ * 1 := mul_le_mul_of_nonneg_left (norm_single_le k) (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact h g

end pb


/-! ### The test function and its derivatives -/

section core
open SharpLSI.FL.Gross
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  (c : ι → ℝ) (Y : ι → (Fin M → ℝ) → ℝ) (Xj : ι → Config N d → ℝ) (u : (Fin M → ℝ) → ℝ) (κ : ℝ)

/-- `a(x,g) = ∑_i c_i Y_i(g) X_i(x)`. -/
def aF (x : Config N d) (g : Fin M → ℝ) : ℝ := ∑ i, (c i * Y i g) * Xj i x

/-- `s(g) = √κ e^{u(g)/2}`. -/
noncomputable def sF (g : Fin M → ℝ) : ℝ := Real.sqrt κ * Real.exp (u g / 2)

/-- The test function `h(x,g) = √κ e^{u(g)/2} a(x,g)`, written as a combination of the `X_i`. -/
noncomputable def hh (x : Config N d) (g : Fin M → ℝ) : ℝ :=
  ∑ i, (sF u κ g * (c i * Y i g)) * Xj i x

/-- The tilt density `e^{-u}/κ`. -/
noncomputable def wd (g : Fin M → ℝ) : ℝ := Real.exp (-u g) / κ

def daF (x : Config N d) (g : Fin M → ℝ) (k : Fin M) : ℝ :=
  ∑ i, (c i * Xj i x) * fderiv ℝ (Y i) g (Pi.single k 1)

def duF (g : Fin M → ℝ) (k : Fin M) : ℝ := fderiv ℝ u g (Pi.single k 1)

/-- `κ e^{-u}`-weighted Gaussian-direction energy density. -/
def Ey0 (lam' : Fin M → ℝ) (x : Config N d) (g : Fin M → ℝ) : ℝ :=
  ∑ k, lam' k * (daF c Y Xj x g k + aF c Y Xj x g * duF u g k / 2) ^ 2

/-- Torus gradient of the `i`-th factor. -/
noncomputable def dXj (i : ι) (p : Fin N × Fin d) (x : Config N d) : ℝ :=
  dT (Xj i ∘ unflat) p (flat x)

/-- Weighted torus energy density. -/
noncomputable def Ex0 (x : Config N d) (g : Fin M → ℝ) : ℝ :=
  ∑ p, (∑ i, (c i * Y i g) * dXj Xj i p x) ^ 2

variable {c Y Xj u κ}

theorem hh_eq (x : Config N d) (g : Fin M → ℝ) :
    hh c Y Xj u κ x g = sF u κ g * aF c Y Xj x g := by
  unfold hh aF; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem sF_sq_mul_wd (hκ : 0 < κ) (g : Fin M → ℝ) : sF u κ g ^ 2 * wd u κ g = 1 := by
  unfold sF wd
  have h1 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have h2 : Real.exp (u g / 2) ^ 2 = Real.exp (u g) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, h1, h2, div_eq_mul_inv]
  have : Real.exp (u g) * Real.exp (-u g) = 1 := by rw [← Real.exp_add]; simp
  calc κ * Real.exp (u g) * (Real.exp (-u g) * κ⁻¹) = (Real.exp (u g) * Real.exp (-u g)) * (κ * κ⁻¹) := by ring
    _ = 1 := by rw [this, mul_inv_cancel₀ hκ.ne']; ring

theorem wd_nonneg (hκ : 0 < κ) (g : Fin M → ℝ) : 0 ≤ wd u κ g :=
  div_nonneg (Real.exp_pos _).le hκ.le

theorem hh_sq_mul_wd (hκ : 0 < κ) (x : Config N d) (g : Fin M → ℝ) :
    hh c Y Xj u κ x g ^ 2 * wd u κ g = aF c Y Xj x g ^ 2 := by
  rw [hh_eq, mul_pow, mul_assoc, mul_comm (aF c Y Xj x g ^ 2), ← mul_assoc, sF_sq_mul_wd hκ]
  ring

theorem hh_sq_log_mul_wd (hκ : 0 < κ) (x : Config N d) (g : Fin M → ℝ) :
    hh c Y Xj u κ x g ^ 2 * Real.log (hh c Y Xj u κ x g ^ 2) * wd u κ g =
      aF c Y Xj x g ^ 2 * (Real.log κ + u g + Real.log (aF c Y Xj x g ^ 2)) := by
  have hsq := hh_sq_mul_wd (c := c) (Y := Y) (Xj := Xj) (u := u) hκ x g
  by_cases ha : aF c Y Xj x g = 0
  · rw [hh_eq, ha]; simp
  · have hs : sF u κ g ^ 2 = κ * Real.exp (u g) := by
      unfold sF
      rw [mul_pow, Real.sq_sqrt hκ.le, ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    have hlog : Real.log (hh c Y Xj u κ x g ^ 2) =
        Real.log κ + u g + Real.log (aF c Y Xj x g ^ 2) := by
      rw [hh_eq, mul_pow, hs, Real.log_mul (by positivity) (by positivity),
        Real.log_mul hκ.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [mul_assoc, mul_comm (Real.log _), ← mul_assoc, hsq, hlog]


section deriv
variable (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth)
include hY

theorem hasFDerivAt_aF (x : Config N d) (g : Fin M → ℝ) :
    HasFDerivAt (fun g' => aF c Y Xj x g')
      (∑ i, (c i * Xj i x) • fderiv ℝ (Y i) g) g := by
  unfold aF
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have := ((((hY i).1.differentiable (by simp)) g).hasFDerivAt.const_mul (c i)).mul_const (Xj i x)
  convert this using 1
  ext v
  simp [mul_left_comm]
  ring

theorem fderiv_aF (x : Config N d) (g : Fin M → ℝ) (k : Fin M) :
    fderiv ℝ (fun g' => aF c Y Xj x g') g (Pi.single k 1) = daF c Y Xj x g k := by
  rw [(hasFDerivAt_aF hY x g).fderiv]
  simp [daF]

include hu

theorem fderiv_hh (x : Config N d) (g : Fin M → ℝ) (k : Fin M) :
    fderiv ℝ (fun g' => hh c Y Xj u κ x g') g (Pi.single k 1) =
      sF u κ g * (daF c Y Xj x g k + aF c Y Xj x g * duF u g k / 2) := by
  have hfun : (fun g' => hh c Y Xj u κ x g') = fun g' => sF u κ g' * aF c Y Xj x g' := by
    funext g'; exact hh_eq x g'
  have hua : HasFDerivAt u (fderiv ℝ u g) g := ((hu.1.differentiable (by simp)) g).hasFDerivAt
  have hs : HasFDerivAt (fun g' => sF u κ g')
      (Real.sqrt κ • (Real.exp (u g / 2) • ((1/2 : ℝ) • fderiv ℝ u g))) g := by
    unfold sF
    have h2 : HasFDerivAt (fun g' => u g' / 2) ((1/2 : ℝ) • fderiv ℝ u g) g := by
      have := hua.const_mul (1/2 : ℝ)
      convert this using 1
      funext g'; ring
    have := h2.exp.const_mul (Real.sqrt κ)
    convert this using 1
  rw [hfun, (hs.fun_mul (hasFDerivAt_aF hY x g)).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have : (∑ i, (c i * Xj i x) • fderiv ℝ (Y i) g) (Pi.single k 1) = daF c Y Xj x g k := by
    simp [daF]
  rw [this]
  unfold sF duF
  ring


theorem wd_mul_energy (hκ : 0 < κ) (lam' : Fin M → ℝ) (x : Config N d) (g : Fin M → ℝ) :
    wd u κ g * ∑ k, lam' k * fderiv ℝ (fun g' => hh c Y Xj u κ x g') g (Pi.single k 1) ^ 2 =
      Ey0 c Y Xj u lam' x g := by
  simp_rw [fderiv_hh hY hu]
  unfold Ey0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := sF_sq_mul_wd (u := u) hκ g
  calc wd u κ g * (lam' k * (sF u κ g * (daF c Y Xj x g k + aF c Y Xj x g * duF u g k / 2)) ^ 2)
      = (sF u κ g ^ 2 * wd u κ g) * (lam' k * (daF c Y Xj x g k +
          aF c Y Xj x g * duF u g k / 2) ^ 2) := by ring
    _ = _ := by rw [this, one_mul]

end deriv

section torusPart
variable (hX : ∀ i, C1C (Xj i))
include hX

theorem C1C_hh (g : Fin M → ℝ) : C1C (fun x => hh c Y Xj u κ x g) := by
  unfold hh
  exact C1C.sum Finset.univ _ fun i _ => hX i

theorem gradPair_hh (g : Fin M → ℝ) (x : Config N d) :
    gradPair (fun x' => hh c Y Xj u κ x' g) (fun x' => hh c Y Xj u κ x' g) x =
      sF u κ g ^ 2 * Ex0 c Y Xj x g := by
  unfold gradPair Ex0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h := dT_sum (Finset.univ : Finset ι) (g := fun i => Xj i ∘ unflat)
    (fun i => sF u κ g * (c i * Y i g)) (fun i _ => hX i) p (flat x)
  have h' : dT ((fun x' => hh c Y Xj u κ x' g) ∘ unflat) p (flat x) =
      sF u κ g * ∑ i, (c i * Y i g) * dXj Xj i p x := by
    unfold hh dXj
    refine h.trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h']; ring

end torusPart

section pbfacts
variable (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth)
  (hX : ∀ i, C1C (Xj i))

omit hu in
include hY hX in
theorem pbu_aF : PBu (aF c Y Xj) := by
  unfold aF
  refine PBu.sum _ fun i _ => ?_
  obtain ⟨K, hK⟩ := (hX i).bounded
  exact ((PBu.of_tg (α := Config N d) (hY i)).const_mul (c i)).mul (PBu.of_bdd K hK)

omit hu in
include hY hX in
theorem pbu_daF (k : Fin M) : PBu (fun x g => daF c Y Xj x g k) := by
  unfold daF
  refine PBu.sum _ fun i _ => ?_
  obtain ⟨K, hK⟩ := (hX i).bounded
  have h1 : PBu (fun (x : Config N d) (_ : Fin M → ℝ) => c i * Xj i x) :=
    PBu.of_bdd (|c i| * K) fun x => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)
  exact h1.mul (PBu.of_fderiv (hY i) k)

include hY hu hX in
theorem pbu_Ey0 (lam' : Fin M → ℝ) : PBu (Ey0 c Y Xj u lam') := by
  unfold Ey0
  refine PBu.sum _ fun k _ => ?_
  have h1 := pbu_daF hY hX (c := c) k
  have h2 := (pbu_aF hY hX (c := c)).mul (PBu.of_fderiv (α := Config N d) hu k)
  have h3 := (h1.add (h2.const_mul (1 / 2))).sq.const_mul (lam' k)
  convert h3 using 3
  unfold duF; ring

omit hu in
include hY hX in
theorem pbu_Ex0 : PBu (Ex0 c Y Xj) := by
  unfold Ex0
  refine PBu.sum _ fun p _ => ?_
  refine PBu.sq (PBu.sum _ fun i _ => ?_)
  obtain ⟨K, hK⟩ := (hX i).dT_bounded p
  have h1 : PBu (fun (x : Config N d) (_ : Fin M → ℝ) => dXj Xj i p x) :=
    PBu.of_bdd K fun x => hK (flat x)
  exact (((PBu.of_tg (α := Config N d) (hY i)).const_mul (c i))).mul h1

end pbfacts

end core

end SharpLSI.FL.HLA

end
