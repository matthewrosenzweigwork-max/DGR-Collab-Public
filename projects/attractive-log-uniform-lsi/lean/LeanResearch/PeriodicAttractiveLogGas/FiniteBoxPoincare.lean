import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxLogSobolev
import LeanResearch.PeriodicAttractiveLogGas.IntegerBoxConditionalEntropy

/-! Source2090–2099: the supplied interval telescoping and successive-coordinate
Poincare proof, followed by comparison of actual conditional box weights.
This module does not infer Poincare from an entropy inequality. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteBoxPoincare
open FiniteBoxLogSobolev IntegerBoxConditionalEntropy
open IntegerBoxLogWeights FiniteEntropyLocalization FiniteGraph

def mean {α : Type*} [Fintype α] (w f : α → ℝ) : ℝ := ∑ x, w x * f x

def variance {α : Type*} [Fintype α] (w f : α → ℝ) : ℝ :=
  ∑ x, w x * (f x - mean w f)^2

theorem variance_nonneg {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) : 0 ≤ variance w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)

theorem centered_moment {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw1 : (∑ x, w x) = 1) (c : ℝ) :
    (∑ x, w x * (f x-c)^2) =
      (∑ x, w x*f x^2) - 2*c*mean w f + c^2 := by
  calc
    _ = ∑ x, (w x*f x^2 - (2*c)*(w x*f x) + c^2*w x) :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hw1, mul_one]
      rfl

theorem variance_eq {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw1 : (∑ x, w x) = 1) :
    variance w f = (∑ x, w x*f x^2) - (mean w f)^2 := by
  rw [variance, centered_moment w f hw1]
  ring

theorem centering_minimizes {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw1 : (∑ x, w x) = 1) (c : ℝ) :
    variance w f ≤ ∑ x, w x*(f x-c)^2 := by
  rw [variance_eq w f hw1, centered_moment w f hw1 c]
  nlinarith only [sq_nonneg (mean w f-c)]

theorem uniform_sum (D n : ℕ) :
    (∑ _ : Box D n, uniformWeight D n) = 1 := by
  simpa only [average, mul_one] using average_const D n (1 : ℝ)

theorem line_weight_sum (n : ℕ) :
    (∑ _ : Fin (n+1), ((n+1 : ℕ) : ℝ)⁻¹) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

def boxVariance (D n : ℕ) (f : Box D n → ℝ) : ℝ :=
  variance (fun _ => uniformWeight D n) f

theorem boxVariance_eq (D n : ℕ) (f : Box D n → ℝ) :
    boxVariance D n f = average D n (fun x => f x^2) - (average D n f)^2 :=
  variance_eq _ _ (uniform_sum D n)

theorem average_sub (D n : ℕ) (f g : Box D n → ℝ) :
    average D n (fun x => f x-g x) = average D n f-average D n g := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

theorem average_sq (D n : ℕ) (f : Box D n → ℝ) :
    (average D n f)^2 ≤ average D n (fun x => f x^2) := by
  have hh := variance_nonneg (fun _ : Box D n => uniformWeight D n) f
    (fun _ => (uniformWeight_pos D n).le)
  rw [show variance (fun _ : Box D n => uniformWeight D n) f = boxVariance D n f from rfl,
    boxVariance_eq] at hh
  linarith only [hh]

/-- Telescoping and Cauchy--Schwarz on n+1 actual interval vertices. -/
theorem line_poincare (n : ℕ) (f : Fin (n+1) → ℝ) :
    variance (fun _ => ((n+1 : ℕ) : ℝ)⁻¹) f ≤
      (n+1 : ℕ)^2 * lineEnergy n f := by
  let g : ℕ → ℝ := fun k => if h : k < n+1 then f ⟨k,h⟩ else 0
  have hg (k : Fin (n+1)) : g k = f k := by simp only [g, dite_eq_left k.isLt]
  have hm : mean (fun _ : Fin (n+1) => ((n+1 : ℕ) : ℝ)⁻¹) f =
      IntervalLogSobolev.intervalMean n g := by
    simp only [mean, IntervalLogSobolev.intervalMean, hg, ← Finset.mul_sum]
    ring
  have he : IntervalLogSobolev.pathEnergy n g = lineEnergy n f := by
    unfold IntervalLogSobolev.pathEnergy lineEnergy
    rw [← Fin.sum_univ_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show g (k+1) = f k.succ from hg k.succ,
      show g k = f k.castSucc from hg k.castSucc]
  have hp (i : Fin (n+1)) :
      (f i-mean (fun _ : Fin (n+1) => ((n+1 : ℕ) : ℝ)⁻¹) f)^2 ≤
        (n+1 : ℕ)^2*lineEnergy n f := by
    simpa only [hg, he, ← hm] using IntervalLogSobolev.centered_sq_le n g i
  unfold variance
  calc
    _ ≤ ∑ _ : Fin (n+1), ((n+1 : ℕ) : ℝ)⁻¹ *
        ((n+1 : ℕ)^2*lineEnergy n f) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hp i) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, line_weight_sum, one_mul]

/-- Exact conditioning of the variance on the first coordinate. -/
theorem boxVariance_succ (D n : ℕ) (f : Box (D+1) n → ℝ) :
    boxVariance (D+1) n f =
      (∑ a : Fin (n+1), ((n+1 : ℕ) : ℝ)⁻¹ *
        boxVariance D n (fun x => f (Fin.cons a x))) +
      variance (fun _ : Fin (n+1) => ((n+1 : ℕ) : ℝ)⁻¹)
        (fun a => average D n (fun x => f (Fin.cons a x))) := by
  rw [boxVariance_eq, average_succ, average_succ,
    variance_eq _ _ (line_weight_sum n)]
  simp only [boxVariance_eq, mul_sub, Finset.sum_sub_distrib, mean]
  ring

/-- Squared increments of conditional means are bounded by mean squared increments. -/
theorem lineEnergy_average_le (D n : ℕ) (f : Fin (n+1) → Box D n → ℝ) :
    lineEnergy n (fun a => average D n (f a)) ≤
      average D n (fun x => lineEnergy n (fun a => f a x)) := by
  have hh (k : Fin n) :
      (average D n (f k.succ)-average D n (f k.castSucc))^2 ≤
        average D n (fun x => (f k.succ x-f k.castSucc x)^2) := by
    rw [← average_sub]
    exact average_sq D n _
  unfold lineEnergy
  calc
    _ ≤ (∑ k : Fin n, average D n (fun x => (f k.succ x-f k.castSucc x)^2)) /
        (n+1 : ℕ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => hh k)) (by positivity)
    _ = _ := by
      simp only [average, Finset.sum_div, mul_div_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Successive coordinate conditioning preserves the interval side-length factor.
Dimension zero and singleton sides are included. -/
theorem box_poincare (D n : ℕ) (f : Box D n → ℝ) :
    boxVariance D n f ≤ (n+1 : ℕ)^2*boxEnergy D n f := by
  induction D with
  | zero =>
    simp [boxVariance, variance, mean, uniformWeight, boxEnergy, average]
  | succ D ih =>
    have hm := line_poincare n (fun a => average D n (fun x => f (Fin.cons a x)))
    have he := lineEnergy_average_le D n (fun a x => f (Fin.cons a x))
    rw [boxVariance_succ, boxEnergy_succ, mul_add]
    apply add_le_add
    · calc
        _ ≤ ∑ a : Fin (n+1), ((n+1 : ℕ) : ℝ)⁻¹ *
            ((n+1 : ℕ)^2*boxEnergy D n (fun x => f (Fin.cons a x))) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih _) (by positivity)
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    · exact hm.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))

theorem variance_density_comparison {α : Type*} [Fintype α]
    (u w f : α → ℝ) (hw1 : (∑ x, w x) = 1)
    {C : ℝ} (hwu : ∀ x, w x ≤ C*u x) :
    variance w f ≤ C*variance u f := by
  calc
    _ ≤ ∑ x, w x*(f x-mean u f)^2 := centering_minimizes w f hw1 (mean u f)
    _ ≤ ∑ x, C*u x*(f x-mean u f)^2 :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hwu x) (sq_nonneg _)
    _ = _ := by simp only [variance, Finset.mul_sum, mul_assoc]

/-- Comparison with actual probability weights and actual forward-coordinate rates. -/
theorem weighted_box_poincare (D n : ℕ)
    (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : (∑ x, w x) = 1)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hwu : ∀ x, w x ≤ C*uniformWeight D n)
    (huw : ∀ x, uniformWeight D n ≤ C*w x)
    (hr : ∀ x i, (x i).val < n → r₀ ≤ r x i) :
    variance w f ≤ C^2*(n+1 : ℕ)^2/r₀*weightedEnergy D n w r f := by
  have he := energy_density_comparison D n w r f hw hC hr₀ huw hr
  calc
    _ ≤ C*boxVariance D n f := variance_density_comparison _ _ _ hw1 hwu
    _ ≤ C*((n+1 : ℕ)^2*boxEnergy D n f) :=
      mul_le_mul_of_nonneg_left (box_poincare D n f) hC
    _ ≤ C*((n+1 : ℕ)^2*(C/r₀*weightedEnergy D n w r f)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (sq_nonneg _)) hC
    _ = _ := by ring


theorem weighted_box_poincare_uniform (D n N : ℕ) (hN : 0 < N)
    (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : (∑ x, w x) = 1)
    {C c K : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hside : ((n+1 : ℕ) : ℝ)^2 ≤ K*N)
    (hwu : ∀ x, w x ≤ C*uniformWeight D n)
    (huw : ∀ x, uniformWeight D n ≤ C*w x)
    (hr : ∀ x i, (x i).val < n → c*N ≤ r x i) :
    variance w f ≤ (C^2*K/c)*weightedEnergy D n w r f := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hden := mul_pos hc hNr
  have hE := weightedEnergy_nonneg D n w r f hw (fun x i hi => hden.le.trans (hr x i hi))
  have hcoef : C^2*(n+1 : ℕ)^2/(c*N) ≤ C^2*K/c := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ C^2*(K*N) := mul_le_mul_of_nonneg_left hside (sq_nonneg _)
      _ = _ := by field_simp
  exact (weighted_box_poincare D n w r f hw hw1 hC hden hwu huw hr).trans
    (mul_le_mul_of_nonneg_right hcoef hE)

theorem mean_conditional_chart {D s : ℕ}
    (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : IntegerBoxMassGeometry.containingBox s y₀ c ⊆ Ω) (w F : ↥Ω → ℝ) :
    mean (conditionalWeight w (IntegerBoxMassGeometry.boxInOuter Ω s y₀ c)) F =
      mean (fun x => w (outerChart Ω y₀ c hB x)/∑ y, w (outerChart Ω y₀ c hB y))
        (fun x => F (outerChart Ω y₀ c hB x)) :=
  sum_conditional_test Ω y₀ c hB w F

theorem variance_conditional_chart {D s : ℕ}
    (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : IntegerBoxMassGeometry.containingBox s y₀ c ⊆ Ω) (w F : ↥Ω → ℝ) :
    variance (conditionalWeight w (IntegerBoxMassGeometry.boxInOuter Ω s y₀ c)) F =
      variance (fun x => w (outerChart Ω y₀ c hB x)/∑ y, w (outerChart Ω y₀ c hB y))
        (fun x => F (outerChart Ω y₀ c hB x)) := by
  unfold variance
  rw [mean_conditional_chart, sum_conditional_test Ω y₀ c hB]

/-- Conditional Poincare on the actual outer type, retaining only internal box
edges. This comparison does not assume an absolute lower bound for box mass. -/
theorem conditional_box_poincare {D s N : ℕ} (hN : 0 < N)
    (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : IntegerBoxMassGeometry.containingBox s y₀ c ⊆ Ω)
    (w F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (hw : ∀ x, 0 < w x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, w x*r x y = w y*r y x)
    {O c₀ K : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hside : ((2*s-2+1 : ℕ) : ℝ)^2 ≤ K*N)
    (hosc : ∀ x y : Box D (2*s-2),
      |Real.log (w (outerChart Ω y₀ c hB x))-Real.log (w (outerChart Ω y₀ c hB y))| ≤ O)
    (hcoord : ∀ x : Box D (2*s-2), ∀ i, (x i).val < 2*s-2 →
      c₀*N ≤ r (outerChart Ω y₀ c hB x) (outerChart Ω y₀ c hB (forward x i))) :
    variance (conditionalWeight w (IntegerBoxMassGeometry.boxInOuter Ω s y₀ c)) F ≤
      (Real.exp (2*O)*K/c₀)*
        energy (conditionalWeight w (IntegerBoxMassGeometry.boxInOuter Ω s y₀ c))
          (restrictedRates r (IntegerBoxMassGeometry.boxInOuter Ω s y₀ c)) F := by
  let e := outerChart Ω y₀ c hB
  let v := fun x => w (e x)
  let p := fun x => v x/∑ y, v y
  let q := fun x i => r (e x) (e (forward x i))
  have hv : ∀ x, 0 < v x := fun x => hw (e x)
  have hp : ∀ x, 0 ≤ p x := fun x => (div_pos (hv x) (positive_weight_sum v hv)).le
  have hd := normalized_density_comparison v hv hosc
  have hh := weighted_box_poincare_uniform D (2*s-2) N hN p q (fun x => F (e x))
    hp (normalized_weight_sum v hv) (Real.exp_pos O).le hc₀ hside hd.1 hd.2 hcoord
  have hexp : Real.exp O^2 = Real.exp (2*O) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hh
  rw [variance_conditional_chart Ω y₀ c hB w F]
  exact hh.trans (mul_le_mul_of_nonneg_left
    (conditional_coordinate_energy_le Ω y₀ c hB w F r (fun x => (hw x).le) hr hb)
    (by positivity))

/-- Multiplying by the actual mass cancels normalization exactly and leaves
the internal-edge form, with the original unnormalized weights. -/
theorem mass_mul_conditional_poincare {α : Type*} [Fintype α]
    (w F : α → ℝ) (r : α → α → ℝ) (B : Finset α)
    (hM : 0 < setMass w B) {A : ℝ}
    (hpi : variance (conditionalWeight w B) F ≤
      A*energy (conditionalWeight w B) (restrictedRates r B) F) :
    (∑ x ∈ B, w x*(F x-mean (conditionalWeight w B) F)^2) ≤
      A*energy (restrictedWeight w B) (restrictedRates r B) F := by
  have hnorm : setMass w B*variance (conditionalWeight w B) F =
      ∑ x ∈ B, w x*(F x-mean (conditionalWeight w B) F)^2 := by
    unfold variance
    simp only [conditionalWeight, mul_assoc, ← Finset.mul_sum]
    rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul, sum_restricted_test]
  have henergy : setMass w B*energy (conditionalWeight w B) (restrictedRates r B) F =
      energy (restrictedWeight w B) (restrictedRates r B) F := by
    change setMass w B*energy (fun x => (setMass w B)⁻¹*restrictedWeight w B x)
      (restrictedRates r B) F = _
    rw [energy_scale_weights, ← mul_assoc,
      mul_inv_cancel₀ hM.ne', one_mul]
  have hh := mul_le_mul_of_nonneg_left hpi hM.le
  rw [hnorm] at hh
  calc
    _ ≤ setMass w B*(A*energy (conditionalWeight w B) (restrictedRates r B) F) := hh
    _ = A*(setMass w B*energy (conditionalWeight w B) (restrictedRates r B) F) := by ring
    _ = _ := by rw [henergy]


open IntegerBoxMassGeometry

/-- Flooring enumerates exactly the closed real-radius integer cube. -/
theorem centered_box_mem_iff {D : ℕ} (y₀ y : Fin D → ℤ) {R : ℝ} (hR : 0 ≤ R) :
    y ∈ containingBox (⌊R⌋₊+1) y₀ (fun _ => 0) ↔
      ∀ i, |((y i-y₀ i : ℤ) : ℝ)| ≤ R := by
  rw [mem_containingBox_iff (by omega)]
  simp only [mul_zero, sub_zero, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  constructor
  · intro h i
    have hi : |((y i-y₀ i : ℤ) : ℝ)| ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h i
    exact hi.trans (Nat.floor_le hR)
  · intro h i
    have habs := congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs (y i-y₀ i))
    simp only [Int.cast_natCast, Int.cast_abs] at habs
    have hn : (y i-y₀ i).natAbs ≤ ⌊R⌋₊ :=
      (Nat.le_floor_iff hR).mpr (by rw [habs]; exact h i)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn

def centralBox {D : ℕ} (Ω : Finset (Fin D → ℤ)) (y₀ : Fin D → ℤ) (R : ℝ) :
    Finset ↥Ω := boxInOuter Ω (⌊R⌋₊+1) y₀ (fun _ => 0)

theorem mem_centralBox_iff {D : ℕ} (Ω : Finset (Fin D → ℤ))
    (y₀ : Fin D → ℤ) {R : ℝ} (hR : 0 ≤ R) (x : ↥Ω) :
    x ∈ centralBox Ω y₀ R ↔ ∀ i, |((x.val i-y₀ i : ℤ) : ℝ)| ≤ R := by
  classical
  simp only [centralBox, boxInOuter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact centered_box_mem_iff y₀ x.val hR

/-- The source M+M² oscillation follows by telescoping actual increments.
There is no absolute point-mass or conditional-mass lower-bound premise. -/
theorem central_log_oscillation {D N : ℕ} (hN : 0 < N)
    (y₀ : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ) {M C T : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hMT : M*Real.sqrt N ≤ T)
    (hinc : LogIncrementBound y₀ T N C w)
    (y z : Fin D → ℤ)
    (hy : ∀ i, |((y i-y₀ i : ℤ) : ℝ)| ≤ M*Real.sqrt N)
    (hz : ∀ i, |((z i-y₀ i : ℤ) : ℝ)| ≤ M*Real.sqrt N) :
    |Real.log (w y)-Real.log (w z)| ≤ 4*D*C*(M+M^2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hcancel1 : M*Real.sqrt (N : ℝ)*(1/Real.sqrt N) = M := by field_simp
  have hcancel2 : (M*Real.sqrt (N : ℝ))^2/N = M^2 := by
    rw [mul_pow, Real.sq_sqrt hNr.le, mul_div_cancel_right₀ _ hNr.ne']
  have hcost : (D : ℝ)*(2*(M*Real.sqrt N))*(C*(1/Real.sqrt N+(M*Real.sqrt N)/N)) =
      2*D*C*(M+M^2) := by
    calc
      _ = 2*D*C*(M*Real.sqrt (N : ℝ)*(1/Real.sqrt N)+(M*Real.sqrt N)^2/N) := by ring
      _ = _ := by rw [hcancel1,hcancel2]
  have hy' := central_log_difference_real hN y₀ y hC
    (mul_nonneg hM hS.le) hMT hy w hinc
  have hz' := central_log_difference_real hN y₀ z hC
    (mul_nonneg hM hS.le) hMT hz w hinc
  rw [hcost] at hy' hz'
  have ht := abs_sub_le (Real.log (w y)) (Real.log (w y₀)) (Real.log (w z))
  rw [abs_sub_comm (Real.log (w y₀)) (Real.log (w z))] at ht
  linarith only [ht,hy',hz']

theorem central_side_bound {N : ℕ} (hN : 1 ≤ N) {M : ℝ} (hM : 0 ≤ M) :
    ((2*(⌊M*Real.sqrt (N : ℝ)⌋₊+1)-2+1 : ℕ) : ℝ)^2 ≤ (2*M+1)^2*N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hS : 1 ≤ Real.sqrt (N : ℝ) := by simpa using Real.sqrt_le_sqrt hNr
  have hf := Nat.floor_le (mul_nonneg hM (Real.sqrt_nonneg (N : ℝ)))
  have hs : (2*(⌊M*Real.sqrt (N : ℝ)⌋₊ : ℝ)+1) ≤ (2*M+1)*Real.sqrt N := by nlinarith
  have he : 2*(⌊M*Real.sqrt (N : ℝ)⌋₊+1)-2+1 = 2*⌊M*Real.sqrt (N : ℝ)⌋₊+1 := by omega
  rw [he]
  push_cast
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(⌊M*Real.sqrt (N : ℝ)⌋₊ : ℝ)+1) hs 2
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using hh

/-- The complete finite central-box argument in source2090–2099: interval
telescoping, coordinate conditioning, actual local increments, rate comparison
and exact cancellation of the box mass. The final form retains only internal
edges and the actual unnormalized weights. -/
theorem source_central_box_poincare {D N : ℕ} (hN : 1 ≤ N)
    (Ω : Finset (Fin D → ℤ)) (y₀ : Fin D → ℤ)
    (w : (Fin D → ℤ) → ℝ) (F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    {M C T c₀ : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hMT : M*Real.sqrt N ≤ T)
    (hΩ : ∀ z, (∀ i, |((z i-y₀ i : ℤ) : ℝ)| ≤ T) → z ∈ Ω)
    (hw : ∀ z ∈ Ω, 0 < w z) (hr : ∀ x z, 0 ≤ r x z)
    (hbalance : ∀ x z : ↥Ω, w x.val*r x z = w z.val*r z x)
    (hinc : LogIncrementBound y₀ T N C w)
    (hcoord : ∀ x z : ↥Ω,
      (∀ i, |((x.val i-y₀ i : ℤ) : ℝ)| ≤ T) →
      (∀ i, |((z.val i-y₀ i : ℤ) : ℝ)| ≤ T) →
      ∀ i, z.val = Function.update x.val i (x.val i+1) → c₀*N ≤ r x z) :
    let B := centralBox Ω y₀ (M*Real.sqrt N)
    let W := fun z : ↥Ω => w z.val
    (∑ z ∈ B, W z*(F z-mean (conditionalWeight W B) F)^2) ≤
      (Real.exp (8*D*C*(M+M^2))*(2*M+1)^2/c₀)*
        energy (restrictedWeight W B) (restrictedRates r B) F := by
  let s := ⌊M*Real.sqrt (N : ℝ)⌋₊+1
  let B := centralBox Ω y₀ (M*Real.sqrt N)
  let W := fun z : ↥Ω => w z.val
  have hR : 0 ≤ M*Real.sqrt (N : ℝ) := mul_nonneg hM (Real.sqrt_nonneg _)
  have hcentral : ∀ z ∈ containingBox s y₀ (fun _ => 0),
      ∀ i, |((z i-y₀ i : ℤ) : ℝ)| ≤ M*Real.sqrt N := by
    intro z hz
    exact (centered_box_mem_iff y₀ z hR).mp hz
  have hB : containingBox s y₀ (fun _ => 0) ⊆ Ω :=
    fun z hz => hΩ z (fun i => (hcentral z hz i).trans hMT)
  have hw' : ∀ z, 0 < W z := fun z => hw z.val z.property
  have hne : B.Nonempty :=
    ⟨outerChart Ω y₀ (fun _ => 0) hB (fun _ => 0),
      outerChart_mem Ω y₀ (fun _ => 0) hB (fun _ => 0)⟩
  have hmass : 0 < setMass W B := setMass_pos W B hw' hne
  have hosc (x z : Box D (2*s-2)) :
      |Real.log (W (outerChart Ω y₀ (fun _ => 0) hB x))-
        Real.log (W (outerChart Ω y₀ (fun _ => 0) hB z))| ≤ 4*D*C*(M+M^2) :=
    central_log_oscillation (by omega) y₀ w hM hC hMT hinc _ _
      (hcentral _ (chart_mem_containingBox (s := s) y₀ _ x))
      (hcentral _ (chart_mem_containingBox (s := s) y₀ _ z))
  have hchart (x : Box D (2*s-2)) :
      ∀ k, |(((outerChart Ω y₀ (fun _ => 0) hB x).val k-y₀ k : ℤ) : ℝ)| ≤ T :=
    fun k => (hcentral _ (chart_mem_containingBox (s := s) y₀ _ x) k).trans hMT
  have hrate (x : Box D (2*s-2)) (i : Fin D) (hi : (x i).val < 2*s-2) :
      c₀*N ≤ r (outerChart Ω y₀ (fun _ => 0) hB x)
        (outerChart Ω y₀ (fun _ => 0) hB (forward x i)) := by
    apply hcoord _ _ (hchart x) (hchart (forward x i)) i
    exact chart_forward_value _ x i hi
  have hh := conditional_box_poincare (by omega : 0 < N) Ω y₀ (fun _ => 0) hB
    W F r hw' hr hbalance hc₀ (sq_nonneg (2*M+1)) (central_side_bound hN hM) hosc hrate
  have hexp : 2*(4*(D : ℝ)*C*(M+M^2)) = 8*D*C*(M+M^2) := by ring
  rw [hexp] at hh
  exact mass_mul_conditional_poincare W F r B hmass hh

end PeriodicAttractiveLogGas.FiniteBoxPoincare
