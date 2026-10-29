import LeanResearch.PeriodicAttractiveLogGas.IntegerBoxMassGeometry

/-! Source2194–2242/2254–2290: literal conditional box laws and the
once-counted coordinate form inside the original reversible outer graph. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.IntegerBoxConditionalEntropy
open IntegerBoxLogWeights IntegerBoxMassGeometry FiniteBoxLogSobolev
open FiniteEntropyLocalization FibreEntropy FiniteGraph

variable {D s : ℕ}

/-- The affine chart lands in the original outer state space. -/
def outerChart (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (x : Box D (2*s-2)) : ↥Ω :=
  ⟨chart (lowerCorner s y₀ c) x, hB (chart_mem_containingBox y₀ c x)⟩

theorem outerChart_injective (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) : Function.Injective (outerChart Ω y₀ c hB) := by
  intro x y h
  have he : chart (lowerCorner s y₀ c) x = chart (lowerCorner s y₀ c) y :=
    congrArg (fun z : ↥Ω => z.val) h
  exact (chartEquiv (lowerCorner s y₀ c)).injective (Subtype.ext he)

theorem outerChart_mem (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (x : Box D (2*s-2)) :
    outerChart Ω y₀ c hB x ∈ boxInOuter Ω s y₀ c := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, chart_mem_containingBox y₀ c x⟩

theorem outerChart_image (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) :
    Finset.univ.image (outerChart Ω y₀ c hB) = boxInOuter Ω s y₀ c := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact outerChart_mem Ω y₀ c hB x
  · intro hz
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).2
    exact Finset.mem_image.mpr ⟨x, hx, Subtype.ext he⟩

/-- Onto the whole containing box, with the original outer subtype retained. -/
def outerChartEquiv (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) :
    Box D (2*s-2) ≃ ↥(boxInOuter Ω s y₀ c) :=
  Equiv.ofBijective (fun x => ⟨outerChart Ω y₀ c hB x, outerChart_mem Ω y₀ c hB x⟩) (by
    constructor
    · intro x y h
      exact outerChart_injective Ω y₀ c hB (congrArg Subtype.val h)
    · intro z
      have hz := z.property
      have hz' : z.val ∈ Finset.univ.image (outerChart Ω y₀ c hB) := by
        simpa only [outerChart_image Ω y₀ c hB] using hz
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hz'
      exact ⟨x, Subtype.ext he⟩)

theorem sum_chart (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (g : ↥Ω → ℝ) :
    (∑ x : Box D (2*s-2), g (outerChart Ω y₀ c hB x)) =
      ∑ z ∈ boxInOuter Ω s y₀ c, g z := by
  classical
  rw [← outerChart_image Ω y₀ c hB, Finset.sum_image]
  exact fun x _ y _ h => outerChart_injective Ω y₀ c hB h

theorem sum_restricted_test {α : Type*} [Fintype α] (w g : α → ℝ) (B : Finset α) :
    (∑ z, restrictedWeight w B z * g z) = ∑ z ∈ B, w z * g z := by
  classical
  calc
    _ = ∑ z : α, if z ∈ B then w z * g z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ B <;> simp [restrictedWeight, hz]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem setMass_eq_chart (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (w : ↥Ω → ℝ) :
    setMass w (boxInOuter Ω s y₀ c) = ∑ x, w (outerChart Ω y₀ c hB x) := by
  have hh := sum_restricted_test w (fun _ => 1) (boxInOuter Ω s y₀ c)
  simp only [mul_one] at hh
  exact hh.trans (sum_chart Ω y₀ c hB w).symm

theorem conditionalWeight_chart (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (w : ↥Ω → ℝ) (x : Box D (2*s-2)) :
    conditionalWeight w (boxInOuter Ω s y₀ c) (outerChart Ω y₀ c hB x) =
      w (outerChart Ω y₀ c hB x) / ∑ z, w (outerChart Ω y₀ c hB z) := by
  classical
  rw [conditionalWeight, setMass_eq_chart Ω y₀ c hB w]
  simp only [restrictedWeight, outerChart_mem Ω y₀ c hB x, ite_true]
  ring

theorem sum_conditional_test (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (w g : ↥Ω → ℝ) :
    (∑ z, conditionalWeight w (boxInOuter Ω s y₀ c) z * g z) =
      ∑ x, (w (outerChart Ω y₀ c hB x) / ∑ y, w (outerChart Ω y₀ c hB y)) *
        g (outerChart Ω y₀ c hB x) := by
  simp only [conditionalWeight, mul_assoc, ← Finset.mul_sum]
  rw [sum_restricted_test, ← sum_chart Ω y₀ c hB (fun z => w z * g z),
    setMass_eq_chart Ω y₀ c hB w]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact entropy transport, including the zero-weight complement of the box. -/
theorem finiteEntropy_conditional_chart (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (w F : ↥Ω → ℝ) :
    finiteEntropy (conditionalWeight w (boxInOuter Ω s y₀ c)) F =
      finiteEntropy (fun x => w (outerChart Ω y₀ c hB x) / ∑ y, w (outerChart Ω y₀ c hB y))
        (fun x => F (outerChart Ω y₀ c hB x)) := by
  unfold finiteEntropy
  rw [sum_conditional_test Ω y₀ c hB w (fun z => F z * Real.log (F z)),
    sum_conditional_test Ω y₀ c hB w F]


/-- A genuine forward neighbor, with a harmless stationary value on the last face. -/
def forward {n : ℕ} (x : Box D n) (i : Fin D) : Box D n :=
  Function.update x i ⟨min ((x i).val + 1) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def rank {n : ℕ} (x : Box D n) : ℕ := ∑ i, (x i).val

theorem forward_val {n : ℕ} (x : Box D n) (i : Fin D) (hi : (x i).val < n) :
    (forward x i i).val = (x i).val + 1 := by
  classical
  simp only [forward, Function.update_self, Nat.min_eq_left (by omega : (x i).val + 1 ≤ n)]

theorem forward_injective {n : ℕ} (x : Box D n) {i j : Fin D}
    (hi : (x i).val < n) (h : forward x i = forward x j) : i = j := by
  classical
  by_contra hij
  have he := congrArg (fun z : Box D n => (z i).val) h
  rw [forward_val x i hi] at he
  have he' : forward x j i = x i := Function.update_of_ne hij _ _
  rw [he'] at he
  omega

theorem rank_forward {n : ℕ} (x : Box D n) (i : Fin D) (hi : (x i).val < n) :
    rank (forward x i) = rank x + 1 := by
  classical
  unfold rank
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun j => (x j).val) (Finset.mem_univ i)]
  have hh : (∑ j ∈ Finset.univ.erase i, (forward x i j).val) =
      ∑ j ∈ Finset.univ.erase i, (x j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show forward x i j = x j from Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _]
  rw [hh, forward_val x i hi]
  omega

/-- Reversing an increasing-rank edge is disjoint from the forward orientation.
Detailed balance pairs their actual conductances; other edges stay nonnegative. -/
theorem increasing_energy_le {α : Type*} [Fintype α] (p : α → ℝ)
    (r : α → α → ℝ) (F : α → ℝ) (k : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, p x * r x y = p y * r y x) :
    (∑ x, ∑ y, if k x < k y then p x * r x y * (F y - F x)^2 else 0) ≤
      energy p r F := by
  classical
  have hswap : (∑ x, ∑ y, if k y < k x then p x * r x y * (F y - F x)^2 else 0) =
      ∑ x, ∑ y, if k x < k y then p x * r x y * (F y - F x)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : k x < k y
    · simp only [h, ite_true, hb y x]
      ring
    · simp only [h, ite_false]
  have hpoint (x y : α) :
      (if k x < k y then p x * r x y * (F y - F x)^2 else 0) +
      (if k y < k x then p x * r x y * (F y - F x)^2 else 0) ≤
      p x * r x y * (F y - F x)^2 := by
    have hpos := mul_nonneg (mul_nonneg (hp x) (hr x y)) (sq_nonneg (F y - F x))
    by_cases hxy : k x < k y
    · simp [hxy, not_lt.mpr (Nat.le_of_lt hxy)]
    · by_cases hyx : k y < k x
      · simp [hxy, hyx]
      · simpa only [hxy, hyx, ite_false, zero_add] using hpos
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun y _ => hpoint x y))
  simp only [Finset.sum_add_distrib] at hs
  rw [hswap] at hs
  unfold energy
  linarith only [hs]



/-- Each positive-coordinate edge is counted once; distinct coordinates have
 distinct destinations. No graph degree or edge-cardinality hypothesis is used. -/
theorem forward_energy_le {n : ℕ} (p : Box D n → ℝ)
    (r : Box D n → Box D n → ℝ) (F : Box D n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, p x * r x y = p y * r y x) :
    weightedEnergy D n p (fun x i => r x (forward x i)) F ≤ energy p r F := by
  classical
  have hrow (x : Box D n) :
      (∑ i, p x * r x (forward x i) * forwardSquare F x i) ≤
        ∑ y, if rank x < rank y then p x * r x y * (F y - F x)^2 else 0 := by
    let I := Finset.univ.filter (fun i : Fin D => (x i).val < n)
    have he : (∑ i, p x * r x (forward x i) * forwardSquare F x i) =
        ∑ i ∈ I, p x * r x (forward x i) * (F (forward x i) - F x)^2 := by
      rw [show I = Finset.univ.filter (fun i : Fin D => (x i).val < n) from rfl,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (x i).val < n
      · simp only [hi, ite_true, forwardSquare, dite_true]
        congr 2
        simp only [forward, Nat.min_eq_left (by omega : (x i).val + 1 ≤ n)]
      · simp only [hi, ite_false, forwardSquare, dite_false, mul_zero]
    rw [he]
    apply Finset.sum_le_sum_of_injOn (forward x)
    · intro i hi j hj hij
      exact forward_injective x (Finset.mem_filter.mp hi).2 hij
    · exact Finset.subset_univ _
    · intro i hi
      have hk : rank x < rank (forward x i) := by
        rw [rank_forward x i (Finset.mem_filter.mp hi).2]
        omega
      simp only [hk, ite_true, le_refl]
    · intro y _ _
      split
      · exact mul_nonneg (mul_nonneg (hp x) (hr x y)) (sq_nonneg _)
      · exact le_rfl
  exact (Finset.sum_le_sum (fun x _ => hrow x)).trans (increasing_energy_le p r F rank hp hr hb)

theorem sum_injective_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (g : β → ℝ) (hg : ∀ y, 0 ≤ g y) :
    (∑ x, g (e x)) ≤ ∑ y, g y := by
  classical
  exact Finset.sum_le_sum_of_injOn e (fun _ _ _ _ h => he h)
    (Finset.subset_univ _) (fun _ _ => le_rfl) (fun y _ _ => hg y)

/-- Restricting to the true injective chart cannot increase the half-directed form. -/
theorem energy_injective_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (p : β → ℝ) (r : β → β → ℝ) (F : β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hr : ∀ x y, 0 ≤ r x y) :
    energy (fun x => p (e x)) (fun x y => r (e x) (e y)) (fun x => F (e x)) ≤ energy p r F := by
  have hnon (x y : β) : 0 ≤ p x * r x y * (F y - F x)^2 :=
    mul_nonneg (mul_nonneg (hp x) (hr x y)) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
  exact (Finset.sum_le_sum (fun x _ =>
    sum_injective_le e he (fun y => p (e x) * r (e x) y * (F y - F (e x))^2)
      (fun y => hnon (e x) y))).trans
    (sum_injective_le e he (fun x => ∑ y, p x * r x y * (F y - F x)^2)
      (fun x => Finset.sum_nonneg (fun y _ => hnon x y)))

theorem coordinate_energy_le {α : Type*} [Fintype α] {n : ℕ}
    (e : Box D n → α) (he : Function.Injective e) (p : α → ℝ) (r : α → α → ℝ)
    (F : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, p x * r x y = p y * r y x) :
    weightedEnergy D n (fun x => p (e x)) (fun x i => r (e x) (e (forward x i)))
      (fun x => F (e x)) ≤ energy p r F :=
  (forward_energy_le (fun x => p (e x)) (fun x y => r (e x) (e y))
    (fun x => F (e x)) (fun x => hp (e x)) (fun x y => hr (e x) (e y))
    (fun x y => hb (e x) (e y))).trans (energy_injective_le e he p r F hp hr)

theorem conditional_balance {α : Type*} [Fintype α] (w : α → ℝ) (r : α → α → ℝ)
    (B : Finset α) (hb : ∀ x y, w x * r x y = w y * r y x) (x y : α) :
    conditionalWeight w B x * restrictedRates r B x y =
      conditionalWeight w B y * restrictedRates r B y x := by
  classical
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
  · simp only [conditionalWeight, restrictedWeight, restrictedRates, hx, hy, and_self,
      ite_true, mul_assoc, hb x y]
  all_goals simp [conditionalWeight, restrictedWeight, restrictedRates, hx, hy]

theorem restrictedRates_nonneg {α : Type*} [Fintype α] (r : α → α → ℝ)
    (B : Finset α) (hr : ∀ x y, 0 ≤ r x y) (x y : α) : 0 ≤ restrictedRates r B x y := by
  classical
  unfold restrictedRates
  split
  · exact hr x y
  · exact le_rfl

/-- The actual original rates occur in the chart form. Both endpoints belong
to the box, so conditional restriction does not alter these rates. -/
theorem conditional_coordinate_energy_le (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (w F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, w x * r x y = w y * r y x) :
    weightedEnergy D (2*s-2)
      (fun x => w (outerChart Ω y₀ c hB x) / ∑ y, w (outerChart Ω y₀ c hB y))
      (fun x i => r (outerChart Ω y₀ c hB x) (outerChart Ω y₀ c hB (forward x i)))
      (fun x => F (outerChart Ω y₀ c hB x)) ≤
    energy (conditionalWeight w (boxInOuter Ω s y₀ c)) (restrictedRates r (boxInOuter Ω s y₀ c)) F := by
  classical
  have hh := coordinate_energy_le (outerChart Ω y₀ c hB) (outerChart_injective Ω y₀ c hB)
    (conditionalWeight w (boxInOuter Ω s y₀ c)) (restrictedRates r (boxInOuter Ω s y₀ c)) F
    (conditionalWeight_nonneg w _ hw) (restrictedRates_nonneg r _ hr) (conditional_balance w r _ hb)
  simpa only [conditionalWeight_chart, restrictedRates, outerChart_mem Ω y₀ c hB,
    and_self, ite_true] using hh



/-- Conditional entropy on the original outer type, with genuine chart rates.
The oscillation hypothesis here is an intermediate interface, discharged below. -/
theorem conditional_box_lsi {N : ℕ} (hN : 0 < N)
    (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) (w F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (hw : ∀ x, 0 < w x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, w x * r x y = w y * r y x)
    {O c₀ K : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hside : ((2*s-2+1 : ℕ) : ℝ)^2 ≤ K*N)
    (hosc : ∀ x y : Box D (2*s-2),
      |Real.log (w (outerChart Ω y₀ c hB x)) - Real.log (w (outerChart Ω y₀ c hB y))| ≤ O)
    (hcoord : ∀ x : Box D (2*s-2), ∀ i, (x i).val < 2*s-2 →
      c₀*N ≤ r (outerChart Ω y₀ c hB x) (outerChart Ω y₀ c hB (forward x i))) :
    finiteEntropy (conditionalWeight w (boxInOuter Ω s y₀ c)) (fun z => F z^2) ≤
      (Real.exp (2*O) * (2+1/Real.exp 1) * K / c₀) *
        energy (conditionalWeight w (boxInOuter Ω s y₀ c)) (restrictedRates r (boxInOuter Ω s y₀ c)) F := by
  let e := outerChart Ω y₀ c hB
  let v := fun x => w (e x)
  let p := fun x => v x / ∑ y, v y
  let q := fun x i => r (e x) (e (forward x i))
  have hv : ∀ x, 0 < v x := fun x => hw (e x)
  have hp : ∀ x, 0 ≤ p x := fun x => (div_pos (hv x) (positive_weight_sum v hv)).le
  have hd := normalized_density_comparison v hv hosc
  have hh := weighted_box_entropy_uniform D (2*s-2) N hN p q (fun x => F (e x))
    hp (normalized_weight_sum v hv) (Real.exp_pos O).le hc₀ hside hd.1 hd.2 hcoord
  rw [entropy_finiteMeasure p _ hp (fun _ => sq_nonneg _)] at hh
  have hreal : finiteEntropy p (fun x => F (e x)^2) ≤
      (Real.exp O^2 * (2+1/Real.exp 1)*K/c₀) *
        weightedEnergy D (2*s-2) p q (fun x => F (e x)) := by exact_mod_cast hh
  have hexp : Real.exp O^2 = Real.exp (2*O) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hreal
  rw [finiteEntropy_conditional_chart Ω y₀ c hB w (fun z => F z^2)]
  exact hreal.trans (mul_le_mul_of_nonneg_left
    (conditional_coordinate_energy_le Ω y₀ c hB w F r (fun x => (hw x).le) hr hb)
    (by positivity))

/-- The affine chart really advances the original integer coordinate by one. -/
theorem chart_forward_value {n : ℕ} (l : Fin D → ℤ) (x : Box D n) (i : Fin D)
    (hi : (x i).val < n) :
    chart l (forward x i) = Function.update (chart l x) i (chart l x i + 1) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp only [chart, forward, Function.update_self,
      Nat.min_eq_left (by omega : (x i).val + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    ring
  · simp only [chart, forward, Function.update_of_ne hj]

/-- The complete source conditional box inequality. Rates are the actual
original rates between primitive integer-coordinate neighbors in the central
cube. All box containment, oscillation and entropy/energy transports are derived. -/
theorem source_conditional_box_lsi {N j : ℕ} (hN : 1 ≤ N) {ε C c₀ : ℝ}
    (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hcut : 8 ≤ ε * Real.sqrt (N : ℝ)) (hj : j ≤ DyadicShellPartition.cutoff ε N)
    (Ω : Finset (Fin D → ℤ)) (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (hΩ : ∀ z, (∀ i, |((z i-y₀ i : ℤ) : ℝ)| ≤ 2*ε*N) → z ∈ Ω)
    (hshell : DyadicShellPartition.shell j (DyadicShellPartition.radius N y₀ y) ≠ 0)
    (htent : ProductTentPartition.productTent (DyadicShellPartition.scale N j) c
      (fun i => y i-y₀ i) ≠ 0)
    (hw : ∀ z ∈ Ω, 0 < w z) (hr : ∀ x z, 0 ≤ r x z)
    (hbalance : ∀ x z : ↥Ω, w x.val * r x z = w z.val * r z x)
    (hinc : LogIncrementBound y₀ (2*ε*N) N C w)
    (hcoord : ∀ x z : ↥Ω,
      (∀ i, |((x.val i-y₀ i : ℤ) : ℝ)| ≤ 2*ε*N) →
      (∀ i, |((z.val i-y₀ i : ℤ) : ℝ)| ≤ 2*ε*N) →
      ∀ i, z.val = Function.update x.val i (x.val i+1) → c₀*N ≤ r x z) :
    let B := boxInOuter Ω (DyadicShellPartition.scale N j) y₀ c
    finiteEntropy (conditionalWeight (fun z : ↥Ω => w z.val) B) (fun z => F z^2) ≤
      (9*Real.exp (40*D*C)*(2+1/Real.exp 1)/c₀) *
        energy (conditionalWeight (fun z : ↥Ω => w z.val) B) (restrictedRates r B) F := by
  let s := DyadicShellPartition.scale N j
  have hcentral := source_box_central hN hcut hj y₀ c y hshell htent
  have hB : containingBox s y₀ c ⊆ Ω := fun z hz => hΩ z (hcentral z hz)
  have hosc := source_box_log_oscillation hN hC hcut hj y₀ c y w hshell htent hinc
  have hside := (ceiling_box_bounds hN (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    (rfl : 2*s-2 = 2*⌈Real.sqrt (N : ℝ)/(2:ℝ)^j⌉₊-2)).1
  have hrate (x : Box D (2*s-2)) (i : Fin D) (hi : (x i).val < 2*s-2) :
      c₀*N ≤ r (outerChart Ω y₀ c hB x) (outerChart Ω y₀ c hB (forward x i)) := by
    apply hcoord _ _ (hcentral _ (chart_mem_containingBox y₀ c x))
      (hcentral _ (chart_mem_containingBox y₀ c (forward x i))) i
    exact chart_forward_value _ x i hi
  have hh := conditional_box_lsi (by omega : 0 < N) Ω y₀ c hB
    (fun z : ↥Ω => w z.val) F r (fun z => hw z.val z.property) hr hbalance hc₀
    (by norm_num : (0 : ℝ) ≤ 9) hside
    (fun x z => hosc _ (chart_mem_containingBox y₀ c z) _ (chart_mem_containingBox y₀ c x)) hrate
  have he : Real.exp (2*(20*(D:ℝ)*C)) * (2+1/Real.exp 1)*9/c₀ =
      9*Real.exp (40*D*C)*(2+1/Real.exp 1)/c₀ := by
    rw [show 2*(20*(D:ℝ)*C) = 40*D*C by ring]
    ring
  simpa only [he] using hh

/-- Conditional entropy of a singleton is identically zero, including zero tests. -/
theorem singleton_conditional_entropy {α : Type*} [Fintype α] (w F : α → ℝ)
    (x : α) (hx : 0 < w x) : finiteEntropy (conditionalWeight w {x}) F = 0 := by
  classical
  have hM : setMass w {x} = w x := by simp [setMass, restrictedWeight]
  have hp (z : α) : conditionalWeight w {x} z = if z = x then 1 else 0 := by
    by_cases hz : z = x
    · subst z
      simp [conditionalWeight, restrictedWeight, hM, hx.ne']
    · simp [conditionalWeight, restrictedWeight, hz]
  simp only [finiteEntropy, hp]
  simp

/-- Multiplication by the original, unnormalized box mass restores the full
outer energy; boundary and additional edges remain on the right. -/
theorem mass_mul_conditional_lsi {α : Type*} [Fintype α]
    (w F : α → ℝ) (r : α → α → ℝ) (B : Finset α)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y) (hM : 0 < setMass w B)
    {A : ℝ} (hA : 0 ≤ A)
    (hlsi : finiteEntropy (conditionalWeight w B) (fun x => F x^2) ≤
      A * energy (conditionalWeight w B) (restrictedRates r B) F) :
    setMass w B * finiteEntropy (conditionalWeight w B) (fun x => F x^2) ≤
      A * energy w r F := by
  calc
    _ ≤ setMass w B * (A * energy (conditionalWeight w B) (restrictedRates r B) F) :=
      mul_le_mul_of_nonneg_left hlsi hM.le
    _ = A * (setMass w B * energy (conditionalWeight w B) (restrictedRates r B) F) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mass_mul_conditional_energy_le w r F hw hr B hM.ne') hA



/-- All source inputs are primitive. The actual box law is normalized here,
its entropy is bounded in both real and extended conventions, and multiplying
by the original mass restores the full outer energy. -/
theorem source_box_lsi_and_outer_energy {N j : ℕ} (hN : 1 ≤ N) {ε C c₀ : ℝ}
    (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hcut : 8 ≤ ε * Real.sqrt (N : ℝ)) (hj : j ≤ DyadicShellPartition.cutoff ε N)
    (Ω : Finset (Fin D → ℤ)) (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (hΩ : ∀ z, (∀ i, |((z i-y₀ i : ℤ) : ℝ)| ≤ 2*ε*N) → z ∈ Ω)
    (hshell : DyadicShellPartition.shell j (DyadicShellPartition.radius N y₀ y) ≠ 0)
    (htent : ProductTentPartition.productTent (DyadicShellPartition.scale N j) c
      (fun i => y i-y₀ i) ≠ 0)
    (hw : ∀ z ∈ Ω, 0 < w z) (hr : ∀ x z, 0 ≤ r x z)
    (hbalance : ∀ x z : ↥Ω, w x.val * r x z = w z.val * r z x)
    (hinc : LogIncrementBound y₀ (2*ε*N) N C w)
    (hcoord : ∀ x z : ↥Ω,
      (∀ i, |((x.val i-y₀ i : ℤ) : ℝ)| ≤ 2*ε*N) →
      (∀ i, |((z.val i-y₀ i : ℤ) : ℝ)| ≤ 2*ε*N) →
      ∀ i, z.val = Function.update x.val i (x.val i+1) → c₀*N ≤ r x z) :
    let B := boxInOuter Ω (DyadicShellPartition.scale N j) y₀ c
    let W := fun z : ↥Ω => w z.val
    let A := 9*Real.exp (40*D*C)*(2+1/Real.exp 1)/c₀
    0 < setMass W B ∧ (∑ z, conditionalWeight W B z) = 1 ∧
      (∀ z ∈ B, 0 < conditionalWeight W B z) ∧
      finiteEntropy (conditionalWeight W B) (fun z => F z^2) ≤
        A * energy (conditionalWeight W B) (restrictedRates r B) F ∧
      entropy (finiteMeasure (conditionalWeight W B)) (fun z => F z^2) ≤
        ((A * energy (conditionalWeight W B) (restrictedRates r B) F : ℝ) : EReal) ∧
      setMass W B * finiteEntropy (conditionalWeight W B) (fun z => F z^2) ≤
        A * energy W r F := by
  classical
  let s := DyadicShellPartition.scale N j
  let B := boxInOuter Ω s y₀ c
  let W := fun z : ↥Ω => w z.val
  let A := 9*Real.exp (40*D*C)*(2+1/Real.exp 1)/c₀
  have hw' : ∀ z, 0 < W z := fun z => hw z.val z.property
  have hcentral := source_box_central hN hcut hj y₀ c y hshell htent
  have hB : containingBox s y₀ c ⊆ Ω := fun z hz => hΩ z (hcentral z hz)
  have hne : B.Nonempty :=
    ⟨outerChart Ω y₀ c hB (fun _ => 0), outerChart_mem Ω y₀ c hB (fun _ => 0)⟩
  have hM : 0 < setMass W B := setMass_pos W B hw' hne
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hp : ∀ z ∈ B, 0 < conditionalWeight W B z := by
    intro z hz
    simp only [conditionalWeight, restrictedWeight, hz, ite_true]
    exact mul_pos (inv_pos.mpr hM) (hw' z)
  have hlsi := source_conditional_box_lsi hN hC hc₀ hcut hj Ω y₀ c y w F r
    hΩ hshell htent hw hr hbalance hinc hcoord
  change finiteEntropy (conditionalWeight W B) (fun z => F z^2) ≤
    A * energy (conditionalWeight W B) (restrictedRates r B) F at hlsi
  refine ⟨hM, sum_conditionalWeight W B hM.ne', hp, hlsi, ?_, ?_⟩
  · rw [entropy_finiteMeasure _ _ (conditionalWeight_nonneg W B (fun z => (hw' z).le))
      (fun z => sq_nonneg (F z))]
    exact EReal.coe_le_coe_iff.mpr hlsi
  · exact mass_mul_conditional_lsi W F r B (fun z => (hw' z).le) hr hM hA hlsi

end PeriodicAttractiveLogGas.IntegerBoxConditionalEntropy
