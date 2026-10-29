import LeanResearch.PeriodicAttractiveLogGas.IntegerBoxLogWeights

/-! Literal product tents for source2160–2188.  Integer centers are finite on a
bounded query cube.  The shell partition and squared normalization are separate. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.ProductTentPartition

/-- The source's positive-part tent. -/
def hat (x : ℝ) : ℝ := max (1 - |x|) 0

/-- Literal tent at the integer lattice center s*c. -/
def tent (s : ℕ) (c y : ℤ) : ℝ := hat (((y - (s : ℤ) * c : ℤ) : ℝ) / s)

theorem hat_nonneg (x : ℝ) : 0 ≤ hat x := le_max_right _ _

theorem hat_le_one (x : ℝ) : hat x ≤ 1 := by
  unfold hat
  exact max_le (by linarith [abs_nonneg x]) (by norm_num)

theorem hat_ne_zero_iff (x : ℝ) : hat x ≠ 0 ↔ |x| < 1 := by
  unfold hat
  constructor
  · intro h
    by_contra hn
    apply h
    exact max_eq_right (by linarith)
  · intro h hz
    have hh := le_max_left (1 - |x|) 0
    rw [hz] at hh
    linarith

theorem hat_lipschitz (x y : ℝ) : |hat x - hat y| ≤ |x - y| := by
  have hh := abs_sub_abs_le_abs_sub x y
  have hh' := abs_sub_abs_le_abs_sub y x
  rw [abs_sub_comm y x] at hh'
  unfold hat
  rcases le_total (1 - |x|) 0 with hx | hx <;>
    rcases le_total (1 - |y|) 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [max_eq_right hx, max_eq_left hy, abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_right hy, abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_left hy]
    rw [abs_le]
    constructor <;> linarith

theorem tent_nonneg (s : ℕ) (c y : ℤ) : 0 ≤ tent s c y := hat_nonneg _
theorem tent_le_one (s : ℕ) (c y : ℤ) : tent s c y ≤ 1 := hat_le_one _

theorem tent_ne_zero_iff {s : ℕ} (hs : 0 < s) (c y : ℤ) :
    tent s c y ≠ 0 ↔ |y - (s : ℤ) * c| < (s : ℤ) := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  rw [tent, hat_ne_zero_iff, abs_div, abs_of_pos hsr, div_lt_one hsr]
  exact_mod_cast (Iff.rfl : |y - (s : ℤ) * c| < (s : ℤ) ↔ _)

/-- Integer nonzero support has the exact closed radius s-1. -/
theorem tent_support {s : ℕ} (hs : 0 < s) {c y : ℤ} (h : tent s c y ≠ 0) :
    |y - (s : ℤ) * c| ≤ (s : ℤ) - 1 := by
  have hh := (tent_ne_zero_iff hs c y).mp h
  omega

theorem tent_change {s : ℕ} (hs : 0 < s) (c y z : ℤ) :
    |tent s c y - tent s c z| ≤ |((y - z : ℤ) : ℝ)| / s := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hh := hat_lipschitz (((y - (s : ℤ) * c : ℤ) : ℝ) / s)
    (((z - (s : ℤ) * c : ℤ) : ℝ) / s)
  have he : (((y - (s : ℤ) * c : ℤ) : ℝ) / s) -
      (((z - (s : ℤ) * c : ℤ) : ℝ) / s) = ((y - z : ℤ) : ℝ) / s := by
    push_cast
    ring
  simpa only [tent, he, abs_div, abs_of_pos hsr] using hh

/-- The two possible tents at a Euclidean quotient/remainder. -/
theorem tent_at_quotient {s : ℕ} (hs : 0 < s) (q r y : ℤ)
    (hy : y = (s : ℤ) * q + r) (hr : 0 ≤ r) (hrs : r < (s : ℤ)) :
    tent s q y = 1 - (r : ℝ) / s ∧ tent s (q + 1) y = (r : ℝ) / s := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hrr : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hrsr : (r : ℝ) < s := by exact_mod_cast hrs
  have hd : (r : ℝ) / s < 1 := (div_lt_one hsr).mpr hrsr
  have hd0 : 0 ≤ (r : ℝ) / s := div_nonneg hrr hsr.le
  have he : y - (s : ℤ) * q = r := by omega
  have he' : y - (s : ℤ) * (q + 1) = r - s := by nlinarith only [hy]
  constructor
  · simp only [tent, he, hat, abs_of_nonneg hd0, max_eq_left (by linarith : 0 ≤ 1 - (r : ℝ) / s)]
  · have hn : ((r - (s : ℤ) : ℤ) : ℝ) / s ≤ 0 := by
      push_cast
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hsr.le
    have hv : 1 - |((r - (s : ℤ) : ℤ) : ℝ) / s| = (r : ℝ) / s := by
      rw [abs_of_nonpos hn]
      push_cast
      field_simp
      ring
    simp only [tent, he', hat, hv, max_eq_left hd0]

theorem tent_only_two {s : ℕ} (hs : 0 < s) (q r y c : ℤ)
    (hy : y = (s : ℤ) * q + r) (hr : 0 ≤ r) (hrs : r < (s : ℤ))
    (h : tent s c y ≠ 0) : c = q ∨ c = q + 1 := by
  have hh := abs_lt.mp ((tent_ne_zero_iff hs c y).mp h)
  have hsi : (0 : ℤ) < s := by exact_mod_cast hs
  by_contra hn
  have hq : c ≠ q := fun h => hn (Or.inl h)
  have hq' : c ≠ q + 1 := fun h => hn (Or.inr h)
  have hc : c < q ∨ q + 1 < c := by omega
  rcases hc with hc | hc
  · have hp := mul_le_mul_of_nonneg_left (show c + 1 ≤ q by omega) hsi.le
    nlinarith only [hp, hy, hr, hh.2]
  · have hp := mul_le_mul_of_nonneg_left (show q + 2 ≤ c by omega) hsi.le
    nlinarith only [hp, hy, hrs, hh.1]

/-- Literal product tent at an integer vector of lattice indices. -/
def productTent {D : ℕ} (s : ℕ) (c y : Fin D → ℤ) : ℝ :=
  ∏ i, tent s (c i) (y i)

private theorem product_bounds {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∏ i ∈ S, f i ∧ (∏ i ∈ S, f i) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hS := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha]
    exact ⟨mul_nonneg hfa.1 hS.1, (mul_le_mul hfa.2 hS.2 hS.1 (by norm_num)).trans_eq (one_mul 1)⟩

theorem productTent_bounds {D : ℕ} (s : ℕ) (c y : Fin D → ℤ) :
    0 ≤ productTent s c y ∧ productTent s c y ≤ 1 :=
  product_bounds Finset.univ _ (fun i _ => ⟨tent_nonneg s (c i) (y i), tent_le_one s (c i) (y i)⟩)

private theorem product_difference {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ ∑ i ∈ S, |f i - g i| := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hb := product_bounds S g hgS
    have hind := ih hfS hgS
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) +
          (f a - g a) * ∏ i ∈ S, g i| := by congr 1; ring
      _ ≤ |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)| +
          |(f a - g a) * ∏ i ∈ S, g i| := abs_add_le _ _
      _ = f a * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| +
          |f a - g a| * ∏ i ∈ S, g i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfa.1, abs_of_nonneg hb.1]
      _ ≤ 1 * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| + |f a - g a| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hfa.2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _))
      _ ≤ |f a - g a| + ∑ i ∈ S, |f i - g i| := by
        simp only [one_mul, mul_one]
        linarith only [hind]

/-- Source sup-coordinate jump bound, with the exact D/s factor. -/
theorem productTent_change {D s : ℕ} (hs : 0 < s) (c y z : Fin D → ℤ)
    (hyz : ∀ i, |y i - z i| ≤ 1) :
    |productTent s c y - productTent s c z| ≤ (D : ℝ) / s := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hh := product_difference Finset.univ (fun i => tent s (c i) (y i))
    (fun i => tent s (c i) (z i))
    (fun i _ => ⟨tent_nonneg _ _ _, tent_le_one _ _ _⟩)
    (fun i _ => ⟨tent_nonneg _ _ _, tent_le_one _ _ _⟩)
  have hb (i : Fin D) : |tent s (c i) (y i) - tent s (c i) (z i)| ≤ 1 / (s : ℝ) :=
    (tent_change hs _ _ _).trans (div_le_div_of_nonneg_right
      (by exact_mod_cast hyz i) hsr.le)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have he : (∑ _ : Fin D, 1 / (s : ℝ)) = (D : ℝ) / s := by simp [div_eq_mul_inv]
  exact hh.trans (hsum.trans_eq he)

/-- A fixed finite index set for all queries in the bounded integer cube. -/
abbrev Center (R : ℕ) := ↥(Finset.Icc (-(R : ℤ) - 1) ((R : ℤ) + 1))

/-- Both Euclidean centers belong to the finite index set. -/
theorem quotient_centers_mem {R s : ℕ} (hs : 0 < s) (q r y : ℤ)
    (hy : y = (s : ℤ) * q + r) (hr : 0 ≤ r) (hrs : r < (s : ℤ))
    (hyR : -(R : ℤ) ≤ y ∧ y ≤ R) :
    q ∈ Finset.Icc (-(R : ℤ) - 1) ((R : ℤ) + 1) ∧
      q + 1 ∈ Finset.Icc (-(R : ℤ) - 1) ((R : ℤ) + 1) := by
  have hs1 : (1 : ℤ) ≤ s := by exact_mod_cast hs
  have hR : (0 : ℤ) ≤ R := by positivity
  have hqlo : -(R : ℤ) ≤ q := by
    by_contra hn
    have hq : q + 1 ≤ -(R : ℤ) := by omega
    have hh := mul_le_mul_of_nonpos_right hs1 (show q + 1 ≤ 0 by omega)
    nlinarith only [hh, hy, hrs, hq, hyR.1]
  have hqhi : q ≤ (R : ℤ) := by
    by_contra hn
    have hq : 0 ≤ q := by omega
    have hh := mul_le_mul_of_nonneg_right hs1 hq
    nlinarith only [hh, hy, hr, hyR.2, show (R : ℤ) < q by omega]
  constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega

/-- Scalar partition, derived from the actual quotient/remainder and literal hats. -/
theorem sum_tent_of_quotient {R s : ℕ} (hs : 0 < s) (q r y : ℤ)
    (hy : y = (s : ℤ) * q + r) (hr : 0 ≤ r) (hrs : r < (s : ℤ))
    (hyR : -(R : ℤ) ≤ y ∧ y ≤ R) :
    (∑ c : Center R, tent s c.val y) = 1 := by
  classical
  have hm := quotient_centers_mem hs q r y hy hr hrs hyR
  let a : Center R := ⟨q, hm.1⟩
  let b : Center R := ⟨q + 1, hm.2⟩
  have hab : a ≠ b := by intro h; have hh := congrArg Subtype.val h; dsimp only [a,b] at hh; omega
  have he : (∑ c : Center R, tent s c.val y) = tent s q y + tent s (q + 1) y := by
    calc
      _ = ∑ c ∈ ({a, b} : Finset (Center R)), tent s c.val y := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro c _ hc
        by_contra hz
        have htwo := tent_only_two hs q r y c.val hy hr hrs hz
        apply hc
        rcases htwo with h | h
        · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h)))
      _ = _ := by rw [Finset.sum_pair hab]
  rw [he]
  have hh := tent_at_quotient hs q r y hy hr hrs
  rw [hh.1, hh.2]
  ring

/-- A nonzero product forces every scalar factor to be nonzero. -/
theorem productTent_factor_ne_zero {D s : ℕ} (c y : Fin D → ℤ)
    (h : productTent s c y ≠ 0) (i : Fin D) : tent s (c i) (y i) ≠ 0 := by
  intro hi
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) hi)

/-- The whole literal integer box, not just the support points, is specified here. -/
theorem productTent_support {D s : ℕ} (hs : 0 < s) (c y : Fin D → ℤ)
    (h : productTent s c y ≠ 0) : ∀ i, |y i - (s : ℤ) * c i| ≤ (s : ℤ) - 1 := by
  intro i
  exact tent_support hs (productTent_factor_ne_zero c y h i)

/-- Partition of one on the entire queried integer interval. -/
theorem sum_tent {R s : ℕ} (hs : 0 < s) (y : ℤ)
    (hyR : -(R : ℤ) ≤ y ∧ y ≤ R) :
    (∑ c : Center R, tent s c.val y) = 1 := by
  have hsi : (0 : ℤ) < s := by exact_mod_cast hs
  exact sum_tent_of_quotient hs (y / s) (y % s) y
    (Int.mul_ediv_add_emod y s).symm (Int.emod_nonneg y hsi.ne')
    (Int.emod_lt_of_pos y hsi) hyR

/-- No omitted integer center can be nonzero at a queried point. -/
theorem tent_zero_outside {R s : ℕ} (hs : 0 < s) (y c : ℤ)
    (hyR : -(R : ℤ) ≤ y ∧ y ≤ R)
    (hc : c ∉ Finset.Icc (-(R : ℤ) - 1) ((R : ℤ) + 1)) : tent s c y = 0 := by
  have hsi : (0 : ℤ) < s := by exact_mod_cast hs
  by_contra hz
  have he := (Int.mul_ediv_add_emod y s).symm
  have hr := Int.emod_nonneg y hsi.ne'
  have hrs := Int.emod_lt_of_pos y hsi
  have ht := tent_only_two hs (y / s) (y % s) y c he hr hrs hz
  have hm := quotient_centers_mem hs (y / s) (y % s) y he hr hrs hyR
  rcases ht with ht | ht
  · exact hc (ht.symm ▸ hm.1)
  · exact hc (ht.symm ▸ hm.2)

/-- The index is fixed on the whole bounded cube, including dimension zero. -/
abbrev Centers (D R : ℕ) := Fin D → Center R

/-- Finite family of the literal product tents; no change to the source functions. -/
def phi {D R : ℕ} (s : ℕ) (c : Centers D R) (y : Fin D → ℤ) : ℝ :=
  productTent s (fun i => (c i).val) y

theorem phi_eq_literal {D R : ℕ} (s : ℕ) (c : Centers D R) (y : Fin D → ℤ) :
    phi s c y = ∏ i, max (1 - |((y i : ℝ) - (s : ℝ) * ((c i).val : ℝ)) / s|) 0 := by
  simp only [phi, productTent, tent, hat, Int.cast_sub, Int.cast_mul, Int.cast_natCast]

theorem phi_bounds {D R : ℕ} (s : ℕ) (c : Centers D R) (y : Fin D → ℤ) :
    0 ≤ phi s c y ∧ phi s c y ≤ 1 := productTent_bounds s _ y

/-- The genuine finite product partition, with no sum-one input. -/
theorem sum_phi {D R s : ℕ} (hs : 0 < s) (y : Fin D → ℤ)
    (hyR : ∀ i, -(R : ℤ) ≤ y i ∧ y i ≤ R) :
    (∑ c : Centers D R, phi s c y) = 1 := by
  classical
  change (∑ c : Fin D → Center R, ∏ i, tent s (c i).val (y i)) = 1
  rw [← Fintype.prod_sum (fun (i : Fin D) (c : Center R) => tent s c.val (y i))]
  simp_rw [sum_tent hs _ (hyR _)]
  simp

/-- Actual nonzero indices, including boundary values where one tent vanishes. -/
def activeCenters {D R : ℕ} (s : ℕ) (y : Fin D → ℤ) : Finset (Centers D R) := by
  classical
  exact Finset.univ.filter (fun c => phi s c y ≠ 0)

/-- Each nonzero index is encoded by its genuine quotient/successor choices. -/
theorem activeCenters_card_le {D R s : ℕ} (hs : 0 < s) (y : Fin D → ℤ) :
    (activeCenters (R := R) s y).card ≤ 2 ^ D := by
  classical
  have hsi : (0 : ℤ) < s := by exact_mod_cast hs
  let T := activeCenters (R := R) s y
  have ht (c : ↥T) (i : Fin D) : (c.val i).val = y i / s ∨ (c.val i).val = y i / s + 1 := by
    have hp : phi s c.val y ≠ 0 := (Finset.mem_filter.mp c.property).2
    exact tent_only_two hs (y i / s) (y i % s) (y i) (c.val i).val
      (Int.mul_ediv_add_emod (y i) s).symm (Int.emod_nonneg _ hsi.ne')
      (Int.emod_lt_of_pos _ hsi) (productTent_factor_ne_zero _ y hp i)
  let code : ↥T → (Fin D → Bool) := fun c i => if (c.val i).val = y i / s then true else false
  have hinj : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    funext i
    apply Subtype.ext
    have hi := congrFun hab i
    by_cases ha : (a.val i).val = y i / s <;>
      by_cases hb : (b.val i).val = y i / s
    · exact ha.trans hb.symm
    · simp [code, ha, hb] at hi
    · simp [code, ha, hb] at hi
    · exact ((ht a i).resolve_left ha).trans ((ht b i).resolve_left hb).symm
  have hcard := Fintype.card_le_of_injective code hinj
  simpa only [T, Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hcard

/-- Every nonzero finite-family tent has the exact source integer-box support. -/
theorem phi_support {D R s : ℕ} (hs : 0 < s) (c : Centers D R) (y : Fin D → ℤ)
    (h : phi s c y ≠ 0) : ∀ i, |y i - (s : ℤ) * (c i).val| ≤ (s : ℤ) - 1 :=
  productTent_support hs _ y h

/-- Actual finite-family variation on every coordinate-sup jump of size at most one. -/
theorem phi_change {D R s : ℕ} (hs : 0 < s) (c : Centers D R) (y z : Fin D → ℤ)
    (hyz : ∀ i, |y i - z i| ≤ 1) : |phi s c y - phi s c z| ≤ (D : ℝ) / s :=
  productTent_change hs _ y z hyz

end PeriodicAttractiveLogGas.ProductTentPartition
