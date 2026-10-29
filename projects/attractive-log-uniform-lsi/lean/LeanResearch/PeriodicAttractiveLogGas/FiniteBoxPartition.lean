import LeanResearch.PeriodicAttractiveLogGas.DyadicShellPartition

/-! The literal finite shell/product-tent family with the source singleton tail.
The finite index includes harmless identically zero functions. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteBoxPartition
open ProductTentPartition DyadicShellPartition FiniteSquaredPartition

variable {Ω : Type*} [Fintype Ω] {D R J : ℕ}

/-- Box indices and singleton indices in the source partition. -/
abbrev Index (Ω : Type*) (D R J : ℕ) := (Fin (J + 1) × Centers D R) ⊕ Ω

/-- Actual unnormalized functions, with their actual singleton tail. -/
def pieces (s : Fin (J + 1) → ℕ) (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ)
    (i : Index Ω D R J) (x : Ω) : ℝ := by
  classical
  exact match i with
  | Sum.inl (j, c) => shell j.val (ρ x) * phi (s j) c (y x)
  | Sum.inr z => if x = z then tail J (ρ x) else 0

omit [Fintype Ω] in
theorem pieces_nonneg (s : Fin (J + 1) → ℕ) (ρ : Ω → ℝ)
    (y : Ω → Fin D → ℤ) (i : Index Ω D R J) (x : Ω) :
    0 ≤ pieces s ρ y i x := by
  classical
  rcases i with ⟨j, c⟩ | z
  · exact mul_nonneg (shell_nonneg _ _) (phi_bounds _ _ _).1
  · simp only [pieces]
    split_ifs <;> first | exact tail_nonneg _ _ | exact le_rfl

/-- Both finite covers are proved covers; there is no partition assumption. -/
theorem sum_pieces (s : Fin (J + 1) → ℕ) (hs : ∀ j, 0 < s j)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ)
    (hy : ∀ x k, -(R : ℤ) ≤ y x k ∧ y x k ≤ R) (x : Ω) :
    (∑ i : Index Ω D R J, pieces s ρ y i x) = 1 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [pieces, ← Finset.mul_sum, sum_phi (hs _) _ (hy x), mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hh := dyadic_sum J (ρ x)
  rw [Finset.sum_range] at hh
  exact hh

/-- The active box count uses the true shell and product-tent support counts. -/
theorem activeCard_pieces (s : Fin (J + 1) → ℕ) (hs : ∀ j, 0 < s j)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ) (x : Ω) :
    activeCard (fun i : Index Ω D R J => pieces s ρ y i x) ≤ 2 ^ (D + 1) + 1 := by
  classical
  have hc (j : Fin (J + 1)) :
      (∑ c : Centers D R, if shell j.val (ρ x) * phi (s j) c (y x) ≠ 0 then 1 else 0 : ℕ) ≤
        if shell j.val (ρ x) ≠ 0 then 2 ^ D else 0 := by
    by_cases hj : shell j.val (ρ x) ≠ 0
    · have he :
          (∑ c : Centers D R, if shell j.val (ρ x) * phi (s j) c (y x) ≠ 0 then 1 else 0 : ℕ) =
          (activeCenters (R := R) (s j) (y x)).card := by
        rw [Finset.card_eq_sum_ones, activeCenters, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro c _
        by_cases hp : phi (s j) c (y x) = 0 <;> simp [hp, hj]
      rw [he]
      simpa only [ite_eq_left hj] using activeCenters_card_le (R := R) (hs j) (y x)
    · simp [hj]
  have hcount :
      (∑ j : Fin (J + 1), if shell j.val (ρ x) ≠ 0 then 2 ^ D else 0) =
        (activeShells J (tau (ρ x))).card * 2 ^ D := by
    calc
      _ = ∑ j ∈ activeShells J (tau (ρ x)), 2 ^ D := by
        simp only [activeShells, Finset.sum_filter, shell]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp_all
      _ = _ := by simp
  have hbox :
      (∑ j : Fin (J + 1), ∑ c : Centers D R,
        if shell j.val (ρ x) * phi (s j) c (y x) ≠ 0 then 1 else 0 : ℕ) ≤ 2 ^ (D + 1) := by
    calc
      _ ≤ ∑ j : Fin (J + 1), if shell j.val (ρ x) ≠ 0 then 2 ^ D else 0 :=
        Finset.sum_le_sum fun j _ => hc j
      _ = (activeShells J (tau (ρ x))).card * 2 ^ D := hcount
      _ ≤ 2 * 2 ^ D := Nat.mul_le_mul_right _ (activeShells_card_le J (tau_nonneg _))
      _ = _ := by rw [pow_succ]; omega
  have htail :
      (∑ z : Ω, if (if x = z then tail J (ρ x) else 0) ≠ 0 then 1 else 0 : ℕ) ≤ 1 := by
    by_cases ht : tail J (ρ x) = 0
    · simp [ht]
    · have he (z : Ω) :
          (if (if x = z then tail J (ρ x) else 0) ≠ 0 then 1 else 0 : ℕ) =
            if x = z then 1 else 0 := by
        by_cases hz : x = z
        · subst z
          simp [ht]
        · simp [hz]
      simp only [he]
      simp
  unfold activeCard
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  have he :
      (∑ j : Fin (J + 1), ∑ c : Centers D R,
        if pieces s ρ y (Sum.inl (j,c)) x ≠ 0 then 1 else 0 : ℕ) =
      ∑ j : Fin (J + 1), ∑ c : Centers D R,
        if shell j.val (ρ x) * phi (s j) c (y x) ≠ 0 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    by_cases hp : shell j.val (ρ x) * phi (s j) c (y x) = 0 <;> simp [pieces, hp]
  have ht : (∑ z : Ω, if pieces (R := R) s ρ y (Sum.inr z) x ≠ 0 then 1 else 0 : ℕ) =
      ∑ z : Ω, if (if x = z then tail J (ρ x) else 0) ≠ 0 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : x = z <;> simp [pieces, hz]
  rw [he, ht]
  exact Nat.add_le_add hbox htail

/-- The literal source square normalization. -/
def chi (s : Fin (J + 1) → ℕ) (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ) :
    Index Ω D R J → Ω → ℝ := partition (pieces s ρ y)

theorem chi_nonneg (s : Fin (J + 1) → ℕ) (ρ : Ω → ℝ)
    (y : Ω → Fin D → ℤ) (i : Index Ω D R J) (x : Ω) : 0 ≤ chi s ρ y i x :=
  partition_nonneg _ (pieces_nonneg s ρ y) i x

theorem sum_chi_sq (s : Fin (J + 1) → ℕ) (hs : ∀ j, 0 < s j)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ)
    (hy : ∀ x k, -(R : ℤ) ≤ y x k ∧ y x k ≤ R) (x : Ω) :
    (∑ i : Index Ω D R J, chi s ρ y i x ^ 2) = 1 :=
  partition_sq_sum _ (sum_pieces s hs ρ y hy) x

theorem denominator_bound (s : Fin (J + 1) → ℕ) (hs : ∀ j, 0 < s j)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ)
    (hy : ∀ x k, -(R : ℤ) ≤ y x k ∧ y x k ≤ R) (x : Ω) :
    1 ≤ ((2 ^ (D + 1) + 1 : ℕ) : ℝ) *
      length (fun i : Index Ω D R J => pieces s ρ y i x) ^ 2 :=
  overlap_denominator_bound _ (sum_pieces s hs ρ y hy x) (activeCard_pieces s hs ρ y x)

theorem chi_box_support (s : Fin (J + 1) → ℕ) (hs : ∀ j, 0 < s j)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ) (j : Fin (J + 1))
    (c : Centers D R) (x : Ω) (hx : chi s ρ y (Sum.inl (j,c)) x ≠ 0) :
    shell j.val (ρ x) ≠ 0 ∧ ∀ k, |y x k - (s j : ℤ) * (c k).val| ≤ (s j : ℤ) - 1 := by
  have hg : pieces s ρ y (Sum.inl (j,c)) x ≠ 0 := by
    intro hz
    exact hx (partition_eq_zero _ _ _ hz)
  have hh := mul_ne_zero_iff.mp hg
  exact ⟨hh.1, phi_support (hs j) c (y x) hh.2⟩

theorem chi_singleton_support (s : Fin (J + 1) → ℕ)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ) (z x : Ω)
    (hx : chi (R := R) s ρ y (Sum.inr z) x ≠ 0) :
    x = z ∧ tail J (ρ x) ≠ 0 := by
  classical
  have hg : pieces (R := R) s ρ y (Sum.inr z) x ≠ 0 := by
    intro hz
    exact hx (partition_eq_zero _ _ _ hz)
  by_cases h : x = z
  · exact ⟨h, by simpa only [pieces, ite_eq_left h] using hg⟩
  · simp only [pieces, ite_eq_right h, ne_eq, not_true_eq_false] at hg

theorem localizationCost_chi_le (s : Fin (J + 1) → ℕ) (hs : ∀ j, 0 < s j)
    (ρ : Ω → ℝ) (y : Ω → Fin D → ℤ)
    (hy : ∀ x k, -(R : ℤ) ≤ y x k ∧ y x k ≤ R)
    (r : Ω → Ω → ℝ) (hr : ∀ x z, 0 ≤ r x z) (x : Ω) :
    FiniteEntropyLocalization.localizationCost r (chi (R := R) s ρ y) x ≤
      4 * ((2 ^ (D + 1) + 1 : ℕ) : ℝ) *
        FiniteEntropyLocalization.localizationCost r (pieces (R := R) s ρ y) x :=
  localizationCost_partition_le _ r hr (sum_pieces s hs ρ y hy)
    (activeCard_pieces s hs ρ y) x

/-- A genuine finite bound covering all centered integer queries. Its size
does not occur in any analytic constant. -/
def queryBound (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) : ℕ :=
  ∑ x, ∑ i, (y x i - center i).natAbs

theorem queryBound_covers (center : Fin D → ℤ) (y : Ω → Fin D → ℤ)
    (x : Ω) (i : Fin D) :
    -(queryBound center y : ℤ) ≤ y x i - center i ∧
      y x i - center i ≤ queryBound center y := by
  have hi : (y x i - center i).natAbs ≤ queryBound center y :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((y x j - center j).natAbs))
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun z _ => Nat.zero_le (∑ j, (y z j - center j).natAbs))
        (Finset.mem_univ x))
  apply abs_le.mp
  rw [← Int.natCast_natAbs]
  exact_mod_cast hi

/-- The manuscript's actual scales, radius and finite family, without a
separate bounded-query or partition hypothesis. -/
def sourcePieces (N : ℕ) (ε : ℝ) (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) :
    Index Ω D (queryBound center y) (cutoff ε N) → Ω → ℝ :=
  pieces (fun j => scale N j.val) (fun x => radius N center (y x))
    (fun x i => y x i - center i)

def sourceChi (N : ℕ) (ε : ℝ) (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) :
    Index Ω D (queryBound center y) (cutoff ε N) → Ω → ℝ :=
  partition (sourcePieces N ε center y)

theorem sourcePieces_sum {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) (x : Ω) :
    (∑ i, sourcePieces N ε center y i x) = 1 :=
  sum_pieces _ (fun j => scale_pos hN j.val) _ _ (queryBound_covers center y) x

theorem sourcePieces_overlap {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) (x : Ω) :
    activeCard (fun i => sourcePieces N ε center y i x) ≤ 2 ^ (D + 1) + 1 :=
  activeCard_pieces _ (fun j => scale_pos hN j.val) _ _ x

theorem sourceChi_sq_sum {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) (x : Ω) :
    (∑ i, sourceChi N ε center y i x ^ 2) = 1 :=
  partition_sq_sum _ (sourcePieces_sum hN ε center y) x

theorem sourceChi_nonneg (N : ℕ) (ε : ℝ) (center : Fin D → ℤ)
    (y : Ω → Fin D → ℤ) (i : Index Ω D (queryBound center y) (cutoff ε N)) (x : Ω) :
    0 ≤ sourceChi N ε center y i x :=
  partition_nonneg _ (pieces_nonneg _ _ _) i x

/-- A uniform coordinate difference only pays for genuinely active indices. -/
theorem squaredDistance_le_overlap {ι : Type*} [Fintype ι] (u v : ι → ℝ)
    {M : ℕ} (hu : activeCard u ≤ M) (hv : activeCard v ≤ M)
    {B : ℝ} (hB : 0 ≤ B) (hchange : ∀ i, |u i - v i| ≤ B) :
    squaredDistance u v ≤ 2 * (M : ℝ) * B ^ 2 := by
  classical
  have count (w : ι → ℝ) :
      (∑ i, if w i ≠ 0 then B ^ 2 else 0) = (activeCard w : ℝ) * B ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), B ^ 2 := by
        rw [Finset.sum_filter]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, activeCard]
  have hi (i : ι) : (u i - v i) ^ 2 ≤
      (if u i ≠ 0 then B ^ 2 else 0) + (if v i ≠ 0 then B ^ 2 else 0) := by
    have hsq : (u i - v i) ^ 2 ≤ B ^ 2 := by
      nlinarith [sq_abs (u i - v i), abs_nonneg (u i - v i), hchange i]
    by_cases h₁ : u i = 0 <;> by_cases h₂ : v i = 0 <;>
      simp [h₁, h₂] at * <;> nlinarith [sq_nonneg B]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_add_distrib, count u, count v] at hh
  have hu' : (activeCard u : ℝ) ≤ M := by exact_mod_cast hu
  have hv' : (activeCard v : ℝ) ≤ M := by exact_mod_cast hv
  have hm := mul_le_mul_of_nonneg_right (add_le_add hu' hv') (sq_nonneg B)
  change (∑ i, (u i - v i) ^ 2) ≤ _
  nlinarith only [hh, hm]

/-- Product variation for two functions bounded between zero and one. -/
theorem unit_product_change {a b c d : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    _ = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
    _ ≤ _ := by nlinarith [abs_nonneg (a - c), abs_nonneg (b - d)]

/-- Every active box at either endpoint has a uniform source variation bound. -/
theorem box_piece_change {N j : ℕ} (hN : 1 ≤ N) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : |r - t| ≤ 1 / Real.sqrt N) (hrt1 : |r - t| ≤ 1)
    (c : Centers D R) (y z : Fin D → ℤ) (hyz : ∀ i, |y i - z i| ≤ 1) :
    |shell j r * phi (scale N j) c y - shell j t * phi (scale N j) c z| ≤
      (4 / Real.log 2 + 4 * D) * (1 + r) / Real.sqrt N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS := Real.sqrt_pos.mpr hNr
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsp := scale_pos (show 0 < N by omega) j
  have hb : 0 ≤ (4 / Real.log 2 + 4 * (D : ℝ)) * (1 + r) / Real.sqrt N := by positivity
  by_cases hs : shell j r = 0 ∧ shell j t = 0
  · simp only [hs.1, hs.2, zero_mul, sub_self, abs_zero]
    exact hb
  have ha : shell j r ≠ 0 ∨ shell j t ≠ 0 := by tauto
  have hscale := shell_scale_neighbor hr hrt1 ha
  have ht := phi_change hsp c y z hyz
  have hi := scale_inverse_bound (show 0 < N by omega) j
  have ht' : |phi (scale N j) c y - phi (scale N j) c z| ≤
      4 * (D : ℝ) * (1 + r) / Real.sqrt N := by
    have hh := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    have hh' := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    have hh'' := div_le_div_of_nonneg_right hh' hS.le
    calc
      _ ≤ (D : ℝ) / scale N j := ht
      _ ≤ (D : ℝ) * ((2 : ℝ) ^ j / Real.sqrt N) := by convert hh using 1; ring
      _ ≤ _ := by convert hh'' using 1 <;> ring
  have hs' : |shell j r - shell j t| ≤ (4 / Real.log 2) * (1 + r) / Real.sqrt N := by
    have hh := shell_change hr hrt1 j
    have hden : 0 < (1 + r) * Real.log 2 := mul_pos (by linarith) hlog
    have hfirst : 4 * |r - t| / ((1 + r) * Real.log 2) ≤
        4 * (1 / Real.sqrt N) / ((1 + r) * Real.log 2) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    have hsecond : 4 * (1 / Real.sqrt N) / ((1 + r) * Real.log 2) ≤
        (4 / Real.log 2) * (1 + r) / Real.sqrt N := by
      apply (div_le_div_iff₀ hden hS).mpr
      field_simp
      nlinarith [sq_nonneg r]
    exact hh.trans (hfirst.trans hsecond)
  have hh := unit_product_change (a := shell j r) (d := phi (scale N j) c z)
    (phi_bounds (scale N j) c y).1
    (phi_bounds (scale N j) c y).2 (shell_nonneg j t) (shell_le_one j t)
  exact hh.trans ((add_le_add hs' ht').trans_eq (by ring))


omit [Fintype Ω] in
/-- A singleton tail can change across a jump only in the far region. -/
theorem singleton_piece_change [DecidableEq Ω] {N : ℕ} {ε r t : ℝ}
    (hε : 0 < ε) (hlarge : 32 ≤ ε * Real.sqrt (N : ℝ))
    (hr : 0 ≤ r) (hrt : |r - t| ≤ 1) (x y z : Ω) :
    |(if x = z then tail (cutoff ε N) r else 0) -
      (if y = z then tail (cutoff ε N) t else 0)| ≤
      (32 / ε) * (1 + r) / Real.sqrt N := by
  classical
  have hS : 0 < Real.sqrt (N : ℝ) := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hb : 0 ≤ (32 / ε) * (1 + r) / Real.sqrt N := by positivity
  by_cases hs : tail (cutoff ε N) r = 0 ∧ tail (cutoff ε N) t = 0
  · simp only [hs.1, hs.2, ite_self, sub_self, abs_zero]
    exact hb
  have ha : tail (cutoff ε N) r ≠ 0 ∨ tail (cutoff ε N) t ≠ 0 := by tauto
  have hnear : ε * Real.sqrt (N : ℝ) / 32 ≤ r := by
    rcases ha with h | h
    · have ht := tail_cutoff_radius (by linarith : 8 ≤ ε * Real.sqrt (N : ℝ)) h
      linarith
    · have ht := tail_cutoff_radius (by linarith : 8 ≤ ε * Real.sqrt (N : ℝ)) h
      have he := (abs_le.mp hrt).1
      linarith
  have hone : 1 ≤ (32 / ε) * (1 + r) / Real.sqrt N := by
    apply (le_div_iff₀ hS).mpr
    have hh : ε * Real.sqrt (N : ℝ) ≤ 32 * (1 + r) := by linarith
    have hh' : Real.sqrt (N : ℝ) ≤ 32 * (1 + r) / ε :=
      (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hh)
    convert hh' using 1 <;> ring
  have hbounds (q : ℝ) (b : Prop) [Decidable b] :
      0 ≤ (if b then tail (cutoff ε N) q else 0) ∧
        (if b then tail (cutoff ε N) q else 0) ≤ 1 := by
    split_ifs
    · exact ⟨tail_nonneg _ _, tail_le_one _ _⟩
    · constructor <;> norm_num
  have hx := hbounds r (x = z)
  have hy := hbounds t (y = z)
  exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hone

/-- A fixed structural constant, independent of N, shell and state. -/
def variationConstant (D : ℕ) (ε : ℝ) : ℝ :=
  4 / Real.log 2 + 4 * D + 32 / ε

theorem variationConstant_nonneg (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ variationConstant D ε := by
  have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold variationConstant
  positivity

/-- The actual combined family has a pointwise jump estimate; the singleton
cost is paid by its proved radial support. -/
theorem sourcePieces_change {N : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 32 ≤ ε * Real.sqrt (N : ℝ))
    (center : Fin D → ℤ) (y : Ω → Fin D → ℤ)
    (x z : Ω) (hyz : ∀ k, |y x k - y z k| ≤ 1)
    (i : Index Ω D (queryBound center y) (cutoff ε N)) :
    |sourcePieces N ε center y i x - sourcePieces N ε center y i z| ≤
      variationConstant D ε * (1 + radius N center (y x)) / Real.sqrt N := by
  classical
  have hNp : 0 < N := by omega
  have hr := radius_nonneg N center (y x)
  have hrt := radius_neighbor_change hNp center (y x) (y z) hyz
  have hrt1 := radius_neighbor_small hNp center (y x) (y z) hyz
  have hf : 0 ≤ (1 + radius N center (y x)) / Real.sqrt N := by positivity
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rcases i with ⟨j,c⟩ | a
  · have hyz' (k : Fin D) : |(y x k - center k) - (y z k - center k)| ≤ 1 := by
      simpa only [sub_sub_sub_cancel_right] using hyz k
    have hh := box_piece_change (R := queryBound center y) (j := j.val) hN hr hrt hrt1 c
      (fun k => y x k - center k) (fun k => y z k - center k) hyz'
    change |shell j.val (radius N center (y x)) * phi (scale N j.val) c (fun k => y x k - center k) -
      shell j.val (radius N center (y z)) * phi (scale N j.val) c (fun k => y z k - center k)| ≤ _
    apply hh.trans
    have hc : 4 / Real.log 2 + 4 * (D : ℝ) ≤ variationConstant D ε := by
      unfold variationConstant
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) hε.le]
    convert mul_le_mul_of_nonneg_right hc hf using 1 <;> ring
  · change |(if x = a then tail (cutoff ε N) (radius N center (y x)) else 0) -
      (if z = a then tail (cutoff ε N) (radius N center (y z)) else 0)| ≤ _
    have hh := singleton_piece_change hε hlarge hr hrt1 x z a
    apply hh.trans
    have hc : 32 / ε ≤ variationConstant D ε := by
      unfold variationConstant
      have : 0 ≤ 4 / Real.log 2 + 4 * (D : ℝ) := by positivity
      linarith
    convert mul_le_mul_of_nonneg_right hc hf using 1 <;> ring

/-- Actual raw localization cost from coordinate jumps and original total rate. -/
theorem localizationCost_sourcePieces {N : ℕ} (hN : 1 ≤ N) {ε C₀ : ℝ}
    (hε : 0 < ε) (hlarge : 32 ≤ ε * Real.sqrt (N : ℝ))
    (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) (r : Ω → Ω → ℝ)
    (hr : ∀ x z, 0 ≤ r x z)
    (hjump : ∀ x z, r x z ≠ 0 → ∀ k, |y x k - y z k| ≤ 1)
    (x : Ω) (hrate : (∑ z, r x z) ≤ C₀ * N) :
    FiniteEntropyLocalization.localizationCost r (sourcePieces N ε center y) x ≤
      2 * ((2 ^ (D + 1) + 1 : ℕ) : ℝ) * variationConstant D ε ^ 2 *
        (1 + radius N center (y x)) ^ 2 * C₀ := by
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  let M : ℝ := ((2 ^ (D + 1) + 1 : ℕ) : ℝ)
  let B := variationConstant D ε * (1 + radius N center (y x)) / Real.sqrt N
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (variationConstant_nonneg D hε)
    (by linarith [radius_nonneg N center (y x)])) hS.le
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hrow (z : Ω) :
      r x z * (∑ i, (sourcePieces N ε center y i z - sourcePieces N ε center y i x)^2) ≤
        r x z * (2 * M * B^2) := by
    by_cases hz : r x z = 0
    · simp [hz]
    have hh := squaredDistance_le_overlap
      (fun i => sourcePieces N ε center y i z) (fun i => sourcePieces N ε center y i x)
      (sourcePieces_overlap hNp ε center y z) (sourcePieces_overlap hNp ε center y x) hB
      (fun i => by
        rw [abs_sub_comm]
        exact sourcePieces_change hN hε hlarge center y x z (hjump x z hz) i)
    exact mul_le_mul_of_nonneg_left hh (hr x z)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hrow z)
  rw [← Finset.sum_mul] at hsum
  have hr' := mul_le_mul_of_nonneg_right hrate
    (show 0 ≤ 2 * M * B^2 by positivity)
  have he : (C₀ * (N : ℝ)) * (2 * M * B^2) =
      2 * M * variationConstant D ε^2 * (1 + radius N center (y x))^2 * C₀ := by
    dsimp only [B]
    rw [div_pow, Real.sq_sqrt hNr.le]
    field_simp
  exact hsum.trans (hr'.trans_eq he)

/-- The source Gamma bound for the literal normalized finite family.
Only primitive jump and total-rate assumptions remain. -/
theorem localizationCost_sourceChi {N : ℕ} (hN : 1 ≤ N) {ε C₀ : ℝ}
    (hε : 0 < ε) (hlarge : 32 ≤ ε * Real.sqrt (N : ℝ)) (hC₀ : 0 ≤ C₀)
    (center : Fin D → ℤ) (y : Ω → Fin D → ℤ) (r : Ω → Ω → ℝ)
    (hr : ∀ x z, 0 ≤ r x z)
    (hjump : ∀ x z, r x z ≠ 0 → ∀ k, |y x k - y z k| ≤ 1)
    (x : Ω) (hrate : (∑ z, r x z) ≤ C₀ * N) :
    FiniteEntropyLocalization.localizationCost r (sourceChi N ε center y) x ≤
      (16 * ((2 ^ (D + 1) + 1 : ℕ) : ℝ)^2 * variationConstant D ε^2 * C₀) *
        (1 + radius N center (y x)^2) := by
  have hNp : 0 < N := by omega
  have hh := localizationCost_partition_le (sourcePieces N ε center y) r hr
    (sourcePieces_sum hNp ε center y) (sourcePieces_overlap hNp ε center y) x
  have hg := localizationCost_sourcePieces hN hε hlarge center y r hr hjump x hrate
  let M : ℝ := ((2 ^ (D + 1) + 1 : ℕ) : ℝ)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hsum := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4 * M by positivity)
  have hp : (1 + radius N center (y x))^2 ≤ 2 * (1 + radius N center (y x)^2) := by
    nlinarith [sq_nonneg (1 - radius N center (y x))]
  have hlast := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 8 * M^2 * variationConstant D ε^2 * C₀ by positivity)
  change FiniteEntropyLocalization.localizationCost r (partition (sourcePieces N ε center y)) x ≤ _
  nlinarith only [hh, hsum, hlast]


end PeriodicAttractiveLogGas.FiniteBoxPartition
