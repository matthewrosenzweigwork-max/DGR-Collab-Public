import DGRHS.Gaussian.PeriodicRieszL2Fourier

/-!
Packet P9a, unit 3: lattice sums over `ℤ^d` by dyadic shells.

* `encard_periodicFrequency_norm_le`: the number of lattice points of Euclidean
  norm `≤ R` is at most `(2R+1)^d`.
* `periodicFrequency_tail_sum_le`: for `2s < d`, `K ≥ 1`,
  `Σ_{‖k‖>K} ‖k‖^{2(s-d)} ≤ C K^{2s-d}`; this is the torus replacement of the
  tail integral `∫_{|ξ|>K} ĝ(ξ)² dξ ≲ K^{2s-d}` of eq. CtailFourier/BtailFourier
  (TeX 1377-1405).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma abs_periodicFrequency_le_norm (k : PeriodicFrequency ι) (j : ι) :
    |(k j : ℝ)| ≤ ‖periodicFrequencyVector k‖ := by
  have h := PiLp.norm_apply_le (periodicFrequencyVector k) j
  simpa [Real.norm_eq_abs] using h

lemma one_le_norm_periodicFrequencyVector {k : PeriodicFrequency ι} (hk : k ≠ 0) :
    1 ≤ ‖periodicFrequencyVector k‖ := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k j : ℝ)| := by
    have : (1 : ℤ) ≤ |k j| := Int.one_le_abs hj
    exact_mod_cast this
  exact h1.trans (abs_periodicFrequency_le_norm k j)

/-- Lattice point count in a Euclidean ball. -/
lemma encard_periodicFrequency_norm_le (R : ℝ) (hR : 0 ≤ R) :
    {k : PeriodicFrequency ι | ‖periodicFrequencyVector k‖ ≤ R}.encard ≤
      ENNReal.ofReal ((2 * R + 1) ^ (Fintype.card ι)) := by
  classical
  let F : Finset (PeriodicFrequency ι) :=
    Fintype.piFinset fun _ : ι => Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ)
  have hsub : {k : PeriodicFrequency ι | ‖periodicFrequencyVector k‖ ≤ R} ⊆ (F : Set _) := by
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    simp only [F, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have h1 : |(k j : ℝ)| ≤ R := (abs_periodicFrequency_le_norm k j).trans hk
    have h2 : |k j| ≤ (⌊R⌋₊ : ℤ) := by
      have h3 : |k j| ≤ ⌊R⌋ := Int.le_floor.mpr (by simpa using h1)
      rwa [← Int.natCast_floor_eq_floor hR] at h3
    exact abs_le.mp h2
  have hcard : F.card = (2 * ⌊R⌋₊ + 1) ^ Fintype.card ι := by
    simp only [F, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  have h1 : {k : PeriodicFrequency ι | ‖periodicFrequencyVector k‖ ≤ R}.encard ≤
      (F.card : ℕ∞) := by
    rw [← Set.encard_coe_eq_coe_finsetCard F]
    exact Set.encard_le_encard hsub
  have h2 : (((2 * ⌊R⌋₊ + 1) ^ Fintype.card ι : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 * R + 1) ^ Fintype.card ι) := by
    have hf : ((⌊R⌋₊ : ℝ)) ≤ R := Nat.floor_le hR
    have hreal : (((2 * ⌊R⌋₊ + 1) ^ Fintype.card ι : ℕ) : ℝ) ≤
        (2 * R + 1) ^ Fintype.card ι := by
      push_cast
      gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ((_ : ℕ∞) : ℝ≥0∞) ≤ ((F.card : ℕ∞) : ℝ≥0∞) := by exact_mod_cast h1
    _ = ((F.card : ℕ) : ℝ≥0∞) := by simp
    _ ≤ _ := by rw [hcard]; exact h2

/-- Dyadic-shell comparison of an indicator sum, in `ℝ≥0∞`. -/
lemma tsum_indicator_le_shells {α : Type*} (S : Set α) (f : α → ℝ≥0∞)
    (E : ℕ → Set α) (c : ℕ → ℝ≥0∞)
    (hcover : ∀ k ∈ S, ∃ j, k ∈ E j) (hle : ∀ j, ∀ k ∈ E j, f k ≤ c j) :
    ∑' k, S.indicator f k ≤ ∑' j, c j * (E j).encard := by
  classical
  have hpt : ∀ k, S.indicator f k ≤ ∑' j, (E j).indicator (fun _ => c j) k := by
    intro k
    by_cases hk : k ∈ S
    · obtain ⟨j, hj⟩ := hcover k hk
      rw [Set.indicator_of_mem hk]
      calc f k ≤ c j := hle j k hj
        _ = (E j).indicator (fun _ => c j) k := by rw [Set.indicator_of_mem hj]
        _ ≤ _ := ENNReal.le_tsum (f := fun j => (E j).indicator (fun _ => c j) k) j
    · rw [Set.indicator_of_notMem hk]
      simp
  calc
    ∑' k, S.indicator f k ≤ ∑' k, ∑' j, (E j).indicator (fun _ => c j) k :=
      ENNReal.tsum_le_tsum hpt
    _ = ∑' j, ∑' k, (E j).indicator (fun _ => c j) k := ENNReal.tsum_comm
    _ = ∑' j, c j * (E j).encard := by
      congr 1
      funext j
      rw [(tsum_subtype (E j) (fun _ => c j)).symm]
      rw [ENNReal.tsum_set_const, mul_comm]

lemma rpow_mul_pow_algebra (x r : ℝ) (m : ℕ) (hx : 0 < x) (a : ℝ) :
    x ^ r * (a * x) ^ m = a ^ m * x ^ (r + (m : ℝ)) := by
  rw [mul_pow, Real.rpow_add hx, Real.rpow_natCast]
  ring

lemma rpow_dyadic (K q : ℝ) (hK : 0 < K) (j : ℕ) :
    (K * 2 ^ j) ^ q = K ^ q * (2 ^ q) ^ j := by
  rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm q]

/-- Tail lattice sum: `Σ_{‖k‖>K} ‖k‖^{2(s-d)} ≤ C K^{2s-d}` for `K ≥ 1`, `2s < d`. -/
theorem periodicFrequency_tail_sum_le (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 1 ≤ K →
      ∑' k : PeriodicFrequency ι,
        (if K < ‖periodicFrequencyVector k‖ then
          ‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ))) else 0) ≤
        C * K ^ (2 * s - (Fintype.card ι : ℝ)) := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set r : ℝ := 2 * (s - (d : ℝ)) with hr
  set q : ℝ := 2 * s - (d : ℝ) with hq
  have hqneg : q < 0 := by rw [hq]; linarith
  have hrneg : r ≤ 0 := by rw [hr]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hq2 : (2 : ℝ) ^ q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hqneg
  have hq20 : 0 ≤ (2 : ℝ) ^ q := by positivity
  refine ⟨5 ^ d * (1 - (2 : ℝ) ^ q)⁻¹, by
    have : 0 < 1 - (2 : ℝ) ^ q := by linarith
    positivity, ?_⟩
  intro K hK
  have hK0 : 0 < K := by linarith
  have hsum : Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ r) :=
    summable_periodicFrequency_rpow r (by rw [hr]; have := hs2; linarith)
  set g : PeriodicFrequency ι → ℝ := fun k =>
    if K < ‖periodicFrequencyVector k‖ then ‖periodicFrequencyVector k‖ ^ r else 0 with hg
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k; simp only [hg]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hgle : ∀ k, g k ≤ ‖periodicFrequencyVector k‖ ^ r := by
    intro k; simp only [hg]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (norm_nonneg _) _
  have hgs : Summable g := Summable.of_nonneg_of_le hgnn hgle hsum
  show ∑' k, g k ≤ _
  set S : Set (PeriodicFrequency ι) := {k | K < ‖periodicFrequencyVector k‖} with hS
  set f : PeriodicFrequency ι → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (‖periodicFrequencyVector k‖ ^ r) with hf
  set E : ℕ → Set (PeriodicFrequency ι) := fun j =>
    {k | K * 2 ^ j < ‖periodicFrequencyVector k‖ ∧
      ‖periodicFrequencyVector k‖ ≤ K * 2 ^ (j + 1)} with hE
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((K * 2 ^ j) ^ r) with hc
  have hcover : ∀ k ∈ S, ∃ j, k ∈ E j := by
    intro k hk
    have hk' : K < ‖periodicFrequencyVector k‖ := hk
    have hex : ∃ n : ℕ, ‖periodicFrequencyVector k‖ ≤ K * 2 ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖periodicFrequencyVector k‖ / K)
        (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, by rw [div_lt_iff₀ hK0] at hn; linarith⟩
    classical
    let n := Nat.find hex
    have hn : ‖periodicFrequencyVector k‖ ≤ K * 2 ^ n := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      have : ‖periodicFrequencyVector k‖ ≤ K * 2 ^ n := hn
      rw [h0] at this
      simp at this
      linarith
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨j, ?_, ?_⟩
    · have hmin := Nat.find_min hex (show j < n by omega)
      push_neg at hmin
      exact hmin
    · rw [show j + 1 = n by omega]; exact hn
  have hle : ∀ j, ∀ k ∈ E j, f k ≤ c j := by
    intro j k hk
    have hpos : 0 < K * 2 ^ j := by positivity
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos hpos hk.1.le hrneg)
  have hmain := tsum_indicator_le_shells S f E c hcover hle
  have hcount : ∀ j, (E j).encard ≤ ENNReal.ofReal ((5 * (K * 2 ^ j)) ^ d) := by
    intro j
    have hsub : E j ⊆ {k | ‖periodicFrequencyVector k‖ ≤ K * 2 ^ (j + 1)} :=
      fun k hk => hk.2
    have hpos : 0 ≤ K * 2 ^ (j + 1) := by positivity
    refine le_trans (b := ((({k : PeriodicFrequency ι |
        ‖periodicFrequencyVector k‖ ≤ K * 2 ^ (j + 1)} : Set _).encard : ℕ∞) : ℝ≥0∞))
      (by exact_mod_cast Set.encard_le_encard hsub)
      ((encard_periodicFrequency_norm_le _ hpos).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ K * 2 ^ j := by
      calc (1 : ℝ) ≤ K := hK
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * 2 ^ j := by gcongr; exact one_le_pow₀ (by norm_num)
    have h2 : 2 * (K * 2 ^ (j + 1)) + 1 ≤ 5 * (K * 2 ^ j) := by
      rw [pow_succ]; nlinarith
    exact pow_le_pow_left₀ (by positivity) h2 d
  have hterm : ∀ j : ℕ, c j * (E j).encard ≤
      ENNReal.ofReal (5 ^ d * K ^ q * ((2 : ℝ) ^ q) ^ j) := by
    intro j
    have hpos : 0 < K * 2 ^ j := by positivity
    calc c j * (E j).encard ≤ ENNReal.ofReal ((K * 2 ^ j) ^ r) *
          ENNReal.ofReal ((5 * (K * 2 ^ j)) ^ d) := by
          rw [hc]; exact mul_le_mul' le_rfl (hcount j)
      _ = ENNReal.ofReal ((K * 2 ^ j) ^ r * (5 * (K * 2 ^ j)) ^ d) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)).symm
      _ = ENNReal.ofReal (5 ^ d * (K * 2 ^ j) ^ (r + (d : ℝ))) := by
          rw [rpow_mul_pow_algebra _ _ _ hpos]
      _ = ENNReal.ofReal (5 ^ d * K ^ q * ((2 : ℝ) ^ q) ^ j) := by
          have : r + (d : ℝ) = q := by rw [hr, hq]; ring
          rw [this, rpow_dyadic K q hK0 j]; ring_nf
  have hgeo : Summable (fun j : ℕ => 5 ^ d * K ^ q * ((2 : ℝ) ^ q) ^ j) :=
    (summable_geometric_of_lt_one hq20 hq2).mul_left _
  have hgeo_val : ∑' j : ℕ, 5 ^ d * K ^ q * ((2 : ℝ) ^ q) ^ j =
      5 ^ d * (1 - (2 : ℝ) ^ q)⁻¹ * K ^ q := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq20 hq2]; ring
  have hLHS : ENNReal.ofReal (∑' k, g k) = ∑' k, S.indicator f k := by
    rw [ENNReal.ofReal_tsum_of_nonneg hgnn hgs]
    congr 1
    funext k
    by_cases hk : K < ‖periodicFrequencyVector k‖
    · have : k ∈ S := hk
      rw [Set.indicator_of_mem this]; simp [hg, hk, hf]
    · have : k ∉ S := hk
      rw [Set.indicator_of_notMem this]; simp [hg, hk]
  have hnonneg : 0 ≤ 5 ^ d * (1 - (2 : ℝ) ^ q)⁻¹ * K ^ q := by
    have : 0 < 1 - (2 : ℝ) ^ q := by linarith
    positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hnonneg, hLHS]
  calc ∑' k, S.indicator f k ≤ ∑' j, c j * (E j).encard := hmain
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (5 ^ d * K ^ q * ((2 : ℝ) ^ q) ^ j) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, 5 ^ d * K ^ q * ((2 : ℝ) ^ q) ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeo).symm
    _ = _ := by rw [hgeo_val]

lemma rpow_geom (K b q : ℝ) (hK : 0 < K) (hb : 0 < b) (j : ℕ) :
    (K * b ^ j) ^ q = K ^ q * (b ^ q) ^ j := by
  rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hb.le, ← Real.rpow_mul hb.le, mul_comm q]

lemma finite_periodicFrequency_norm_le (R : ℝ) (hR : 0 ≤ R) :
    {k : PeriodicFrequency ι | ‖periodicFrequencyVector k‖ ≤ R}.Finite := by
  refine Set.encard_ne_top_iff.mp ?_
  intro h
  have := encard_periodicFrequency_norm_le (ι := ι) R hR
  rw [h] at this
  simp at this

/-- Low-mode lattice sum: `Σ_{0<‖k‖≤K} ‖k‖^{s-d} ≤ C K^s` for `0 < s < d`, `K ≥ 1`. -/
theorem periodicFrequency_low_sum_le (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 1 ≤ K →
      ∑' k : PeriodicFrequency ι,
        (if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
          ‖periodicFrequencyVector k‖ ^ (s - (Fintype.card ι : ℝ)) else 0) ≤
        C * K ^ s := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set p : ℝ := s - (d : ℝ) with hp
  have hpneg : p ≤ 0 := by rw [hp]; linarith
  set b : ℝ := (2 : ℝ)⁻¹ with hb
  have hb0 : 0 < b := by rw [hb]; norm_num
  have hb1 : b < 1 := by rw [hb]; norm_num
  have hρ1 : b ^ s < 1 := Real.rpow_lt_one hb0.le hb1 hs
  have hρ0 : 0 ≤ b ^ s := by positivity
  have h1ρ : 0 < 1 - b ^ s := by linarith
  refine ⟨6 ^ d * (b ^ s * (1 - b ^ s)⁻¹), by positivity, ?_⟩
  intro K hK
  have hK0 : 0 < K := by linarith
  set g : PeriodicFrequency ι → ℝ := fun k =>
    if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then ‖periodicFrequencyVector k‖ ^ p
    else 0 with hg
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k; simp only [hg]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hgs : Summable g := by
    apply summable_of_hasFiniteSupport
    refine (finite_periodicFrequency_norm_le K hK0.le).subset ?_
    intro k hk
    by_contra hcon
    apply hk
    simp only [hg, Set.mem_ofPred_eq] at hcon ⊢
    rw [ite_eq_right (fun h => hcon h.2)]
  show ∑' k, g k ≤ _
  set S : Set (PeriodicFrequency ι) := {k | k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K} with hS
  set f : PeriodicFrequency ι → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (‖periodicFrequencyVector k‖ ^ p) with hf
  set E : ℕ → Set (PeriodicFrequency ι) := fun j =>
    {k | k ≠ 0 ∧ K * b ^ (j + 1) < ‖periodicFrequencyVector k‖ ∧
      ‖periodicFrequencyVector k‖ ≤ K * b ^ j} with hE
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((K * b ^ (j + 1)) ^ p) with hc
  have hcover : ∀ k ∈ S, ∃ j, k ∈ E j := by
    intro k hk
    obtain ⟨hk0, hkK⟩ := hk
    have hk1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk0
    have hkpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
    have hex : ∃ n : ℕ, K * b ^ n < ‖periodicFrequencyVector k‖ := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K / ‖periodicFrequencyVector k‖)
        (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hkpos] at hn
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have : b ^ n = (2 ^ n)⁻¹ := by rw [hb, inv_pow]
      rw [this, ← div_eq_mul_inv, div_lt_iff₀ h2n]
      linarith
    let n := Nat.find hex
    have hn : K * b ^ n < ‖periodicFrequencyVector k‖ := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      have : K * b ^ n < ‖periodicFrequencyVector k‖ := hn
      rw [h0] at this
      simp at this
      linarith
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨j, hk0, ?_, ?_⟩
    · rw [show j + 1 = n by omega]; exact hn
    · have hmin := Nat.find_min hex (show j < n by omega)
      push_neg at hmin
      exact hmin
  have hle : ∀ j, ∀ k ∈ E j, f k ≤ c j := by
    intro j k hk
    have hpos : 0 < K * b ^ (j + 1) := by positivity
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos hpos hk.2.1.le hpneg)
  have hmain := tsum_indicator_le_shells S f E c hcover hle
  have hcount : ∀ j, (E j).encard ≤ ENNReal.ofReal ((6 * (K * b ^ (j + 1))) ^ d) := by
    intro j
    by_cases hne : (E j).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
    obtain ⟨k0, hk0⟩ := hne
    have hk01 : 1 ≤ ‖periodicFrequencyVector k0‖ :=
      one_le_norm_periodicFrequencyVector hk0.1
    have hup : 1 ≤ K * b ^ j := hk01.trans hk0.2.2
    have hsub : E j ⊆ {k | ‖periodicFrequencyVector k‖ ≤ K * b ^ j} :=
      fun k hk => hk.2.2
    have hpos : 0 ≤ K * b ^ j := by positivity
    refine le_trans (b := ((({k : PeriodicFrequency ι |
        ‖periodicFrequencyVector k‖ ≤ K * b ^ j} : Set _).encard : ℕ∞) : ℝ≥0∞))
      (by exact_mod_cast Set.encard_le_encard hsub)
      ((encard_periodicFrequency_norm_le _ hpos).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hbj : K * b ^ (j + 1) = (K * b ^ j) / 2 := by rw [pow_succ, hb]; ring
    have h2 : 2 * (K * b ^ j) + 1 ≤ 6 * (K * b ^ (j + 1)) := by
      rw [hbj]
      generalize K * b ^ j = X at hup ⊢
      linarith
    exact pow_le_pow_left₀ (by positivity) h2 d
  have hterm : ∀ j : ℕ, c j * (E j).encard ≤
      ENNReal.ofReal (6 ^ d * K ^ s * b ^ s * (b ^ s) ^ j) := by
    intro j
    have hpos : 0 < K * b ^ (j + 1) := by positivity
    calc c j * (E j).encard ≤ ENNReal.ofReal ((K * b ^ (j + 1)) ^ p) *
          ENNReal.ofReal ((6 * (K * b ^ (j + 1))) ^ d) := by
          rw [hc]; exact mul_le_mul' le_rfl (hcount j)
      _ = ENNReal.ofReal ((K * b ^ (j + 1)) ^ p * (6 * (K * b ^ (j + 1))) ^ d) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)).symm
      _ = ENNReal.ofReal (6 ^ d * (K * b ^ (j + 1)) ^ (p + (d : ℝ))) := by
          rw [rpow_mul_pow_algebra _ _ _ hpos]
      _ = ENNReal.ofReal (6 ^ d * K ^ s * b ^ s * (b ^ s) ^ j) := by
          have : p + (d : ℝ) = s := by rw [hp]; ring
          rw [this, rpow_geom K b s hK0 hb0 (j + 1), pow_succ]; ring_nf
  have hgeo : Summable (fun j : ℕ => 6 ^ d * K ^ s * b ^ s * (b ^ s) ^ j) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hgeo_val : ∑' j : ℕ, 6 ^ d * K ^ s * b ^ s * (b ^ s) ^ j =
      6 ^ d * (b ^ s * (1 - b ^ s)⁻¹) * K ^ s := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]; ring
  have hLHS : ENNReal.ofReal (∑' k, g k) = ∑' k, S.indicator f k := by
    rw [ENNReal.ofReal_tsum_of_nonneg hgnn hgs]
    congr 1
    funext k
    by_cases hk : k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K
    · have : k ∈ S := hk
      rw [Set.indicator_of_mem this]; simp [hg, hk, hf]
    · have : k ∉ S := hk
      rw [Set.indicator_of_notMem this]; simp [hg, hk]
  have hnonneg : 0 ≤ 6 ^ d * (b ^ s * (1 - b ^ s)⁻¹) * K ^ s := by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hnonneg, hLHS]
  calc ∑' k, S.indicator f k ≤ ∑' j, c j * (E j).encard := hmain
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (6 ^ d * K ^ s * b ^ s * (b ^ s) ^ j) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, 6 ^ d * K ^ s * b ^ s * (b ^ s) ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeo).symm
    _ = _ := by rw [hgeo_val]

end DGRHS.Periodic

#print axioms DGRHS.Periodic.encard_periodicFrequency_norm_le
#print axioms DGRHS.Periodic.tsum_indicator_le_shells
#print axioms DGRHS.Periodic.periodicFrequency_tail_sum_le
#print axioms DGRHS.Periodic.periodicFrequency_low_sum_le
