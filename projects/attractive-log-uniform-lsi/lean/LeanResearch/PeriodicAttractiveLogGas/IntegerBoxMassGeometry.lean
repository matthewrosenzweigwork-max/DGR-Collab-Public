import LeanResearch.PeriodicAttractiveLogGas.ProductTentPartition
import LeanResearch.PeriodicAttractiveLogGas.FiniteEntropyLocalization
import LeanResearch.PeriodicAttractiveLogGas.DyadicShellPartition

/-! Whole containing boxes and their actual masses in source2185–2239.
Shell activity is supplied through primitive coordinate-radius inequalities. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.IntegerBoxMassGeometry
open IntegerBoxLogWeights FiniteBoxLogSobolev ProductTentPartition

/-- Lower corner of the literal source containing box. -/
def lowerCorner {D : ℕ} (s : ℕ) (y₀ c : Fin D → ℤ) : Fin D → ℤ :=
  fun i => y₀ i + (s : ℤ) * c i - ((s : ℤ) - 1)

/-- Actual integer points, enumerated once by the released affine chart. -/
def containingBox {D : ℕ} (s : ℕ) (y₀ c : Fin D → ℤ) : Finset (Fin D → ℤ) := by
  classical
  exact Finset.univ.image (chart (n := 2 * s - 2) (lowerCorner s y₀ c))

theorem mem_containingBox_iff {D s : ℕ} (hs : 0 < s) (y₀ c y : Fin D → ℤ) :
    y ∈ containingBox s y₀ c ↔
      ∀ i, |y i - y₀ i - (s : ℤ) * c i| ≤ (s : ℤ) - 1 := by
  classical
  have hn : ((2 * s - 2 : ℕ) : ℤ) = 2 * (s : ℤ) - 2 := by omega
  have he : y ∈ integerBox (lowerCorner s y₀ c) (2 * s - 2) ↔
      ∀ i, |y i - y₀ i - (s : ℤ) * c i| ≤ (s : ℤ) - 1 := by
    constructor
    · intro h i
      have hi := h i
      change lowerCorner s y₀ c i ≤ y i ∧ y i ≤ lowerCorner s y₀ c i + (2 * s - 2 : ℕ) at hi
      dsimp only [lowerCorner] at hi
      rw [hn] at hi
      rw [abs_le]
      constructor <;> omega
    · intro h i
      have hi := abs_le.mp (h i)
      change lowerCorner s y₀ c i ≤ y i ∧ y i ≤ lowerCorner s y₀ c i + (2 * s - 2 : ℕ)
      dsimp only [lowerCorner]
      rw [hn]
      constructor <;> omega
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact he.mp (chart_mem _ x)
  · intro h
    let z : ↥(integerBox (lowerCorner s y₀ c) (2 * s - 2)) := ⟨y, he.mpr h⟩
    apply Finset.mem_image.mpr
    refine ⟨(chartEquiv _).symm z, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((chartEquiv _).apply_symm_apply z)

/-- The whole box has exactly (2s-1)^D integer points, even for s=1 or D=0. -/
theorem card_containingBox {D s : ℕ} (hs : 0 < s) (y₀ c : Fin D → ℤ) :
    (containingBox s y₀ c).card = (2 * s - 1) ^ D := by
  classical
  have hinj : Function.Injective (chart (n := 2 * s - 2) (lowerCorner s y₀ c)) := by
    intro x y h
    apply (chartEquiv (lowerCorner s y₀ c)).injective
    exact Subtype.ext h
  unfold containingBox
  rw [Finset.card_image_of_injOn hinj.injOn]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  congr 1
  omega

/-- Positive or merely nonzero literal tents have their actual containing box. -/
theorem tent_mem_containingBox {D s : ℕ} (hs : 0 < s) (y₀ c y : Fin D → ℤ)
    (h : productTent s c (fun i => y i - y₀ i) ≠ 0) : y ∈ containingBox s y₀ c :=
  (mem_containingBox_iff hs y₀ c y).mpr (productTent_support hs c _ h)

/-- Any two points in the whole containing box are at coordinate distance at most 2s. -/
theorem containingBox_distance {D s : ℕ} (hs : 0 < s) (y₀ c y z : Fin D → ℤ)
    (hy : y ∈ containingBox s y₀ c) (hz : z ∈ containingBox s y₀ c) :
    ∀ i, |z i - y i| ≤ 2 * (s : ℤ) := by
  intro i
  have hyi := (mem_containingBox_iff hs y₀ c y).mp hy i
  have hzi := (mem_containingBox_iff hs y₀ c z).mp hz i
  have hh := abs_sub_le (z i - y₀ i - (s : ℤ) * c i) 0
    (y i - y₀ i - (s : ℤ) * c i)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  have he : (z i - y₀ i - (s : ℤ) * c i) -
      (y i - y₀ i - (s : ℤ) * c i) = z i - y i := by ring
  rw [he] at hh
  omega

/-- Radius comparison uses an actual point of the box, not only its center. -/
theorem containingBox_radius {D s : ℕ} (hs : 0 < s) (y₀ c y z : Fin D → ℤ)
    (hy : y ∈ containingBox s y₀ c) (hz : z ∈ containingBox s y₀ c)
    {r : ℝ} (hr : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ r) :
    ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ r + 2 * s := by
  intro i
  have hd : |((z i - y i : ℤ) : ℝ)| ≤ 2 * (s : ℝ) := by
    exact_mod_cast containingBox_distance hs y₀ c y z hy hz i
  have hh := abs_add_le (((z i - y i : ℤ) : ℝ)) (((y i - y₀ i : ℤ) : ℝ))
  have he : ((z i - y i : ℤ) : ℝ) + ((y i - y₀ i : ℤ) : ℝ) = ((z i - y₀ i : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he] at hh
  linarith [hr i]

/-- Actual source central inclusion from the explicit scalar large-N gate. -/
theorem containingBox_central {D s N : ℕ} (hs : 0 < s) (y₀ c y : Fin D → ℤ)
    (hy : y ∈ containingBox s y₀ c) {u ε : ℝ}
    (hr : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ 2 * u * Real.sqrt N)
    (hscale : u * Real.sqrt N ≤ ε * N / 8)
    (hside : (s : ℝ) ≤ Real.sqrt N + 1)
    (hlarge : 2 * (Real.sqrt N + 1) ≤ 7 * ε * N / 4) :
    ∀ z ∈ containingBox s y₀ c, ∀ i,
      |((z i - y₀ i : ℤ) : ℝ)| ≤ 2 * ε * N := by
  intro z hz i
  have hh := containingBox_radius hs y₀ c y z hy hz hr i
  linarith

/-- The source local log-increment hypothesis, on the actual central cube.
The radius in the increment is the literal Pi sup norm. -/
def LogIncrementBound {D : ℕ} (y₀ : Fin D → ℤ) (T : ℝ) (N : ℕ)
    (C : ℝ) (w : (Fin D → ℤ) → ℝ) : Prop :=
  ∀ x, (∀ j, |((x j - y₀ j : ℤ) : ℝ)| ≤ T) → ∀ i : Fin D,
    (∀ j, |(((Function.update x i (x i + 1)) j - y₀ j : ℤ) : ℝ)| ≤ T) →
    |Real.log (w (Function.update x i (x i + 1))) - Real.log (w x)| ≤
      C * (1 / Real.sqrt N + ‖fun j => ((x j - y₀ j : ℤ) : ℝ)‖ / N)

private theorem chart_forward {D n : ℕ} (l : Fin D → ℤ) (x : Box D n)
    (i : Fin D) (hi : (x i).val < n) :
    chart l (Function.update x i ⟨(x i).val + 1, Nat.succ_lt_succ hi⟩) =
      Function.update (chart l x) i (chart l x i + 1) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp only [chart, Function.update_self, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [chart, Function.update_of_ne hj]

private theorem centered_chart_bound {D r : ℕ} (y₀ : Fin D → ℤ) (x : Box D (2 * r)) :
    ∀ i, |((chart (fun j => y₀ j - (r : ℤ)) x i - y₀ i : ℤ) : ℝ)| ≤ r := by
  intro i
  have hi := (x i).isLt
  have hh : |chart (fun j => y₀ j - (r : ℤ)) x i - y₀ i| ≤ (r : ℤ) := by
    dsimp only [chart]
    rw [abs_le]
    constructor <;> omega
  exact_mod_cast hh

/-- Integrating the actual local increments along constructed integer paths.
No log-weight oscillation is a hypothesis. -/
theorem central_log_difference {D r N : ℕ} (hN : 0 < N)
    (y₀ y : Fin D → ℤ) {T C : ℝ} (hC : 0 ≤ C) (hrT : (r : ℝ) ≤ T)
    (hy : ∀ i, |y i - y₀ i| ≤ (r : ℤ)) (w : (Fin D → ℤ) → ℝ)
    (hinc : LogIncrementBound y₀ T N C w) :
    |Real.log (w y) - Real.log (w y₀)| ≤
      (D : ℝ) * (2 * r) * (C * (1 / Real.sqrt N + (r : ℝ) / N)) := by
  classical
  let l : Fin D → ℤ := fun i => y₀ i - (r : ℤ)
  have hmem (z : Fin D → ℤ) (hz : ∀ i, |z i - y₀ i| ≤ (r : ℤ)) :
      z ∈ integerBox l (2 * r) := by
    intro i
    have hi := abs_le.mp (hz i)
    change y₀ i - (r : ℤ) ≤ z i ∧ z i ≤ y₀ i - (r : ℤ) + (2 * r : ℕ)
    constructor <;> omega
  let a := (chartEquiv l).symm ⟨y₀, hmem y₀ (by intro i; simp)⟩
  let b := (chartEquiv l).symm ⟨y, hmem y hy⟩
  have ha : chart l a = y₀ := congrArg Subtype.val ((chartEquiv l).apply_symm_apply _)
  have hb : chart l b = y := congrArg Subtype.val ((chartEquiv l).apply_symm_apply _)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf (x : Box D (2 * r)) (i : Fin D) (hi : (x i).val < 2 * r) :
      |Real.log (w (chart l (Function.update x i ⟨(x i).val + 1, Nat.succ_lt_succ hi⟩))) -
        Real.log (w (chart l x))| ≤ C * (1 / Real.sqrt N + (r : ℝ) / N) := by
    have hx := centered_chart_bound y₀ x
    have hz := centered_chart_bound y₀ (Function.update x i ⟨(x i).val + 1, Nat.succ_lt_succ hi⟩)
    have he := chart_forward l x i hi
    have hn : ‖fun j => ((chart l x j - y₀ j : ℤ) : ℝ)‖ ≤ (r : ℝ) := by
      apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg r)).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hx j
    have hh := hinc (chart l x) (fun j => (hx j).trans hrT) i
      (fun j => by rw [← he]; exact (hz j).trans hrT)
    rw [← he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (div_le_div_of_nonneg_right hn hNr.le)) hC)
  have hh := oscillation_of_forward_bound (fun x : Box D (2 * r) => Real.log (w (chart l x)))
    (show 0 ≤ C * (1 / Real.sqrt N + (r : ℝ) / N) by positivity) hf a b
  simpa only [ha, hb, Nat.cast_mul, Nat.cast_ofNat] using hh

/-- Real-radius version: flooring does not enlarge the central cube. -/
theorem central_log_difference_real {D N : ℕ} (hN : 0 < N)
    (y₀ y : Fin D → ℤ) {T C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hrT : r ≤ T)
    (hy : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ r) (w : (Fin D → ℤ) → ℝ)
    (hinc : LogIncrementBound y₀ T N C w) :
    |Real.log (w y) - Real.log (w y₀)| ≤
      (D : ℝ) * (2 * r) * (C * (1 / Real.sqrt N + r / N)) := by
  have hk : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr
  have hyk (i : Fin D) : |y i - y₀ i| ≤ (⌊r⌋₊ : ℤ) := by
    have habs := congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs (y i - y₀ i))
    simp only [Int.cast_natCast, Int.cast_abs] at habs
    have hh : ((y i - y₀ i).natAbs : ℝ) ≤ r := by rw [habs]; exact hy i
    have hn : (y i - y₀ i).natAbs ≤ ⌊r⌋₊ := (Nat.le_floor_iff hr).mpr hh
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  have hh := central_log_difference hN y₀ y hC (hk.trans hrT) hyk w hinc
  apply hh.trans
  gcongr

theorem radial_path_cost {D N : ℕ} (hN : 0 < N) {C r : ℝ} (hC : 0 ≤ C) :
    (D : ℝ) * (2 * r) * (C * (1 / Real.sqrt N + r / N)) ≤
      4 * D * C * (1 + r ^ 2 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hSq := Real.sq_sqrt hNr.le
  have he : r / Real.sqrt N = r * Real.sqrt N / N := by
    apply (div_eq_div_iff hS.ne' hNr.ne').mpr
    rw [mul_assoc, ← pow_two, hSq]
  have hl : r * Real.sqrt N ≤ (N : ℝ) + r ^ 2 := by
    nlinarith [sq_nonneg (r - Real.sqrt N)]
  have hb : r / Real.sqrt N ≤ 1 + r ^ 2 / N := by
    rw [he]
    apply (div_le_iff₀ hNr).mpr
    have he' : (1 + r ^ 2 / (N : ℝ)) * N = N + r ^ 2 := by field_simp
    rwa [he']
  have hdc : 0 ≤ 2 * (D : ℝ) * C := by positivity
  calc
    _ = (2 * (D : ℝ) * C) * (r / Real.sqrt N + r ^ 2 / N) := by ring
    _ ≤ (2 * (D : ℝ) * C) * ((1 + r ^ 2 / N) + r ^ 2 / N) :=
      mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) hdc
    _ ≤ 4 * D * C * (1 + r ^ 2 / N) := by nlinarith

/-- The source central point-mass bound is derived from the actual center mass
and local increments; no point-mass conclusion is assumed. -/
theorem central_point_mass_log {D N : ℕ} (hN : 0 < N)
    (y₀ y : Fin D → ℤ) {T C r c₀ : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hrT : r ≤ T) (hc₀ : 0 < c₀)
    (hy : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ r) (w : (Fin D → ℤ) → ℝ)
    (hcenter : c₀ * (N : ℝ) ^ (-(D : ℝ) / 2) ≤ w y₀)
    (hinc : LogIncrementBound y₀ T N C w) :
    -Real.log (w y) ≤ (D : ℝ) / 2 * Real.log N - Real.log c₀ +
      4 * D * C * (1 + r ^ 2 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := Real.rpow_pos_of_pos hNr (-(D : ℝ) / 2)
  have hw₀ : 0 < w y₀ := (mul_pos hc₀ hp).trans_le hcenter
  have hc := (Real.log_le_log_iff (mul_pos hc₀ hp) hw₀).mpr hcenter
  rw [Real.log_mul hc₀.ne' hp.ne', Real.log_rpow hNr] at hc
  have hd := (central_log_difference_real hN y₀ y hC hr hrT hy w hinc).trans
    (radial_path_cost hN hC)
  have hd' := abs_le.mp hd
  nlinarith

/-- Summing all the genuine lattice points produces the cardinality term.
This intermediate lemma is subsequently applied with derived point-mass bounds. -/
theorem box_mass_of_point_logs {D s : ℕ} (hs : 0 < s) (y₀ c : Fin D → ℤ)
    (w : (Fin D → ℤ) → ℝ) {A : ℝ}
    (hw : ∀ z ∈ containingBox s y₀ c, 0 < w z)
    (hlog : ∀ z ∈ containingBox s y₀ c, -Real.log (w z) ≤ A) :
    0 < ∑ z ∈ containingBox s y₀ c, w z ∧
      -Real.log (∑ z ∈ containingBox s y₀ c, w z) ≤
        A - (D : ℝ) * Real.log (2 * s - 1 : ℕ) := by
  have hp (z) (hz : z ∈ containingBox s y₀ c) : Real.exp (-A) ≤ w z := by
    have hh := Real.exp_le_exp.mpr (show -A ≤ Real.log (w z) by linarith [hlog z hz])
    rwa [Real.exp_log (hw z hz)] at hh
  have hsum := Finset.sum_le_sum hp
  have hcard := card_containingBox hs y₀ c
  have he : (∑ _z ∈ containingBox s y₀ c, Real.exp (-A)) =
      ((2 * s - 1 : ℕ) : ℝ) ^ D * Real.exp (-A) := by
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_pow]
  rw [he] at hsum
  have hm : (0 : ℝ) < (2 * s - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * s - 1 by omega)
  have hpos := mul_pos (pow_pos hm D) (Real.exp_pos (-A))
  have hmass := hpos.trans_le hsum
  refine ⟨hmass, ?_⟩
  have hh := (Real.log_le_log_iff hpos hmass).mpr hsum
  rw [Real.log_mul (pow_ne_zero _ hm.ne') (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp] at hh
  linarith

/-- Actual point masses and the full box cardinality give the normalization cost.
The displayed radius inequalities are primitive geometric bounds on the whole box. -/
theorem containingBox_mass_log {D s N : ℕ} (hs : 0 < s) (hN : 0 < N)
    (y₀ c : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ) {T C B c₀ : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : 0 ≤ B) (hc₀ : 0 < c₀)
    (hw : ∀ z ∈ containingBox s y₀ c, 0 < w z)
    (hcentral : ∀ z ∈ containingBox s y₀ c, ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ T)
    (hradius : ∀ z ∈ containingBox s y₀ c, ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ B)
    (hcenter : c₀ * (N : ℝ) ^ (-(D : ℝ) / 2) ≤ w y₀)
    (hinc : LogIncrementBound y₀ T N C w) :
    0 < ∑ z ∈ containingBox s y₀ c, w z ∧
      -Real.log (∑ z ∈ containingBox s y₀ c, w z) ≤
        (D : ℝ) / 2 * Real.log N - (D : ℝ) * Real.log (2 * s - 1 : ℕ) -
          Real.log c₀ + 4 * D * C * (1 + B ^ 2 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp (z) (hz : z ∈ containingBox s y₀ c) :
      -Real.log (w z) ≤ (D : ℝ) / 2 * Real.log N - Real.log c₀ +
        4 * D * C * (1 + B ^ 2 / N) := by
    let r := ‖fun i => ((z i - y₀ i : ℤ) : ℝ)‖
    have hr : 0 ≤ r := norm_nonneg _
    have hrT : r ≤ T := (pi_norm_le_iff_of_nonneg hT).mpr (by
      intro i; simpa only [Real.norm_eq_abs] using hcentral z hz i)
    have hrB : r ≤ B := (pi_norm_le_iff_of_nonneg hB).mpr (by
      intro i; simpa only [Real.norm_eq_abs] using hradius z hz i)
    have hcoords (i : Fin D) : |((z i - y₀ i : ℤ) : ℝ)| ≤ r := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j => ((z j - y₀ j : ℤ) : ℝ)) i
    have hh := central_point_mass_log hN y₀ z hC hr hrT hc₀ hcoords w hcenter hinc
    apply hh.trans
    gcongr
  have hh := box_mass_of_point_logs hs y₀ c w hw hp
  refine ⟨hh.1, ?_⟩
  nlinarith only [hh.2]

/-- The literal ceiling side gives the volume needed for logarithmic cancellation. -/
theorem ceiling_side_bounds {s N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : 1 ≤ u)
    (hs : s = ⌈Real.sqrt (N : ℝ) / u⌉₊) :
    0 < s ∧ (s : ℝ) ≤ Real.sqrt N + 1 ∧
      Real.sqrt N / u ≤ ((2 * s - 1 : ℕ) : ℝ) := by
  have hup : 0 < u := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsp : 0 < s := by rw [hs]; exact Nat.ceil_pos.mpr (div_pos hS hup)
  have hlow : Real.sqrt (N : ℝ) / u ≤ (s : ℝ) :=
    Nat.ceil_le.mp (show ⌈Real.sqrt (N : ℝ) / u⌉₊ ≤ s by rw [hs])
  have hhigh : (s : ℝ) < Real.sqrt (N : ℝ) / u + 1 := by
    rw [hs]
    exact Nat.ceil_lt_add_one (div_nonneg hS.le hup.le)
  have hdiv : Real.sqrt (N : ℝ) / u ≤ Real.sqrt N :=
    (div_le_iff₀ hup).mpr (by nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hu)])
  have hm : (s : ℝ) ≤ (2 * s - 1 : ℕ) := by exact_mod_cast (show s ≤ 2 * s - 1 by omega)
  exact ⟨hsp, by linarith, hlow.trans hm⟩

/-- Exact cancellation of the central N-power by the counted lattice side. -/
theorem log_size_cancellation {D N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {u : ℝ} (hu : 0 < u) (hside : Real.sqrt N / u ≤ (m : ℝ)) :
    (D : ℝ) / 2 * Real.log N - D * Real.log m ≤ D * Real.log u := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS := Real.sqrt_pos.mpr hNr
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hh := (Real.log_le_log_iff (div_pos hS hu) hmr).mpr hside
  rw [Real.log_div hS.ne' hu.ne', Real.log_sqrt hNr.le] at hh
  have hd := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg D)
  nlinarith only [hd]

/-- Box normalization after the genuine volume cancellation, before shell activity
converts log u and the whole-box radius into a uniform quadratic cost. -/
theorem ceiling_box_mass_log {D s N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : 1 ≤ u)
    (hs : s = ⌈Real.sqrt (N : ℝ) / u⌉₊)
    (y₀ c : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ) {T C B c₀ : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : 0 ≤ B) (hc₀ : 0 < c₀)
    (hw : ∀ z ∈ containingBox s y₀ c, 0 < w z)
    (hcentral : ∀ z ∈ containingBox s y₀ c, ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ T)
    (hradius : ∀ z ∈ containingBox s y₀ c, ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ B)
    (hcenter : c₀ * (N : ℝ) ^ (-(D : ℝ) / 2) ≤ w y₀)
    (hinc : LogIncrementBound y₀ T N C w) :
    0 < ∑ z ∈ containingBox s y₀ c, w z ∧
      -Real.log (∑ z ∈ containingBox s y₀ c, w z) ≤
        (D : ℝ) * Real.log u - Real.log c₀ + 4 * D * C * (1 + B ^ 2 / N) := by
  have hb := ceiling_side_bounds hN hu hs
  have hh := containingBox_mass_log hb.1 (by omega) y₀ c w hC hT hB hc₀
    hw hcentral hradius hcenter hinc
  have hc := log_size_cancellation (D := D) (by omega : 0 < N)
    (by omega : 0 < 2 * s - 1) (by linarith : 0 < u) hb.2.2
  refine ⟨hh.1, ?_⟩
  linarith only [hh.2, hc]

/-- The actual counted lower bound before taking logarithms. -/
theorem box_mass_lower_bound {D s : ℕ} (hs : 0 < s) (y₀ c : Fin D → ℤ)
    (w : (Fin D → ℤ) → ℝ) {A : ℝ}
    (hw : ∀ z ∈ containingBox s y₀ c, 0 < w z)
    (hlog : ∀ z ∈ containingBox s y₀ c, -Real.log (w z) ≤ A) :
    ((2 * s - 1 : ℕ) : ℝ) ^ D * Real.exp (-A) ≤ ∑ z ∈ containingBox s y₀ c, w z := by
  have hp (z) (hz : z ∈ containingBox s y₀ c) : Real.exp (-A) ≤ w z := by
    have hh := Real.exp_le_exp.mpr (show -A ≤ Real.log (w z) by linarith [hlog z hz])
    rwa [Real.exp_log (hw z hz)] at hh
  have hh := Finset.sum_le_sum hp
  simpa only [Finset.sum_const, nsmul_eq_mul, card_containingBox hs y₀ c, Nat.cast_pow] using hh

/-- Whole-box radius compared with the primitive active-point radius. -/
theorem active_box_radius {D s N : ℕ} (hs : 0 < s) (hN : 1 ≤ N)
    (y₀ c y : Fin D → ℤ) (hy : y ∈ containingBox s y₀ c) {ρ : ℝ}
    (hr : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ ρ * Real.sqrt N)
    (hside : (s : ℝ) ≤ Real.sqrt N + 1) :
    ∀ z ∈ containingBox s y₀ c, ∀ i,
      |((z i - y₀ i : ℤ) : ℝ)| ≤ (ρ + 4) * Real.sqrt N := by
  have hS : (1 : ℝ) ≤ Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  intro z hz i
  have hh := containingBox_radius hs y₀ c y z hy hz hr i
  nlinarith only [hh, hside, hS]

/-- Conversion of the genuine radius and shell-scale costs to a uniform quadratic cost. -/
theorem normalization_cost_arithmetic {D N : ℕ} (hN : 0 < N)
    {C c₀ ρ u : ℝ} (hC : 0 ≤ C) (hu : 0 < u)
    (hscale : u ≤ 2 * max ρ 1) :
    (D : ℝ) * Real.log u - Real.log c₀ +
        4 * D * C * (1 + ((ρ + 4) * Real.sqrt N) ^ 2 / N) ≤
      ((D : ℝ) * (Real.log 2 + 1) + |Real.log c₀| + 132 * D * C) * (1 + ρ ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : 0 < max ρ 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hl := (Real.log_le_log_iff hu (mul_pos (by norm_num) hm)).mpr hscale
  rw [Real.log_mul (by norm_num) hm.ne'] at hl
  have hlog : Real.log (max ρ 1) ≤ ρ ^ 2 := by
    by_cases h : ρ ≤ 1
    · rw [max_eq_right h, Real.log_one]
      exact sq_nonneg _
    · rw [max_eq_left (by linarith : 1 ≤ ρ)]
      have hh := Real.log_le_sub_one_of_pos (show 0 < ρ by linarith)
      nlinarith [sq_nonneg ρ]
  have he : ((ρ + 4) * Real.sqrt (N : ℝ)) ^ 2 / N = (ρ + 4) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hNr.le, mul_div_cancel_right₀ _ hNr.ne']
  rw [he]
  have hq : 1 + (ρ + 4) ^ 2 ≤ 33 * (1 + ρ ^ 2) := by nlinarith [sq_nonneg (ρ - 4)]
  have hc := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * (D : ℝ) * C by positivity)
  have hd := mul_le_mul_of_nonneg_left (show Real.log u ≤ Real.log 2 + ρ ^ 2 by linarith)
    (Nat.cast_nonneg D)
  have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hab := neg_le_abs (Real.log c₀)
  have hp := mul_nonneg (abs_nonneg (Real.log c₀)) (sq_nonneg ρ)
  have hp' := mul_nonneg (mul_nonneg (Nat.cast_nonneg D) hl2) (sq_nonneg ρ)
  nlinarith only [hc, hd, hab, hp, hp', (show (0 : ℝ) ≤ D from Nat.cast_nonneg D)]

/-- The complete active-box cost from primitive shell radius inequalities,
actual tent support, center mass and actual local log increments. -/
theorem active_box_normalization {D s N : ℕ} (hN : 1 ≤ N) {u ε ρ C c₀ : ℝ}
    (hu : 1 ≤ u) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hs : s = ⌈Real.sqrt (N : ℝ) / u⌉₊)
    (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (htent : productTent s c (fun i => y i - y₀ i) ≠ 0)
    (hr : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ ρ * Real.sqrt N)
    (hρu : ρ ≤ 2 * u) (huρ : u ≤ 2 * max ρ 1)
    (hscale : u * Real.sqrt N ≤ ε * N / 8)
    (hlarge : 2 * (Real.sqrt N + 1) ≤ 7 * ε * N / 4)
    (hw : ∀ z ∈ containingBox s y₀ c, 0 < w z)
    (hcenter : c₀ * (N : ℝ) ^ (-(D : ℝ) / 2) ≤ w y₀)
    (hinc : LogIncrementBound y₀ (2 * ε * N) N C w) :
    0 < ∑ z ∈ containingBox s y₀ c, w z ∧
      Real.log (∑ z ∈ containingBox s y₀ c, w z)⁻¹ ≤
        ((D : ℝ) * (Real.log 2 + 1) + |Real.log c₀| + 132 * D * C) * (1 + ρ ^ 2) := by
  have hb := ceiling_side_bounds hN hu hs
  have hy := tent_mem_containingBox hb.1 y₀ c y htent
  have hr' (i : Fin D) : |((y i - y₀ i : ℤ) : ℝ)| ≤ 2 * u * Real.sqrt N :=
    (hr i).trans (mul_le_mul_of_nonneg_right hρu (Real.sqrt_nonneg _))
  have hcentral := containingBox_central hb.1 y₀ c y hy hr' hscale hb.2.1 hlarge
  have hrad := active_box_radius hb.1 hN y₀ c y hy hr hb.2.1
  have hh := ceiling_box_mass_log hN hu hs y₀ c w hC (by positivity)
    (by positivity : 0 ≤ (ρ + 4) * Real.sqrt N) hc₀ hw hcentral hrad hcenter hinc
  refine ⟨hh.1, ?_⟩
  rw [Real.log_inv]
  exact hh.2.trans (normalization_cost_arithmetic (by omega) hC (by linarith) huρ)

/-- The source cutoff gate implies both scalar large-N conditions used above. -/
theorem source_scale_geometry {N j : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (hcut : 8 ≤ ε * Real.sqrt (N : ℝ)) (hj : j ≤ DyadicShellPartition.cutoff ε N) :
    (2 : ℝ) ^ j * Real.sqrt N ≤ ε * N / 8 ∧
      2 * (Real.sqrt N + 1) ≤ 7 * ε * N / 4 := by
  have hS : (1 : ℝ) ≤ Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  have hSq := Real.sq_sqrt (Nat.cast_nonneg N)
  have hp := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (show j + 3 ≤ DyadicShellPartition.cutoff ε N + 3 by omega)).trans
      (DyadicShellPartition.cutoff_bounds hcut).1
  rw [pow_add] at hp
  norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num] at hp
  have he : (ε * Real.sqrt (N : ℝ)) * Real.sqrt N = ε * N := by
    rw [mul_assoc, ← pow_two, hSq]
  have hh := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (N : ℝ))
  have hh' := mul_le_mul_of_nonneg_right hcut (Real.sqrt_nonneg (N : ℝ))
  rw [he] at hh hh'
  constructor <;> nlinarith only [hh, hh', hS]

/-- Actual source shell and actual physical radius instantiate every geometric
input to the box-mass cancellation. No final normalization estimate is assumed. -/
theorem source_box_normalization {D N j : ℕ} (hN : 1 ≤ N) {ε C c₀ : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hcut : 8 ≤ ε * Real.sqrt (N : ℝ)) (hj : j ≤ DyadicShellPartition.cutoff ε N)
    (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (hshell : DyadicShellPartition.shell j (DyadicShellPartition.radius N y₀ y) ≠ 0)
    (htent : productTent (DyadicShellPartition.scale N j) c (fun i => y i - y₀ i) ≠ 0)
    (hw : ∀ z ∈ containingBox (DyadicShellPartition.scale N j) y₀ c, 0 < w z)
    (hcenter : c₀ * (N : ℝ) ^ (-(D : ℝ) / 2) ≤ w y₀)
    (hinc : LogIncrementBound y₀ (2 * ε * N) N C w) :
    0 < ∑ z ∈ containingBox (DyadicShellPartition.scale N j) y₀ c, w z ∧
      Real.log (∑ z ∈ containingBox (DyadicShellPartition.scale N j) y₀ c, w z)⁻¹ ≤
        ((D : ℝ) * (Real.log 2 + 1) + |Real.log c₀| + 132 * D * C) *
          (1 + DyadicShellPartition.radius N y₀ y ^ 2) := by
  have hg := source_scale_geometry hN hcut hj
  have hr := (DyadicShellPartition.shell_radius_upper hshell).le
  rw [pow_succ] at hr
  have hu := (DyadicShellPartition.shell_scale_bound hshell).le
  exact active_box_normalization hN (one_le_pow₀ (by norm_num)) hε
    (DyadicShellPartition.radius_nonneg N y₀ y) hC hc₀ rfl y₀ c y w htent
    (DyadicShellPartition.coordinate_le_radius (by omega) y₀ y)
    (by nlinarith only [hr]) hu hg.1 hg.2 hw hcenter hinc

theorem chart_mem_containingBox {D s : ℕ} (y₀ c : Fin D → ℤ)
    (x : Box D (2 * s - 2)) : chart (lowerCorner s y₀ c) x ∈ containingBox s y₀ c := by
  classical
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- Each actual coordinate increment in the whole box inherits the source bound. -/
theorem box_forward_increment {D s N : ℕ} (y₀ c : Fin D → ℤ)
    (w : (Fin D → ℤ) → ℝ) {T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcentral : ∀ z ∈ containingBox s y₀ c, ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ T)
    (hradius : ∀ z ∈ containingBox s y₀ c, ∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ B)
    (hinc : LogIncrementBound y₀ T N C w)
    (x : Box D (2 * s - 2)) (i : Fin D) (hi : (x i).val < 2 * s - 2) :
    |Real.log (w (chart (lowerCorner s y₀ c)
        (Function.update x i ⟨(x i).val + 1, Nat.succ_lt_succ hi⟩))) -
      Real.log (w (chart (lowerCorner s y₀ c) x))| ≤ C * (1 / Real.sqrt N + B / N) := by
  let l := lowerCorner s y₀ c
  have hx := chart_mem_containingBox y₀ c x
  have hz := chart_mem_containingBox y₀ c
    (Function.update x i ⟨(x i).val + 1, Nat.succ_lt_succ hi⟩)
  have he := chart_forward l x i hi
  have hn : ‖fun j => ((chart l x j - y₀ j : ℤ) : ℝ)‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    simpa only [Real.norm_eq_abs] using hradius _ hx j
  have hh := hinc (chart l x) (hcentral _ hx) i
    (fun j => by rw [← he]; exact hcentral _ hz j)
  rw [← he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (div_le_div_of_nonneg_right hn (Nat.cast_nonneg N))) hC)

/-- Uniform oscillation from the primitive active-point radius and the source
local increments on actual chart edges. -/
theorem active_box_log_oscillation {D s N : ℕ} (hN : 1 ≤ N) {u ε C : ℝ}
    (hu : 1 ≤ u) (hC : 0 ≤ C) (hs : s = ⌈Real.sqrt (N : ℝ) / u⌉₊)
    (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (htent : productTent s c (fun i => y i - y₀ i) ≠ 0)
    (hr : ∀ i, |((y i - y₀ i : ℤ) : ℝ)| ≤ 2 * u * Real.sqrt N)
    (hscale : u * Real.sqrt N ≤ ε * N / 8)
    (hlarge : 2 * (Real.sqrt N + 1) ≤ 7 * ε * N / 4)
    (hinc : LogIncrementBound y₀ (2 * ε * N) N C w) :
    ∀ a ∈ containingBox s y₀ c, ∀ b ∈ containingBox s y₀ c,
      |Real.log (w b) - Real.log (w a)| ≤ 20 * D * C := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS := Real.sqrt_pos.mpr hNr
  have hb := ceiling_side_bounds hN hu hs
  have hy := tent_mem_containingBox hb.1 y₀ c y htent
  have hcentral := containingBox_central hb.1 y₀ c y hy hr hscale hb.2.1 hlarge
  have hrad := active_box_radius hb.1 hN y₀ c y hy hr hb.2.1
  have he : Real.sqrt (N : ℝ) / N = 1 / Real.sqrt N := by
    apply (div_eq_div_iff hNr.ne' hS.ne').mpr
    simpa only [one_mul, ← pow_two] using Real.sq_sqrt hNr.le
  have hraw : C * (1 / Real.sqrt N + ((2 * u + 4) * Real.sqrt N) / N) ≤
      (5 * C) * (1 + u) / Real.sqrt N := by
    rw [mul_div_assoc, he]
    have hid : C * (1 / Real.sqrt N + (2 * u + 4) * (1 / Real.sqrt N)) =
        C * (5 + 2 * u) / Real.sqrt N := by ring
    rw [hid]
    apply div_le_div_of_nonneg_right _ hS.le
    nlinarith [mul_nonneg hC (show 0 ≤ u by linarith)]
  have hL : 0 ≤ (5 * C) * (1 + u) / Real.sqrt N := by positivity
  have hf (x : Box D (2 * s - 2)) (i : Fin D) (hi : (x i).val < 2 * s - 2) :=
    (box_forward_increment y₀ c w hC
      (show 0 ≤ (2 * u + 4) * Real.sqrt N by positivity)
      hcentral hrad hinc x i hi).trans hraw
  have hn := (ceiling_box_bounds hN hu
    (show 2 * s - 2 = 2 * ⌈Real.sqrt (N : ℝ) / u⌉₊ - 2 by rw [hs])).2
      (5 * C) (by positivity)
  intro a ha b hb'
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb'
  have hh := oscillation_of_forward_bound
    (fun x : Box D (2 * s - 2) => Real.log (w (chart (lowerCorner s y₀ c) x))) hL hf a' b'
  have hd := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg D)
  nlinarith only [hh, hd]

/-- The actual source shell/cutoff instantiate the uniform box oscillation. -/
theorem source_box_log_oscillation {D N j : ℕ} (hN : 1 ≤ N) {ε C : ℝ}
    (hC : 0 ≤ C) (hcut : 8 ≤ ε * Real.sqrt (N : ℝ))
    (hj : j ≤ DyadicShellPartition.cutoff ε N)
    (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (hshell : DyadicShellPartition.shell j (DyadicShellPartition.radius N y₀ y) ≠ 0)
    (htent : productTent (DyadicShellPartition.scale N j) c (fun i => y i - y₀ i) ≠ 0)
    (hinc : LogIncrementBound y₀ (2 * ε * N) N C w) :
    ∀ a ∈ containingBox (DyadicShellPartition.scale N j) y₀ c,
      ∀ b ∈ containingBox (DyadicShellPartition.scale N j) y₀ c,
        |Real.log (w b) - Real.log (w a)| ≤ 20 * D * C := by
  have hg := source_scale_geometry hN hcut hj
  have hr := (DyadicShellPartition.shell_radius_upper hshell).le
  rw [pow_succ] at hr
  apply active_box_log_oscillation hN (one_le_pow₀ (by norm_num)) hC rfl y₀ c y w htent
    _ hg.1 hg.2 hinc
  intro i
  exact (DyadicShellPartition.coordinate_le_radius (by omega) y₀ y i).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [hr]) (Real.sqrt_nonneg _))

/-- Actual source whole-box central containment, exposed for outer-domain transport. -/
theorem source_box_central {D N j : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (hcut : 8 ≤ ε * Real.sqrt (N : ℝ)) (hj : j ≤ DyadicShellPartition.cutoff ε N)
    (y₀ c y : Fin D → ℤ)
    (hshell : DyadicShellPartition.shell j (DyadicShellPartition.radius N y₀ y) ≠ 0)
    (htent : productTent (DyadicShellPartition.scale N j) c (fun i => y i - y₀ i) ≠ 0) :
    ∀ z ∈ containingBox (DyadicShellPartition.scale N j) y₀ c, ∀ i,
      |((z i - y₀ i : ℤ) : ℝ)| ≤ 2 * ε * N := by
  have hg := source_scale_geometry hN hcut hj
  have hb := ceiling_side_bounds hN (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    (rfl : DyadicShellPartition.scale N j = ⌈Real.sqrt (N : ℝ) / (2 : ℝ) ^ j⌉₊)
  have hy := tent_mem_containingBox hb.1 y₀ c y htent
  have hr := (DyadicShellPartition.shell_radius_upper hshell).le
  rw [pow_succ] at hr
  apply containingBox_central hb.1 y₀ c y hy _ hg.1 hb.2.1 hg.2
  intro i
  exact (DyadicShellPartition.coordinate_le_radius (by omega) y₀ y i).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [hr]) (Real.sqrt_nonneg _))

/-- The same literal box viewed inside the actual finite outer domain. -/
def boxInOuter {D : ℕ} (Ω : Finset (Fin D → ℤ)) (s : ℕ) (y₀ c : Fin D → ℤ) :
    Finset ↥Ω := by
  classical
  exact Finset.univ.filter (fun z => z.val ∈ containingBox s y₀ c)

theorem boxInOuter_image {D s : ℕ} (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (hB : containingBox s y₀ c ⊆ Ω) :
    (boxInOuter Ω s y₀ c).image Subtype.val = containingBox s y₀ c := by
  classical
  ext z
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hx).2
  · intro hz
    exact Finset.mem_image.mpr ⟨⟨z, hB hz⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

/-- Exact identity with the existing unnormalized outer restriction mass. -/
theorem setMass_boxInOuter {D s : ℕ} (Ω : Finset (Fin D → ℤ)) (y₀ c : Fin D → ℤ)
    (w : (Fin D → ℤ) → ℝ) (hB : containingBox s y₀ c ⊆ Ω) :
    FiniteEntropyLocalization.setMass (fun z : ↥Ω => w z.val) (boxInOuter Ω s y₀ c) =
      ∑ z ∈ containingBox s y₀ c, w z := by
  classical
  have he : (Finset.univ.filter (fun z : ↥Ω => z ∈ boxInOuter Ω s y₀ c)) =
      boxInOuter Ω s y₀ c := by ext z; simp
  calc
    _ = ∑ z ∈ boxInOuter Ω s y₀ c, w z.val := by
      unfold FiniteEntropyLocalization.setMass FiniteEntropyLocalization.restrictedWeight
      calc
        _ = ∑ z : ↥Ω, if z ∈ boxInOuter Ω s y₀ c then w z.val else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z ∈ boxInOuter Ω s y₀ c
          · simp only [hz, ite_true]
          · simp only [hz, ite_false]
        _ = _ := by rw [← Finset.sum_filter, he]
    _ = ∑ z ∈ (boxInOuter Ω s y₀ c).image Subtype.val, w z := by
      rw [Finset.sum_image]
      intro a _ b _ h
      exact Subtype.ext h
    _ = _ := by rw [boxInOuter_image Ω y₀ c hB]

/-- The source cost for the actual outer subprobability restriction mass.
Central-cube inclusion, rather than an assumed box image or mass identity, is primitive. -/
theorem source_outer_box_normalization {D N j : ℕ} (hN : 1 ≤ N) {ε C c₀ : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hcut : 8 ≤ ε * Real.sqrt (N : ℝ)) (hj : j ≤ DyadicShellPartition.cutoff ε N)
    (Ω : Finset (Fin D → ℤ)) (y₀ c y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ)
    (hΩ : ∀ z, (∀ i, |((z i - y₀ i : ℤ) : ℝ)| ≤ 2 * ε * N) → z ∈ Ω)
    (hshell : DyadicShellPartition.shell j (DyadicShellPartition.radius N y₀ y) ≠ 0)
    (htent : productTent (DyadicShellPartition.scale N j) c (fun i => y i - y₀ i) ≠ 0)
    (hw : ∀ z ∈ Ω, 0 < w z)
    (hcenter : c₀ * (N : ℝ) ^ (-(D : ℝ) / 2) ≤ w y₀)
    (hinc : LogIncrementBound y₀ (2 * ε * N) N C w) :
    let M := FiniteEntropyLocalization.setMass (fun z : ↥Ω => w z.val)
      (boxInOuter Ω (DyadicShellPartition.scale N j) y₀ c)
    0 < M ∧ Real.log M⁻¹ ≤
      ((D : ℝ) * (Real.log 2 + 1) + |Real.log c₀| + 132 * D * C) *
        (1 + DyadicShellPartition.radius N y₀ y ^ 2) := by
  have hc := source_box_central hN hcut hj y₀ c y hshell htent
  have hB : containingBox (DyadicShellPartition.scale N j) y₀ c ⊆ Ω :=
    fun z hz => hΩ z (hc z hz)
  dsimp only
  rw [setMass_boxInOuter Ω y₀ c w hB]
  exact source_box_normalization hN hε hC hc₀ hcut hj y₀ c y w hshell htent
    (fun z hz => hw z (hB hz)) hcenter hinc

end PeriodicAttractiveLogGas.IntegerBoxMassGeometry
