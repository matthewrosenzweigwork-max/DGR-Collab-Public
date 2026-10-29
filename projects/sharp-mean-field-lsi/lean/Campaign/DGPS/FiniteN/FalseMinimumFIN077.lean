import DGPS.FiniteN.FalseMinimum
import DGPS.Analysis.OneDimensionalHardy

/-!
# FIN077: upper barrier bound for the Hardy resistance products at the false minimum

For `ψ = scalarPsi κ h` with `κ > 2`, `0 < h < h_c(κ)`, and the FIN076 critical points, the Hardy
products of `η_N ∝ e^{-Nψ}` anchored at the right minimum are bounded by `C e^{N B}`, uniformly in
the cut point and in `N ≥ 1`.  The proof abstracts the down-up-down-up shape of `ψ` with linear
growth outside a compact set (`ProfileFIN077`).
-/

open Filter Topology MeasureTheory Set

namespace DGPS.FiniteN.FalseMinimumFIN077

section Tails

variable {φ : ℝ → ℝ} {N d R : ℝ}

theorem intervalIntegral_exp_mul_FIN077 {b : ℝ} (hb : b ≠ 0) (u v : ℝ) :
    ∫ z in u..v, Real.exp (b * z) = (Real.exp (b * v) - Real.exp (b * u)) / b := by
  have hd : ∀ z ∈ Set.uIcc u v, HasDerivAt (fun z => Real.exp (b * z) / b) (Real.exp (b * z)) z := by
    intro z _
    have h1 : HasDerivAt (fun z : ℝ => b * z) b z := by
      simpa using (hasDerivAt_id z).const_mul b
    have h2 := (h1.exp).div_const b
    refine h2.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- Right tail of `e^{-Nφ}`. -/
theorem tail_right_FIN077 (hφc : Continuous φ)
    (hφ : ∀ u v, R ≤ v → v ≤ u → d * (u - v) ≤ φ u - φ v) (hN : 0 < N) (hd : 0 < d)
    {x : ℝ} (hx : R ≤ x) :
    IntegrableOn (fun y => Real.exp (-(N * φ y))) (Ioi x) ∧
      ∫ y in Ioi x, Real.exp (-(N * φ y)) ≤ Real.exp (-(N * φ x)) / (N * d) := by
  have hNd : 0 < N * d := mul_pos hN hd
  have ha : -(N * d) < 0 := by linarith
  set c : ℝ := Real.exp (-(N * φ x) + N * d * x) with hc
  have hb : ∀ y ∈ Ioi x, Real.exp (-(N * φ y)) ≤ c * Real.exp (-(N * d) * y) := by
    intro y hy
    have hxy : x ≤ y := le_of_lt hy
    have := hφ y x hx hxy
    rw [hc, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left this hN.le]
  have hint : IntegrableOn (fun y => c * Real.exp (-(N * d) * y)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi ha x).const_mul c
  have hf : IntegrableOn (fun y => Real.exp (-(N * φ y))) (Ioi x) := by
    refine Integrable.mono' hint ?_ ?_
    · exact (by fun_prop : Continuous fun y => Real.exp (-(N * φ y))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hb y hy
  refine ⟨hf, ?_⟩
  calc ∫ y in Ioi x, Real.exp (-(N * φ y))
      ≤ ∫ y in Ioi x, c * Real.exp (-(N * d) * y) :=
        setIntegral_mono_on hf hint measurableSet_Ioi hb
    _ = c * (-Real.exp (-(N * d) * x) / (-(N * d))) := by
        rw [integral_const_mul, integral_exp_mul_Ioi ha]
    _ = Real.exp (-(N * φ x)) / (N * d) := by
        rw [hc]
        have : Real.exp (-(N * φ x) + N * d * x) * Real.exp (-(N * d) * x) =
            Real.exp (-(N * φ x)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [neg_div_neg_eq, ← mul_div_assoc, this]

/-- Compact part of the right resistance. -/
theorem resist_right_FIN077 (hφc : Continuous φ)
    (hφ : ∀ u v, R ≤ v → v ≤ u → d * (u - v) ≤ φ u - φ v) (hN : 0 < N) (hd : 0 < d)
    {x : ℝ} (hx : R ≤ x) :
    ∫ z in R..x, Real.exp (N * φ z) ≤ Real.exp (N * φ x) / (N * d) := by
  have hNd : 0 < N * d := mul_pos hN hd
  set c : ℝ := Real.exp (N * φ x - N * d * x) with hc
  have hb : ∀ z ∈ Set.Icc R x, Real.exp (N * φ z) ≤ c * Real.exp ((N * d) * z) := by
    intro z hz
    have := hφ x z hz.1 hz.2
    rw [hc, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left this hN.le]
  calc ∫ z in R..x, Real.exp (N * φ z)
      ≤ ∫ z in R..x, c * Real.exp ((N * d) * z) :=
        intervalIntegral.integral_mono_on hx
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) hb
    _ = c * ((Real.exp ((N * d) * x) - Real.exp ((N * d) * R)) / (N * d)) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral_exp_mul_FIN077 hNd.ne']
    _ ≤ c * (Real.exp ((N * d) * x) / (N * d)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hNd.le)
          (Real.exp_pos _).le
        linarith [Real.exp_pos ((N * d) * R)]
    _ = Real.exp (N * φ x) / (N * d) := by
        rw [hc]
        have : Real.exp (N * φ x - N * d * x) * Real.exp ((N * d) * x) =
            Real.exp (N * φ x) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← mul_div_assoc, this]

/-- Left tail of `e^{-Nφ}`. -/
theorem tail_left_FIN077 (hφc : Continuous φ)
    (hφ : ∀ u v, u ≤ v → v ≤ -R → d * (v - u) ≤ φ u - φ v) (hN : 0 < N) (hd : 0 < d)
    {x : ℝ} (hx : x ≤ -R) :
    IntegrableOn (fun y => Real.exp (-(N * φ y))) (Iic x) ∧
      ∫ y in Iic x, Real.exp (-(N * φ y)) ≤ Real.exp (-(N * φ x)) / (N * d) := by
  have hNd : 0 < N * d := mul_pos hN hd
  set c : ℝ := Real.exp (-(N * φ x) - N * d * x) with hc
  have hb : ∀ y ∈ Iic x, Real.exp (-(N * φ y)) ≤ c * Real.exp ((N * d) * y) := by
    intro y hy
    have hxy : y ≤ x := hy
    have := hφ y x hxy hx
    rw [hc, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left this hN.le]
  have hint : IntegrableOn (fun y => c * Real.exp ((N * d) * y)) (Iic x) :=
    (integrableOn_exp_mul_Iic hNd x).const_mul c
  have hf : IntegrableOn (fun y => Real.exp (-(N * φ y))) (Iic x) := by
    refine Integrable.mono' hint ?_ ?_
    · exact (by fun_prop : Continuous fun y => Real.exp (-(N * φ y))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun y hy => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hb y hy
  refine ⟨hf, ?_⟩
  calc ∫ y in Iic x, Real.exp (-(N * φ y))
      ≤ ∫ y in Iic x, c * Real.exp ((N * d) * y) :=
        setIntegral_mono_on hf hint measurableSet_Iic hb
    _ = c * (Real.exp ((N * d) * x) / (N * d)) := by
        rw [integral_const_mul, integral_exp_mul_Iic hNd]
    _ = Real.exp (-(N * φ x)) / (N * d) := by
        rw [hc]
        have : Real.exp (-(N * φ x) - N * d * x) * Real.exp ((N * d) * x) =
            Real.exp (-(N * φ x)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← mul_div_assoc, this]

/-- Compact part of the left resistance. -/
theorem resist_left_FIN077 (hφc : Continuous φ)
    (hφ : ∀ u v, u ≤ v → v ≤ -R → d * (v - u) ≤ φ u - φ v) (hN : 0 < N) (hd : 0 < d)
    {x : ℝ} (hx : x ≤ -R) :
    ∫ z in x..-R, Real.exp (N * φ z) ≤ Real.exp (N * φ x) / (N * d) := by
  have hNd : 0 < N * d := mul_pos hN hd
  set c : ℝ := Real.exp (N * φ x + N * d * x) with hc
  have hb : ∀ z ∈ Set.Icc x (-R), Real.exp (N * φ z) ≤ c * Real.exp (-(N * d) * z) := by
    intro z hz
    have := hφ x z hz.1 hz.2
    rw [hc, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left this hN.le]
  calc ∫ z in x..-R, Real.exp (N * φ z)
      ≤ ∫ z in x..-R, c * Real.exp (-(N * d) * z) :=
        intervalIntegral.integral_mono_on hx
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) hb
    _ = c * ((Real.exp (-(N * d) * (-R)) - Real.exp (-(N * d) * x)) / (-(N * d))) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_exp_mul_FIN077 (by linarith : -(N * d) ≠ 0)]
    _ ≤ c * (Real.exp (-(N * d) * x) / (N * d)) := by
        have : (Real.exp (-(N * d) * (-R)) - Real.exp (-(N * d) * x)) / (-(N * d)) =
            (Real.exp (-(N * d) * x) - Real.exp (-(N * d) * (-R))) / (N * d) := by
          ring
        rw [this]
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hNd.le)
          (Real.exp_pos _).le
        linarith [Real.exp_pos (-(N * d) * (-R))]
    _ = Real.exp (N * φ x) / (N * d) := by
        rw [hc]
        have : Real.exp (N * φ x + N * d * x) * Real.exp (-(N * d) * x) =
            Real.exp (N * φ x) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← mul_div_assoc, this]

end Tails


section Profile

/-- The abstract shape of the auxiliary potential: a strict-free `down-up-down-up` profile with
critical values at `a < m < p`, and uniform linear growth outside the compact interval `[-R, R]`. -/
structure ProfileFIN077 (ψ : ℝ → ℝ) (a m p R d : ℝ) : Prop where
  cont : Continuous ψ
  anti_a : AntitoneOn ψ (Iic a)
  mono_am : MonotoneOn ψ (Icc a m)
  anti_mp : AntitoneOn ψ (Icc m p)
  mono_p : MonotoneOn ψ (Ici p)
  am : a ≤ m
  mp : m ≤ p
  Ra : -R ≤ a
  pR : p ≤ R
  d_pos : 0 < d
  gR : ∀ u v, R ≤ v → v ≤ u → d * (u - v) ≤ ψ u - ψ v
  gL : ∀ u v, u ≤ v → v ≤ -R → d * (v - u) ≤ ψ u - ψ v

variable {ψ : ℝ → ℝ} {a m p R d N : ℝ}

theorem ProfileFIN077.barrier_nonneg (P : ProfileFIN077 ψ a m p R d) : 0 ≤ ψ m - ψ a := by
  have := P.mono_am (Set.left_mem_Icc.2 P.am) (Set.right_mem_Icc.2 P.am) P.am
  linarith

/-- Every exponent `ψ(z) - ψ(y)` with `y ≤ z ≤ p` is at most the barrier. -/
theorem ProfileFIN077.key (P : ProfileFIN077 ψ a m p R d) {y z : ℝ} (hyz : y ≤ z) (hzp : z ≤ p) :
    ψ z - ψ y ≤ ψ m - ψ a := by
  have hB := P.barrier_nonneg
  by_cases hza : z ≤ a
  · have := P.anti_a (show y ∈ Iic a from le_trans hyz hza) (show z ∈ Iic a from hza) hyz
    linarith
  · have hza' : a ≤ z := (not_le.1 hza).le
    have hzm : ψ z ≤ ψ m := by
      by_cases hzm : z ≤ m
      · exact P.mono_am ⟨hza', hzm⟩ ⟨P.am, le_rfl⟩ hzm
      · exact P.anti_mp ⟨le_rfl, P.mp⟩ ⟨(not_le.1 hzm).le, hzp⟩ (not_le.1 hzm).le
    by_cases hym : y ≤ m
    · have hya : ψ a ≤ ψ y := by
        by_cases hya : y ≤ a
        · exact P.anti_a hya (show a ∈ Iic a from le_refl a) hya
        · exact P.mono_am ⟨le_rfl, P.am⟩ ⟨(not_le.1 hya).le, hym⟩ (not_le.1 hya).le
      linarith
    · have hym' : m ≤ y := (not_le.1 hym).le
      have := P.anti_mp ⟨hym', hyz.trans hzp⟩ ⟨hym'.trans hyz, hzp⟩ hyz
      linarith

theorem ProfileFIN077.right_mono (P : ProfileFIN077 ψ a m p R d) {z y : ℝ} (hz : p ≤ z)
    (hzy : z ≤ y) : ψ z ≤ ψ y :=
  P.mono_p hz (hz.trans hzy) hzy

theorem ProfileFIN077.integrableOn_Ioi (P : ProfileFIN077 ψ a m p R d) (hN : 0 < N) (x : ℝ) :
    IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Ioi x) := by
  have hcont : Continuous fun y => Real.exp (-(N * ψ y)) := by
    have := P.cont; fun_prop
  by_cases hx : R ≤ x
  · exact (tail_right_FIN077 P.cont P.gR hN P.d_pos hx).1
  · have hx' : x ≤ R := (not_le.1 hx).le
    have h1 := (tail_right_FIN077 P.cont P.gR hN P.d_pos (le_refl R)).1
    have h2 : IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Ioc x R) :=
      hcont.integrableOn_Ioc
    have := h2.union h1
    rwa [Ioc_union_Ioi_eq_Ioi hx'] at this

theorem ProfileFIN077.integrableOn_Iic (P : ProfileFIN077 ψ a m p R d) (hN : 0 < N) (x : ℝ) :
    IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Iic x) := by
  have hcont : Continuous fun y => Real.exp (-(N * ψ y)) := by
    have := P.cont; fun_prop
  by_cases hx : x ≤ -R
  · exact (tail_left_FIN077 P.cont P.gL hN P.d_pos hx).1
  · have hx' : -R ≤ x := (not_le.1 hx).le
    have h1 := (tail_left_FIN077 P.cont P.gL hN P.d_pos (le_refl (-R))).1
    have h2 : IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Ioc (-R) x) :=
      hcont.integrableOn_Ioc
    have := h1.union h2
    rwa [Iic_union_Ioc_eq_Iic hx'] at this

theorem ProfileFIN077.integrable (P : ProfileFIN077 ψ a m p R d) (hN : 0 < N) :
    Integrable (fun y => Real.exp (-(N * ψ y))) := by
  have h1 := P.integrableOn_Iic hN 0
  have h2 := P.integrableOn_Ioi hN 0
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- Resistance integral over `[x, p]` bounded using a point `y ≤ x`. -/
theorem ProfileFIN077.resist_left_bound (P : ProfileFIN077 ψ a m p R d) {x y : ℝ} (hyx : y ≤ x)
    (hxp : x ≤ p) (hN : 0 ≤ N) :
    ∫ z in x..p, Real.exp (N * ψ z) ≤ (p - x) * Real.exp (N * ψ y + N * (ψ m - ψ a)) := by
  have hcont : Continuous fun z => Real.exp (N * ψ z) := by
    have := P.cont; fun_prop
  calc ∫ z in x..p, Real.exp (N * ψ z)
      ≤ ∫ z in x..p, Real.exp (N * ψ y + N * (ψ m - ψ a)) := by
        refine intervalIntegral.integral_mono_on hxp (hcont.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) fun z hz => ?_
        rw [Real.exp_le_exp]
        have := P.key (hyx.trans hz.1) hz.2
        nlinarith [mul_le_mul_of_nonneg_left this hN]
    _ = (p - x) * Real.exp (N * ψ y + N * (ψ m - ψ a)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Resistance integral over `[p, x]` bounded using a point `y ≥ x`. -/
theorem ProfileFIN077.resist_right_bound (P : ProfileFIN077 ψ a m p R d) {x y : ℝ} (hpx : p ≤ x)
    (hxy : x ≤ y) (hN : 0 ≤ N) :
    ∫ z in p..x, Real.exp (N * ψ z) ≤ (x - p) * Real.exp (N * ψ y) := by
  have hcont : Continuous fun z => Real.exp (N * ψ z) := by
    have := P.cont; fun_prop
  calc ∫ z in p..x, Real.exp (N * ψ z)
      ≤ ∫ z in p..x, Real.exp (N * ψ y) := by
        refine intervalIntegral.integral_mono_on hpx (hcont.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) fun z hz => ?_
        rw [Real.exp_le_exp]
        have := P.right_mono hz.1 (hz.2.trans hxy)
        nlinarith [mul_le_mul_of_nonneg_left this hN]
    _ = (x - p) * Real.exp (N * ψ y) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]


theorem ProfileFIN077.R_nonneg (P : ProfileFIN077 ψ a m p R d) : 0 ≤ R := by
  linarith [P.Ra, P.am, P.mp, P.pR]

/-- The uniform constant. -/
noncomputable def constFIN077 (R d : ℝ) : ℝ := 1 / d ^ 2 + 2 * R / d + 4 * R ^ 2

theorem inv_sq_le_FIN077 {N d : ℝ} (hN : 1 ≤ N) (hd : 0 < d) :
    1 / (N * d * (N * d)) ≤ 1 / d ^ 2 := by
  have hN0 : 0 < N := by linarith
  refine one_div_le_one_div_of_le (by positivity) ?_
  have : 0 ≤ d ^ 2 * (N ^ 2 - 1) := mul_nonneg (sq_nonneg d) (by nlinarith)
  nlinarith

theorem inv_le_FIN077 {N d : ℝ} (hN : 1 ≤ N) (hd : 0 < d) : 1 / (N * d) ≤ 1 / d := by
  have hN0 : 0 < N := by linarith
  refine one_div_le_one_div_of_le hd ?_
  nlinarith

/-- Left Hardy product, cut point `x ≤ p`. -/
theorem ProfileFIN077.left_product_le (P : ProfileFIN077 ψ a m p R d) (hN : 1 ≤ N) {x : ℝ}
    (hx : x ≤ p) :
    (∫ y in Iic x, Real.exp (-(N * ψ y))) * (∫ z in x..p, Real.exp (N * ψ z)) ≤
      constFIN077 R d * Real.exp (N * (ψ m - ψ a)) := by
  have hN0 : 0 < N := by linarith
  have hd := P.d_pos
  have hB := P.barrier_nonneg
  have hR0 := P.R_nonneg
  have hE : 1 ≤ Real.exp (N * (ψ m - ψ a)) := Real.one_le_exp (by positivity)
  have hNd : 0 < N * d := mul_pos hN0 hd
  have hcont : Continuous fun z => Real.exp (N * ψ z) := by
    have := P.cont; fun_prop
  have hcont' : Continuous fun z => Real.exp (-(N * ψ z)) := by
    have := P.cont; fun_prop
  have hpR := P.pR
  have hRa := P.Ra
  have hmp := P.mp
  have ham := P.am
  have hfn : ∀ y, 0 ≤ Real.exp (-(N * ψ y)) := fun y => (Real.exp_pos _).le
  have hgn : ∀ y, 0 ≤ Real.exp (N * ψ y) := fun y => (Real.exp_pos _).le
  set eB := Real.exp (N * (ψ m - ψ a)) with heB
  have heB0 : 0 < eB := Real.exp_pos _
  have hC : 1 / d ^ 2 * eB + 2 * R / d * eB + 4 * R ^ 2 * eB = constFIN077 R d * eB := by
    unfold constFIN077; ring
  have hone : 1 / d ^ 2 ≤ 1 / d ^ 2 * eB := le_mul_of_one_le_right (by positivity) hE
  by_cases hxR : x ≤ -R
  · obtain ⟨-, hT⟩ := tail_left_FIN077 P.cont P.gL hN0 hd hxR
    have hR1 := resist_left_FIN077 P.cont P.gL hN0 hd hxR
    have hR2 := P.resist_left_bound (x := -R) (y := x) hxR (by linarith) hN0.le
    have hsplit : ∫ z in x..p, Real.exp (N * ψ z) = (∫ z in x..-R, Real.exp (N * ψ z)) +
        ∫ z in -R..p, Real.exp (N * ψ z) :=
      (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)).symm
    have hI1 : 0 ≤ ∫ z in x..-R, Real.exp (N * ψ z) :=
      intervalIntegral.integral_nonneg hxR (fun z _ => hgn z)
    have hI2 : 0 ≤ ∫ z in -R..p, Real.exp (N * ψ z) :=
      intervalIntegral.integral_nonneg (by linarith) (fun z _ => hgn z)
    have hu := Real.exp_pos (-(N * ψ x))
    have hv := Real.exp_pos (N * ψ x)
    have huv : Real.exp (-(N * ψ x)) * Real.exp (N * ψ x) = 1 := by
      rw [← Real.exp_add]; simp
    have e1 : (∫ y in Iic x, Real.exp (-(N * ψ y))) * (∫ z in x..-R, Real.exp (N * ψ z)) ≤
        1 / d ^ 2 := by
      calc _ ≤ (Real.exp (-(N * ψ x)) / (N * d)) * (Real.exp (N * ψ x) / (N * d)) :=
            mul_le_mul hT hR1 hI1 (by positivity)
        _ = 1 / (N * d * (N * d)) := by rw [div_mul_div_comm, huv]
        _ ≤ 1 / d ^ 2 := inv_sq_le_FIN077 hN hd
    have e2 : (∫ y in Iic x, Real.exp (-(N * ψ y))) * (∫ z in -R..p, Real.exp (N * ψ z)) ≤
        2 * R / d * eB := by
      calc _ ≤ (Real.exp (-(N * ψ x)) / (N * d)) *
              ((p - -R) * Real.exp (N * ψ x + N * (ψ m - ψ a))) :=
            mul_le_mul hT hR2 hI2 (by positivity)
        _ = (p - -R) * eB * (Real.exp (-(N * ψ x)) * Real.exp (N * ψ x)) / (N * d) := by
            rw [Real.exp_add]; ring
        _ = (p - -R) * eB / (N * d) := by rw [huv, mul_one]
        _ = (p - -R) * eB * (1 / (N * d)) := by ring
        _ ≤ (2 * R) * eB * (1 / d) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) heB0.le)
              (inv_le_FIN077 hN hd) (by positivity) (by positivity)
        _ = 2 * R / d * eB := by ring
    rw [hsplit, mul_add]
    nlinarith [mul_nonneg (sq_nonneg R) heB0.le]
  · have hxR' : -R ≤ x := (not_le.1 hxR).le
    obtain ⟨-, hT⟩ := tail_left_FIN077 P.cont P.gL hN0 hd (le_refl (-R))
    have hRz := fun y (hy : y ≤ x) => P.resist_left_bound (x := x) (y := y) hy hx hN0.le
    have hI : 0 ≤ ∫ z in x..p, Real.exp (N * ψ z) :=
      intervalIntegral.integral_nonneg hx (fun z _ => hgn z)
    have hint1 : IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Iic (-R)) :=
      (tail_left_FIN077 P.cont P.gL hN0 hd (le_refl (-R))).1
    have hint2 : IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Ioc (-R) x) :=
      hcont'.integrableOn_Ioc
    have hsplit : ∫ y in Iic x, Real.exp (-(N * ψ y)) = (∫ y in Iic (-R), Real.exp (-(N * ψ y))) +
        ∫ y in Ioc (-R) x, Real.exp (-(N * ψ y)) := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioc (le_refl (-R))) measurableSet_Ioc hint1 hint2,
        Iic_union_Ioc_eq_Iic hxR']
    have e1 : (∫ y in Iic (-R), Real.exp (-(N * ψ y))) * (∫ z in x..p, Real.exp (N * ψ z)) ≤
        2 * R / d * eB := by
      have hu := Real.exp_pos (-(N * ψ (-R)))
      have hv := Real.exp_pos (N * ψ (-R))
      have huv : Real.exp (-(N * ψ (-R))) * Real.exp (N * ψ (-R)) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ ≤ (Real.exp (-(N * ψ (-R))) / (N * d)) *
              ((p - x) * Real.exp (N * ψ (-R) + N * (ψ m - ψ a))) :=
            mul_le_mul hT (hRz (-R) hxR') hI (by positivity)
        _ = (p - x) * eB * (Real.exp (-(N * ψ (-R))) * Real.exp (N * ψ (-R))) / (N * d) := by
            rw [Real.exp_add]; ring
        _ = (p - x) * eB * (1 / (N * d)) := by rw [huv]; ring
        _ ≤ (2 * R) * eB * (1 / d) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) heB0.le)
              (inv_le_FIN077 hN hd) (by positivity) (by positivity)
        _ = 2 * R / d * eB := by ring
    have e2 : (∫ y in Ioc (-R) x, Real.exp (-(N * ψ y))) * (∫ z in x..p, Real.exp (N * ψ z)) ≤
        4 * R ^ 2 * eB := by
      rw [← intervalIntegral.integral_of_le hxR', ← intervalIntegral.integral_mul_const]
      calc ∫ y in -R..x, Real.exp (-(N * ψ y)) * ∫ z in x..p, Real.exp (N * ψ z)
          ≤ ∫ y in -R..x, (p - x) * eB := by
            refine intervalIntegral.integral_mono_on hxR'
              ((hcont'.mul continuous_const).intervalIntegrable _ _)
              (continuous_const.intervalIntegrable _ _) fun y hy => ?_
            calc Real.exp (-(N * ψ y)) * ∫ z in x..p, Real.exp (N * ψ z)
                ≤ Real.exp (-(N * ψ y)) * ((p - x) * Real.exp (N * ψ y + N * (ψ m - ψ a))) :=
                  mul_le_mul_of_nonneg_left (hRz y hy.2) (hfn y)
              _ = (p - x) * eB * (Real.exp (-(N * ψ y)) * Real.exp (N * ψ y)) := by
                  rw [Real.exp_add]; ring
              _ = (p - x) * eB := by
                  rw [← Real.exp_add]; simp
        _ = (x + R) * ((p - x) * eB) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ (2 * R) * ((2 * R) * eB) := by
            refine mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right (by linarith) heB0.le)
              (by nlinarith) (by positivity)
        _ = 4 * R ^ 2 * eB := by ring
    have h0 : 0 ≤ 1 / d ^ 2 * eB := by positivity
    rw [hsplit, add_mul]
    linarith [hC]

/-- Right Hardy product, cut point `x ≥ p`. -/
theorem ProfileFIN077.right_product_le (P : ProfileFIN077 ψ a m p R d) (hN : 1 ≤ N) {x : ℝ}
    (hx : p ≤ x) :
    (∫ y in Ioi x, Real.exp (-(N * ψ y))) * (∫ z in p..x, Real.exp (N * ψ z)) ≤
      constFIN077 R d * Real.exp (N * (ψ m - ψ a)) := by
  have hN0 : 0 < N := by linarith
  have hd := P.d_pos
  have hB := P.barrier_nonneg
  have hR0 := P.R_nonneg
  have hE : 1 ≤ Real.exp (N * (ψ m - ψ a)) := Real.one_le_exp (by positivity)
  have hNd : 0 < N * d := mul_pos hN0 hd
  have hcont : Continuous fun z => Real.exp (N * ψ z) := by
    have := P.cont; fun_prop
  have hcont' : Continuous fun z => Real.exp (-(N * ψ z)) := by
    have := P.cont; fun_prop
  have hpR := P.pR
  have hRa := P.Ra
  have hmp := P.mp
  have ham := P.am
  have hfn : ∀ y, 0 ≤ Real.exp (-(N * ψ y)) := fun y => (Real.exp_pos _).le
  have hgn : ∀ y, 0 ≤ Real.exp (N * ψ y) := fun y => (Real.exp_pos _).le
  set eB := Real.exp (N * (ψ m - ψ a)) with heB
  have heB0 : 0 < eB := Real.exp_pos _
  have hone : 1 / d ^ 2 ≤ 1 / d ^ 2 * eB := le_mul_of_one_le_right (by positivity) hE
  have hC : 1 / d ^ 2 * eB + 2 * R / d * eB + 4 * R ^ 2 * eB = constFIN077 R d * eB := by
    unfold constFIN077; ring
  by_cases hxR : R ≤ x
  · obtain ⟨-, hT⟩ := tail_right_FIN077 P.cont P.gR hN0 hd hxR
    have hR2 := resist_right_FIN077 P.cont P.gR hN0 hd hxR
    have hR1 := P.resist_right_bound (x := R) (y := x) hpR hxR hN0.le
    have hsplit : ∫ z in p..x, Real.exp (N * ψ z) = (∫ z in p..R, Real.exp (N * ψ z)) +
        ∫ z in R..x, Real.exp (N * ψ z) :=
      (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)).symm
    have hI1 : 0 ≤ ∫ z in p..R, Real.exp (N * ψ z) :=
      intervalIntegral.integral_nonneg hpR (fun z _ => hgn z)
    have hI2 : 0 ≤ ∫ z in R..x, Real.exp (N * ψ z) :=
      intervalIntegral.integral_nonneg hxR (fun z _ => hgn z)
    have hu := Real.exp_pos (-(N * ψ x))
    have hv := Real.exp_pos (N * ψ x)
    have huv : Real.exp (-(N * ψ x)) * Real.exp (N * ψ x) = 1 := by
      rw [← Real.exp_add]; simp
    have e1 : (∫ y in Ioi x, Real.exp (-(N * ψ y))) * (∫ z in p..R, Real.exp (N * ψ z)) ≤
        2 * R / d := by
      calc _ ≤ (Real.exp (-(N * ψ x)) / (N * d)) * ((R - p) * Real.exp (N * ψ x)) :=
            mul_le_mul hT hR1 hI1 (by positivity)
        _ = (R - p) * (Real.exp (-(N * ψ x)) * Real.exp (N * ψ x)) / (N * d) := by ring
        _ = (R - p) * (1 / (N * d)) := by rw [huv]; ring
        _ ≤ (2 * R) * (1 / d) :=
            mul_le_mul (by linarith) (inv_le_FIN077 hN hd) (by positivity) (by positivity)
        _ = 2 * R / d := by ring
    have e2 : (∫ y in Ioi x, Real.exp (-(N * ψ y))) * (∫ z in R..x, Real.exp (N * ψ z)) ≤
        1 / d ^ 2 := by
      calc _ ≤ (Real.exp (-(N * ψ x)) / (N * d)) * (Real.exp (N * ψ x) / (N * d)) :=
            mul_le_mul hT hR2 hI2 (by positivity)
        _ = 1 / (N * d * (N * d)) := by rw [div_mul_div_comm, huv]
        _ ≤ 1 / d ^ 2 := inv_sq_le_FIN077 hN hd
    have h2Rd : 2 * R / d ≤ 2 * R / d * eB := le_mul_of_one_le_right (by positivity) hE
    rw [hsplit, mul_add]
    nlinarith [mul_nonneg (sq_nonneg R) heB0.le]
  · have hxR' : x ≤ R := (not_le.1 hxR).le
    obtain ⟨-, hT⟩ := tail_right_FIN077 P.cont P.gR hN0 hd (le_refl R)
    have hRz := fun y (hy : x ≤ y) => P.resist_right_bound (x := x) (y := y) hx hy hN0.le
    have hI : 0 ≤ ∫ z in p..x, Real.exp (N * ψ z) :=
      intervalIntegral.integral_nonneg hx (fun z _ => hgn z)
    have hint1 : IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Ioi R) :=
      (tail_right_FIN077 P.cont P.gR hN0 hd (le_refl R)).1
    have hint2 : IntegrableOn (fun y => Real.exp (-(N * ψ y))) (Ioc x R) :=
      hcont'.integrableOn_Ioc
    have hsplit : ∫ y in Ioi x, Real.exp (-(N * ψ y)) = (∫ y in Ioc x R, Real.exp (-(N * ψ y))) +
        ∫ y in Ioi R, Real.exp (-(N * ψ y)) := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl R)) measurableSet_Ioi hint2 hint1,
        Ioc_union_Ioi_eq_Ioi hxR']
    have e1 : (∫ y in Ioi R, Real.exp (-(N * ψ y))) * (∫ z in p..x, Real.exp (N * ψ z)) ≤
        2 * R / d := by
      have hu := Real.exp_pos (-(N * ψ R))
      have hv := Real.exp_pos (N * ψ R)
      have huv : Real.exp (-(N * ψ R)) * Real.exp (N * ψ R) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ ≤ (Real.exp (-(N * ψ R)) / (N * d)) * ((x - p) * Real.exp (N * ψ R)) :=
            mul_le_mul hT (hRz R hxR') hI (by positivity)
        _ = (x - p) * (Real.exp (-(N * ψ R)) * Real.exp (N * ψ R)) / (N * d) := by ring
        _ = (x - p) * (1 / (N * d)) := by rw [huv]; ring
        _ ≤ (2 * R) * (1 / d) :=
            mul_le_mul (by linarith) (inv_le_FIN077 hN hd) (by positivity) (by positivity)
        _ = 2 * R / d := by ring
    have e2 : (∫ y in Ioc x R, Real.exp (-(N * ψ y))) * (∫ z in p..x, Real.exp (N * ψ z)) ≤
        4 * R ^ 2 := by
      rw [← intervalIntegral.integral_of_le hxR', ← intervalIntegral.integral_mul_const]
      calc ∫ y in x..R, Real.exp (-(N * ψ y)) * ∫ z in p..x, Real.exp (N * ψ z)
          ≤ ∫ y in x..R, (x - p) := by
            refine intervalIntegral.integral_mono_on hxR'
              ((hcont'.mul continuous_const).intervalIntegrable _ _)
              (continuous_const.intervalIntegrable _ _) fun y hy => ?_
            calc Real.exp (-(N * ψ y)) * ∫ z in p..x, Real.exp (N * ψ z)
                ≤ Real.exp (-(N * ψ y)) * ((x - p) * Real.exp (N * ψ y)) :=
                  mul_le_mul_of_nonneg_left (hRz y hy.1) (hfn y)
              _ = (x - p) * (Real.exp (-(N * ψ y)) * Real.exp (N * ψ y)) := by ring
              _ = (x - p) := by
                  rw [← Real.exp_add]; simp
        _ = (R - x) * (x - p) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ (2 * R) * (2 * R) :=
            mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
        _ = 4 * R ^ 2 := by ring
    have h2Rd : 2 * R / d ≤ 2 * R / d * eB := le_mul_of_one_le_right (by positivity) hE
    have h4 : 4 * R ^ 2 ≤ 4 * R ^ 2 * eB := le_mul_of_one_le_right (by positivity) hE
    rw [hsplit, add_mul]
    nlinarith [mul_nonneg (sq_nonneg R) heB0.le, mul_nonneg (div_nonneg (by positivity :
      (0:ℝ) ≤ 1) (sq_nonneg d)) heB0.le]


/-- Constructor of the profile from derivative sign information. -/
theorem ProfileFIN077.of_deriv {ψ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt ψ (ψ' t) t)
    (h1 : ∀ t, t < a → ψ' t ≤ 0) (h2 : ∀ t, a < t → t < m → 0 ≤ ψ' t)
    (h3 : ∀ t, m < t → t < p → ψ' t ≤ 0) (h4 : ∀ t, p < t → 0 ≤ ψ' t)
    (am : a ≤ m) (mp : m ≤ p) (Ra : -R ≤ a) (pR : p ≤ R) (dpos : 0 < d)
    (hR : ∀ t, R < t → d ≤ ψ' t) (hL : ∀ t, t < -R → ψ' t ≤ -d) :
    ProfileFIN077 ψ a m p R d := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hder : deriv ψ = ψ' := funext fun t => (hd t).deriv
  have hdiff : Differentiable ℝ ψ := fun t => (hd t).differentiableAt
  have hD : ∀ s : Set ℝ, DifferentiableOn ℝ ψ (interior s) := fun s => hdiff.differentiableOn
  refine ⟨hcont, ?_, ?_, ?_, ?_, am, mp, Ra, pR, dpos, ?_, ?_⟩
  · refine antitoneOn_of_deriv_nonpos (convex_Iic a) hcont.continuousOn (hD _) fun t ht => ?_
    rw [interior_Iic] at ht
    rw [hder]; exact h1 t ht
  · refine monotoneOn_of_deriv_nonneg (convex_Icc a m) hcont.continuousOn (hD _) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [hder]; exact h2 t ht.1 ht.2
  · refine antitoneOn_of_deriv_nonpos (convex_Icc m p) hcont.continuousOn (hD _) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [hder]; exact h3 t ht.1 ht.2
  · refine monotoneOn_of_deriv_nonneg (convex_Ici p) hcont.continuousOn (hD _) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [hder]; exact h4 t ht
  · intro u v hv hvu
    exact (convex_Ici R).mul_sub_le_image_sub_of_le_deriv hcont.continuousOn (hD _)
      (C := d) (fun t ht => by rw [interior_Ici] at ht; rw [hder]; exact hR t ht)
      v (Set.mem_Ici.2 hv) u (Set.mem_Ici.2 (hv.trans hvu)) hvu
  · intro u v huv hv
    have := (convex_Iic (-R)).image_sub_le_mul_sub_of_deriv_le hcont.continuousOn (hD _)
      (C := -d) (fun t ht => by rw [interior_Iic] at ht; rw [hder]; exact hL t ht)
      u (Set.mem_Iic.2 (huv.trans hv)) v (Set.mem_Iic.2 hv) huv
    linarith

end Profile

section Concrete

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity
open DGPS.Circle.BesselMonotonicity DGPS.FiniteN.ScalarFoldFIN056 DGPS.FiniteN.FalseMinimumFIN076

/-- The scalar auxiliary potential has the abstract profile at the three FIN076 critical points. -/
theorem profile_of_geometry_FIN077 {κ h s1 s2 tp : ℝ} (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) (hs1 : s1 < scalarFoldPoint κ)
    (hs2 : scalarFoldPoint κ < s2) (hs10 : 0 < s1) (htp : 0 < tp)
    (G : FalseMinimumGeometryFIN076 κ h s1 s2 tp) :
    ∃ R d : ℝ, ProfileFIN077 (scalarPsi κ h) (-s2) (-s1) tp R d := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨hs, hsd'⟩ := scalarFoldPoint_spec κ hκ
  have hsd : ratioDeriv (scalarFoldPoint κ) = 1 / κ := by rw [deriv_ratio] at hsd'; exact hsd'
  have hhc' : h < κ * besselRatio (scalarFoldPoint κ) - scalarFoldPoint κ := hhc
  obtain ⟨a, m, p, has, hm1, hm2, hps, hfa, hfm, hfp, S1, S2, S3, S4⟩ :=
    three_roots_FIN076 hκ0 hs hsd hh0 hhc'
  have hder : deriv (scalarPsi κ h) = psiDerivFIN056 κ h := deriv_scalarPsi_FIN056 hκ0 h
  have hcrit := G.2.2.2.1
  have mem : ∀ t, psiDerivFIN056 κ h t = 0 → t = -s2 ∨ t = -s1 ∨ t = tp := by
    intro t ht
    exact (hcrit t).1 (by rw [hder]; exact ht)
  have o1 : -s2 < -s1 := by linarith
  have o2 : -s1 < tp := by linarith
  have hid : a = -s2 ∧ m = -s1 ∧ p = tp := by
    have ha := mem a hfa
    have hm := mem m hfm
    have hp := mem p hfp
    have o3 : a < m := by linarith
    have o4 : m < p := by linarith
    rcases ha with ha | ha | ha <;> rcases hm with hm | hm | hm <;>
      rcases hp with hp | hp | hp <;>
      first | exact ⟨ha, hm, hp⟩ | (exfalso; linarith)
  obtain ⟨rfl, rfl, rfl⟩ := hid
  set sS := scalarFoldPoint κ with hsS
  have hR1 : 0 < psiDerivFIN056 κ h (max p s2 + 1) :=
    S4 _ (by linarith [le_max_left p s2])
  have hR2 : psiDerivFIN056 κ h (-(max p s2 + 1)) < 0 :=
    S1 _ (by linarith [le_max_right p s2])
  refine ⟨max p s2 + 1, min (psiDerivFIN056 κ h (max p s2 + 1))
    (-psiDerivFIN056 κ h (-(max p s2 + 1))), ?_⟩
  refine ProfileFIN077.of_deriv (fun t => hasDerivAt_scalarPsi_FIN056 hκ0 h t)
    (fun t ht => (S1 t ht).le) (fun t h1 h2 => (S2 t h1 h2).le) (fun t h1 h2 => (S3 t h1 h2).le)
    (fun t ht => (S4 t ht).le) (by linarith) (by linarith)
    (by linarith [le_max_right p s2]) (by linarith [le_max_left p s2])
    (lt_min hR1 (by linarith)) ?_ ?_
  · intro t ht
    have hmono := (psiDeriv_strictMonoOn_FIN056 (κ := κ) (h := h) hs hsd).monotoneOn
    have hge : psiDerivFIN056 κ h (max p s2 + 1) ≤ psiDerivFIN056 κ h t :=
      hmono (show max p s2 + 1 ∈ Set.Ici sS from
        Set.mem_Ici.2 (by linarith [le_max_right p s2]))
        (show t ∈ Set.Ici sS from Set.mem_Ici.2 (by linarith [le_max_right p s2])) ht.le
    exact (min_le_left _ _).trans hge
  · intro t ht
    have hmono := (psiDeriv_strictMonoOn_left_FIN076 (κ := κ) (h := h) hs hsd).monotoneOn
    have hle : psiDerivFIN056 κ h t ≤ psiDerivFIN056 κ h (-(max p s2 + 1)) :=
      hmono (show t ∈ Set.Iic (-sS) from Set.mem_Iic.2 (by linarith [le_max_right p s2]))
        (show -(max p s2 + 1) ∈ Set.Iic (-sS) from
          Set.mem_Iic.2 (by linarith [le_max_right p s2])) ht.le
    have := min_le_right (psiDerivFIN056 κ h (max p s2 + 1))
      (-psiDerivFIN056 κ h (-(max p s2 + 1)))
    linarith

end Concrete

section Bridge

variable {ψ : ℝ → ℝ} {a m p R d N : ℝ}

/-- The normalized auxiliary density `e^{-Nψ} / ∫ e^{-Nψ}` (the density of `η_N`). -/
noncomputable def auxDensityFIN077 (ψ : ℝ → ℝ) (N : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(N * ψ t)) / ∫ y, Real.exp (-(N * ψ y))

theorem ProfileFIN077.Z_pos (P : ProfileFIN077 ψ a m p R d) (hN : 0 < N) :
    0 < ∫ y, Real.exp (-(N * ψ y)) :=
  integral_exp_pos (f := fun y => -(N * ψ y)) (P.integrable hN)

theorem ProfileFIN077.measure_toReal (P : ProfileFIN077 ψ a m p R d) (hN : 0 < N) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) s).toReal =
      (∫ y in s, Real.exp (-(N * ψ y))) / ∫ y, Real.exp (-(N * ψ y)) := by
  have hZ := P.Z_pos hN
  rw [DGPS.FiniteN.densityMeasure_apply hs (Set.subset_univ _)]
  have hcont : Continuous fun y => Real.exp (-(N * ψ y)) := by
    have := P.cont; fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict s] fun x => auxDensityFIN077 ψ N x :=
    Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le
  have hm : AEStronglyMeasurable (auxDensityFIN077 ψ N) (volume.restrict s) := by
    unfold auxDensityFIN077
    exact (hcont.div_const _).aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnn hm]
  unfold auxDensityFIN077
  rw [integral_div]

theorem inv_integral_FIN077 (ψ : ℝ → ℝ) (N u v : ℝ) :
    ∫ t in u..v, (auxDensityFIN077 ψ N t)⁻¹ =
      (∫ y, Real.exp (-(N * ψ y))) * ∫ t in u..v, Real.exp (N * ψ t) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [auxDensityFIN077]
  rw [inv_div, Real.exp_neg, div_inv_eq_mul]

theorem ProfileFIN077.right_resistance_le (P : ProfileFIN077 ψ a m p R d) (hN : 1 ≤ N) {x : ℝ}
    (hx : p ≤ x) :
    (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) (Set.Ici x)).toReal *
        ∫ t in p..x, (auxDensityFIN077 ψ N t)⁻¹ ≤
      constFIN077 R d * Real.exp (N * (ψ m - ψ a)) := by
  have hN0 : 0 < N := by linarith
  have hZ := P.Z_pos hN0
  rw [P.measure_toReal hN0 measurableSet_Ici, inv_integral_FIN077 ψ N,
    ← setIntegral_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := x))]
  have := P.right_product_le hN hx
  calc _ = (∫ y in Ioi x, Real.exp (-(N * ψ y))) * ∫ z in p..x, Real.exp (N * ψ z) := by
        field_simp
    _ ≤ _ := this

theorem ProfileFIN077.left_resistance_le (P : ProfileFIN077 ψ a m p R d) (hN : 1 ≤ N) {x : ℝ}
    (hx : x ≤ p) :
    (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) (Set.Iic x)).toReal *
        ∫ t in x..p, (auxDensityFIN077 ψ N t)⁻¹ ≤
      constFIN077 R d * Real.exp (N * (ψ m - ψ a)) := by
  have hN0 : 0 < N := by linarith
  have hZ := P.Z_pos hN0
  rw [P.measure_toReal hN0 measurableSet_Iic, inv_integral_FIN077 ψ N]
  have := P.left_product_le hN hx
  calc _ = (∫ y in Iic x, Real.exp (-(N * ψ y))) * ∫ z in x..p, Real.exp (N * ψ z) := by
        field_simp
    _ ≤ _ := this

/-- The two FIN006 resistance constants of the normalized density, anchored at `p`, are at most
`C e^{NB}` (all the suprema are over nonempty sets bounded above). -/
theorem ProfileFIN077.resistance_constants_le (P : ProfileFIN077 ψ a m p R d) (hN : 1 ≤ N) :
    BddAbove ((fun x => (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)
        (Set.Ici x)).toReal * ∫ t in p..x, (auxDensityFIN077 ψ N t)⁻¹) ''
      (Set.univ ∩ Set.Ioi p)) ∧
    BddAbove ((fun x => (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)
        (Set.Iic x)).toReal * ∫ t in x..p, (auxDensityFIN077 ψ N t)⁻¹) ''
      (Set.univ ∩ Set.Iio p)) ∧
    DGPS.FiniteN.rightResistanceConstant Set.univ (auxDensityFIN077 ψ N) p ≤
      constFIN077 R d * Real.exp (N * (ψ m - ψ a)) ∧
    DGPS.FiniteN.leftResistanceConstant Set.univ (auxDensityFIN077 ψ N) p ≤
      constFIN077 R d * Real.exp (N * (ψ m - ψ a)) := by
  refine ⟨⟨constFIN077 R d * Real.exp (N * (ψ m - ψ a)), ?_⟩,
    ⟨constFIN077 R d * Real.exp (N * (ψ m - ψ a)), ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact P.right_resistance_le hN (le_of_lt hx)
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact P.left_resistance_le hN (le_of_lt hx)
  · refine csSup_le ⟨_, p + 1, ⟨Set.mem_univ _, by simp⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact P.right_resistance_le hN (le_of_lt hx)
  · refine csSup_le ⟨_, p - 1, ⟨Set.mem_univ _, by simp⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact P.left_resistance_le hN (le_of_lt hx)

end Bridge

theorem constFIN077_pos {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) : 0 < constFIN077 R d := by
  unfold constFIN077
  positivity

end DGPS.FiniteN.FalseMinimumFIN077

namespace DGPS.FiniteN

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN056 DGPS.FiniteN.FalseMinimumFIN076
  DGPS.FiniteN.FalseMinimumFIN077

/-- **FIN077.** For `κ > 2`, `0 < h < h_c(κ)`, with `ψ = scalarPsi κ h` and FIN076 critical points
`t₋ = -s₂`, `t_b = -s₁`, `t₊ = tp`, the Hardy products of `η_N ∝ e^{-Nψ}` anchored at `t₊` satisfy,
uniformly in the cut point `x` and in the real `N ≥ 1`,
`(∫_{-∞}^x e^{-Nψ})(∫_x^{t₊} e^{Nψ}) ≤ C e^{N B}` (for `x ≤ t₊`) and
`(∫_x^∞ e^{-Nψ})(∫_{t₊}^x e^{Nψ}) ≤ C e^{N B}` (for `x ≥ t₊`), with `B = ψ(t_b) - ψ(t₋)`.
The normalizing constant of `η_N` cancels from the products; `e^{-Nψ}` is integrable. -/
theorem false_minimum_resistance_product_barrier_upper (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
      FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
        MeasureTheory.Integrable (fun t => Real.exp (-(N * scalarPsi κ h t))) ∧
        (∀ x : ℝ, x ≤ tp →
          (∫ y in Set.Iic x, Real.exp (-(N * scalarPsi κ h y))) *
              (∫ z in x..tp, Real.exp (N * scalarPsi κ h z)) ≤
            C * Real.exp (N * (scalarPsi κ h (-s1) - scalarPsi κ h (-s2)))) ∧
        (∀ x : ℝ, tp ≤ x →
          (∫ y in Set.Ioi x, Real.exp (-(N * scalarPsi κ h y))) *
              (∫ z in tp..x, Real.exp (N * scalarPsi κ h z)) ≤
            C * Real.exp (N * (scalarPsi κ h (-s1) - scalarPsi κ h (-s2)))) := by
  obtain ⟨s1, s2, tp, h1, h2, h3, h4, G⟩ := general_FIN076 κ h hκ hh0 hhc
  obtain ⟨R, d, P⟩ := profile_of_geometry_FIN077 hκ hh0 hhc h2 h3 h1 h4 G
  refine ⟨s1, s2, tp, h1, h2, h3, h4, G, constFIN077 R d,
    constFIN077_pos P.R_nonneg P.d_pos, fun N hN => ⟨P.integrable (by linarith),
      fun x hx => P.left_product_le hN hx, fun x hx => P.right_product_le hN hx⟩⟩

end DGPS.FiniteN
