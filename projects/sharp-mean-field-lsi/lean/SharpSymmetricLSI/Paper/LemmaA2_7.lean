import SharpSymmetricLSI.Paper.LemmaA2_6

/-!
# R25 (A.9), part 7: the doubling-variables maximum principle

Let `U` be `C²` and periodic on `ℝ^ι` with `U - τΔU + τ B·∇U = F + E`, where `F` is
`L`-Lipschitz for the Euclidean distance `dE`, `|E| ≤ η`, and `B` is `K`-semimonotone:
`(B(x) - B(y))·(x - y) ≥ -K|x - y|²`. If `L ≤ M(1 - Kτ)`, `M > 0`, then
`U(x) - U(y) ≤ M|x - y| + 2η` (`doubling_bound`).

At a maximum `(x, y)` of `U(x) - U(y) - M|x - y|` (attained by periodicity), `x ≠ y`, the first
order conditions give `∇U(x) = ∇U(y) = M(x - y)/|x - y|`, and the second derivative test along
`t ↦ (x + t e_k, y + t e_k)` gives `ΔU(x) ≤ ΔU(y)` (`second_deriv_nonpos`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

/-- The Euclidean distance on `ℝ^ι`. -/
noncomputable def dE {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ := Real.sqrt (∑ i, (x i - y i) ^ 2)

section dE

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem dE_nonneg (x y : ι → ℝ) : 0 ≤ dE x y := Real.sqrt_nonneg _

theorem dE_sq (x y : ι → ℝ) : dE x y ^ 2 = ∑ i, (x i - y i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem dE_self (x : ι → ℝ) : dE x x = 0 := by simp [dE]

theorem dE_pos {x y : ι → ℝ} (h : x ≠ y) : 0 < dE x y := by
  refine Real.sqrt_pos.mpr ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact lt_of_lt_of_le (by positivity : 0 < (x i - y i) ^ 2) (Finset.single_le_sum
    (f := fun j => (x j - y j) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

theorem abs_sub_le_dE (x y : ι → ℝ) (i : ι) : |x i - y i| ≤ dE x y :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

theorem dE_add_add (x y m : ι → ℝ) : dE (x + m) (y + m) = dE x y := by
  simp only [dE, Pi.add_apply, add_sub_add_right_eq_sub]

theorem dE_sub_sub (x y m : ι → ℝ) : dE (x - m) (y - m) = dE x y := by
  simp only [dE, Pi.sub_apply, sub_sub_sub_cancel_right]

theorem hasDerivAt_sqrt_sum_line (c a : ι → ℝ) (hc : ∑ i, c i ^ 2 ≠ 0) :
    HasDerivAt (fun t => Real.sqrt (∑ i, (c i + t * a i) ^ 2))
      ((∑ i, c i * a i) / Real.sqrt (∑ i, c i ^ 2)) 0 := by
  have hs : HasDerivAt (fun t => ∑ i, (c i + t * a i) ^ 2) (∑ i, 2 * c i * a i) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i t => (c i + t * a i) ^ 2)
      (A' := fun i => 2 * c i * a i) (x := 0) fun i _ => by
        have h1 : HasDerivAt (fun t => c i + t * a i) (a i) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a i)).const_add (c i)
        have h2 := h1.mul h1
        convert h2 using 1
        · funext t; simp only [Pi.mul_apply]; ring
        · simp; ring
    simpa using this
  have h := hs.sqrt (by simpa using hc)
  convert h using 1
  simp only [zero_mul, add_zero]
  have e : ∑ i, 2 * c i * a i = 2 * ∑ i, c i * a i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, mul_div_mul_left _ _ two_ne_zero]

theorem dE_line_left (x y v : ι → ℝ) (t : ℝ) :
    dE (x + t • v) y = Real.sqrt (∑ i, ((x i - y i) + t * v i) ^ 2) := by
  unfold dE; congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem dE_line_right (x y v : ι → ℝ) (t : ℝ) :
    dE x (y + t • v) = Real.sqrt (∑ i, ((x i - y i) + t * (-v) i) ^ 2) := by
  unfold dE; congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]; ring

theorem hasDerivAt_line {U : (ι → ℝ) → ℝ} (hU : Differentiable ℝ U) (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => U (x + s • v)) (fderiv ℝ U (x + t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hU (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl

end dE

/-- **Second derivative test.** -/
theorem second_deriv_nonpos {g g' g'' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (hc : Continuous g'') (hmax : ∀ t, g t ≤ g 0) :
    g'' 0 ≤ 0 := by
  by_contra h
  push_neg at h
  have h0 : g' 0 = 0 :=
    IsLocalMax.hasDerivAt_eq_zero (Eventually.of_forall hmax) (hg 0)
  obtain ⟨δ, hδ, hpos⟩ : ∃ δ > 0, ∀ t, |t| < δ → 0 < g'' t := by
    have := (hc.continuousAt (x := 0)).eventually (lt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp this
    exact ⟨δ, hδ, fun t ht => hball (by simpa [Real.dist_eq] using ht)⟩
  set t := δ / 2
  have ht : 0 < t := by positivity
  have hg'c : Continuous g' := continuous_iff_continuousAt.mpr fun s => (hg' s).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun s => (hg s).continuousAt
  have hg'pos : ∀ s, 0 < s → s ≤ t → 0 < g' s := by
    intro s hs hst
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g' g'' hs hg'c.continuousOn
      fun x _ => hg' x
    have htd : t = δ / 2 := rfl
    have hp : 0 < g'' ξ := hpos ξ (by rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2])
    rw [hξe, h0, sub_zero, sub_zero] at hp
    exact (div_pos_iff_of_pos_right hs).mp hp
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' ht hgc.continuousOn fun x _ => hg x
  have h1 := hg'pos ξ hξ.1 hξ.2.le
  rw [hξe, sub_zero] at h1
  have h2 : 0 < g t - g 0 := (div_pos_iff_of_pos_right ht).mp h1
  linarith [hmax t]

section doubling

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Doubling-variables maximum principle.** -/
theorem doubling_bound {U F E : (ι → ℝ) → ℝ} {B : (ι → ℝ) → ι → ℝ} {τ K L M η : ℝ}
    (hU : ContDiff ℝ 2 U) (hUp : IsPer U) (hτ : 0 < τ) (hM : 0 < M)
    (hML : L ≤ M * (1 - K * τ)) (hη : 0 ≤ η)
    (hF : ∀ x y, F x - F y ≤ L * dE x y) (hE : ∀ x, |E x| ≤ η)
    (hB : ∀ x y, -K * dE x y ^ 2 ≤ ∑ k, (B x k - B y k) * (x k - y k))
    (heq : ∀ x, U x - τ * ∑ k, secondDirDeriv U (Pi.single k 1) x +
      τ * ∑ k, B x k * fderiv ℝ U x (Pi.single k 1) = F x + E x) :
    ∀ x y, U x - U y ≤ M * dE x y + 2 * η := by
  set Φ : (ι → ℝ) × (ι → ℝ) → ℝ := fun p => U p.1 - U p.2 - M * dE p.1 p.2
  have hU1 : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdEc : Continuous fun p : (ι → ℝ) × (ι → ℝ) => dE p.1 p.2 := by
    refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
    exact (((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)).pow 2
  have hΦc : Continuous Φ := ((hU.continuous.comp continuous_fst).sub
    (hU.continuous.comp continuous_snd)).sub (continuous_const.mul hdEc)
  obtain ⟨BU, hBU⟩ := periodic_bounded hU.continuous hUp
  have hBU0 : 0 ≤ BU := (norm_nonneg _).trans (hBU 0)
  set R := 2 * BU / M
  have hR : 0 ≤ R := by positivity
  set S : Set ((ι → ℝ) × (ι → ℝ)) :=
    (univ.pi fun _ => Icc (0 : ℝ) 1) ×ˢ (univ.pi fun _ => Icc (-R - 1) (R + 2))
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_Icc).prod
    (isCompact_univ_pi fun _ => isCompact_Icc)
  have h0S : ((0 : ι → ℝ), (0 : ι → ℝ)) ∈ S := by
    refine ⟨fun i _ => ⟨le_rfl, zero_le_one⟩, fun i _ => ⟨?_, ?_⟩⟩ <;> simp only [Pi.zero_apply] <;> linarith
  obtain ⟨p, hpS, hpmax⟩ := hS.exists_isMaxOn ⟨_, h0S⟩ hΦc.continuousOn
  -- translation invariance
  have hΦtr : ∀ (q : (ι → ℝ) × (ι → ℝ)) (m : ι → ℤ),
      Φ (q.1 - intVec m, q.2 - intVec m) = Φ q := by
    intro q m
    have h1 : ∀ z, U (z - intVec m) = U z := fun z => by
      have := hUp (-m) z
      rwa [show z + intVec (-m) = z - intVec m by
        funext i; simp [intVec, sub_eq_add_neg]] at this
    simp only [Φ, h1, dE_sub_sub]
  have hΦ00 : Φ ((0 : ι → ℝ), (0 : ι → ℝ)) = 0 := by simp [Φ, dE_self]
  have hglob : ∀ q, Φ q ≤ Φ p := by
    intro q
    by_cases hq : Φ q < 0
    · exact hq.le.trans (hΦ00 ▸ hpmax h0S)
    push_neg at hq
    set m : ι → ℤ := fun i => ⌊q.1 i⌋
    have hmem : (q.1 - intVec m, q.2 - intVec m) ∈ S := by
      have hdq : M * dE q.1 q.2 ≤ 2 * BU := by
        have h1 := hBU q.1; have h2 := hBU q.2
        rw [Real.norm_eq_abs] at h1 h2
        simp only [Φ] at hq
        linarith [le_abs_self (U q.1), neg_abs_le (U q.2)]
      have hdR : dE q.1 q.2 ≤ R := by
        simp only [R]; rw [le_div_iff₀ hM]; linarith
      refine ⟨fun i _ => ?_, fun i _ => ?_⟩
      · simp only [Pi.sub_apply, intVec, m]
        exact ⟨by linarith [Int.floor_le (q.1 i)], by linarith [Int.lt_floor_add_one (q.1 i)]⟩
      · have hi := abs_sub_le_dE q.1 q.2 i
        rw [abs_le] at hi
        simp only [Pi.sub_apply, intVec, m]
        constructor <;> linarith [Int.floor_le (q.1 i), Int.lt_floor_add_one (q.1 i)]
    calc Φ q = Φ (q.1 - intVec m, q.2 - intVec m) := (hΦtr q m).symm
      _ ≤ Φ p := hpmax hmem
  -- conclude by contradiction
  intro x0 y0
  by_contra hcon
  push_neg at hcon
  have hp2 : 2 * η < Φ p := by
    have := hglob (x0, y0); simp only [Φ] at this ⊢; linarith
  set x := p.1
  set y := p.2
  have hxy : x ≠ y := by
    intro h
    have : Φ p = 0 := by simp only [Φ, x, y] at h ⊢; rw [h, sub_self, dE_self, mul_zero, sub_zero]
    linarith
  set r := dE x y
  have hr : 0 < r := dE_pos hxy
  have hr2 : ∑ i, (x i - y i) ^ 2 ≠ 0 := by rw [← dE_sq]; positivity
  -- first order conditions
  have hgradx : ∀ k, fderiv ℝ U x (Pi.single k 1) = M * (x k - y k) / r := by
    intro k
    set v : ι → ℝ := Pi.single k 1
    have hd1 := hasDerivAt_line hU1 x v 0
    have hd2 := hasDerivAt_sqrt_sum_line (fun i => x i - y i) v hr2
    have hd := (hd1.sub_const (U y)).sub (hd2.const_mul M)
    have e : (fun t => Φ (x + t • v, y)) = fun t =>
        U (x + t • v) - U y - M * Real.sqrt (∑ i, ((x i - y i) + t * v i) ^ 2) := by
      funext t; simp only [Φ]; rw [dE_line_left]
    replace hd : HasDerivAt (fun t : ℝ => Φ (x + t • v, y))
        (fderiv ℝ U (x + (0 : ℝ) • v) v -
          M * ((∑ i, (x i - y i) * v i) / Real.sqrt (∑ i, (x i - y i) ^ 2))) (0 : ℝ) := by
      rw [e]; exact hd
    have h0 := IsLocalMax.hasDerivAt_eq_zero (f := fun t : ℝ => Φ (x + t • v, y))
      (Eventually.of_forall fun t => (hglob _).trans_eq (by simp only [zero_smul, add_zero, x, y]))
      hd
    simp only [zero_smul, add_zero] at h0
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [v, Pi.single_apply, hik]) (by simp)] at h0
    simp only [v, Pi.single_eq_same, mul_one] at h0
    rw [← dE] at h0
    rw [mul_div_assoc]; linarith
  have hgrady : ∀ k, fderiv ℝ U y (Pi.single k 1) = M * (x k - y k) / r := by
    intro k
    set v : ι → ℝ := Pi.single k 1
    have hd1 := hasDerivAt_line hU1 y v 0
    have hd2 := hasDerivAt_sqrt_sum_line (fun i => x i - y i) (-v) hr2
    have hd := (hd1.const_sub (U x)).sub (hd2.const_mul M)
    have e : (fun t => Φ (x, y + t • v)) = fun t =>
        U x - U (y + t • v) - M * Real.sqrt (∑ i, ((x i - y i) + t * (-v) i) ^ 2) := by
      funext t; simp only [Φ]; rw [dE_line_right]
    replace hd : HasDerivAt (fun t : ℝ => Φ (x, y + t • v))
        (-fderiv ℝ U (y + (0 : ℝ) • v) v -
          M * ((∑ i, (x i - y i) * (-v) i) / Real.sqrt (∑ i, (x i - y i) ^ 2))) (0 : ℝ) := by
      rw [e]; exact hd
    have h0 := IsLocalMax.hasDerivAt_eq_zero (f := fun t : ℝ => Φ (x, y + t • v))
      (Eventually.of_forall fun t => (hglob _).trans_eq (by simp only [zero_smul, add_zero, x, y]))
      hd
    simp only [zero_smul, add_zero, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h0
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [v, Pi.single_apply, hik]) (by simp)] at h0
    simp only [v, Pi.single_eq_same, mul_one] at h0
    rw [← dE, neg_div] at h0
    have hr' : r = dE x y := rfl
    rw [mul_div_assoc, hr']; simp only [v]; linarith
  -- second order condition
  have hlap : ∀ k, secondDirDeriv U (Pi.single k 1) x - secondDirDeriv U (Pi.single k 1) y ≤ 0 := by
    intro k
    set v : ι → ℝ := Pi.single k 1
    have hD : Differentiable ℝ fun z => fderiv ℝ U z v :=
      ((hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
    have hD2 : Continuous fun z => secondDirDeriv U v z := by
      have h2 : ContDiff ℝ 1 fun z => fderiv ℝ U z v :=
        (hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      exact (h2.continuous_fderiv (by norm_num)).clm_apply continuous_const
    refine second_deriv_nonpos (g := fun t => U (x + t • v) - U (y + t • v))
      (g' := fun t => fderiv ℝ U (x + t • v) v - fderiv ℝ U (y + t • v) v)
      (g'' := fun t => secondDirDeriv U v (x + t • v) - secondDirDeriv U v (y + t • v))
      (fun t => (hasDerivAt_line hU1 x v t).sub (hasDerivAt_line hU1 y v t))
      (fun t => (hasDerivAt_line hD x v t).sub (hasDerivAt_line hD y v t))
      ((hD2.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
        (hD2.comp (continuous_const.add (continuous_id.smul continuous_const))))
      (fun t => ?_) |>.trans_eq' (by simp)
    have := hglob (x + t • v, y + t • v)
    simp only [Φ] at this
    rw [dE_add_add] at this
    simp only [zero_smul, add_zero]
    simp only [Φ, x, y] at this ⊢
    linarith
  -- combine
  have hDx : ∑ k, B x k * fderiv ℝ U x (Pi.single k 1) - ∑ k, B y k * fderiv ℝ U y (Pi.single k 1)
      = M / r * ∑ k, (B x k - B y k) * (x k - y k) := by
    simp_rw [hgradx, hgrady, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
    try ring
  have hBxy := hB x y
  have hdrift : -(M * K * r) ≤ ∑ k, B x k * fderiv ℝ U x (Pi.single k 1) -
      ∑ k, B y k * fderiv ℝ U y (Pi.single k 1) := by
    rw [hDx]
    have : M / r * (-K * r ^ 2) = -(M * K * r) := by field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hBxy (by positivity)
  have hΔ : ∑ k, secondDirDeriv U (Pi.single k 1) x - ∑ k, secondDirDeriv U (Pi.single k 1) y ≤ 0 := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_nonpos fun k _ => hlap k
  have h1 := heq x
  have h2 := heq y
  have hFxy := hF x y
  have hEx := hE x
  have hEy := hE y
  rw [abs_le] at hEx hEy
  have hΦp : Φ p = U x - U y - M * r := rfl
  have hfin : Φ p ≤ (L + τ * M * K - M) * r + 2 * η := by
    rw [hΦp]; nlinarith [mul_le_mul_of_nonneg_left hΔ hτ.le, mul_le_mul_of_nonneg_left hdrift hτ.le]
  have hcoef : (L + τ * M * K - M) * r ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hr.le
  linarith

end doubling

end SharpLSI

namespace SharpLSI

section maxbound

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Maximum principle**: `U - τΔU + τB·∇U = F + E` with `F ≤ BF`, `|E| ≤ η` gives `U ≤ BF + η`. -/
theorem max_bound {U F E : (ι → ℝ) → ℝ} {B : (ι → ℝ) → ι → ℝ} {τ BF η : ℝ}
    (hU : ContDiff ℝ 2 U) (hUp : IsPer U) (hτ : 0 < τ) (hF : ∀ x, F x ≤ BF)
    (hE : ∀ x, E x ≤ η)
    (heq : ∀ x, U x - τ * ∑ k, secondDirDeriv U (Pi.single k 1) x +
      τ * ∑ k, B x k * fderiv ℝ U x (Pi.single k 1) = F x + E x) (x : ι → ℝ) :
    U x ≤ BF + η := by
  have hU1 : Differentiable ℝ U := hU.differentiable (by norm_num)
  -- the maximum is attained in the unit box
  set S : Set (ι → ℝ) := univ.pi fun _ => Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨x₀, -, hmax⟩ := hS.exists_isMaxOn ⟨0, fun i _ => ⟨le_rfl, zero_le_one⟩⟩
    hU.continuous.continuousOn
  have hglob : ∀ z, U z ≤ U x₀ := by
    intro z
    set m : ι → ℤ := fun i => ⌊z i⌋
    have h1 : U (z - intVec m) = U z := by
      have := hUp (-m) z
      rwa [show z + intVec (-m) = z - intVec m by funext i; simp [intVec, sub_eq_add_neg]] at this
    rw [← h1]
    refine hmax ?_
    intro i _
    simp only [Pi.sub_apply, intVec, m]
    exact ⟨by linarith [Int.floor_le (z i)], by linarith [Int.lt_floor_add_one (z i)]⟩
  have hgrad : ∀ k, fderiv ℝ U x₀ (Pi.single k 1) = 0 := by
    intro k
    have hd := hasDerivAt_line hU1 x₀ (Pi.single k 1) 0
    simp only [zero_smul, add_zero] at hd
    exact IsLocalMax.hasDerivAt_eq_zero (f := fun s : ℝ => U (x₀ + s • Pi.single k 1))
      (Eventually.of_forall fun s => by simpa using hglob _) hd
  have hlap : ∀ k, secondDirDeriv U (Pi.single k 1) x₀ ≤ 0 := by
    intro k
    set v : ι → ℝ := Pi.single k 1
    have hD : Differentiable ℝ fun z => fderiv ℝ U z v :=
      ((hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
        (by norm_num)
    have hD2 : Continuous fun z => secondDirDeriv U v z := by
      have h2 : ContDiff ℝ 1 fun z => fderiv ℝ U z v :=
        (hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      exact (h2.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have := second_deriv_nonpos (g := fun s => U (x₀ + s • v))
      (g' := fun s => fderiv ℝ U (x₀ + s • v) v)
      (g'' := fun s => secondDirDeriv U v (x₀ + s • v))
      (fun s => hasDerivAt_line hU1 x₀ v s) (fun s => hasDerivAt_line hD x₀ v s)
      (hD2.comp (continuous_const.add (continuous_id.smul continuous_const)))
      (fun s => by simpa using hglob _)
    simpa using this
  have h1 := heq x₀
  simp only [hgrad, mul_zero, Finset.sum_const_zero, add_zero] at h1
  have hΔ : ∑ k, secondDirDeriv U (Pi.single k 1) x₀ ≤ 0 := Finset.sum_nonpos fun k _ => hlap k
  have := hF x₀
  have := hE x₀
  have h2 : U x₀ ≤ BF + η := by nlinarith [mul_le_mul_of_nonneg_left hΔ hτ.le]
  exact (hglob x).trans h2

end maxbound

end SharpLSI
