import SharpSymmetricLSI.Paper.Occ13

/-!
# Uniform moments of the occupation basis for bounded eigenfunctions (Phase 3, lane D; R28(e))

If the eigenfunctions are essentially bounded, `B_{α,N}` is bounded by a fixed polynomial in the
normalized sums `Z_{N,j}` (the higher Newton coefficients are uniformly bounded), and the `Z_{N,j}`
are uniformly sub-Gaussian (Hoeffding). Hence every moment of `B_{α,N}` is bounded uniformly in `N`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology MvPolynomial Finset.HasAntidiagonal
open scoped ENNReal NNReal

namespace SharpLSI

variable {K : ℕ}

theorem card_antidiagonal_le (α : Fin K →₀ ℕ) : (antidiagonal α).card ≤ (α.degree + 1) ^ K := by
  classical
  have hdeg : ∀ i, α i ≤ α.degree := fun i => by
    rw [Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (f := fun i => α i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  calc (antidiagonal α).card ≤ (Finset.Iic α).card := by
        refine Finset.card_le_card_of_injOn Prod.fst (fun x hx => ?_) (fun x hx y hy hxy => ?_)
        · have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          simp only [Finset.coe_Iic, Set.mem_Iic]
          rw [← hx']; exact le_self_add
        · have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
          refine Prod.ext hxy ?_
          have := hx'.trans hy'.symm
          rw [hxy] at this
          exact add_left_cancel this
    _ = ∏ i ∈ α.support, (α i + 1) := by rw [Finsupp.card_Iic]; simp
    _ ≤ ∏ _i ∈ α.support, (α.degree + 1) := Finset.prod_le_prod fun i _ => by
          have := hdeg i; omega
    _ = (α.degree + 1) ^ α.support.card := Finset.prod_const _
    _ ≤ (α.degree + 1) ^ K := Nat.pow_le_pow_right (Nat.succ_pos _)
          (by simpa using Finset.card_le_univ α.support)

/-- Polynomial growth of the Newton recursion. -/
theorem abs_newtonRec_le (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : Fin K → (Fin K →₀ ℕ) → ℝ) (R : ℝ),
    1 ≤ R → (∀ j γ, |q j γ| ≤ R) → ∀ α : Fin K →₀ ℕ, α.degree ≤ n →
      |newtonRec q n α| ≤ (A * R) ^ α.degree := by
  induction n with
  | zero =>
    refine ⟨1, le_rfl, fun q R _ _ α hα => ?_⟩
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    simp [newtonRec, this]
  | succ n ih =>
    obtain ⟨A, hA1, hA⟩ := ih
    refine ⟨((n + 1 : ℕ) : ℝ) ^ K * A, one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)) hA1, fun q R hR hq α hα => ?_⟩
    by_cases h : α = 0
    · simp [newtonRec, h]
    rw [newtonRec, dite_eq_right h]
    set j := α.support.min' (Finsupp.support_nonempty_iff.mpr h)
    have hj : α j ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    have hle : Finsupp.single j 1 ≤ α := by rw [Finsupp.single_le_iff]; omega
    set α' := α - Finsupp.single j 1
    have hdeg : α'.degree + 1 = α.degree := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add, Finsupp.degree_single]
    have hAR : 1 ≤ A * R := one_le_mul_of_one_le_of_one_le hA1 hR
    have hterm : ∀ x ∈ antidiagonal α', |newtonRec q n x.1 * q j x.2| ≤ (A * R) ^ α'.degree * R :=
      fun x hx => by
        rw [abs_mul]
        have h1 := (degree_le_of_mem_antidiagonal hx).2
        exact mul_le_mul ((hA q R hR hq x.1 (by omega)).trans (pow_le_pow_right₀ hAR h1)) (hq _ _)
          (abs_nonneg _) (by positivity)
    have hcard : ((antidiagonal α').card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ K := by
      have := card_antidiagonal_le α'
      have h2 : (α'.degree + 1) ^ K ≤ (n + 1) ^ K := Nat.pow_le_pow_left (by omega) _
      exact_mod_cast this.trans h2
    have hinv : |((α j : ℝ))⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj)
    rw [abs_mul]
    calc |((α j : ℝ))⁻¹| * |∑ x ∈ antidiagonal α', newtonRec q n x.1 * q j x.2|
        ≤ 1 * ∑ x ∈ antidiagonal α', (A * R) ^ α'.degree * R :=
          mul_le_mul hinv ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm))
            (abs_nonneg _) zero_le_one
      _ = (antidiagonal α').card * ((A * R) ^ α'.degree * R) := by
          rw [one_mul, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ K * ((A * R) ^ α'.degree * R) := by gcongr
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ K * A * R) ^ α.degree := by
          rw [← hdeg]
          have hc : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ K := one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)
          have h3 : ((n + 1 : ℕ) : ℝ) ^ K ≤ (((n + 1 : ℕ) : ℝ) ^ K) ^ α'.degree * ((n + 1 : ℕ) : ℝ) ^ K :=
            le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc)
          have h4 : (A * R) ^ α'.degree * R ≤ (A * R) ^ α'.degree * (A * R) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hA1) (by positivity)
          calc ((n + 1 : ℕ) : ℝ) ^ K * ((A * R) ^ α'.degree * R)
              ≤ ((((n + 1 : ℕ) : ℝ) ^ K) ^ α'.degree * ((n + 1 : ℕ) : ℝ) ^ K) *
                ((A * R) ^ α'.degree * (A * R)) := mul_le_mul h3 h4 (by positivity) (by positivity)
            _ = _ := by ring

/-! ### Sub-Gaussian moments of normalized sums -/

theorem abs_pow_le_factorial_mul_exp (x : ℝ) (r : ℕ) :
    |x| ^ r ≤ r.factorial * (Real.exp x + Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) r
  rw [div_le_iff₀ (by positivity)] at h
  have h2 : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; linarith [Real.exp_pos (-x)]
    · rw [h1]; linarith [Real.exp_pos x]
  calc |x| ^ r ≤ Real.exp |x| * r.factorial := h
    _ ≤ (Real.exp x + Real.exp (-x)) * r.factorial := by gcongr
    _ = _ := by ring

theorem moment_le_of_subgaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Ω → ℝ} {c : ℝ≥0} (hS : HasSubgaussianMGF S c P) (r : ℕ) :
    Integrable (fun ω => |S ω| ^ r) P ∧
      ∫ ω, |S ω| ^ r ∂P ≤ 2 * r.factorial * Real.exp (c / 2) := by
  have hi1 := hS.integrable_exp_mul 1
  have hi2 := hS.integrable_exp_mul (-1)
  simp only [one_mul, neg_one_mul] at hi1 hi2
  have hint : Integrable (fun ω => (r.factorial : ℝ) * (Real.exp (S ω) + Real.exp (-S ω))) P :=
    (hi1.add hi2).const_mul _
  have hmeas : AEStronglyMeasurable (fun ω => |S ω| ^ r) P :=
    (hS.aestronglyMeasurable.norm.pow r).congr (Eventually.of_forall fun ω => by simp)
  have hle : ∀ ω, |S ω| ^ r ≤ (r.factorial : ℝ) * (Real.exp (S ω) + Real.exp (-S ω)) :=
    fun ω => abs_pow_le_factorial_mul_exp _ _
  refine ⟨hint.mono' hmeas (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hle ω), ?_⟩
  calc ∫ ω, |S ω| ^ r ∂P ≤ ∫ ω, (r.factorial : ℝ) * (Real.exp (S ω) + Real.exp (-S ω)) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hint
          (Eventually.of_forall hle)
    _ = r.factorial * (mgf S P 1 + mgf S P (-1)) := by
        rw [integral_const_mul, integral_add hi1 hi2]
        simp [mgf]
    _ ≤ r.factorial * (Real.exp (c * 1 ^ 2 / 2) + Real.exp (c * (-1) ^ 2 / 2)) := by
        gcongr
        · exact hS.mgf_le 1
        · exact hS.mgf_le (-1)
    _ = 2 * r.factorial * Real.exp (c / 2) := by norm_num; ring

/-- Normalized sums of a bounded centered function are uniformly sub-Gaussian. -/
theorem moment_normSum_le {T : Type*} [MeasurableSpace T] {ν : Measure T} [IsProbabilityMeasure ν]
    {f : T → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) (h0 : ∫ x, f x ∂ν = 0)
    {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    Integrable (fun X : Fin N → T => |(Real.sqrt N)⁻¹ * ∑ l, f (X l)| ^ r)
        (Measure.pi fun _ : Fin N => ν) ∧
      ∫ X, |(Real.sqrt N)⁻¹ * ∑ l, f (X l)| ^ r ∂(Measure.pi fun _ : Fin N => ν) ≤
        2 * r.factorial * Real.exp (M ^ 2 / 2) := by
  set P := Measure.pi fun _ : Fin N => ν
  set s := (Real.sqrt N)⁻¹
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hY : ∀ l : Fin N, HasSubgaussianMGF (fun X : Fin N → T => s * f (X l))
      (⟨s ^ 2, sq_nonneg s⟩ * (‖M - -M‖₊ / 2) ^ 2) P := fun l => by
    have hmp := measurePreserving_eval (fun _ : Fin N => ν) l
    refine HasSubgaussianMGF.const_mul ?_ s
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hf.comp (measurable_pi_apply l)).aemeasurable
      (Eventually.of_forall fun X => ⟨(abs_le.mp (hb _)).1, (abs_le.mp (hb _)).2⟩) ?_
    rw [← h0, ← hmp.map_eq, integral_map (measurable_pi_apply l).aemeasurable hf.aestronglyMeasurable]
  have hind : iIndepFun (fun (l : Fin N) (X : Fin N → T) => s * f (X l)) P :=
    iIndepFun_pi (X := fun _ x => s * f x) fun _ => (hf.const_mul s).aemeasurable
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) fun l _ => hY l
  have hfun : (fun X : Fin N → T => ∑ l ∈ Finset.univ, s * f (X l)) =
      fun X => s * ∑ l, f (X l) := funext fun X => (Finset.mul_sum _ _ _).symm
  rw [hfun] at hS
  obtain ⟨hint, hle⟩ := moment_le_of_subgaussian hS r
  refine ⟨hint, hle.trans ?_⟩
  gcongr
  have key : ∀ (a : ℝ) (ha : 0 ≤ a) (b : ℝ≥0), ((⟨a, ha⟩ * b : ℝ≥0) : ℝ) = a * b :=
    fun _ _ _ => rfl
  simp only [NNReal.coe_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [NNReal.coe_mul, NNReal.coe_natCast]
  change (N : ℝ) * (s ^ 2 * (((‖M - -M‖₊ / 2 : ℝ≥0) : ℝ)) ^ 2) ≤ M ^ 2
  rw [NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat, sub_neg_eq_add, ← two_mul,
    abs_mul, abs_two]
  simp only [s, inv_pow, Real.sq_sqrt hNpos.le]
  field_simp
  rw [sq_abs]

/-- The normalization `N^k / (N)_k ≤ k^k` for `N ≥ k`. -/
theorem pow_div_descFactorial_le {N k : ℕ} (hk : k ≤ N) :
    (N : ℝ) ^ k ≤ (k : ℝ) ^ k * N.descFactorial k := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, ← Finset.card_range k, ← Finset.prod_const,
    ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.cast_sub (by omega)]
  have h1 : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
  have h2 : (k : ℝ) ≤ N := by exact_mod_cast hk
  nlinarith

/-- Power mean: `(∑ t)^m ≤ (#s)^m ∑ t^m`. -/
theorem pow_sum_le_card_pow_mul {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (m : ℕ) : (∑ i ∈ s, t i) ^ m ≤ (s.card : ℝ) ^ m * ∑ i ∈ s, t i ^ m := by
  rcases m with _ | m
  · simp only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul]
    exact_mod_cast hs.card_pos
  rcases Nat.eq_zero_or_pos s.card with h | h
  · simp [Finset.card_eq_zero.mp h]
  have := pow_sum_div_card_le_sum_pow ht m
  have hc : (0 : ℝ) < s.card := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)] at this
  calc (∑ i ∈ s, t i) ^ (m + 1) ≤ (∑ i ∈ s, t i ^ (m + 1)) * (s.card : ℝ) ^ m := this
    _ ≤ (∑ i ∈ s, t i ^ (m + 1)) * (s.card : ℝ) ^ (m + 1) := by
        gcongr
        · exact Finset.sum_nonneg fun i hi => pow_nonneg (ht i hi) _
        · exact_mod_cast h
        · omega
    _ = _ := by ring

section moments
variable {d : ℕ} {ν : Measure (Torus d)} [IsProbabilityMeasure ν] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} (he : IsRefEigenbasis ν e lam)

/-- A bounded measurable modification of the eigenbasis with `e 0 = 1`. -/
def ebd (Cb : ℕ → ℝ) (i : ℕ) : Torus d → ℝ :=
  if i = 0 then fun _ => 1 else fun x => max (-Cb i) (min (Cb i) (emod he i x))

include he in
theorem ebd_zero (Cb : ℕ → ℝ) (x : Torus d) : ebd he Cb 0 x = 1 := by simp [ebd]

include he in
theorem measurable_ebd (Cb : ℕ → ℝ) (i : ℕ) : Measurable (ebd he Cb i) := by
  unfold ebd; split_ifs
  · exact measurable_const
  · exact measurable_const.max (measurable_const.min (measurable_emod he i))

include he in
theorem abs_ebd_le {Cb : ℕ → ℝ} {i : ℕ} (hC : 0 ≤ Cb i) (hi : i ≠ 0) (x : Torus d) :
    |ebd he Cb i x| ≤ Cb i := by
  simp only [ebd, hi, ↓reduceIte]
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

include he in
theorem ebd_ae_eq {Cb : ℕ → ℝ} (hCb : ∀ i, ∀ᵐ x ∂ν, |e i x| ≤ Cb i) (i : ℕ) :
    ebd he Cb i =ᵐ[ν] e i := by
  by_cases hi : i = 0
  · subst hi; rw [he.zero]; exact Eventually.of_forall fun x => ebd_zero he Cb x
  filter_upwards [emod_ae_eq he i, hCb i] with x h1 h2
  simp only [ebd, hi, ↓reduceIte, h1]
  rw [min_eq_right (abs_le.mp h2).2, max_eq_right (abs_le.mp h2).1]

include he in
/-- **Uniform moments of `B_{α,N}` for essentially bounded eigenfunctions.** -/
theorem occBasis_moments_of_bdd (hb : ∀ j, ∃ C, ∀ᵐ x ∂ν, |e j x| ≤ C) (α : ℕ →₀ ℕ) (p : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, occSize α ≤ N →
      ∫ X, |occBasis e α N X| ^ p ∂Measure.pi (fun _ : Fin N => ν) ≤ C := by
  choose Cb hCb using hb
  set Cp : ℕ → ℝ := fun i => max (Cb i) 0
  have hCp0 : ∀ i, 0 ≤ Cp i := fun i => le_max_right _ _
  have hCp : ∀ i, ∀ᵐ x ∂ν, |e i x| ≤ Cp i := fun i =>
    (hCb i).mono fun x hx => hx.trans (le_max_left _ _)
  set E := ebd he Cp
  have hE0 : ∀ x, E 0 x = 1 := ebd_zero he Cp
  have hEm : ∀ i, Measurable (E i) := measurable_ebd he Cp
  have hEae : ∀ i, E i =ᵐ[ν] e i := ebd_ae_eq he hCp
  have hEmean : ∀ j : ℕ, ∫ x, E (j + 1) x ∂ν = 0 := fun j => by
    rw [integral_congr_ae (hEae _)]
    have h := he.orthonormal (j + 1) 0
    simp only [he.zero, mul_one, Nat.add_one_ne_zero, ite_false] at h
    exact h
  set k := occSize α
  set K := α.support.sup id + 1
  have hK : ∀ n, K ≤ n → α n = 0 := fun n hn => by
    by_contra h
    have := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)
    simp only [id] at this
    omega
  have hdeg := degree_finK α hK
  obtain ⟨A, hA1, hA⟩ := abs_newtonRec_le (K := K) k
  set G : ℝ := ∑ j : Fin K, Cp (j + 1)
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => hCp0 _
  have hEG : ∀ (j : Fin K) x, |E (j + 1) x| ≤ G := fun j x =>
    (abs_ebd_le he (hCp0 _) (Nat.add_one_ne_zero _) x).trans
      (Finset.single_le_sum (f := fun j : Fin K => Cp (j + 1)) (fun j _ => hCp0 _)
        (Finset.mem_univ j))
  set C0 : ℝ := (1 + G) ^ (k + 1)
  set m := k * p
  set cα : ℝ := Real.sqrt (occFactorial α) * Real.sqrt ((k : ℝ) ^ k) * A ^ k
  have hcα : 0 ≤ cα := by positivity
  set Bnd : ℝ := cα ^ p * ((K + 1 : ℕ) : ℝ) ^ m *
    ((1 + C0) ^ m + K * (2 * m.factorial * Real.exp (G ^ 2 / 2)))
  refine ⟨max Bnd (∫ X, |occBasis e α 0 X| ^ p ∂Measure.pi (fun _ : Fin 0 => ν)), fun N hN => ?_⟩
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · subst h0; exact le_max_right _ _
  refine le_trans ?_ (le_max_left _ _)
  set P := Measure.pi fun _ : Fin N => ν
  -- replace `e` by the bounded modification
  have hall : ∀ᵐ X ∂P, ∀ i (l : Fin N), E i (X l) = e i (X l) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro l
    exact (measurePreserving_eval (fun _ : Fin N => ν) l).quasiMeasurePreserving.ae_eq_comp
      (hEae i)
  have hae : ∀ᵐ X ∂P, |occBasis e α N X| ^ p = |occBasis E α N X| ^ p := by
    filter_upwards [hall] with X hX
    unfold occBasis
    congr 3
    exact Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => (hX _ _).symm
  rw [integral_congr_ae hae]
  -- the pointwise bound
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set sN := (Real.sqrt N)⁻¹
  have hsN0 : 0 ≤ sN := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hsN1 : sN ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by exact_mod_cast hNpos))
  have hsqN : Real.sqrt N ^ k * sN ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (Real.sqrt_pos.mpr hNr).ne', one_pow]
  set Z : Fin K → (Fin N → Torus d) → ℝ := fun j X => sN * ∑ l, E (j + 1) (X l)
  have hpt : ∀ X, |occBasis E α N X| ^ p ≤
      cα ^ p * ((K + 1 : ℕ) : ℝ) ^ m * ((1 + C0) ^ m + ∑ j, |Z j X| ^ m) := fun X => by
    set a : Fin N → Fin K → ℝ := fun i j => E (j + 1) (X i)
    set q : Fin K → (Fin K →₀ ℕ) → ℝ := fun j γ => sN ^ (γ.degree + 1) * newtonCoeff a j γ
    set q' : Fin K → (Fin K →₀ ℕ) → ℝ := fun j γ => if γ.degree < k then q j γ else 0
    set R : ℝ := 1 + C0 + ∑ j, |Z j X|
    have hC0 : 0 ≤ C0 := by positivity
    have hR1 : 1 ≤ R := by
      have : 0 ≤ ∑ j, |Z j X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    have hq' : ∀ j γ, |q' j γ| ≤ R := fun j γ => by
      simp only [q']
      split_ifs with hγ
      · by_cases hγ0 : γ = 0
        · subst hγ0
          have : q j 0 = Z j X := by
            simp only [q, map_zero, zero_add, pow_one, newtonCoeff_zero, Z, a]
          rw [this]
          have := Finset.single_le_sum (f := fun j => |Z j X|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
          linarith
        · have hd1 : 1 ≤ γ.degree := Nat.one_le_iff_ne_zero.mpr
            fun h => hγ0 ((Finsupp.degree_eq_zero_iff _).mp h)
          have hsum : ∀ i, ∑ l, |a i l| ≤ G := fun i =>
            Finset.sum_le_sum fun l _ =>
              abs_ebd_le he (hCp0 _) (Nat.add_one_ne_zero _) (X i)
          have h1 : |q j γ| ≤ sN ^ (γ.degree + 1) * (N * G ^ (γ.degree + 1)) := by
            simp only [q]
            rw [abs_mul, abs_of_nonneg (pow_nonneg hsN0 _)]
            refine mul_le_mul_of_nonneg_left ((abs_newtonCoeff_le _ _ _).trans ?_)
              (pow_nonneg hsN0 _)
            calc ∑ i, (∑ l, |a i l|) ^ (γ.degree + 1) ≤ ∑ _i : Fin N, G ^ (γ.degree + 1) :=
                  Finset.sum_le_sum fun i _ => pow_le_pow_left₀
                    (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hsum i) _
              _ = N * G ^ (γ.degree + 1) := by simp
          have h2 : sN ^ (γ.degree + 1) * N ≤ 1 := by
            obtain ⟨t, ht⟩ : ∃ t, γ.degree + 1 = t + 2 := ⟨γ.degree - 1, by omega⟩
            rw [ht, pow_add, mul_assoc]
            have : sN ^ 2 * N = 1 := by
              rw [inv_pow, Real.sq_sqrt hNr.le, inv_mul_cancel₀ hNr.ne']
            rw [this, mul_one]
            exact pow_le_one₀ hsN0 hsN1
          have h3 : G ^ (γ.degree + 1) ≤ C0 :=
            (pow_le_pow_left₀ hG0 (by linarith) _).trans
              (pow_le_pow_right₀ (by linarith) (by omega))
          calc |q j γ| ≤ sN ^ (γ.degree + 1) * N * G ^ (γ.degree + 1) := by
                rw [mul_assoc]; exact h1
            _ ≤ 1 * C0 := mul_le_mul h2 h3 (pow_nonneg hG0 _) zero_le_one
            _ ≤ R := by
                have : 0 ≤ ∑ j, |Z j X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
                linarith
      · rw [abs_zero]; linarith
    have hrec : newtonRec q' k (finK K α) = sN ^ k * (genPoly a).coeff (finK K α) := by
      rw [newtonRec_congr k (finK K α) (q' := q) fun j γ hγ => by
        simp only [q']; simp only [show γ.degree < k by omega, ↓reduceIte]]
      rw [newtonRec_scaled sN a k (finK K α) hdeg.le, hdeg]
    have hB : occBasis E α N X = Real.sqrt (occFactorial α / N.descFactorial k) *
        (Real.sqrt N ^ k * newtonRec q' k (finK K α)) := by
      have hcoef : (genPoly a).coeff (finK K α) = Real.sqrt N ^ k * newtonRec q' k (finK K α) := by
        rw [hrec, ← mul_assoc, hsqN, one_mul]
      unfold occBasis
      rw [labelling_sum_eq_coeff E hE0 α hK X]
      exact congrArg _ hcoef
    have hbd := hA q' R hR1 hq' (finK K α) hdeg.le
    rw [hdeg] at hbd
    have hdesc : (0 : ℝ) < N.descFactorial k := by
      exact_mod_cast Nat.descFactorial_pos.mpr hN
    have hfac : Real.sqrt (occFactorial α / N.descFactorial k) * Real.sqrt N ^ k ≤
        Real.sqrt (occFactorial α) * Real.sqrt ((k : ℝ) ^ k) := by
      rw [sqrt_pow_eq _ (Nat.cast_nonneg _), ← Real.sqrt_mul (by positivity),
        ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      rw [div_mul_eq_mul_div, div_le_iff₀ hdesc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_div_descFactorial_le hN) (Nat.cast_nonneg _)
    have hBabs : |occBasis E α N X| ≤ cα * R ^ k := by
      rw [hB, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ← mul_assoc]
      calc Real.sqrt (occFactorial α / N.descFactorial k) * Real.sqrt N ^ k *
            |newtonRec q' k (finK K α)| ≤
            Real.sqrt (occFactorial α) * Real.sqrt ((k : ℝ) ^ k) * (A * R) ^ k :=
            mul_le_mul hfac hbd (abs_nonneg _) (by positivity)
        _ = cα * R ^ k := by simp only [cα]; rw [mul_pow]; ring
    have hRm : R ^ m ≤ ((K + 1 : ℕ) : ℝ) ^ m * ((1 + C0) ^ m + ∑ j, |Z j X| ^ m) := by
      have := pow_sum_le_card_pow_mul (Finset.univ : Finset (Option (Fin K))) Finset.univ_nonempty
        (fun o => Option.elim o (1 + C0) fun j => |Z j X|)
        (fun o _ => by cases o <;> simp [abs_nonneg] <;> positivity) m
      simp only [Fintype.sum_option, Option.elim, Finset.card_univ, Fintype.card_option,
        Fintype.card_fin] at this
      calc R ^ m = (1 + C0 + ∑ j, |Z j X|) ^ m := rfl
        _ ≤ _ := by
          convert this using 2
    calc |occBasis E α N X| ^ p ≤ (cα * R ^ k) ^ p := pow_le_pow_left₀ (abs_nonneg _) hBabs _
      _ = cα ^ p * R ^ m := by rw [mul_pow, ← pow_mul]
      _ ≤ cα ^ p * (((K + 1 : ℕ) : ℝ) ^ m * ((1 + C0) ^ m + ∑ j, |Z j X| ^ m)) :=
          mul_le_mul_of_nonneg_left hRm (pow_nonneg hcα _)
      _ = _ := by ring
  -- integrate
  have hmom : ∀ j : Fin K, Integrable (fun X => |Z j X| ^ m) P ∧
      ∫ X, |Z j X| ^ m ∂P ≤ 2 * m.factorial * Real.exp (G ^ 2 / 2) := fun j =>
    moment_normSum_le (hEm _) (hEG j) (hEmean _) hNpos m
  have hint : Integrable (fun X => cα ^ p * ((K + 1 : ℕ) : ℝ) ^ m *
      ((1 + C0) ^ m + ∑ j, |Z j X| ^ m)) P :=
    ((integrable_const _).add (integrable_finsetSum _ fun j _ => (hmom j).1)).const_mul _
  calc ∫ X, |occBasis E α N X| ^ p ∂P ≤ ∫ X, cα ^ p * ((K + 1 : ℕ) : ℝ) ^ m *
        ((1 + C0) ^ m + ∑ j, |Z j X| ^ m) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun X => by positivity) hint
          (Eventually.of_forall hpt)
    _ = cα ^ p * ((K + 1 : ℕ) : ℝ) ^ m * ((1 + C0) ^ m + ∑ j, ∫ X, |Z j X| ^ m ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_finsetSum _ fun j _ => (hmom j).1), integral_finsetSum _ fun j _ => (hmom j).1]
        simp
    _ ≤ Bnd := by
        refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (by positivity)
        calc ∑ j, ∫ X, |Z j X| ^ m ∂P ≤ ∑ _j : Fin K, 2 * m.factorial * Real.exp (G ^ 2 / 2) :=
              Finset.sum_le_sum fun j _ => (hmom j).2
          _ = K * (2 * m.factorial * Real.exp (G ^ 2 / 2)) := by simp

end moments

end SharpLSI
