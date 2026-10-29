import SharpSymmetricLSI.Paper.Occ3

/-!
# Completeness of the Hermite basis in `L²(γ)` (Phase 3, lane D; R28)

If `F ∈ L²(γ)` is orthogonal to every `h_α`, then `F` is orthogonal to every polynomial in
finitely many coordinates (Hermite polynomials span the polynomials), hence to every
`exp(i⟨t, z_I⟩)` (Taylor expansion and dominated convergence). By Fourier uniqueness the
measures `F⁺γ` and `F⁻γ` agree on cylinder sets, hence everywhere, and `F = 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI

/-- `He_j` as a real polynomial. -/
def hermiteR (j : ℕ) : ℝ[X] := (hermite j).map (Int.castRingHom ℝ)

theorem natDegree_hermiteR (j : ℕ) : (hermiteR j).natDegree = j := by
  rw [hermiteR, natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_hermite]

theorem leadingCoeff_hermiteR (j : ℕ) : (hermiteR j).leadingCoeff = 1 := by
  rw [hermiteR, leadingCoeff_map_of_injective (RingHom.injective_int _), leadingCoeff_hermite]
  simp

/-- The Hermite polynomials span `ℝ[X]`. -/
theorem mem_span_hermiteR (p : ℝ[X]) : p ∈ Submodule.span ℝ (Set.range hermiteR) := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hp : p = 0
    · rw [hp]; exact Submodule.zero_mem _
    set q := p - C p.leadingCoeff * hermiteR n
    have hdecomp : p = q + p.leadingCoeff • hermiteR n := by
      simp only [q, smul_eq_C_mul]; ring
    rw [hdecomp]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩))
    by_cases hq : q = 0
    · rw [hq]; exact Submodule.zero_mem _
    have hlc : (C p.leadingCoeff * hermiteR n).leadingCoeff = p.leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_hermiteR, mul_one]
    have hdeg : (C p.leadingCoeff * hermiteR n).degree = p.degree := by
      rw [degree_C_mul (leadingCoeff_ne_zero.mpr hp), degree_eq_natDegree hp, h,
        degree_eq_natDegree (fun h0 => by
          have := leadingCoeff_hermiteR n; rw [h0] at this; simp at this), natDegree_hermiteR]
    have hlt : q.degree < p.degree := degree_sub_lt hdeg.symm hp hlc.symm
    have hlt' : q.natDegree < n := by
      rw [← h]; exact natDegree_lt_natDegree hq hlt
    exact ih _ hlt' q rfl


/-! ### Polynomials in finitely many coordinates under `γ` -/

theorem integrable_gammaRef_prod (S : Finset ℕ) (g : ℕ → ℝ → ℝ) (hg : ∀ n, Continuous (g n))
    (hi : ∀ n, Integrable (g n) (gaussianReal 0 1)) :
    Integrable (fun z : ℕ → ℝ => ∏ n ∈ S, g n (z n)) gammaRef := by
  have hmap : gammaRef.map S.restrict = Measure.pi fun _ : S => gaussianReal 0 1 := by
    unfold gammaRef; exact Measure.infinitePi_map_restrict _
  have hF : Integrable (fun w : S → ℝ => ∏ i : S, g i (w i)) (gammaRef.map S.restrict) := by
    rw [hmap]; exact Integrable.fintype_prod (f := fun (i : S) x => g i x) fun i => hi i
  refine (hF.comp_measurable (Finset.measurable_restrict S)).congr
    (Eventually.of_forall fun z => ?_)
  simp only [Function.comp, Finset.restrict]
  exact Finset.prod_coe_sort S (fun n => g n (z n))

theorem continuous_polyProd (S : Finset ℕ) (q : ℕ → ℝ[X]) :
    Continuous fun z : ℕ → ℝ => ∏ n ∈ S, (q n).eval (z n) :=
  continuous_finsetProd _ fun n _ => (q n).continuous.comp (continuous_apply n)

theorem memLp_polyProd (S : Finset ℕ) (q : ℕ → ℝ[X]) :
    MemLp (fun z : ℕ → ℝ => ∏ n ∈ S, (q n).eval (z n)) 2 gammaRef := by
  refine (memLp_two_iff_integrable_sq (continuous_polyProd S q).aestronglyMeasurable).mpr ?_
  have e : (fun z : ℕ → ℝ => (∏ n ∈ S, (q n).eval (z n)) ^ 2) =
      fun z => ∏ n ∈ S, ((q n) ^ 2).eval (z n) := by
    funext z; rw [← Finset.prod_pow]; simp [eval_pow]
  rw [e]
  exact integrable_gammaRef_prod S _ (fun n => (q n ^ 2).continuous)
    fun n => integrable_poly_gaussian _

/-- `He_k/√(k!)` as a real polynomial. -/
def hermiteQ (k : ℕ) : ℝ[X] := C (Real.sqrt (k.factorial : ℝ))⁻¹ * hermiteR k

theorem hermiteN_eq_eval (k : ℕ) (x : ℝ) : hermiteN k x = (hermiteQ k).eval x := by
  rw [hermiteN, hermiteQ, eval_mul, eval_C, aeval_hermite_eq, div_eq_inv_mul]; rfl

theorem hermiteBasis_mul_polyProd_eq {β : ℕ →₀ ℕ} {I : Finset ℕ} (hdis : Disjoint β.support I)
    (p : ℕ → ℝ[X]) (z : ℕ → ℝ) :
    hermiteBasis β z * ∏ n ∈ I, (p n).eval (z n) =
      ∏ n ∈ β.support ∪ I, (if n ∈ β.support then hermiteQ (β n) else p n).eval (z n) := by
  rw [Finset.prod_union hdis]
  congr 1
  · unfold hermiteBasis
    refine Finset.prod_congr rfl fun n hn => ?_
    rw [if_pos hn, ← hermiteN_eq_eval]; rfl
  · refine Finset.prod_congr rfl fun n hn => ?_
    rw [if_neg (Finset.disjoint_right.mp hdis hn)]

theorem memLp_hermiteBasis_mul_polyProd {β : ℕ →₀ ℕ} {I : Finset ℕ} (hdis : Disjoint β.support I)
    (p : ℕ → ℝ[X]) :
    MemLp (fun z => hermiteBasis β z * ∏ n ∈ I, (p n).eval (z n)) 2 gammaRef := by
  simp_rw [hermiteBasis_mul_polyProd_eq hdis p]
  exact memLp_polyProd _ _

theorem hermiteBasis_add_single {β : ℕ →₀ ℕ} {a : ℕ} (ha : a ∉ β.support) (j : ℕ) (z : ℕ → ℝ) :
    hermiteBasis (β + Finsupp.single a j) z = hermiteBasis β z * hermiteN j (z a) := by
  have hsub : (β + Finsupp.single a j).support ⊆ insert a β.support := by
    intro n hn
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hn
    by_cases h : n = a
    · exact Finset.mem_insert.mpr (Or.inl h)
    · rw [Finsupp.single_apply, if_neg (Ne.symm h), add_zero] at hn
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hn)
  have hβa : β a = 0 := by simpa using ha
  rw [hermiteBasis_eq_prod _ hsub, Finset.prod_insert ha, hermiteBasis_eq_prod β
    (Finset.Subset.refl _), mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun n hn => ?_
    have : n ≠ a := by rintro rfl; exact ha hn
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm this), add_zero]
  · simp [hβa]

/-- Orthogonality to all `h_α` gives orthogonality to products of coordinate polynomials. -/
theorem integral_mul_hermite_polyProd {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 gammaRef)
    (horth : ∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α z ∂gammaRef = 0) (I : Finset ℕ) :
    ∀ (p : ℕ → ℝ[X]) (β : ℕ →₀ ℕ), Disjoint β.support I →
      ∫ z, F z * (hermiteBasis β z * ∏ n ∈ I, (p n).eval (z n)) ∂gammaRef = 0 := by
  induction I using Finset.induction_on with
  | empty => intro p β _; simpa using horth β
  | insert a I ha ih =>
    intro p β hdis
    have haβ : a ∉ β.support := fun h => Finset.disjoint_left.mp hdis h (Finset.mem_insert_self a I)
    have hdisI : Disjoint β.support I :=
      Finset.disjoint_of_subset_right (Finset.subset_insert a I) hdis
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp (mem_span_hermiteR (p a))
    have hpa : ∀ x, (p a).eval x = ∑ j ∈ c.support, c j * (hermiteR j).eval x := fun x => by
      rw [← hc, Finsupp.sum, eval_finsetSum]
      simp [smul_eq_C_mul]
    have hterm : ∀ j, ∫ z, F z * (hermiteBasis (β + Finsupp.single a j) z *
        ∏ n ∈ I, (p n).eval (z n)) ∂gammaRef = 0 := fun j => by
      refine ih p _ ?_
      rw [Finset.disjoint_left]
      intro n hn hnI
      rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hn
      by_cases h : n = a
      · exact ha (h ▸ hnI)
      · rw [Finsupp.single_apply, if_neg (Ne.symm h), add_zero] at hn
        exact Finset.disjoint_left.mp hdisI (Finsupp.mem_support_iff.mpr hn) hnI
    have hint : ∀ j, Integrable (fun z => F z * (hermiteBasis (β + Finsupp.single a j) z *
        ∏ n ∈ I, (p n).eval (z n))) gammaRef := fun j => by
      refine hF.integrable_mul (memLp_hermiteBasis_mul_polyProd ?_ p)
      rw [Finset.disjoint_left]
      intro n hn hnI
      rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hn
      by_cases h : n = a
      · exact ha (h ▸ hnI)
      · rw [Finsupp.single_apply, if_neg (Ne.symm h), add_zero] at hn
        exact Finset.disjoint_left.mp hdisI (Finsupp.mem_support_iff.mpr hn) hnI
    have hexp : ∀ z, F z * (hermiteBasis β z * ∏ n ∈ insert a I, (p n).eval (z n)) =
        ∑ j ∈ c.support, (c j * Real.sqrt (j.factorial : ℝ)) *
          (F z * (hermiteBasis (β + Finsupp.single a j) z * ∏ n ∈ I, (p n).eval (z n))) := by
      intro z
      rw [Finset.prod_insert ha, hpa]
      simp_rw [hermiteBasis_add_single haβ]
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hf : (0 : ℝ) < Real.sqrt (j.factorial : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos j)
      have hN : (hermiteR j).eval (z a) = Real.sqrt (j.factorial : ℝ) * hermiteN j (z a) := by
        rw [hermiteN_eq_eval, hermiteQ, eval_mul, eval_C]; field_simp
      rw [hN]; ring
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ => (hint j).const_mul _]
    exact Finset.sum_eq_zero fun j _ => by rw [integral_const_mul, hterm j, mul_zero]


/-! ### Complex polynomials in finitely many coordinates -/

/-- `∑_{k<K} c_k y^k` with complex coefficients. -/
def cpoly (c : ℕ → ℂ) (K : ℕ) (y : ℝ) : ℂ := ∑ k ∈ Finset.range K, c k * (y : ℂ) ^ k

theorem norm_cpoly_le (c : ℕ → ℂ) (K : ℕ) (y : ℝ) :
    ‖cpoly c K y‖ ≤ (∑ k ∈ Finset.range K, ‖c k‖) * (1 + y ^ 2) ^ K := by
  unfold cpoly
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : |y| ≤ 1 + y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]
  have h2 : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  calc |y| ^ k ≤ (1 + y ^ 2) ^ k := pow_le_pow_left₀ (abs_nonneg _) h1 k
    _ ≤ (1 + y ^ 2) ^ K := pow_le_pow_right₀ h2 (Finset.mem_range.mp hk).le

theorem integrable_F_mul_cpolyProd {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 gammaRef) (J I : Finset ℕ)
    (q : ℕ → ℝ[X]) (c : ℕ → ℕ → ℂ) (K : ℕ) :
    Integrable (fun z => (F z : ℂ) * (((∏ n ∈ J, (q n).eval (z n) : ℝ) : ℂ) *
      ∏ n ∈ I, cpoly (c n) K (z n))) gammaRef := by
  set G1 : (ℕ → ℝ) → ℝ := fun z => ∏ n ∈ J, (q n).eval (z n)
  set r : ℕ → ℝ[X] := fun n => C (∑ k ∈ Finset.range K, ‖c n k‖) * (1 + X ^ 2) ^ K
  set G2 : (ℕ → ℝ) → ℝ := fun z => ∏ n ∈ I, (r n).eval (z n)
  have hG1 := memLp_polyProd J q
  have hG2 := memLp_polyProd I r
  have hb1 : Integrable (fun z => |F z| * G1 z ^ 2) gammaRef := by
    have : MemLp (fun z => G1 z ^ 2) 2 gammaRef := by
      have e : (fun z => G1 z ^ 2) = fun z => ∏ n ∈ J, ((q n) ^ 2).eval (z n) := by
        funext z; simp only [G1]; rw [← Finset.prod_pow]; simp [eval_pow]
      rw [e]; exact memLp_polyProd J _
    exact hF.abs.integrable_mul this
  have hb2 : Integrable (fun z => |F z| * G2 z ^ 2) gammaRef := by
    have : MemLp (fun z => G2 z ^ 2) 2 gammaRef := by
      have e : (fun z => G2 z ^ 2) = fun z => ∏ n ∈ I, ((r n) ^ 2).eval (z n) := by
        funext z; simp only [G2]; rw [← Finset.prod_pow]; simp [eval_pow]
      rw [e]; exact memLp_polyProd I _
    exact hF.abs.integrable_mul this
  have hmeas : AEStronglyMeasurable (fun z => (F z : ℂ) * (((∏ n ∈ J, (q n).eval (z n) : ℝ) : ℂ) *
      ∏ n ∈ I, cpoly (c n) K (z n))) gammaRef := by
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hF.aestronglyMeasurable).mul
      ((Complex.continuous_ofReal.comp (continuous_polyProd J q)).mul
        (continuous_finsetProd _ fun n _ => ?_)).aestronglyMeasurable
    unfold cpoly
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul ((Complex.continuous_ofReal.comp (continuous_apply n)).pow k)
  refine ((hb1.add hb2).div_const 2).mono' hmeas (Eventually.of_forall fun z => ?_)
  have hG2b : ‖∏ n ∈ I, cpoly (c n) K (z n)‖ ≤ G2 z := by
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun n _ => norm_nonneg _) fun n _ => ?_
    simp only [r, eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
    exact norm_cpoly_le _ _ _
  have hG2n : 0 ≤ G2 z := (norm_nonneg _).trans hG2b
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hF0 : 0 ≤ |F z| := abs_nonneg _
  have key : |G1 z| * G2 z ≤ (G1 z ^ 2 + G2 z ^ 2) / 2 := by
    nlinarith [sq_nonneg (|G1 z| - G2 z), sq_abs (G1 z)]
  calc |F z| * (|∏ n ∈ J, (q n).eval (z n)| * ‖∏ n ∈ I, cpoly (c n) K (z n)‖)
      ≤ |F z| * (|G1 z| * G2 z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG2b (abs_nonneg _)) hF0
    _ ≤ |F z| * ((G1 z ^ 2 + G2 z ^ 2) / 2) := mul_le_mul_of_nonneg_left key hF0
    _ = (|F z| * G1 z ^ 2 + |F z| * G2 z ^ 2) / 2 := by ring

/-- Orthogonality to complex polynomials in finitely many coordinates. -/
theorem integral_mul_cpolyProd {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 gammaRef)
    (horth : ∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α z ∂gammaRef = 0) (c : ℕ → ℕ → ℂ) (K : ℕ)
    (I : Finset ℕ) :
    ∀ (J : Finset ℕ), Disjoint J I → ∀ q : ℕ → ℝ[X],
      ∫ z, (F z : ℂ) * (((∏ n ∈ J, (q n).eval (z n) : ℝ) : ℂ) *
        ∏ n ∈ I, cpoly (c n) K (z n)) ∂gammaRef = 0 := by
  induction I using Finset.induction_on with
  | empty =>
    intro J _ q
    simp only [Finset.prod_empty, mul_one]
    have h := integral_mul_hermite_polyProd hF horth J q 0 (by simp)
    simp only [hermiteBasis, Finsupp.support_zero, Finset.prod_empty, one_mul] at h
    rw [show (fun z : ℕ → ℝ => (F z : ℂ) * ((∏ n ∈ J, (q n).eval (z n) : ℝ) : ℂ)) =
      fun z => ((F z * ∏ n ∈ J, (q n).eval (z n) : ℝ) : ℂ) by funext z; push_cast; ring,
      integral_complex_ofReal, h]
    simp
  | insert a I ha ih =>
    intro J hJ q
    have haJ : a ∉ J := fun h => Finset.disjoint_left.mp hJ h (Finset.mem_insert_self a I)
    have hJI : Disjoint J I := Finset.disjoint_of_subset_right (Finset.subset_insert a I) hJ
    have hJ' : Disjoint (insert a J) I := by
      rw [Finset.disjoint_insert_left]; exact ⟨ha, hJI⟩
    have hterm : ∀ k, ∫ z, (F z : ℂ) * (((∏ n ∈ insert a J,
        (Function.update q a (X ^ k) n).eval (z n) : ℝ) : ℂ) * ∏ n ∈ I, cpoly (c n) K (z n))
        ∂gammaRef = 0 := fun k => ih (insert a J) hJ' _
    have hprod : ∀ (k : ℕ) (z : ℕ → ℝ), (∏ n ∈ insert a J, (Function.update q a (X ^ k) n).eval (z n)) =
        z a ^ k * ∏ n ∈ J, (q n).eval (z n) := fun k z => by
      rw [Finset.prod_insert haJ, Function.update_self, eval_pow, eval_X]
      congr 1
      refine Finset.prod_congr rfl fun n hn => ?_
      have : n ≠ a := by rintro rfl; exact haJ hn
      rw [Function.update_of_ne this]
    have hexp : ∀ z, (F z : ℂ) * (((∏ n ∈ J, (q n).eval (z n) : ℝ) : ℂ) *
        ∏ n ∈ insert a I, cpoly (c n) K (z n)) =
        ∑ k ∈ Finset.range K, c a k * ((F z : ℂ) * (((∏ n ∈ insert a J,
          (Function.update q a (X ^ k) n).eval (z n) : ℝ) : ℂ) * ∏ n ∈ I, cpoly (c n) K (z n))) := by
      intro z
      simp_rw [hprod]
      rw [Finset.prod_insert ha]
      unfold cpoly
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    simp_rw [hexp]
    rw [integral_finsetSum _ fun k _ => (integrable_F_mul_cpolyProd hF _ _ _ _ _).const_mul _]
    exact Finset.sum_eq_zero fun k _ => by rw [integral_const_mul, hterm k, mul_zero]


/-! ### Characteristic functions and the conclusion -/

theorem integrable_exp_abs_gaussian (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|)) (gaussianReal 0 1) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (a * x)) (gaussianReal 0 1) := by
    have : a ∈ integrableExpSet id (gaussianReal 0 1) := by
      rw [integrableExpSet_id_gaussianReal]; trivial
    exact this
  have h2 : Integrable (fun x : ℝ => Real.exp (-a * x)) (gaussianReal 0 1) := by
    have : -a ∈ integrableExpSet id (gaussianReal 0 1) := by
      rw [integrableExpSet_id_gaussianReal]; trivial
    exact this
  refine (h1.add h2).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-a * x)]
  · rw [abs_of_nonpos hx]
    have : a * -x = -a * x := by ring
    rw [this]; linarith [Real.exp_pos (a * x)]

/-- **`∫ F(z) e^{i⟨t, z_I⟩} dγ = 0`.** -/
theorem integral_mul_cexp_eq_zero {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 gammaRef)
    (horth : ∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α z ∂gammaRef = 0) (I : Finset ℕ)
    (t : ℕ → ℝ) :
    ∫ z, (F z : ℂ) * Complex.exp ((∑ n ∈ I, t n * z n : ℝ) * Complex.I) ∂gammaRef = 0 := by
  set c : ℕ → ℕ → ℂ := fun n k => ((t n : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
  have hzero : ∀ K, ∫ z, (F z : ℂ) * ∏ n ∈ I, cpoly (c n) K (z n) ∂gammaRef = 0 := fun K => by
    have h := integral_mul_cpolyProd hF horth c K I ∅ (Finset.disjoint_empty_left _) (fun _ => 1)
    simpa using h
  -- pointwise convergence of the truncated exponentials
  have hcp : ∀ (n : ℕ) (y : ℝ), Tendsto (fun K => cpoly (c n) K y) atTop
      (𝓝 (Complex.exp ((t n * y : ℝ) * Complex.I))) := by
    intro n y
    have h := (NormedSpace.expSeries_div_hasSum_exp (((t n * y : ℝ) : ℂ) * Complex.I)).tendsto_sum_nat
    rw [← Complex.exp_eq_exp_ℂ] at h
    refine h.congr fun K => ?_
    unfold cpoly
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c]; push_cast; ring
  have hexp : ∀ z : ℕ → ℝ, Complex.exp ((∑ n ∈ I, t n * z n : ℝ) * Complex.I) =
      ∏ n ∈ I, Complex.exp ((t n * z n : ℝ) * Complex.I) := fun z => by
    rw [← Complex.exp_sum]; push_cast; rw [Finset.sum_mul]
  -- domination
  set G : (ℕ → ℝ) → ℝ := fun z => ∏ n ∈ I, Real.exp (|t n| * |z n|)
  have hGL : MemLp G 2 gammaRef := by
    have hc : Continuous G := continuous_finsetProd _ fun n _ =>
      Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp (continuous_apply n)))
    refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr ?_
    have e : (fun z => G z ^ 2) = fun z => ∏ n ∈ I, Real.exp ((2 * |t n|) * |z n|) := by
      funext z; simp only [G]; rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun n _ => ?_
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    exact integrable_gammaRef_prod I _ (fun n => Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)) fun n => integrable_exp_abs_gaussian _
  have hbound : ∀ K, ∀ z : ℕ → ℝ, ‖(F z : ℂ) * ∏ n ∈ I, cpoly (c n) K (z n)‖ ≤ |F z| * G z := by
    intro K z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun n _ => norm_nonneg _)
      fun n _ => ?_) (abs_nonneg _)
    unfold cpoly
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k, ‖c n k * ((z n : ℝ) : ℂ) ^ k‖ = (|t n| * |z n|) ^ k / k.factorial := fun k => by
      simp only [c, norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Complex.norm_natCast]
      ring
    simp_rw [this]
    exact Real.sum_le_exp_of_nonneg (by positivity) K
  have hlim := tendsto_integral_of_dominated_convergence
    (f := fun z => (F z : ℂ) * Complex.exp ((∑ n ∈ I, t n * z n : ℝ) * Complex.I))
    (fun z => |F z| * G z)
    (fun K => (integrable_F_mul_cpolyProd hF ∅ I (fun _ => 1) c K).aestronglyMeasurable.congr
      (Eventually.of_forall fun z => by simp))
    (hF.abs.integrable_mul hGL) (fun K => Eventually.of_forall (hbound K))
    (Eventually.of_forall fun z => by
      show Tendsto _ atTop (𝓝 ((F z : ℂ) * Complex.exp ((∑ n ∈ I, t n * z n : ℝ) * Complex.I)))
      rw [hexp]
      exact (tendsto_finset_prod I fun n _ => hcp n (z n)).const_mul _)
  simp_rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds


/-- **Completeness of the Hermite basis in `L²(γ)`.** -/
theorem hermiteBasis_complete {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 gammaRef)
    (horth : ∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α z ∂gammaRef = 0) : F =ᵐ[gammaRef] 0 := by
  -- reduce to a measurable representative
  set F' := hF.aestronglyMeasurable.mk F
  have hFF : F =ᵐ[gammaRef] F' := hF.aestronglyMeasurable.ae_eq_mk
  have hF'm : Measurable F' := hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hF' : MemLp F' 2 gammaRef := hF.ae_eq hFF
  have horth' : ∀ α : ℕ →₀ ℕ, ∫ z, F' z * hermiteBasis α z ∂gammaRef = 0 := fun α => by
    rw [← horth α]
    exact integral_congr_ae (hFF.mono fun z hz => by simp only [hz])
  refine hFF.trans ?_
  have hi : Integrable F' gammaRef := hF'.integrable one_le_two
  set μp := gammaRef.withDensity fun z => ENNReal.ofReal (F' z)
  set μm := gammaRef.withDensity fun z => ENNReal.ofReal (-F' z)
  haveI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hi.2
  haveI : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hi.neg.2
  -- the two measures agree on cylinders
  have hcyl : ∀ (I : Finset ℕ), μp.map I.restrict = μm.map I.restrict := by
    intro I
    set e := MeasurableEquiv.toLp 2 (I → ℝ)
    suffices h : (μp.map I.restrict).map e = (μm.map I.restrict).map e by
      have := congrArg (fun ν => ν.map e.symm) h
      simpa [Measure.map_map e.symm.measurable e.measurable] using this
    refine Measure.ext_of_charFun (E := EuclideanSpace ℝ I) (funext fun w => ?_)
    set t : ℕ → ℝ := fun n => if h : n ∈ I then w ⟨n, h⟩ else 0
    have hin : ∀ z : ℕ → ℝ, inner ℝ (e (I.restrict z)) w = ∑ n ∈ I, t n * z n := fun z => by
      rw [PiLp.inner_apply, ← Finset.sum_coe_sort I]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [t, dif_pos i.2, e, MeasurableEquiv.toLp_apply, PiLp.toLp_apply, Finset.restrict,
        RCLike.inner_apply, conj_trivial]
    have hm : Measurable fun z : ℕ → ℝ => e (I.restrict z) :=
      e.measurable.comp (Finset.measurable_restrict I)
    have hpm : ∀ (f : (ℕ → ℝ) → ℝ), Measurable f →
        charFun (((gammaRef.withDensity fun z => ENNReal.ofReal (f z)).map I.restrict).map e) w =
          ∫ z, ((ENNReal.ofReal (f z)).toReal : ℂ) * Complex.exp ((∑ n ∈ I, t n * z n : ℝ) * Complex.I)
            ∂gammaRef := by
      intro f hf
      have hc1 : Continuous fun x : EuclideanSpace ℝ I => Complex.exp (↑(inner ℝ x w) * Complex.I) := by
        fun_prop
      rw [charFun_apply, integral_map e.measurable.aemeasurable hc1.aestronglyMeasurable,
        integral_map (Finset.measurable_restrict I).aemeasurable
          (hc1.comp (PiLp.continuous_toLp 2 _)).aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Function.comp, Complex.real_smul]
      rw [hin z]
    rw [hpm F' hF'm, hpm (fun z => -F' z) hF'm.neg, ← sub_eq_zero,
      ← integral_sub]
    · have h := integral_mul_cexp_eq_zero hF' horth' I t
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      rw [← sub_mul]
      congr 1
      rcases le_total 0 (F' z) with hz | hz
      · rw [ENNReal.toReal_ofReal hz, ENNReal.ofReal_of_nonpos (by linarith)]; simp
      · simp [ENNReal.ofReal_of_nonpos hz, ENNReal.toReal_ofReal (show 0 ≤ -F' z by linarith)]
    all_goals
      refine hi.norm.mono' ?_ (Eventually.of_forall fun z => ?_)
      · exact ((Complex.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
          (ENNReal.measurable_ofReal.comp (by fun_prop)))).mul (Complex.measurable_exp.comp
          ((Complex.measurable_ofReal.comp (Finset.measurable_sum I fun n _ =>
            measurable_const.mul (measurable_pi_apply n))).mul_const _))).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_ofReal', Real.norm_eq_abs]
        rcases le_total 0 (F' z) with hz | hz
        · simp [abs_of_nonneg hz, hz]
        · simp [abs_of_nonpos hz, hz]
  -- hence everywhere
  have heq : μp = μm := by
    refine ext_of_generate_finite (measurableCylinders fun _ : ℕ => ℝ)
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_) ?_
    · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
      rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _) hS,
        ← Measure.map_apply (Finset.measurable_restrict _) hS, hcyl I]
    · have := congrArg (fun ν => ν Set.univ) (hcyl ∅)
      simpa [Measure.map_apply (Finset.measurable_restrict _) MeasurableSet.univ] using this
  have hae : (fun z => ENNReal.ofReal (F' z)) =ᵐ[gammaRef] fun z => ENNReal.ofReal (-F' z) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀
      (ENNReal.measurable_ofReal.comp hF'm).aemeasurable
      (ENNReal.measurable_ofReal.comp hF'm.neg).aemeasurable fun s hs _ => ?_
    have := congrArg (fun ν => ν s) heq
    simpa [μp, μm, withDensity_apply _ hs] using this
  filter_upwards [hae] with z hz
  rcases lt_trichotomy (F' z) 0 with h | h | h
  · rw [ENNReal.ofReal_of_nonpos h.le] at hz
    exact absurd hz.symm (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  · exact h
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -F' z ≤ 0)] at hz
    exact absurd hz (ENNReal.ofReal_pos.mpr h).ne'

end SharpLSI
