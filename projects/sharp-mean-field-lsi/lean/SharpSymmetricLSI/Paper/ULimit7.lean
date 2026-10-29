import SharpSymmetricLSI.Paper.ULimit6

/-!
# Truncation of the kernel in the reference basis (Phase 3, lane D; R26)

`K_R(x,y) = ∑_{a,b<R} T_{ab} e_{a+1}(x) e_{b+1}(y)`: centered, symmetric, and
`‖K - K_R‖²_{L²(μ⊗μ)} = ‖K‖² - ∑_{a,b<R} T_{ab}²`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

section kernel
variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
  {κ : α → α → ℝ} {e : ℕ → α → ℝ} {T : ℕ → ℕ → ℝ}

/-- The data of a bounded centered symmetric kernel and its matrix in an orthonormal family. -/
structure KerData (ν : Measure α) (κ : α → α → ℝ) (e : ℕ → α → ℝ) (T : ℕ → ℕ → ℝ) : Prop where
  meas : Measurable (Function.uncurry κ)
  bdd : ∃ B, ∀ x y, |κ x y| ≤ B
  symm : ∀ x y, κ x y = κ y x
  cent : ∀ w, ∫ y, κ y w ∂ν = 0
  emeas : ∀ i, Measurable (e i)
  eL2 : ∀ i, MemLp (e i) 2 ν
  orth : ∀ i j, ∫ x, e i x * e j x ∂ν = if i = j then 1 else 0
  emean : ∀ i, ∫ x, e (i + 1) x ∂ν = 0
  Tdef : ∀ a b, T a b = ∫ x, ∫ y, κ x y * e (a + 1) x * e (b + 1) y ∂ν ∂ν
  hs : HasSum (fun p : ℕ × ℕ => T p.1 p.2 ^ 2) (∫ x, ∫ y, κ x y ^ 2 ∂ν ∂ν)

/-- `K_R`. -/
def kTrunc (T : ℕ → ℕ → ℝ) (e : ℕ → α → ℝ) (R : ℕ) (x y : α) : ℝ :=
  ∑ a ∈ Finset.range R, ∑ b ∈ Finset.range R, T a b * (e (a + 1) x * e (b + 1) y)

namespace KerData
variable (hD : KerData ν κ e T)
include hD

theorem integrable_prod_e (i j : ℕ) :
    Integrable (fun p : α × α => e i p.1 * e j p.2) (ν.prod ν) :=
  ((hD.eL2 i).integrable one_le_two).mul_prod ((hD.eL2 j).integrable one_le_two)

theorem memLp_prod_e (i j : ℕ) : MemLp (fun p : α × α => e i p.1 * e j p.2) 2 (ν.prod ν) := by
  refine (memLp_two_iff_integrable_sq ((hD.emeas i).comp measurable_fst |>.mul
    ((hD.emeas j).comp measurable_snd)).aestronglyMeasurable).mpr ?_
  exact ((hD.eL2 i).integrable_sq.mul_prod (hD.eL2 j).integrable_sq).congr
    (Eventually.of_forall fun p => by simp [mul_pow])

theorem integrable_kappa_mul (i j : ℕ) :
    Integrable (fun p : α × α => κ p.1 p.2 * (e i p.1 * e j p.2)) (ν.prod ν) := by
  obtain ⟨B, hB⟩ := hD.bdd
  exact (hD.integrable_prod_e i j).bdd_mul (c := B) hD.meas.aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB _ _)

theorem T_eq_prod (a b : ℕ) :
    T a b = ∫ p, κ p.1 p.2 * (e (a + 1) p.1 * e (b + 1) p.2) ∂(ν.prod ν) := by
  rw [hD.Tdef, integral_prod _ (hD.integrable_kappa_mul _ _)]
  refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae
    (Eventually.of_forall fun y => ?_))
  simp only; ring

theorem T_symm (a b : ℕ) : T a b = T b a := by
  rw [hD.T_eq_prod, hD.T_eq_prod, ← integral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only; rw [hD.symm]; ring

theorem kTrunc_symm (R : ℕ) (x y : α) : kTrunc T e R x y = kTrunc T e R y x := by
  unfold kTrunc
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hD.T_symm]; ring

theorem integral_kTrunc_left (R : ℕ) (w : α) : ∫ y, kTrunc T e R y w ∂ν = 0 := by
  unfold kTrunc
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (((hD.eL2 (a + 1)).integrable one_le_two).mul_const _).const_mul _]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ =>
    (((hD.eL2 (a + 1)).integrable one_le_two).mul_const _).const_mul _]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [integral_const_mul, integral_mul_const, hD.emean, zero_mul, mul_zero]

theorem measurable_kTrunc (R : ℕ) : Measurable (Function.uncurry (kTrunc T e R)) := by
  unfold kTrunc
  have : ∀ a b, Measurable fun p : α × α => T a b * (e (a + 1) p.1 * e (b + 1) p.2) := fun a b =>
    ((((hD.emeas _).comp measurable_fst).mul ((hD.emeas _).comp measurable_snd))).const_mul _
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => this a b

theorem memLp_kTrunc (R : ℕ) :
    MemLp (fun p : α × α => kTrunc T e R p.1 p.2) 2 (ν.prod ν) := by
  unfold kTrunc
  exact memLp_finsetSum _ fun a _ => memLp_finsetSum
    (f := fun b (p : α × α) => T a b * (e (a + 1) p.1 * e (b + 1) p.2)) _
    fun b _ => (hD.memLp_prod_e _ _).const_mul _

theorem memLp_kappa : MemLp (fun p : α × α => κ p.1 p.2) 2 (ν.prod ν) := by
  obtain ⟨B, hB⟩ := hD.bdd
  exact MemLp.of_bound hD.meas.aestronglyMeasurable B
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB _ _)

/-- `∬ K K_R = ∑_{a,b<R} T_{ab}²`. -/
theorem integral_kappa_mul_kTrunc (R : ℕ) :
    ∫ p, κ p.1 p.2 * kTrunc T e R p.1 p.2 ∂(ν.prod ν) = sqSum T R := by
  unfold kTrunc sqSum
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((hD.integrable_kappa_mul _ _).const_mul (T a b)).congr
      (Eventually.of_forall fun p => by simp only; ring)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ =>
    ((hD.integrable_kappa_mul _ _).const_mul (T a b)).congr
      (Eventually.of_forall fun p => by simp only; ring)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (fun p : α × α => κ p.1 p.2 * (T a b * (e (a + 1) p.1 * e (b + 1) p.2))) =
      fun p => T a b * (κ p.1 p.2 * (e (a + 1) p.1 * e (b + 1) p.2)) := by
    funext p; ring
  rw [this, integral_const_mul, ← hD.T_eq_prod, sq]

/-- `∬ K_R² = ∑_{a,b<R} T_{ab}²`. -/
theorem integral_kTrunc_sq (R : ℕ) :
    ∫ p, kTrunc T e R p.1 p.2 ^ 2 ∂(ν.prod ν) = sqSum T R := by
  have hprod : ∀ a b c d : ℕ, ∫ p : α × α, (e (a + 1) p.1 * e (b + 1) p.2) *
      (e (c + 1) p.1 * e (d + 1) p.2) ∂(ν.prod ν) =
      (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
    intro a b c d
    have : (fun p : α × α => (e (a + 1) p.1 * e (b + 1) p.2) * (e (c + 1) p.1 * e (d + 1) p.2)) =
        fun p => (e (a + 1) p.1 * e (c + 1) p.1) * (e (b + 1) p.2 * e (d + 1) p.2) := by
      funext p; ring
    rw [this, integral_prod_mul (f := fun x => e (a + 1) x * e (c + 1) x)
      (g := fun y => e (b + 1) y * e (d + 1) y), hD.orth, hD.orth]
    simp
  set S := Finset.range R ×ˢ Finset.range R
  set F : ℕ × ℕ → α × α → ℝ := fun q p => e (q.1 + 1) p.1 * e (q.2 + 1) p.2
  have hrw : ∀ p : α × α, kTrunc T e R p.1 p.2 = ∑ q ∈ S, T q.1 q.2 * F q p := fun p => by
    rw [kTrunc, Finset.sum_product]
  simp_rw [hrw]
  rw [integral_sq_sum_orth S (fun q => T q.1 q.2) F (fun q => hD.memLp_prod_e _ _) ?_]
  · rw [sqSum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [F, sq]
    rw [hprod]; simp
  · intro q _ q' _ hqq'
    simp only [F]
    rw [hprod]
    rcases q with ⟨a, b⟩; rcases q' with ⟨c, d⟩
    by_cases hac : a = c
    · subst hac
      have : b ≠ d := fun h => hqq' (by rw [h])
      simp [this]
    · simp [hac]

/-- **`‖K - K_R‖² = ‖K‖² - ∑_{a,b<R} T_{ab}²`.** -/
theorem integral_kappa_sub_kTrunc_sq (R : ℕ) :
    ∫ p, (κ p.1 p.2 - kTrunc T e R p.1 p.2) ^ 2 ∂(ν.prod ν) =
      (∫ x, ∫ y, κ x y ^ 2 ∂ν ∂ν) - sqSum T R := by
  have hK := hD.memLp_kappa
  have hKR := hD.memLp_kTrunc R
  have e1 : ∀ p : α × α, (κ p.1 p.2 - kTrunc T e R p.1 p.2) ^ 2 =
      κ p.1 p.2 ^ 2 - 2 * (κ p.1 p.2 * kTrunc T e R p.1 p.2) + kTrunc T e R p.1 p.2 ^ 2 :=
    fun p => by ring
  simp_rw [e1]
  rw [integral_add (f := fun p : α × α => κ p.1 p.2 ^ 2 - 2 * (κ p.1 p.2 * kTrunc T e R p.1 p.2))
      (g := fun p : α × α => kTrunc T e R p.1 p.2 ^ 2)
      (hK.integrable_sq.sub ((hK.integrable_mul hKR).const_mul 2)) hKR.integrable_sq,
    integral_sub (f := fun p : α × α => κ p.1 p.2 ^ 2)
      (g := fun p : α × α => 2 * (κ p.1 p.2 * kTrunc T e R p.1 p.2))
      hK.integrable_sq ((hK.integrable_mul hKR).const_mul 2), integral_const_mul,
    hD.integral_kappa_mul_kTrunc, hD.integral_kTrunc_sq, integral_prod _ hK.integrable_sq]
  ring

theorem tendsto_integral_kappa_sub_kTrunc_sq :
    Tendsto (fun R => ∫ p, (κ p.1 p.2 - kTrunc T e R p.1 p.2) ^ 2 ∂(ν.prod ν)) atTop (𝓝 0) := by
  simp_rw [hD.integral_kappa_sub_kTrunc_sq]
  have h := (tendsto_sqSum hD.hs.summable).const_sub (∫ x, ∫ y, κ x y ^ 2 ∂ν ∂ν)
  rwa [hD.hs.tsum_eq, sub_self] at h

/-- The diagonal of `K_R`. -/
theorem integrable_kTrunc_diag (R : ℕ) : Integrable (fun x => kTrunc T e R x x) ν := by
  unfold kTrunc
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((hD.eL2 _).integrable_mul (hD.eL2 _)).const_mul _

theorem integral_kTrunc_diag (R : ℕ) :
    ∫ x, kTrunc T e R x x ∂ν = ∑ a ∈ Finset.range R, T a a := by
  unfold kTrunc
  rw [integral_finsetSum (f := fun a x => ∑ b ∈ Finset.range R, T a b * (e (a + 1) x * e (b + 1) x))
    _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((hD.eL2 _).integrable_mul (hD.eL2 _)).const_mul _]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum (f := fun b x => T a b * (e (a + 1) x * e (b + 1) x)) _
    fun b _ => ((hD.eL2 _).integrable_mul (hD.eL2 _)).const_mul _]
  simp_rw [integral_const_mul, hD.orth]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba; simp [Ne.symm hba]
  · intro h; exact absurd ha h

end KerData

end kernel

end SharpLSI
