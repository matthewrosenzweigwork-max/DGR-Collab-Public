import SharpSymmetricLSI.Paper.Occ7

/-!
# The Dirichlet matrix of the occupation basis (Phase 3, lane D; R28)

`∫ ∑ᵢ ∇ᵢB_α·∇ᵢB_β dμ^{⊗N} = Λ_α δ_{αβ}`: the block gradients of the tensor products are
orthogonal, and `∫ ∇e_a·∇e_b dμ = λ_a δ_{ab}` (the eigen-equation), with `λ_0 = 0`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The block gradient `∂_{(i,k)} ∏ⱼ e_{c j}(X j)`. -/
def tensorGrad (e : ℕ → Torus d → ℝ) {N : ℕ} (c : Fin N → ℕ) (i : Fin N) (k : Fin d)
    (X : Config N d) : ℝ :=
  ∏ j, (Function.update (fun j => e (c j)) i (fun x => weakGrad (e (c i)) x k)) j (X j)

section dir
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

/-- `∑ₖ ∫ ∂ₖe_a ∂ₖe_b dμ = λ_a δ_{ab}`. -/
theorem sum_integral_grad_e (a b : ℕ) :
    ∑ k, ∫ x, weakGrad (e a) x k * weakGrad (e b) x k ∂(μ : Measure (Torus d)) =
      lam a * (if a = b then 1 else 0) := by
  rw [← integral_finsetSum (f := fun k x => weakGrad (e a) x k * weakGrad (e b) x k) _ fun k _ =>
    (memLp_grad_e hyp hμ he a k).integrable_mul (memLp_grad_e hyp hμ he b k)]
  rw [he.eigen a (e b) (he.memH1 b), he.orthonormal]

/-- `λ_0 = 0`. -/
theorem lam_zero : lam 0 = 0 := by
  have h := sum_integral_grad_e hyp hμ he 0 0
  simp only [if_true, mul_one] at h
  rw [← h]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hc : IsWeakGrad (e 0) (fun y k => fderiv ℝ (e 0 ∘ liftT) (secT y) (Pi.single k 1)) := by
    refine isWeakGrad_of_contDiff ?_
    rw [he.zero]; exact contDiff_const
  have hz : ∀ y k, fderiv ℝ (e 0 ∘ liftT) (secT y) (Pi.single k 1) = 0 := fun y k => by
    rw [he.zero]; simp [Function.comp_def]
  have hae := (minimizer_ac hyp hμ).ae_le (weakGrad_ae_eq hc)
  rw [integral_eq_zero_of_ae]
  filter_upwards [hae] with x hx
  simp [hx, hz]

/-- `∑ᵢ λ_{c i} = Λ_α` for a labelling of type `α`. -/
theorem sum_lam_labelling {α : ℕ →₀ ℕ} {N : ℕ} {c : Fin N → Fin (α.support.sup id + 2)}
    (hc : c ∈ occLabellings α N) : ∑ i, lam (c i : ℕ) = occEnergy lam α := by
  rw [← Finset.sum_fiberwise' Finset.univ c (fun ℓ => lam (ℓ : ℕ))]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, lam_zero hyp hμ he, mul_zero, zero_add, Fin.val_succ]
  have hcount : ∀ n : Fin (α.support.sup id + 1),
      ((Finset.univ.filter fun i => c i = n.succ).card : ℝ) = α n := fun n => by
    rw [← mem_occLabellings.mp hc n]
    congr 2
  simp_rw [hcount]
  rw [Fin.sum_univ_eq_sum_range (fun n => (α n : ℝ) * lam (n + 1)), occEnergy, Finsupp.sum]
  symm
  rw [Finset.sum_subset (fun n hn => Finset.mem_range.mpr (support_lt α hn)) (fun n _ hn => by
    have : α n = 0 := by simpa using hn
    simp [this])]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- One block-gradient pairing. -/
theorem integral_grad_tensor (N : ℕ) (c c' : Fin N → ℕ) (i : Fin N) (k : Fin d) :
    ∫ X : Config N d, (∏ j, (Function.update (fun j => e (c j)) i
        (fun x => weakGrad (e (c i)) x k)) j (X j)) *
      (∏ j, (Function.update (fun j => e (c' j)) i (fun x => weakGrad (e (c' i)) x k)) j (X j))
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
      (∫ x, weakGrad (e (c i)) x k * weakGrad (e (c' i)) x k ∂(μ : Measure (Torus d))) *
        ∏ j ∈ Finset.univ.erase i, (if c j = c' j then 1 else 0) := by
  rw [show (fun X : Config N d => (∏ j, (Function.update (fun j => e (c j)) i
        (fun x => weakGrad (e (c i)) x k)) j (X j)) *
      (∏ j, (Function.update (fun j => e (c' j)) i (fun x => weakGrad (e (c' i)) x k)) j (X j))) =
      fun X => ∏ j, (Function.update (fun j x => e (c j) x * e (c' j) x) i
        (fun x => weakGrad (e (c i)) x k * weakGrad (e (c' i)) x k)) j (X j) by
      funext X; rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]]
  rw [integral_fintype_prod_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), he.orthonormal]

theorem sum_grad_pair (N : ℕ) (c c' : Fin N → ℕ) :
    ∑ i, ∑ k, ∫ X : Config N d, (∏ j, (Function.update (fun j => e (c j)) i
        (fun x => weakGrad (e (c i)) x k)) j (X j)) *
      (∏ j, (Function.update (fun j => e (c' j)) i (fun x => weakGrad (e (c' i)) x k)) j (X j))
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
      (∑ i, lam (c i)) * ∏ j, (if c j = c' j then (1 : ℝ) else 0) := by
  simp_rw [integral_grad_tensor hyp hμ he]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, sum_integral_grad_e hyp hμ he, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  ring

/-- **The Dirichlet matrix of the occupation basis.** -/
theorem dirichlet_occBasis {N : ℕ} {α β : ℕ →₀ ℕ} (hα : occSize α ≤ N) (hβ : occSize β ≤ N) :
    ∫ X, ∑ i, ∑ k, weakGradC (occBasis e α N) X i k * weakGradC (occBasis e β N) X i k
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
      if α = β then occEnergy lam α else 0 := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have hac : P.map flat ≪ volume := by
    rw [← map_flat_volume N]
    exact (pi_ac_volume (minimizer_ac hyp hμ) N).map measurable_flat
  have hrep : ∀ γ : ℕ →₀ ℕ, ∀ᵐ X ∂P, ∀ i k, weakGradC (occBasis e γ N) X i k =
      occGrad e γ N (flat X) (i, k) := fun γ => by
    have h1 := hac.ae_le (weakGrad_ae_eq (isWeakGrad_occBasis hyp hμ he γ N))
    have h2 := ae_of_ae_map measurable_flat.aemeasurable h1
    filter_upwards [h2] with X hX i k
    simp only [weakGradC, hX]
  set sα := Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ))
  set sβ := Real.sqrt ((occFactorial β : ℝ) / (N.descFactorial (occSize β) : ℝ))
  have hAL : ∀ c i k, MemLp (tensorGrad e c i k) 2 P := fun c i k => memLp_prod_eval fun j => by
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact memLp_grad_e hyp hμ he _ _
    · rw [Function.update_of_ne hj]; exact he.memLp _
  have hG : ∀ (γ : ℕ →₀ ℕ) (X : Config N d) (i : Fin N) (k : Fin d), occGrad e γ N (flat X) (i, k) =
      Real.sqrt ((occFactorial γ : ℝ) / (N.descFactorial (occSize γ) : ℝ)) *
        ∑ c ∈ occLabellings γ N, tensorGrad e (fun j => (c j : ℕ)) i k X := fun _ _ _ _ => rfl
  have hexp : ∀ X, (∑ i, ∑ k, occGrad e α N (flat X) (i, k) * occGrad e β N (flat X) (i, k)) =
      sα * sβ * ∑ c ∈ occLabellings α N, ∑ c' ∈ occLabellings β N,
        ∑ i, ∑ k, tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X := by
    intro X
    have h1 : ∀ i k, occGrad e α N (flat X) (i, k) * occGrad e β N (flat X) (i, k) =
        sα * sβ * ∑ c ∈ occLabellings α N, ∑ c' ∈ occLabellings β N,
          tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X := by
      intro i k
      rw [hG α, hG β, mul_mul_mul_comm, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h1 i k]
    set T : Fin N → Fin d → ℝ := fun i k => ∑ c ∈ occLabellings α N, ∑ c' ∈ occLabellings β N,
      tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X
    rw [show (∑ i, ∑ k, sα * sβ * T i k) = sα * sβ * ∑ i, ∑ k, T i k by
      simp only [Finset.mul_sum]]
    congr 1
    simp only [T]
    calc ∑ i, ∑ k, ∑ c ∈ occLabellings α N, ∑ c' ∈ occLabellings β N,
          tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X
        = ∑ i, ∑ c ∈ occLabellings α N, ∑ k, ∑ c' ∈ occLabellings β N,
          tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c ∈ occLabellings α N, ∑ i, ∑ k, ∑ c' ∈ occLabellings β N,
          tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X :=
          Finset.sum_comm
      _ = ∑ c ∈ occLabellings α N, ∑ i, ∑ c' ∈ occLabellings β N, ∑ k,
          tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [integral_congr_ae (g := fun X => ∑ i, ∑ k, occGrad e α N (flat X) (i, k) *
      occGrad e β N (flat X) (i, k)) ((hrep α).and (hrep β) |>.mono fun X hX => by
    simp only [hX.1, hX.2])]
  simp_rw [hexp]
  rw [integral_const_mul]
  rw [integral_finsetSum (occLabellings α N) (f := fun (c : Fin N → Fin (α.support.sup id + 2)) X =>
      ∑ c' ∈ occLabellings β N, ∑ i, ∑ k,
        tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X)
    fun c _ => integrable_finsetSum _ fun c' _ => integrable_finsetSum _
    fun i _ => integrable_finsetSum _ fun k _ => (hAL _ i k).integrable_mul (hAL _ i k)]
  simp_rw [fun (c : Fin N → Fin (α.support.sup id + 2)) => integral_finsetSum (μ := P)
    (occLabellings β N) (f := fun (c' : Fin N → Fin (β.support.sup id + 2)) X =>
      ∑ i, ∑ k, tensorGrad e (fun j => (c j : ℕ)) i k X * tensorGrad e (fun j => (c' j : ℕ)) i k X)
    fun c' _ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      (hAL _ i k).integrable_mul (hAL _ i k)]
  have hpair : ∀ c c' : Fin N → ℕ, ∫ X, ∑ i, ∑ k, tensorGrad e c i k X * tensorGrad e c' i k X ∂P =
      (∑ i, lam (c i)) * ∏ j, (if c j = c' j then (1 : ℝ) else 0) := by
    intro c c'
    rw [integral_finsetSum (f := fun i X => ∑ k, tensorGrad e c i k X * tensorGrad e c' i k X) _
      fun i _ => integrable_finsetSum _ fun k _ => (hAL _ i k).integrable_mul (hAL _ i k)]
    simp_rw [fun i => integral_finsetSum (μ := P) Finset.univ
      (f := fun k X => tensorGrad e c i k X * tensorGrad e c' i k X)
      fun k _ => (hAL c i k).integrable_mul (hAL c' i k)]
    exact sum_grad_pair hyp hμ he N c c'
  simp_rw [hpair]
  split_ifs with hab
  · subst hab
    have hq := hα
    have hinner : ∀ c ∈ occLabellings α N, (∑ c' ∈ occLabellings α N,
        (∑ i, lam (c i : ℕ)) * ∏ j, (if (c j : ℕ) = (c' j : ℕ) then (1 : ℝ) else 0)) =
          occEnergy lam α := by
      intro c hc
      have : ∀ c' : Fin N → Fin (α.support.sup id + 2),
          (∏ j, (if (c j : ℕ) = (c' j : ℕ) then (1 : ℝ) else 0)) = if c = c' then 1 else 0 :=
        fun c' => by
          rw [Finset.prod_boole]
          congr 1
          apply propext
          constructor
          · intro h; exact funext fun j => Fin.ext (h j (Finset.mem_univ _))
          · intro h j _; rw [h]
      simp_rw [this, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp [hc, sum_lam_labelling hyp hμ he hc]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
    have hc := card_occLabellings α hq
    have hpos : (0 : ℝ) < N.descFactorial (occSize α) := by
      exact_mod_cast Nat.descFactorial_pos.mpr hq
    have hc' : ((occLabellings α N).card : ℝ) * occFactorial α = N.descFactorial (occSize α) := by
      exact_mod_cast hc
    have hss : sα * sα = (occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    rw [show sα * sα * ((occLabellings α N).card * occEnergy lam α) =
      (sα * sα) * (occLabellings α N).card * occEnergy lam α by ring, hss]
    field_simp
    rw [← hc']; ring
  · rw [Finset.sum_eq_zero, mul_zero]
    intro c hc
    refine Finset.sum_eq_zero fun c' hc' => ?_
    rw [Finset.prod_boole, if_neg, mul_zero]
    intro h
    apply hab
    ext n
    rw [← mem_occLabellings.mp hc n, ← mem_occLabellings.mp hc' n]
    exact congrArg Finset.card (Finset.filter_congr fun i _ => by rw [h i (Finset.mem_univ _)])

end dir

end SharpLSI
