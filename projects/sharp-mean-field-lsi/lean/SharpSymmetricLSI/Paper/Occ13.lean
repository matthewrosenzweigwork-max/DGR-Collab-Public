import SharpSymmetricLSI.Paper.Occ12
import SharpSymmetricLSI.Paper.ULimit10

/-!
# Joint Gaussian limit of the occupation basis (Phase 3, lane D; R28(d))

On the infinite product space, `B_{α,N}` is a fixed continuous function of the normalized sums
`Z_N` (CLT) and of the higher Newton coefficients and normalizations (strong law: they converge
almost surely to constants). Slutsky and the continuous mapping theorem give the joint law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology MvPolynomial Finset.HasAntidiagonal
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- The strong law on the infinite product. -/
theorem slln_infinitePi {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {h : α → ℝ} (hm : Measurable h) (hi : Integrable h ν) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν),
      Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, h (ω k)) / N) atTop (𝓝 (∫ x, h x ∂ν)) := by
  set P := Measure.infinitePi fun _ : ℕ => ν
  set X : ℕ → (ℕ → α) → ℝ := fun k ω => h (ω k)
  have hXmap : ∀ k, P.map (X k) = ν.map h := fun k => by
    rw [show X k = h ∘ fun ω => ω k from rfl, ← Measure.map_map hm (measurable_pi_apply k),
      Measure.infinitePi_map_eval]
  have hind : iIndepFun X P := iIndepFun_infinitePi (X := fun _ => h) fun _ => hm
  have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    ⟨(hm.comp (measurable_pi_apply k)).aemeasurable, (hm.comp (measurable_pi_apply 0)).aemeasurable,
      by rw [hXmap, hXmap]⟩
  have hint : Integrable (X 0) P := by
    have : Integrable h (P.map fun ω : ℕ → α => ω 0) := by
      rw [Measure.infinitePi_map_eval]; exact hi
    exact this.comp_measurable (measurable_pi_apply 0)
  have hE : ∫ ω, X 0 ω ∂P = ∫ x, h x ∂ν := by
    have h' := integral_map (μ := P) (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable
    rw [Measure.infinitePi_map_eval] at h'
    exact h'.symm
  have hslln := strong_law_ae_real X hint (fun i j hij => hind.indepFun hij) hident
  filter_upwards [hslln] with ω hω
  rw [hE] at hω
  exact hω

section emod
variable {ν : Measure (Torus d)} [IsProbabilityMeasure ν] {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis ν e lam)

/-- A measurable modification of the eigenbasis with `e 0 = 1`. -/
def emod (i : ℕ) : Torus d → ℝ :=
  if i = 0 then fun _ => 1 else (he.memLp i).aestronglyMeasurable.mk (e i)

include he in
theorem emod_zero (x : Torus d) : emod he 0 x = 1 := by simp [emod]

include he in
theorem measurable_emod (i : ℕ) : Measurable (emod he i) := by
  unfold emod; split_ifs
  · exact measurable_const
  · exact (he.memLp i).aestronglyMeasurable.stronglyMeasurable_mk.measurable

include he in
theorem emod_ae_eq (i : ℕ) : emod he i =ᵐ[ν] e i := by
  unfold emod; split_ifs with h
  · subst h; rw [he.zero]
  · exact (he.memLp i).aestronglyMeasurable.ae_eq_mk.symm

include he in
theorem memLp_emod (i : ℕ) : MemLp (emod he i) 2 ν := (he.memLp i).ae_eq (emod_ae_eq he i).symm

include he in
theorem integral_emod_mul (i j : ℕ) :
    ∫ x, emod he i x * emod he j x ∂ν = if i = j then 1 else 0 := by
  rw [← he.orthonormal i j]
  refine integral_congr_ae ?_
  filter_upwards [emod_ae_eq he i, emod_ae_eq he j] with x h1 h2
  rw [h1, h2]

include he in
theorem integral_emod_succ (i : ℕ) : ∫ x, emod he (i + 1) x ∂ν = 0 := by
  have h := integral_emod_mul he (i + 1) 0
  simp only [emod_zero, mul_one, Nat.add_one_ne_zero, ite_false] at h
  exact h

include he in
theorem occBasis_fluct_ae_eq (N : ℕ) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => ν), ∀ i (l : Fin N), emod he i (X l) = e i (X l) := by
  rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro l
  exact (measurePreserving_eval (fun _ : Fin N => ν) l).quasiMeasurePreserving.ae_eq_comp
    (emod_ae_eq he i)

end emod

/-! ### The continuous map -/

section phi
variable {K D J : ℕ} (A : Finset (ℕ →₀ ℕ))

/-- Bounded multi-indices as finitely supported functions. -/
def hatΓ (γ : Fin K → Fin (D + 1)) : Fin K →₀ ℕ := Finsupp.equivFunOnFinite.symm fun k => (γ k : ℕ)

/-- Clipping a multi-index to entries `≤ D`. -/
def clipΓ (D : ℕ) (γ : Fin K →₀ ℕ) : Fin K → Fin (D + 1) := fun k => ⟨min (γ k) D, by omega⟩

theorem hatΓ_clipΓ {γ : Fin K →₀ ℕ} (hγ : ∀ k, γ k ≤ D) : hatΓ (clipΓ D γ) = γ := by
  ext k; simp [hatΓ, clipΓ, min_eq_left (hγ k)]

/-- The rest space. -/
abbrev RestSp (K D : ℕ) (A : Finset (ℕ →₀ ℕ)) := (Fin K → (Fin K → Fin (D + 1)) → ℝ) × (A → ℝ)

/-- The input coefficients of the Newton recursion. -/
def Qmap (u : EuclideanSpace ℝ (Fin K) × RestSp K D A) (j : Fin K) (γ : Fin K →₀ ℕ) : ℝ :=
  if γ = 0 then u.1 j else u.2.1 j (clipΓ D γ)

/-- The continuous map `(Z, rest) ↦ ((B_α)_α, (Z_n)_{n<J})`. -/
def occPhi (hJK : J ≤ K) (u : EuclideanSpace ℝ (Fin K) × RestSp K D A) : (A → ℝ) × (Fin J → ℝ) :=
  (fun α => Real.sqrt (occFactorial (α : ℕ →₀ ℕ)) * u.2.2 α *
    newtonRec (Qmap A u) D (finK K α), fun n => u.1 (Fin.castLE hJK n))

theorem continuous_occPhi (hJK : J ≤ K) : Continuous (occPhi (D := D) A hJK) := by
  refine Continuous.prodMk (continuous_pi fun α => ?_) (continuous_pi fun n => ?_)
  · refine (continuous_const.mul ((continuous_apply α).comp (continuous_snd.comp continuous_snd))).mul
      (continuous_newtonRec (fun j γ => ?_) _ _)
    unfold Qmap
    split_ifs
    · exact (PiLp.continuous_apply 2 _ j).comp continuous_fst
    · show Continuous fun u : EuclideanSpace ℝ (Fin K) × RestSp K D A => u.2.1 j (clipΓ D γ)
      fun_prop
  · exact (PiLp.continuous_apply 2 _ _).comp continuous_fst

/-- The Newton coefficients of the sample. -/
def qN {T : Type*} (f : Fin K → T → ℝ) (N : ℕ) (ω : ℕ → T) (j : Fin K) (γ : Fin K →₀ ℕ) : ℝ :=
  (Real.sqrt N)⁻¹ ^ (γ.degree + 1) * newtonCoeff (fun (i : Fin N) k => f k (ω i)) j γ

/-- The rest data of the sample. -/
def restN {T : Type*} (f : Fin K → T → ℝ) (N : ℕ) (ω : ℕ → T) : RestSp K D A :=
  (fun j γ => if hatΓ γ = 0 then 0 else qN f N ω j (hatΓ γ),
    fun α => Real.sqrt N ^ occSize (α : ℕ →₀ ℕ) /
      Real.sqrt (N.descFactorial (occSize (α : ℕ →₀ ℕ))))

/-- The limit of the rest data. -/
def restInf : RestSp K D A :=
  (fun j γ => if hatΓ γ = 0 then 0 else qLim 0 j (hatΓ γ), fun _ => 1)

variable {A}

theorem degree_lt_le {α' γ : Fin K →₀ ℕ} (hγ : γ.degree < α'.degree) (hα : α'.degree ≤ D) (k : Fin K) :
    γ k ≤ D := by
  have : γ k ≤ γ.degree := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (f := fun k => γ k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

/-- **Pathwise identity.** -/
theorem occPhi_pathwise (hJK : J ≤ K) (hA : ∀ α ∈ A, ∀ n, K ≤ n → α n = 0)
    (hD : ∀ α ∈ A, occSize α ≤ D) {e0 : ℕ → Torus d → ℝ} (he0 : ∀ x, e0 0 x = 1) {N : ℕ}
    (hN : 1 ≤ N) (ω : ℕ → Torus d) :
    occPhi A hJK (cltVec (fun k : Fin K => e0 (k + 1)) N ω,
        restN A (D := D) (fun k : Fin K => e0 (k + 1)) N ω) =
      (fun α : A => occBasis e0 α N (fun i => ω i), fun n : Fin J => fluct e0 N n (fun i => ω i)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  refine Prod.ext (funext fun α => ?_) (funext fun n => ?_)
  · obtain ⟨α, hαA⟩ := α
    simp only [occPhi]
    set a : Fin N → Fin K → ℝ := fun i k => e0 (k + 1) (ω i)
    have hdeg := degree_finK α (hA α hαA)
    have hcongr : newtonRec (Qmap A (cltVec (fun k : Fin K => e0 (k + 1)) N ω,
        restN A (D := D) (fun k : Fin K => e0 (k + 1)) N ω)) D (finK K α) =
        newtonRec (fun j γ => (Real.sqrt N)⁻¹ ^ (γ.degree + 1) * newtonCoeff a j γ) D (finK K α) := by
      refine newtonRec_congr _ _ fun j γ hγ => ?_
      unfold Qmap
      split_ifs with h0
      · subst h0
        simp only [cltVec, PiLp.toLp_apply, map_zero, zero_add, pow_one, newtonCoeff_zero, a]
        rw [Fin.sum_univ_eq_sum_range (fun i => e0 (j + 1) (ω i))]
      · simp only [restN]
        rw [hatΓ_clipΓ (degree_lt_le hγ (hdeg ▸ hD α hαA))]
        simp only [h0, ↓reduceIte]
        rfl
    rw [hcongr, newtonRec_scaled _ _ _ _ (hdeg ▸ hD α hαA), hdeg]
    unfold occBasis
    rw [labelling_sum_eq_coeff e0 he0 α (hA α hαA) (fun i => ω i)]
    simp only [restN]
    rw [Real.sqrt_div' _ (Nat.cast_nonneg _)]
    have h1 : Real.sqrt N ^ occSize α * (Real.sqrt N)⁻¹ ^ occSize α = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hsN, one_pow]
    calc Real.sqrt (occFactorial α) * (Real.sqrt N ^ occSize α /
          Real.sqrt (N.descFactorial (occSize α))) *
          ((Real.sqrt N)⁻¹ ^ occSize α * (genPoly a).coeff (finK K α))
        = Real.sqrt (occFactorial α) / Real.sqrt (N.descFactorial (occSize α)) *
          (Real.sqrt N ^ occSize α * (Real.sqrt N)⁻¹ ^ occSize α) *
          (genPoly a).coeff (finK K α) := by ring
      _ = _ := by rw [h1, mul_one]
  · simp only [occPhi, cltVec, PiLp.toLp_apply, fluct, Fin.val_castLE]
    rw [Real.rpow_neg (Nat.cast_nonneg N), ← Real.sqrt_eq_rpow,
      Fin.sum_univ_eq_sum_range (fun i => e0 (n + 1) (ω i))]

/-- **The limit identity.** -/
theorem occPhi_limit (hJK : J ≤ K) (hA : ∀ α ∈ A, ∀ n, K ≤ n → α n = 0)
    (hD : ∀ α ∈ A, occSize α ≤ D) (z : ℕ → ℝ) :
    occPhi A hJK (gaussVec K z, restInf A (K := K) (D := D)) =
      (fun α : A => hermiteBasis α z, fun n : Fin J => z n) := by
  refine Prod.ext (funext fun α => ?_) (funext fun n => ?_)
  · obtain ⟨α, hαA⟩ := α
    simp only [occPhi]
    have hdeg := degree_finK α (hA α hαA)
    have hcongr : newtonRec (Qmap A (gaussVec K z, restInf A (K := K) (D := D))) D (finK K α) =
        newtonRec (qLim fun k : Fin K => z k) D (finK K α) := by
      refine newtonRec_congr _ _ fun j γ hγ => ?_
      unfold Qmap
      split_ifs with h0
      · subst h0; simp [gaussVec, qLim]
      · simp only [restInf]
        rw [hatΓ_clipΓ (degree_lt_le hγ (hdeg ▸ hD α hαA))]
        simp only [h0, ↓reduceIte]
        simp [qLim, h0]
    rw [hcongr, newtonRec_eq (hermLim_zero _) (hermLim_rec _) _ _ (hdeg ▸ hD α hαA),
      hermiteBasis_eq_hermLim α (hA α hαA)]
    simp [restInf]
  · simp [occPhi, gaussVec]

end phi

theorem eq_single_of_degree_eq_one {K : ℕ} {γ : Fin K →₀ ℕ} (h : γ.degree = 1) :
    ∃ k, γ = Finsupp.single k 1 := by
  have hne : γ ≠ 0 := by rintro rfl; simp at h
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single k 1 ≤ γ := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)
  refine ⟨k, ?_⟩
  have h2 := tsub_add_cancel_of_le hle
  have h3 : (γ - Finsupp.single k 1).degree = 0 := by
    have := congrArg Finsupp.degree h2
    rw [map_add, Finsupp.degree_single, h] at this
    omega
  rw [(Finsupp.degree_eq_zero_iff _).mp h3, zero_add] at h2
  exact h2.symm

/-! ### Assembly -/

section assembly
variable {ν : Measure (Torus d)} [IsProbabilityMeasure ν] {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis ν e lam)
include he

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Joint convergence in law of the occupation basis and the fluctuations.** -/
theorem tendsto_occBasis_joint (A : Finset (ℕ →₀ ℕ)) (J : ℕ)
    (g : (A → ℝ) × (Fin J → ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ X, g (fun α => occBasis e α N X, fun n => fluct e N n X)
        ∂Measure.pi (fun _ : Fin N => ν)) atTop
      (𝓝 (∫ z, g (fun α => hermiteBasis α z, fun n => z n) ∂gammaRef)) := by
  set K := J + ∑ α ∈ A, (α.support.sup id + 1)
  set D := ∑ α ∈ A, occSize α
  have hJK : J ≤ K := Nat.le_add_right _ _
  have hA : ∀ α ∈ A, ∀ n, K ≤ n → α n = 0 := fun α hα n hn => by
    by_contra h
    have h1 : n ≤ α.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)
    have h2 : α.support.sup id + 1 ≤ ∑ α ∈ A, (α.support.sup id + 1) :=
      Finset.single_le_sum (f := fun α : ℕ →₀ ℕ => α.support.sup id + 1) (fun _ _ => Nat.zero_le _) hα
    omega
  have hD : ∀ α ∈ A, occSize α ≤ D := fun α hα =>
    Finset.single_le_sum (f := occSize) (fun _ _ => Nat.zero_le _) hα
  set f : Fin K → Torus d → ℝ := fun k => emod he (k + 1)
  set P := Measure.infinitePi fun _ : ℕ => ν
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_emod he _
  have hfL : ∀ k, MemLp (f k) 2 ν := fun k => memLp_emod he _
  -- the CLT
  have hclt : TendstoInDistribution (cltVec f) atTop (gaussVec K) (fun _ => P) gammaRef :=
    tendstoInDistribution_cltVec hfm hfL (fun k => integral_emod_succ he _) fun a b => by
      simp only [f]; rw [integral_emod_mul]
      by_cases h : a = b
      · simp [h]
      · have : (a : ℕ) ≠ b := fun h' => h (Fin.ext h')
        simp [h, this]
  -- measurability of the rest data
  have hmeasA : ∀ N, Measurable fun ω : ℕ → Torus d => fun (i : Fin N) (k : Fin K) => f k (ω i) :=
    fun N => measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k =>
      (hfm k).comp (measurable_pi_apply _)
  have hrm : ∀ N, Measurable (restN A (D := D) f N) := fun N => by
    refine Measurable.prodMk (measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun γ => ?_)
      measurable_const
    by_cases h : hatΓ γ = 0
    · simp only [h, ite_true]; exact measurable_const
    · simp only [h, ite_false, qN]
      exact ((continuous_newtonCoeff j _).measurable.comp (hmeasA N)).const_mul _
  -- the strong laws
  set gs : Torus d → ℝ := fun x => ∑ k, |f k x|
  have hgsL : MemLp gs 2 ν := memLp_finsetSum _ fun k _ => (hfL k).abs
  have hgsm : Measurable gs := Finset.measurable_sum _ fun k _ => (hfm k).abs
  have hE1 : ∀ᵐ ω ∂P, ∀ jk : Fin K × Fin K, Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, f jk.1 (ω i) * f jk.2 (ω i)) / N) atTop
        (𝓝 (∫ x, f jk.1 x * f jk.2 x ∂ν)) := by
    rw [ae_all_iff]; intro jk
    exact slln_infinitePi ((hfm _).mul (hfm _)) ((hfL _).integrable_mul (hfL _))
  have hE2 : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, gs (ω i) ^ 2) / N) atTop
      (𝓝 (∫ x, gs x ^ 2 ∂ν)) :=
    slln_infinitePi (hgsm.pow_const 2) hgsL.integrable_sq
  have hrest : ∀ᵐ ω ∂P, Tendsto (fun N => restN A (D := D) f N ω) atTop
      (𝓝 (restInf A (K := K) (D := D))) := by
    filter_upwards [hE1, hE2] with ω h1 h2
    refine Tendsto.prodMk_nhds (tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun γ => ?_)
      (tendsto_pi_nhds.mpr fun α => tendsto_kappa _)
    show Tendsto (fun N => (if hatΓ γ = 0 then (0 : ℝ) else qN f N ω j (hatΓ γ))) atTop
      (𝓝 (if hatΓ γ = 0 then 0 else qLim 0 j (hatΓ γ)))
    by_cases h0 : hatΓ γ = 0
    · simp only [h0, ite_true]; exact tendsto_const_nhds
    simp only [h0, ite_false]
    set γ' := hatΓ γ
    have hdeg0 : γ'.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    rcases Nat.lt_or_ge γ'.degree 2 with hlt | hge
    · obtain ⟨k, hk⟩ := eq_single_of_degree_eq_one (show γ'.degree = 1 by omega)
      rw [hk]
      have hlim := (h1 (j, k)).neg
      have hq : ∀ N : ℕ, 1 ≤ N → qN f N ω j (Finsupp.single k 1) =
          -((∑ i ∈ Finset.range N, f j (ω i) * f k (ω i)) / N) := fun N hN => by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        simp only [qN, Finsupp.degree_single, newtonCoeff_single]
        rw [Fin.sum_univ_eq_sum_range (fun i => f j (ω i) * f k (ω i)), inv_pow,
          Real.sq_sqrt hNpos.le]
        ring
      have hval : qLim 0 j (Finsupp.single k 1) = -∫ x, f j x * f k x ∂ν := by
        simp only [f]
        rw [integral_emod_mul]
        by_cases hjk : j = k
        · subst hjk; simp [qLim]
        · have h'' : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
          have hs : Finsupp.single k 1 ≠ Finsupp.single j 1 := fun hs =>
            hjk ((Finsupp.single_left_inj one_ne_zero).mp hs).symm
          simp [qLim, hs, h'']
      rw [hval]
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hq N hN]
    · have hval : qLim 0 j γ' = 0 := by
        have hs : γ' ≠ Finsupp.single j 1 := fun hs => by
          rw [hs, Finsupp.degree_single] at hge; omega
        simp [qLim, h0, hs]
      rw [hval]
      have hsum := tendsto_sum_pow_of_mean_sq (v := fun i => gs (ω i))
        (fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _) h2 (p := γ'.degree + 1) (by omega)
      refine squeeze_zero_norm' ?_ hsum
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Real.norm_eq_abs]
      simp only [qN]
      rw [abs_mul, abs_pow, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      calc (Real.sqrt N)⁻¹ ^ (γ'.degree + 1) *
            |newtonCoeff (fun (i : Fin N) k => f k (ω i)) j γ'|
          ≤ (Real.sqrt N)⁻¹ ^ (γ'.degree + 1) *
            ∑ i : Fin N, (∑ k, |f k (ω i)|) ^ (γ'.degree + 1) :=
            mul_le_mul_of_nonneg_left (abs_newtonCoeff_le _ _ _) (by positivity)
        _ = ∑ i ∈ Finset.range N, ((Real.sqrt N)⁻¹ * gs (ω i)) ^ (γ'.degree + 1) := by
            rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range
              (fun i => (Real.sqrt N)⁻¹ ^ (γ'.degree + 1) * (∑ k, |f k (ω i)|) ^ (γ'.degree + 1))]
            simp only [mul_pow, gs]
  -- Slutsky
  have hR : TendstoInMeasure P (fun N => restN A (D := D) f N) atTop
      (fun _ => restInf A (K := K) (D := D)) :=
    tendstoInMeasure_of_tendsto_ae (fun N => (hrm N).aestronglyMeasurable) hrest
  have hdist := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const (continuous_occPhi A hJK) hR
    (fun N => (hrm N).aemeasurable)
  have h := TendstoInDistribution.tendsto_integral_bcf hdist g
  simp_rw [occPhi_limit hJK hA hD] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpw : ∀ ω : ℕ → Torus d, occPhi A hJK (cltVec f N ω, restN A (D := D) f N ω) =
      (fun α : A => occBasis (emod he) α N (fun i => ω i),
        fun n : Fin J => fluct (emod he) N n (fun i => ω i)) :=
    fun ω => occPhi_pathwise hJK hA hD (emod_zero he) hN ω
  simp_rw [hpw]
  -- transfer to the finite product
  set G : Config N d → ℝ := fun X =>
    g (fun α : A => occBasis (emod he) α N X, fun n : Fin J => fluct (emod he) N n X)
  have hGm : Measurable G := by
    refine g.continuous.measurable.comp (Measurable.prodMk (measurable_pi_iff.mpr fun α => ?_)
      (measurable_pi_iff.mpr fun n => ?_))
    · unfold occBasis
      exact (Finset.measurable_sum _ fun c _ => Finset.measurable_prod _ fun i _ =>
        (measurable_emod he _).comp (measurable_pi_apply i)).const_mul _
    · unfold fluct
      exact (Finset.measurable_sum _ fun l _ =>
        (measurable_emod he _).comp (measurable_pi_apply l)).const_mul _
  have hrestr : Measurable fun (ω : ℕ → Torus d) (i : Fin N) => ω i := by fun_prop
  have e1 := integral_map (μ := P) hrestr.aemeasurable hGm.aestronglyMeasurable
  rw [infinitePi_map_fin ν N] at e1
  change ∫ ω, G (fun i : Fin N => ω i) ∂P = _
  rw [← e1]
  refine integral_congr_ae ?_
  filter_upwards [occBasis_fluct_ae_eq he N] with X hX
  simp only [G]
  congr 2
  · funext α
    unfold occBasis
    congr 1
    exact Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => hX _ _
  · funext n
    unfold fluct
    congr 1
    exact Finset.sum_congr rfl fun l _ => hX _ _

end assembly

end SharpLSI
