import SharpSymmetricLSI.Paper.CondForce1
import SharpSymmetricLSI.Paper.ForceExp

/-!
# Lemma 5.4, reduction (Phase 3, lane D; R21)

Conditional Jensen removes the conditional expectation, and a.e. (under `ν ≪ μ^{⊗N}`) the
force `B_j` and the particle force agree with their versions built from the bounded field
`b̃(x,y) = ∇₁W(x,y) - β(x)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `ℱ_j ∨ σ(X_{j+1})` (a copy of `pastAndNext` from the R21 statement file). -/
abbrev pastNextSA {N : ℕ} (j : ℕ) (hj : j < N) : MeasurableSpace (Config N d) :=
  MeasurableSpace.comap (fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩)) inferInstance

/-- The summand of (5.17) (a copy of `forceComparisonTerm` from the R21 statement file). -/
noncomputable def fcTerm (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    {N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (j : ℕ) : ℝ :=
  if hj : j < N then
    ∫ X, ∑ k, (condForce W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k -
      (ν[fun Y => weakGradC (Ucentered W μ N) Y ⟨j, hj⟩ k | pastNextSA j hj]) X) ^ 2 ∂ν
  else 0

/-- `∫ (E[F|m])² ≤ ∫ F²`. -/
theorem integral_sq_condExp_le {Ω : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Measure[m₀] Ω} [IsProbabilityMeasure P] {F : Ω → ℝ} (hF : MemLp F 2 P) :
    ∫ ω, (P[F | m] ω) ^ 2 ∂P ≤ ∫ ω, F ω ^ 2 ∂P := by
  have h0 : 0 ≤ᵐ[P] Var[F; P | m] := by
    unfold condVar
    exact condExp_nonneg (Eventually.of_forall fun ω => by simp only [Pi.zero_apply, Pi.pow_apply]; positivity)
  have h1 : ∀ᵐ ω ∂P, (P[F | m] ω) ^ 2 ≤ (P[F ^ 2 | m]) ω := by
    filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hF, h0] with ω hω h0ω
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply] at hω h0ω
    linarith
  calc ∫ ω, (P[F | m] ω) ^ 2 ∂P ≤ ∫ ω, (P[F ^ 2 | m]) ω ∂P :=
        integral_mono_ae (hF.condExp one_le_two).integrable_sq integrable_condExp h1
    _ = ∫ ω, F ω ^ 2 ∂P := by rw [integral_condExp hm]; rfl

/-- Conditional Jensen for an `m`-measurable center: `∫ (B - E[G|m])² ≤ ∫ (B - G)²`. -/
theorem integral_sq_sub_condExp_le {Ω : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Measure[m₀] Ω} [IsProbabilityMeasure P] {B G : Ω → ℝ} (hBm : StronglyMeasurable[m] B)
    (hB : MemLp B 2 P) (hG : MemLp G 2 P) :
    ∫ ω, (B ω - P[G | m] ω) ^ 2 ∂P ≤ ∫ ω, (B ω - G ω) ^ 2 ∂P := by
  have hBi := hB.integrable one_le_two
  have hGi := hG.integrable one_le_two
  have he : (fun ω => B ω - P[G | m] ω) =ᵐ[P] P[B - G | m] := by
    filter_upwards [condExp_sub hBi hGi m] with ω hω
    rw [hω, Pi.sub_apply, condExp_of_stronglyMeasurable hm hBm hBi]
  calc ∫ ω, (B ω - P[G | m] ω) ^ 2 ∂P = ∫ ω, (P[B - G | m] ω) ^ 2 ∂P :=
        integral_congr_ae (he.mono fun ω hω => by simp only [hω])
    _ ≤ ∫ ω, (B - G) ω ^ 2 ∂P := integral_sq_condExp_le hm (hB.sub hG)
    _ = _ := rfl

/-- The bounded off-diagonal field `b̃(x,y) = ∇₁W(x,y) - β(x)`. -/
def bfixF (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (x y : Torus d) (k : Fin d) : ℝ :=
  bGrad W x y k - bForceL W (densOf μ) x k

/-- `B̃_j(p, x) = ∫ b̃(x,y) dρ_j(p)(y)`. -/
def BfixF (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (ν : Measure (Config N d))
    [IsFiniteMeasure ν] (j : ℕ) (hj : j < N) (p : Fin j → Torus d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, bfixF W μ x y k ∂condNext ν j hj p

/-- `∇_jU_N` in closed form (5.12). -/
def GfixF (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (j : Fin N) (X : Config N d)
    (k : Fin d) : ℝ :=
  (N : ℝ)⁻¹ * ((∑ l ∈ Finset.univ.erase j, bfixF W μ (X j) (X l) k) +
    -bForceL W (densOf μ) (X j) k)

section bounds
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
include hyp hac

theorem bfixF_props : (∀ k, Measurable (Function.uncurry fun x y => bfixF W μ x y k)) ∧
    ∃ M, 0 ≤ M ∧ (∀ x y k, |bfixF W μ x y k| ≤ M) ∧ (∀ x k, |bForceL W (densOf μ) x k| ≤ M) ∧
      (∀ x k, ∫ y, bfixF W μ x y k ∂μ = 0) := by
  obtain ⟨-, hβm, ⟨Cβ, hCβ⟩, hβint⟩ := forceMean_props hyp hac
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  obtain ⟨x0⟩ : Nonempty (Torus d) := inferInstance
  refine ⟨fun k => (measurable_bGrad hyp (W := W) k).sub ((hβm k).comp measurable_fst),
    |Cb| + |Cβ|, by positivity, fun x y k => ?_, fun x k => ?_, fun x k => ?_⟩
  · exact (abs_sub _ _).trans (add_le_add ((hCb x y k).trans (le_abs_self _))
      ((hCβ x k).trans (le_abs_self _)))
  · exact ((hCβ x k).trans (le_abs_self _)).trans (le_add_of_nonneg_left (abs_nonneg _))
  · have hbi : Integrable (fun y => bGrad W x y k) μ :=
      integrable_of_bdd (measurable_bGrad hyp (W := W) k).of_uncurry_left (fun y => hCb x y k)
    unfold bfixF
    rw [integral_sub hbi (integrable_const _), integral_const, hβint x k]
    simp

end bounds

theorem measurable_BfixF (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N)
    (k : Fin d) : Measurable (Function.uncurry fun p x => BfixF W μ ν j hj p x k) := by
  have hp : Measurable fun q : ((Fin j → Torus d) × Torus d) × Torus d => (q.1.2, q.2) := by
    fun_prop
  have hf := Measurable.comp (g := Function.uncurry fun x y => bfixF W μ x y k) ((bfixF_props hyp hac).1 k) hp
  have := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (condNext ν j hj).comap Prod.fst measurable_fst)
  convert this.measurable using 1
  funext q
  rw [Kernel.comap_apply]
  rfl

theorem abs_BfixF_le (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) {M : ℝ} (hM : ∀ x y k, |bfixF W μ x y k| ≤ M) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N) (p : Fin j → Torus d) (x : Torus d) (k : Fin d) :
    |BfixF W μ ν j hj p x k| ≤ M :=
  abs_integral_le_of_bdd fun y => hM x y k

theorem abs_GfixF_le {μ : Measure (Torus d)} {M : ℝ} (hM : ∀ x y k, |bfixF W μ x y k| ≤ M)
    (hMβ : ∀ x k, |bForceL W (densOf μ) x k| ≤ M) (j : Fin N) (X : Config N d) (k : Fin d) :
    |GfixF W μ j X k| ≤ M := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos j
  unfold GfixF
  rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
  have h1 : |(∑ l ∈ Finset.univ.erase j, bfixF W μ (X j) (X l) k) + -bForceL W (densOf μ) (X j) k|
      ≤ N * M := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    have h2 : |∑ l ∈ Finset.univ.erase j, bfixF W μ (X j) (X l) k| ≤ ((N : ℝ) - 1) * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ M fun l _ => hM _ _ _).trans (le_of_eq ?_)
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (Fin.pos j)]
      simp
    linarith [hMβ (X j) k]
  calc (N : ℝ)⁻¹ * |_| ≤ (N : ℝ)⁻¹ * (N * M) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = M := by field_simp

theorem measurable_pair_comp {F : Torus d → Torus d → ℝ} (hF : Measurable (Function.uncurry F))
    (j l : Fin N) : Measurable fun X : Config N d => F (X j) (X l) := by
  have hp : Measurable fun X : Config N d => (X j, X l) := by fun_prop
  exact hF.comp hp

theorem measurable_GfixF (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) (j : Fin N) (k : Fin d) : Measurable fun X : Config N d => GfixF W μ j X k := by
  obtain ⟨-, hβm, -, -⟩ := forceMean_props hyp hac
  have h1 : ∀ l, Measurable fun X : Config N d => bfixF W μ (X j) (X l) k := fun l =>
    measurable_pair_comp (F := fun x y => bfixF W μ x y k) ((bfixF_props hyp hac).1 k) j l
  have h2 : Measurable fun X : Config N d => bForceL W (densOf μ) (X j) k :=
    (hβm k).comp (measurable_pi_apply j)
  exact measurable_const.mul ((Finset.measurable_sum _ fun l _ => h1 l).add h2.neg)

/-- `B_j = B̃_j` a.e. -/
theorem condForce_ae_eq (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hνac : ν ≪ Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) {j : ℕ} (hj : j < N) :
    ∀ᵐ X ∂ν, ∀ k, condForce W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k =
      BfixF W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k := by
  have hac := minimizer_ac hyp hμ
  have hgood := Measure.ae_ae_of_ae_prod (bForce_ae_prod hyp hac)
  have h1 : ∀ᵐ X ∂ν, ∀ᵐ y ∂haar d, ∀ k, bForce W μ (X ⟨j, hj⟩) y k =
      bGrad W (X ⟨j, hj⟩) y k - bForceL W (densOf (μ : Measure (Torus d))) (X ⟨j, hj⟩) k := by
    have h := (measurePreserving_eval (fun _ : Fin N => (μ : Measure (Torus d))) ⟨j, hj⟩
      ).quasiMeasurePreserving.ae (hac.ae_le hgood)
    exact hνac.ae_le h
  have h2 : ∀ᵐ X ∂ν, condNext ν j hj (past j hj.le X) ≪ μ :=
    ae_of_ae_map (measurable_past _).aemeasurable (condNext_ac _ ν hνac hj)
  filter_upwards [h1, h2] with X hX1 hX2 k
  unfold condForce BfixF bfixF
  refine integral_congr_ae ?_
  filter_upwards [(hX2.trans hac).ae_le hX1] with y hy
  exact hy k

/-- `∇_jU_N = G̃_j` a.e. -/
theorem weakGradC_ae_eq_GfixF (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (ν : Measure (Config N d))
    (hνac : ν ≪ Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (j : Fin N) :
    ∀ᵐ X ∂ν, ∀ k, weakGradC (Ucentered W μ N) X j k = GfixF W μ j X k := by
  have hac := minimizer_ac hyp hμ
  filter_upwards [hνac.ae_le (weakGradC_Ucentered_ae hyp hac (Fin.pos j))] with X hX k
  rw [hX j k]; rfl

/-- **Reduction by conditional Jensen.** -/
theorem fcTerm_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hνac : ν ≪ Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) {j : ℕ} (hj : j < N) :
    fcTerm W μ ν j ≤ ∫ X, ∑ k, (BfixF W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k -
      GfixF W μ ⟨j, hj⟩ X k) ^ 2 ∂ν := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨-, M, -, hM, hMβ, -⟩ := bfixF_props hyp hac
  have hf : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
    (measurable_past _).prodMk (measurable_pi_apply _)
  have hm : pastNextSA (d := d) j hj ≤ MeasurableSpace.pi := measurable_iff_comap_le.mp hf
  set B : Fin d → Config N d → ℝ := fun k X => BfixF W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k
    with hBdef
  set G : Fin d → Config N d → ℝ := fun k X => GfixF W μ ⟨j, hj⟩ X k with hGdef
  have hBm : ∀ k, StronglyMeasurable[pastNextSA j hj] (B k) := fun k =>
    ((measurable_BfixF hyp hac ν hj k).comp (comap_measurable _)).stronglyMeasurable
  have hBL : ∀ k, MemLp (B k) 2 ν := fun k =>
    MemLp.of_bound ((hBm k).mono hm).aestronglyMeasurable M (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact abs_BfixF_le hyp hac hM ν hj _ _ k)
  have hGL : ∀ k, MemLp (G k) 2 ν := fun k =>
    MemLp.of_bound (measurable_GfixF hyp hac _ k).aestronglyMeasurable M
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact abs_GfixF_le hM hMβ _ X k)
  have hce : ∀ k, ν[fun Y => weakGradC (Ucentered W μ N) Y ⟨j, hj⟩ k | pastNextSA j hj] =ᵐ[ν]
      ν[G k | pastNextSA j hj] := fun k =>
    condExp_congr_ae ((weakGradC_ae_eq_GfixF hyp hμ ν hνac ⟨j, hj⟩).mono fun X hX => hX k)
  unfold fcTerm
  rw [dif_pos hj]
  have e1 : (fun X => ∑ k, (condForce W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k -
      (ν[fun Y => weakGradC (Ucentered W μ N) Y ⟨j, hj⟩ k | pastNextSA j hj]) X) ^ 2) =ᵐ[ν]
      fun X => ∑ k, (B k X - ν[G k | pastNextSA j hj] X) ^ 2 := by
    filter_upwards [condForce_ae_eq hyp hμ ν hνac hj, ae_all_iff.mpr hce] with X h1 h2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1 k, h2 k]
  rw [integral_congr_ae e1, integral_finset_sum (f := fun k X => (B k X -
      ν[G k | pastNextSA j hj] X) ^ 2) _ fun k _ =>
      ((hBL k).sub ((hGL k).condExp one_le_two)).integrable_sq,
    integral_finset_sum (f := fun k X => (B k X - G k X) ^ 2) _ fun k _ =>
      ((hBL k).sub (hGL k)).integrable_sq]
  exact Finset.sum_le_sum fun k _ => integral_sq_sub_condExp_le hm (hBm k) (hBL k) (hGL k)

end SharpLSI
