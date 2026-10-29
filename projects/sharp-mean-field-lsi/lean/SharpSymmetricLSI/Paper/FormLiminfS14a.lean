import SharpSymmetricLSI.Paper.FormLiminf8
import SharpSymmetricLSI.Paper.TestEnergy7
import SharpSymmetricLSI.Paper.TestEnergy8

/-!
# R33 cross term (S14a): bounded measurable pieces of the particle generator

For fixed `N`, every ingredient of `genL` (the fluctuations `zC`, `∂_iφ(zC)`, its derivatives,
the mobility `mobA`, the force `forceD`) is a bounded measurable function of the configuration.
Hence `f · g` is integrable for `f ∈ L²` and any such `g` (`integrable_mul_of_bddMeas`).
-/

open MeasureTheory Filter Topology

namespace SharpLSI

variable {d : ℕ}

/-- `g` is measurable and bounded. -/
def BddMeas {α : Type*} [MeasurableSpace α] (g : α → ℝ) : Prop :=
  Measurable g ∧ ∃ M, ∀ x, |g x| ≤ M

section bdd
variable {α : Type*} [MeasurableSpace α]

theorem BddMeas.const (a : ℝ) : BddMeas fun _ : α => a := ⟨measurable_const, |a|, fun _ => le_rfl⟩

theorem BddMeas.add {g h : α → ℝ} (hg : BddMeas g) (hh : BddMeas h) :
    BddMeas fun x => g x + h x := by
  obtain ⟨hgm, Mg, hMg⟩ := hg; obtain ⟨hhm, Mh, hMh⟩ := hh
  exact ⟨hgm.add hhm, Mg + Mh, fun x => (abs_add_le _ _).trans (add_le_add (hMg x) (hMh x))⟩

theorem BddMeas.neg {g : α → ℝ} (hg : BddMeas g) : BddMeas fun x => -g x := by
  obtain ⟨hgm, Mg, hMg⟩ := hg
  exact ⟨hgm.neg, Mg, fun x => by rw [abs_neg]; exact hMg x⟩

theorem BddMeas.sub {g h : α → ℝ} (hg : BddMeas g) (hh : BddMeas h) :
    BddMeas fun x => g x - h x := by
  simpa [sub_eq_add_neg] using hg.add hh.neg

theorem BddMeas.mul {g h : α → ℝ} (hg : BddMeas g) (hh : BddMeas h) :
    BddMeas fun x => g x * h x := by
  obtain ⟨hgm, Mg, hMg⟩ := hg; obtain ⟨hhm, Mh, hMh⟩ := hh
  refine ⟨hgm.mul hhm, Mg * Mh, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hMg x) (hMh x) (abs_nonneg _) ((abs_nonneg _).trans (hMg x))

theorem BddMeas.sum {ι : Type*} (s : Finset ι) {g : ι → α → ℝ} (hg : ∀ i ∈ s, BddMeas (g i)) :
    BddMeas fun x => ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BddMeas.const (α := α) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- `f · g` is integrable for `f ∈ L²` (finite measure) and `g` bounded measurable. -/
theorem integrable_mul_of_bddMeas {P : Measure α} [IsFiniteMeasure P] {f g : α → ℝ}
    (hf : MemLp f 2 P) (hg : BddMeas g) : Integrable (fun x => f x * g x) P := by
  obtain ⟨hgm, M, hM⟩ := hg
  have h := (hf.integrable one_le_two).bdd_mul (c := M) hgm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  exact h.congr (Eventually.of_forall fun x => by simp [mul_comm])

end bdd

section fixedN
variable {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (N : ℕ)
include hφ

theorem bddMeas_eCsum (q : ℕ) :
    BddMeas fun X : Config N d => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l) := by
  obtain ⟨Ce, hCe⟩ := exists_bound_of_contDiff (hφ (q + 1))
  refine (BddMeas.const _).mul (BddMeas.sum _ fun l _ =>
    ⟨(measurable_of_contDiff (hφ _)).comp (measurable_pi_apply l), Ce, fun X => hCe _⟩)

theorem measurable_zC (J : ℕ) : Measurable fun X : Config N d => zC eC N J X :=
  measurable_pi_iff.2 fun i => (bddMeas_eCsum hφ N i).1

theorem bddMeas_comp_zC {J : ℕ} {ψ : (Fin J → ℝ) → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) : BddMeas fun X : Config N d => ψ (zC eC N J X) := by
  obtain ⟨K, -, hK⟩ := exists_bound_of_compact hψ hc
  exact ⟨hψ.measurable.comp (measurable_zC hφ N J), K, fun X => hK _⟩

theorem bddMeas_mobA (i j : ℕ) : BddMeas fun X : Config N d => mobA eC N X i j := by
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  obtain ⟨Cj, hCj⟩ := exists_bound_cgrad (hφ (j + 1))
  refine ⟨measurable_mobA hφ N i j, ?_⟩
  have h : BddMeas fun X : Config N d => (N : ℝ)⁻¹ * ∑ l, ∑ k,
      cgrad (eC (i + 1)) (X l) k * cgrad (eC (j + 1)) (X l) k :=
    (BddMeas.const _).mul (BddMeas.sum _ fun l _ => BddMeas.sum _ fun k _ =>
      BddMeas.mul (g := fun X : Config N d => cgrad (eC (i + 1)) (X l) k)
        ⟨(measurable_cgrad (hφ (i + 1)) k).comp (measurable_pi_apply l), Ci, fun X => hCi _ _⟩
        ⟨(measurable_cgrad (hφ (j + 1)) k).comp (measurable_pi_apply l), Cj, fun X => hCj _ _⟩)
  exact h.2

theorem bddMeas_forceD {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) (i : ℕ) :
    BddMeas fun X : Config N d => forceD W (μ : Measure (Torus d)) eC N i X := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨CG, -, hCG⟩ := exists_bound_gsG hyp hac (N := N)
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  unfold forceD
  refine (BddMeas.const _).mul (BddMeas.sum _ fun l _ => BddMeas.sum _ fun k _ =>
    BddMeas.mul (g := fun X : Config N d => gsG W (μ : Measure (Torus d)) N (flat X) (l, k))
      ⟨(measurable_gsG hyp hac (l, k)).comp measurable_flat, CG, fun X => hCG _ _⟩
      ⟨(measurable_cgrad (hφ (i + 1)) k).comp (measurable_pi_apply l), Ci, fun X => hCi _ _⟩)

end fixedN

end SharpLSI
