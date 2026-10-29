import FullLabeledLSI.Paper.Sec5ForceMeas
import FullLabeledLSI.Paper.Sec5Products

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### Counting -/

section CountT2a
variable {N : ℕ}

theorem injective_fin3_iff {α : Type*} (t : Fin 3 → α) :
    Function.Injective t ↔ (t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2) := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · exact absurd (h e) (by decide)
    · exact absurd (h e) (by decide)
    · exact absurd (h e) (by decide)
  · rintro ⟨h01, h02, h12⟩ x y hxy
    fin_cases x <;> fin_cases y <;>
      first | rfl | (exfalso; first
        | exact h01 hxy | exact h01 hxy.symm | exact h02 hxy | exact h02 hxy.symm
        | exact h12 hxy | exact h12 hxy.symm)

theorem card_mixed_aux (j : ℕ) (hj : 1 ≤ j) (l i J : Fin N) (hli : l ≠ i) (hlJ : l ≠ J)
    (hiJ : i ≠ J) :
    (((Finset.univ : Finset (Fin N)).powersetCard j).filter
      (fun S => l ∈ S ∧ i ∉ S ∧ J ∉ S)).card = (N - 3).choose (j - 1) := by
  classical
  have h3 : ({l, i, J} : Finset (Fin N)).card = 3 :=
    Finset.card_eq_three.mpr ⟨l, i, J, hli, hlJ, hiJ, rfl⟩
  have hcard : (({l, i, J} : Finset (Fin N))ᶜ.powersetCard (j - 1)).card =
      (N - 3).choose (j - 1) := by
    rw [Finset.card_powersetCard, Finset.card_compl, h3]; simp
  rw [← hcard]
  refine Finset.card_bij (fun S _ => S.erase l) ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
    obtain ⟨hc, hl, hi, hJ'⟩ := hS
    rw [Finset.mem_powersetCard]
    refine ⟨?_, by rw [Finset.card_erase_of_mem hl, hc]⟩
    intro x hx
    rw [Finset.mem_erase] at hx
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx.1, fun h => hi (h ▸ hx.2), fun h => hJ' (h ▸ hx.2)⟩
  · intro S hS S' hS' h
    simp only [Finset.mem_filter] at hS hS'
    rw [← Finset.insert_erase hS.2.1, ← Finset.insert_erase hS'.2.1]
    exact congrArg (insert l) h
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    have hmem : ∀ x ∈ T, x ≠ l ∧ x ≠ i ∧ x ≠ J := fun x hx => by
      have := hT.1 hx
      simpa [not_or] using this
    have hlT : l ∉ T := fun h => (hmem l h).1 rfl
    refine ⟨insert l T, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      refine ⟨by rw [Finset.card_insert_of_notMem hlT, hT.2]; omega, Finset.mem_insert_self _ _, ?_, ?_⟩
      · rw [Finset.mem_insert]
        rintro (h | h)
        · exact hli h.symm
        · exact (hmem i h).2.1 rfl
      · rw [Finset.mem_insert]
        rintro (h | h)
        · exact hlJ h.symm
        · exact (hmem J h).2.2 rfl
    · exact Finset.erase_insert hlT

theorem sum_compl_eq (S : Finset (Fin N)) (g : Fin N → ℝ) :
    ∑ i ∈ Sᶜ, g i = ∑ i, if i ∉ S then g i else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext; simp

theorem sum_mem_eq (S : Finset (Fin N)) (g : Fin N → ℝ) :
    ∑ i ∈ S, g i = ∑ i, if i ∈ S then g i else 0 := by
  classical
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_erase_compl (S : Finset (Fin N)) (i : Fin N) (g : Fin N → ℝ) :
    ∑ J ∈ Sᶜ.erase i, g J = ∑ J, if (J ∉ S ∧ i ≠ J) then g J else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext J; simp [Finset.mem_erase, eq_comm, and_comm]

/-- Equivalence of triples. -/
def tripleEquiv (N : ℕ) : (Fin 3 → Fin N) ≃ Fin N × Fin N × Fin N where
  toFun t := (t 0, t 1, t 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv t := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem tripleEquiv_apply (t : Fin 3 → Fin N) : tripleEquiv N t = (t 0, t 1, t 2) := rfl

theorem sum_inj_triples (H : Fin N → Fin N → Fin N → ℝ) :
    ∑ t ∈ injTuples N 3, H (t 0) (t 1) (t 2) =
      ∑ i, ∑ J, ∑ l, if (i ≠ J ∧ i ≠ l ∧ J ≠ l) then H i J l else 0 := by
  classical
  rw [injTuples, Finset.sum_filter]
  rw [Fintype.sum_equiv (tripleEquiv N) _
    (fun p : Fin N × Fin N × Fin N => if (p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) then
      H p.1 p.2.1 p.2.2 else 0)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  · intro t
    by_cases h : Function.Injective t
    · have h' := (injective_fin3_iff t).1 h
      simp [h, h', tripleEquiv_apply]
    · have h' : ¬ (t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2) := fun hh => h ((injective_fin3_iff t).2 hh)
      simp [h, h', tripleEquiv_apply]

theorem sum_mixed (j : ℕ) (hj : 1 ≤ j) (H : Fin N → Fin N → Fin N → ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ l ∈ S, ∑ i ∈ Sᶜ,
        ∑ J ∈ Sᶜ.erase i, H i J l =
      ((N - 3).choose (j - 1) : ℝ) * ∑ t ∈ injTuples N 3, H (t 0) (t 1) (t 2) := by
  classical
  have e1 : ∀ S : Finset (Fin N), ∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i, H i J l =
      ∑ l, ∑ i, ∑ J, if (l ∈ S ∧ i ∉ S ∧ J ∉ S ∧ i ≠ J) then H i J l else 0 := by
    intro S
    rw [sum_mem_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l ∈ S
    · rw [if_pos hl, sum_compl_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∉ S
      · rw [if_pos hi, sum_erase_compl]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp [hl, hi]
      · rw [if_neg hi]
        refine (Finset.sum_eq_zero fun J _ => ?_).symm
        simp [hi]
    · rw [if_neg hl]
      refine (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun J _ => ?_).symm
      simp [hl]
  have e2 : ∀ l i J : Fin N,
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
        (if (l ∈ S ∧ i ∉ S ∧ J ∉ S ∧ i ≠ J) then H i J l else 0) =
      if (i ≠ J ∧ i ≠ l ∧ J ≠ l) then ((N - 3).choose (j - 1) : ℝ) * H i J l else 0 := by
    intro l i J
    by_cases hd : i ≠ J ∧ i ≠ l ∧ J ≠ l
    · rw [if_pos hd]
      rw [Finset.sum_congr rfl (g := fun S => if (l ∈ S ∧ i ∉ S ∧ J ∉ S) then H i J l else 0)
        (fun S _ => by simp [hd.1])]
      rw [← Finset.sum_filter, Finset.sum_const,
        card_mixed_aux j hj l i J (Ne.symm hd.2.1) (Ne.symm hd.2.2) hd.1, nsmul_eq_mul]
    · rw [if_neg hd]
      refine Finset.sum_eq_zero fun S hS => ?_
      rw [if_neg]
      rintro ⟨hl, hi, hJ, hij⟩
      exact hd ⟨hij, fun h => hi (h ▸ hl), fun h => hJ (h ▸ hl)⟩
  calc _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ l, ∑ i, ∑ J,
        (if (l ∈ S ∧ i ∉ S ∧ J ∉ S ∧ i ≠ J) then H i J l else 0) :=
        Finset.sum_congr rfl fun S _ => e1 S
    _ = ∑ l, ∑ i, ∑ J, ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
        (if (l ∈ S ∧ i ∉ S ∧ J ∉ S ∧ i ≠ J) then H i J l else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    _ = ∑ l, ∑ i, ∑ J, if (i ≠ J ∧ i ≠ l ∧ J ≠ l) then
        ((N - 3).choose (j - 1) : ℝ) * H i J l else 0 := by
      simp only [e2]
    _ = ∑ i, ∑ J, ∑ l, if (i ≠ J ∧ i ≠ l ∧ J ≠ l) then
        ((N - 3).choose (j - 1) : ℝ) * H i J l else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    _ = _ := by
      rw [sum_inj_triples, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp

theorem sum_distinctTuples_two (S : Finset (Fin N)) (G : Fin N → Fin N → ℝ) :
    ∑ I ∈ distinctTuples S 2, G (I 0) (I 1) = ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i, G i J := by
  classical
  rw [Finset.sum_sigma' (Sᶜ) (fun i => Sᶜ.erase i) (fun i J => G i J)]
  refine Finset.sum_bij' (fun I _ => (⟨I 0, I 1⟩ : Σ _ : Fin N, Fin N))
    (fun x _ => ![x.1, x.2]) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [Finset.mem_sigma, Finset.mem_compl, Finset.mem_erase]
    refine ⟨hI.2 0, fun h => ?_, hI.2 1⟩
    exact absurd (hI.1 h) (by decide)
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_compl, Finset.mem_erase] at hx
    simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        first | rfl | (exfalso; first | exact hx.2.1 (by simpa using hab.symm) | exact hx.2.1 (by simpa using hab))
    · intro a
      fin_cases a
      · exact hx.1
      · exact hx.2.2
  · intro I _
    funext a; fin_cases a <;> rfl
  · intro x _
    rfl
  · intro I _
    rfl

end CountT2a

/-! ### Measure-theoretic pieces -/

section MeasT2a
variable {N : ℕ} {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- Integral against `ρ̄_S` is the average of integrals against `ρ_{S,i}`. -/
theorem t2a_integral_barCond (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (X : Config N d) (g : Torus d → ℝ) (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) :
    ∫ x, g x ∂barCond ν S X =
      ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫ x, g x ∂condLawS ν S i (restrictS S X) := by
  unfold barCond
  rw [integral_smul_measure, integral_finsetSum_measure]
  · rw [smul_eq_mul]
    congr 1
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact Integrable.of_bound hg.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun z => by simpa using hc z)

/-- Disintegration for one label. -/
theorem t2a_integral_eq_condLawS (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (i : Fin N) (f : (S → Torus d) → Torus d → ℝ)
    (hf : Measurable fun p : (S → Torus d) × Torus d => f p.1 p.2) {c : ℝ}
    (hc : ∀ a x, |f a x| ≤ c) :
    ∫ X, f (restrictS S X) (X i) ∂ν =
      ∫ X, ∫ x, f (restrictS S X) x ∂condLawS ν S i (restrictS S X) ∂ν := by
  set P0 : Measure (S → Torus d) := ν.map (restrictS S) with hP0def
  have hFm : Measurable fun a : S → Torus d => ∫ x, f a x ∂condLawS ν S i a :=
    (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := condLawS ν S i)).measurable
  have hlaw : ν.map (fun X => (restrictS S X, X i)) = P0 ⊗ₘ condLawS ν S i :=
    (compProd_map_condDistrib (measurable_restrictS S).aemeasurable
      (measurable_pi_apply i).aemeasurable).symm
  have hBi : Integrable (fun q : (S → Torus d) × Torus d => f q.1 q.2) (P0 ⊗ₘ condLawS ν S i) :=
    Integrable.of_bound hf.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hc q.1 q.2)
  have e2 : ∫ X, f (restrictS S X) (X i) ∂ν = ∫ a, ∫ x, f a x ∂condLawS ν S i a ∂P0 := by
    rw [← integral_map ((measurable_restrictS S).prodMk (measurable_pi_apply i)).aemeasurable
      hf.aestronglyMeasurable, hlaw, Measure.integral_compProd hBi]
  rw [e2, hP0def, integral_map (measurable_restrictS S).aemeasurable hFm.aestronglyMeasurable]

theorem abs_sum_mul_le (u v : Fin d → ℝ) (hu : ∀ k, |u k| ≤ Bb) (hv : ∀ k, |v k| ≤ Bb) :
    |∑ k, u k * v k| ≤ (d : ℝ) * Bb ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |u k * v k| ≤ ∑ _k : Fin d, Bb * Bb := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hu k) (hv k) (abs_nonneg _) ((abs_nonneg _).trans (hu k))
    _ = (d : ℝ) * Bb ^ 2 := by simp [sq]

/-- measurability of `(a, x) ↦ ∫ bF x y k dρ_{S,J}(a)(y)` -/
theorem measurable_condInt (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (J : Fin N) (k : Fin d) :
    Measurable fun p : (S → Torus d) × Torus d => ∫ y, bF p.2 y k ∂condLawS ν S J p.1 := by
  have hf : Measurable fun q : ((S → Torus d) × Torus d) × Torus d => bF q.1.2 q.2 k :=
    (hB.meas k).comp (measurable_fst.snd.prodMk measurable_snd)
  have h := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (condLawS ν S J).comap (Prod.fst : (S → Torus d) × Torus d → S → Torus d)
      measurable_fst)
  exact h.measurable

theorem abs_condInt_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (J : Fin N) (k : Fin d) (a : S → Torus d)
    (x : Torus d) : |∫ y, bF x y k ∂condLawS ν S J a| ≤ Bb :=
  abs_integral_le_of_prob _ _ fun y => hB.bound x y k

/-- The test function appearing after expanding `ρ̄_S`. -/
noncomputable def fSLJ (bF : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d))
    [IsFiniteMeasure ν] (S : Finset (Fin N)) (l : Fin N) (hl : l ∈ S) (J : Fin N)
    (a : S → Torus d) (x : Torus d) : ℝ :=
  ∑ k : Fin d, (∫ y, bF x y k ∂condLawS ν S J a) * bF x (a ⟨l, hl⟩) k

theorem measurable_fSLJ (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (l : Fin N) (hl : l ∈ S) (J : Fin N) :
    Measurable fun p : (S → Torus d) × Torus d => fSLJ bF ν S l hl J p.1 p.2 := by
  unfold fSLJ
  refine Finset.measurable_sum _ fun k _ => (measurable_condInt hB ν S J k).mul ?_
  exact (hB.meas k).comp (measurable_snd.prodMk
    ((measurable_pi_apply (⟨l, hl⟩ : S)).comp measurable_fst))

theorem abs_fSLJ_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (l : Fin N) (hl : l ∈ S) (J : Fin N)
    (a : S → Torus d) (x : Torus d) : |fSLJ bF ν S l hl J a x| ≤ (d : ℝ) * Bb ^ 2 :=
  abs_sum_mul_le _ _ (fun k => abs_condInt_le hB ν S J k a x) (fun k => hB.bound _ _ k)

/-- `T(S,l,i,J) = ∫ ∑_k (∫ b_k(X_i, y) dρ_{S,J}(y)) b_k(X_i, X_l) dν`. -/
noncomputable def Tf (bF : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d))
    [IsFiniteMeasure ν] (S : Finset (Fin N)) (l i J : Fin N) : ℝ :=
  ∫ X, ∑ k : Fin d, (∫ y, bF (X i) y k ∂condLawS ν S J (restrictS S X)) * bF (X i) (X l) k ∂ν

theorem Tf_eq (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N)) (l : Fin N)
    (hl : l ∈ S) (i J : Fin N) :
    Tf bF ν S l i J = ∫ X, fSLJ bF ν S l hl J (restrictS S X) (X i) ∂ν := rfl

theorem abs_Tf_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (l i J : Fin N) : |Tf bF ν S l i J| ≤ (d : ℝ) * Bb ^ 2 :=
  abs_integral_le_of_prob ν _ fun _ => abs_sum_mul_le _ _
    (fun k => abs_condInt_le hB ν S J k _ _) (fun k => hB.bound _ _ k)

theorem V_expand (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (l : Fin N) (hl : l ∈ S) (i : Fin N) :
    ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν =
      ((Sᶜ.card : ℝ)⁻¹) * ∑ J ∈ Sᶜ, Tf bF ν S l i J := by
  have hpt : ∀ X : Config N d, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k =
      ((Sᶜ.card : ℝ)⁻¹) * ∑ J ∈ Sᶜ, fSLJ bF ν S l hl J (restrictS S X) (X i) := by
    intro X
    have hbs : ∀ k, BS bF ν S X (X i) k = ((Sᶜ.card : ℝ)⁻¹) *
        ∑ J ∈ Sᶜ, ∫ y, bF (X i) y k ∂condLawS ν S J (restrictS S X) := fun k =>
      t2a_integral_barCond ν S X (fun y => bF (X i) y k)
        ((hB.meas k).comp (measurable_const.prodMk measurable_id)) (fun y => hB.bound _ y k)
    simp only [hbs, fSLJ]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => Finset.sum_mul ..)
  have hint : ∀ J, Integrable (fun X : Config N d => fSLJ bF ν S l hl J (restrictS S X) (X i)) ν :=
    fun J => integrable_of_bdd ν
      ((measurable_fSLJ hB ν S l hl J).comp
        ((measurable_restrictS S).prodMk (measurable_pi_apply i)))
      (fun X => abs_fSLJ_le hB ν S l hl J _ _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_finsetSum _ (fun J _ => hint J)]
  rfl

theorem integral_pi_two {T : Type*} [MeasurableSpace T] (μ : Fin 2 → Measure T)
    [∀ m, IsProbabilityMeasure (μ m)] (g : T → T → ℝ)
    (hg : Measurable fun p : T × T => g p.1 p.2) {c : ℝ} (hc : ∀ x y, |g x y| ≤ c) :
    ∫ z, g (z 0) (z 1) ∂Measure.pi μ = ∫ x, ∫ y, g x y ∂μ 1 ∂μ 0 := by
  have hmp := measurePreserving_piFinTwo (α := fun _ : Fin 2 => T) μ
  have h1 := hmp.integral_comp' (g := fun p : T × T => g p.1 p.2)
  have h2 : ∫ z, g (z 0) (z 1) ∂Measure.pi μ = ∫ y, g y.1 y.2 ∂(μ 0).prod (μ 1) := h1
  rw [h2]
  exact integral_prod (fun p : T × T => g p.1 p.2) (integrable_of_bdd _ hg (fun p => hc p.1 p.2))

theorem Tf_pinsker (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (l : Fin N) (hl : l ∈ S) (i J : Fin N) (hD : DRev ν S ![i, J] ≠ ⊤) :
    |Tf bF ν S l i J - ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν| ≤
      ((d : ℝ) * Bb ^ 2) * Real.sqrt (2 * (DRev ν S ![i, J]).toReal) := by
  set A : (S → Torus d) → (Fin 2 → Torus d) → ℝ :=
    fun a z => ∑ k : Fin d, bF (z 0) (z 1) k * bF (z 0) (a ⟨l, hl⟩) k with hAdef
  have hA : Measurable fun p : (S → Torus d) × (Fin 2 → Torus d) => A p.1 p.2 := by
    have h0 : Measurable fun p : (S → Torus d) × (Fin 2 → Torus d) => p.2 0 :=
      (measurable_pi_apply 0).comp measurable_snd
    have h1 : Measurable fun p : (S → Torus d) × (Fin 2 → Torus d) => p.2 1 :=
      (measurable_pi_apply 1).comp measurable_snd
    have h2 : Measurable fun p : (S → Torus d) × (Fin 2 → Torus d) => p.1 ⟨l, hl⟩ :=
      (measurable_pi_apply (⟨l, hl⟩ : S)).comp measurable_fst
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((hB.meas k).comp (h0.prodMk h1)).mul ((hB.meas k).comp (h0.prodMk h2))
  have hc : ∀ a z, |A a z| ≤ (d : ℝ) * Bb ^ 2 := fun a z =>
    abs_sum_mul_le _ _ (fun k => hB.bound _ _ k) (fun k => hB.bound _ _ k)
  have key := condPinsker_tuple ν S ![i, J] A hA hc hD
  have e1 : ∫ X, (∫ z, A (restrictS S X) z
      ∂Measure.pi (fun m => condLawS ν S (![i, J] m) (restrictS S X))) ∂ν = Tf bF ν S l i J := by
    rw [Tf_eq ν S l hl i J, t2a_integral_eq_condLawS ν S i (fSLJ bF ν S l hl J)
      (measurable_fSLJ hB ν S l hl J) (fun a x => abs_fSLJ_le hB ν S l hl J a x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    set a := restrictS S X with ha
    have hg : Measurable fun p : Torus d × Torus d =>
        ∑ k : Fin d, bF p.1 p.2 k * bF p.1 (a ⟨l, hl⟩) k :=
      Finset.measurable_sum _ fun k _ =>
        (hB.meas k).mul ((hB.meas k).comp (measurable_fst.prodMk measurable_const))
    have := integral_pi_two (fun m => condLawS ν S (![i, J] m) a)
      (fun x y => ∑ k : Fin d, bF x y k * bF x (a ⟨l, hl⟩) k) hg
      (fun x y => abs_sum_mul_le _ _ (fun k => hB.bound _ _ k) (fun k => hB.bound _ _ k))
    refine this.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∫ y, ∑ k : Fin d, bF x y k * bF x (a ⟨l, hl⟩) k ∂condLawS ν S J a = _
    rw [integral_finsetSum]
    · simp_rw [integral_mul_const]
      rfl
    · intro k _
      exact (integrable_of_bdd _ ((hB.meas k).comp (measurable_const.prodMk measurable_id))
        (fun y => hB.bound x y k)).mul_const _
  have e2 : ∫ X, A (restrictS S X) (fun m => X (![i, J] m)) ∂ν =
      ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν := rfl
  rw [e1, e2] at key
  exact key

theorem perS_err (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) (S : Finset (Fin N)) :
    |∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i,
        (Tf bF ν S l i J - ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν)| ≤
      S.card * (((d : ℝ) * Bb ^ 2) *
        ∑ I ∈ distinctTuples S 2, Real.sqrt (2 * (DRev ν S I).toReal)) := by
  have hl : ∀ l ∈ S, |∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i,
      (Tf bF ν S l i J - ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν)| ≤
      ((d : ℝ) * Bb ^ 2) * ∑ I ∈ distinctTuples S 2, Real.sqrt (2 * (DRev ν S I).toReal) := by
    intro l hl
    rw [← sum_distinctTuples_two S
      (fun i J => Tf bF ν S l i J - ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I hI => ?_)
    have hI2 : ![I 0, I 1] = I := by funext a; fin_cases a <;> rfl
    have hD : DRev ν S ![I 0, I 1] ≠ ⊤ := by rw [hI2]; exact DRev_ne_top ν μ hH S I hI
    have := Tf_pinsker hB ν S l hl (I 0) (I 1) hD
    rw [hI2] at this
    exact this
  calc _ ≤ ∑ l ∈ S, |∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i,
        (Tf bF ν S l i J - ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ S, (((d : ℝ) * Bb ^ 2) *
        ∑ I ∈ distinctTuples S 2, Real.sqrt (2 * (DRev ν S I).toReal)) :=
        Finset.sum_le_sum hl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end MeasT2a

theorem count_id (N j : ℕ) (hj : 1 ≤ j) (hjN : j + 3 ≤ N) :
    N.choose j * j * (N - j).descFactorial 2 = (N - 3).choose (j - 1) * N.descFactorial 3 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 := Nat.add_one_mul_choose_eq M j'
  have h2 := choose_descFactorial_glob (N := M) (j := j') (k := 2) (by omega)
  have h3 : (M + 1).descFactorial 3 = (M + 1) * M.descFactorial 2 :=
    Nat.succ_descFactorial_succ M 2
  have h4 : M + 1 - (j' + 1) = M - j' := by omega
  have h5 : M + 1 - 3 = M - 2 := by omega
  have h6 : j' + 1 - 1 = j' := by omega
  rw [h4, h5, h3, h6, ← h1]
  calc (M + 1) * M.choose j' * (M - j').descFactorial 2
      = (M + 1) * (M.choose j' * (M - j').descFactorial 2) := by ring
    _ = _ := by rw [h2]; ring

theorem card_injTuples (N : ℕ) : (injTuples N 3).card = N.descFactorial 3 := by
  have := card_injMaps_aux (α := Fin 3) (β := Fin N) Finset.univ
  simpa [injTuples] using this

theorem final_alg (K Nr n jr Cnt D3 Q C3 Sd Se c s : ℝ) (hK : 0 < K) (hN : 0 < Nr) (hn : 1 < n)
    (hj0 : 0 ≤ jr) (hjN : jr ≤ Nr) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hid : K * jr * (n * (n - 1)) = Cnt * D3)
    (hQ : Q = K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * (Sd + Cnt * (D3 * C3) + Se))
    (hSd : |Sd| ≤ K * (jr * (n * c)))
    (hSe : |Se| ≤ jr * c * (n * (n - 1)) * (K * s))
    (hC3 : |C3| ≤ c) :
    |Q - jr / Nr * C3| ≤ 2 * c * (1 / n + s) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hKne : K ≠ 0 := hK.ne'
  have hNne : Nr ≠ 0 := hN.ne'
  have hnne : n ≠ 0 := hn0.ne'
  have ha : 0 < K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) := by positivity
  have hcore : K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * (Cnt * D3) = jr / Nr - jr / (Nr * n) := by
    rw [← hid]; field_simp
  have hQ' : Q - jr / Nr * C3 = K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Sd +
      K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Se - jr / (Nr * n) * C3 := by
    rw [hQ]; linear_combination C3 * hcore
  have hjr : jr / Nr ≤ 1 := (div_le_one hN).2 hjN
  have hjr0 : 0 ≤ jr / Nr := div_nonneg hj0 hN.le
  have b1 : K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * |Sd| ≤ c / n := by
    calc _ ≤ K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * (K * (jr * (n * c))) :=
          mul_le_mul_of_nonneg_left hSd ha.le
      _ = jr / Nr * (c / n) := by field_simp
      _ ≤ 1 * (c / n) := mul_le_mul_of_nonneg_right hjr (by positivity)
      _ = c / n := one_mul _
  have b2 : K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * |Se| ≤ c * s := by
    calc _ ≤ K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * (jr * c * (n * (n - 1)) * (K * s)) :=
          mul_le_mul_of_nonneg_left hSe ha.le
      _ = jr / Nr * ((n - 1) / n) * (c * s) := by field_simp
      _ ≤ 1 * 1 * (c * s) := by
          have h1 : (n - 1) / n ≤ 1 := (div_le_one hn0).2 (by linarith)
          have h2 : 0 ≤ (n - 1) / n := by positivity
          have h3 : jr / Nr * ((n - 1) / n) ≤ 1 * 1 := mul_le_mul hjr h1 h2 zero_le_one
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = c * s := by ring
  have b3 : jr / (Nr * n) * |C3| ≤ c / n := by
    calc _ ≤ jr / (Nr * n) * c := mul_le_mul_of_nonneg_left hC3 (by positivity)
      _ = jr / Nr * (c / n) := by field_simp
      _ ≤ 1 * (c / n) := mul_le_mul_of_nonneg_right hjr (by positivity)
      _ = c / n := one_mul _
  rw [hQ']
  have e1 : |K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Sd| = K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * |Sd| := by
    rw [abs_mul, abs_of_pos ha]
  have e2 : |K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Se| = K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * |Se| := by
    rw [abs_mul, abs_of_pos ha]
  have e3 : |jr / (Nr * n) * C3| = jr / (Nr * n) * |C3| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  calc _ ≤ |K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Sd + K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Se| +
        |jr / (Nr * n) * C3| := abs_sub _ _
    _ ≤ |K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Sd| + |K⁻¹ * (Nr⁻¹ * (n ^ 2)⁻¹) * Se| +
        |jr / (Nr * n) * C3| := by gcongr; exact abs_add_le _ _
    _ ≤ c / n + c * s + c / n := by rw [e1, e2, e3]; linarith
    _ ≤ 2 * c * (1 / n + s) := by
        have : 0 ≤ c * s := mul_nonneg hc hs
        have e : c / n = c * (1 / n) := by ring
        nlinarith

/-- Cross term from the revealed coordinates: coefficient `j/N`. -/
theorem T2a_close {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) :
    ∃ C : ℝ, ∀ (N : ℕ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
      (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ → ∀ j, j + 3 ≤ N →
      |avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ S,
            ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) -
          ((j : ℝ) / N) * globTupleMean ν 3 (A3 bF)| ≤
        C * (1 / ((N - j : ℕ) : ℝ) + Real.sqrt (2 * (dRev ν j 2).toReal)) := by
  refine ⟨2 * ((d : ℝ) * Bb ^ 2), ?_⟩
  intro N μ _ ν _ hH j hj
  have hc0 : (0 : ℝ) ≤ (d : ℝ) * Bb ^ 2 := by positivity
  by_cases hj0 : j = 0
  · subst hj0
    have h0 : avg1R N 0 (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ S,
        ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) = 0 := by
      unfold avg1R
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun S hS => ?_)
      have : S = ∅ := Finset.card_eq_zero.1 (Finset.mem_powersetCard.1 hS).2
      subst this
      simp
    rw [h0]
    simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero, abs_zero]
    positivity
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
  have hnN : (N - j : ℕ) + j = N := by omega
  set n : ℕ := N - j with hn
  have hn3 : 3 ≤ n := by omega
  set P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard j with hP
  have hPcard : P.card = N.choose j := by simp [hP]
  have hSj : ∀ S ∈ P, S.card = j := fun S hS => (Finset.mem_powersetCard.1 hS).2
  have hSc : ∀ S ∈ P, Sᶜ.card = n := fun S hS => by
    rw [Finset.card_compl, Fintype.card_fin, hSj S hS]
  set K : ℝ := (N.choose j : ℝ) with hK
  have hKpos : 0 < K := by
    have : 0 < N.choose j := Nat.choose_pos (by omega)
    rw [hK]; exact_mod_cast this
  set c : ℝ := (d : ℝ) * Bb ^ 2 with hc
  set E : Fin N → Fin N → Fin N → ℝ := fun i J l => ∫ X, A3 bF (X ∘ ![i, J, l]) ∂ν with hE
  -- expansion of the quantity
  have hQ : avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ S,
      ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) =
      K⁻¹ * (((N : ℝ)⁻¹ * ((n : ℝ) ^ 2)⁻¹) *
        ∑ S ∈ P, ∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ, Tf bF ν S l i J) := by
    unfold avg1R
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hcard : ((Sᶜ.card : ℕ) : ℝ) = (n : ℝ) := by rw [hSc S hS]
    rw [hcard]
    have hV : ∀ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ l ∈ S,
        ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν =
        (N : ℝ)⁻¹ * ∑ l ∈ S, ((n : ℝ)⁻¹ * ∑ J ∈ Sᶜ, Tf bF ν S l i J) := by
      intro i _
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [V_expand hB ν S l hl i, hcard]
    rw [Finset.sum_congr rfl hV]
    calc (n : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ l ∈ S, (n : ℝ)⁻¹ * ∑ J ∈ Sᶜ, Tf bF ν S l i J
        = (n : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∑ l ∈ S, ((N : ℝ)⁻¹ * (n : ℝ)⁻¹) * ∑ J ∈ Sᶜ, Tf bF ν S l i J := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = (n : ℝ)⁻¹ * ∑ l ∈ S, ∑ i ∈ Sᶜ, ((N : ℝ)⁻¹ * (n : ℝ)⁻¹) * ∑ J ∈ Sᶜ, Tf bF ν S l i J := by
          rw [Finset.sum_comm]
      _ = _ := by
          simp_rw [← Finset.mul_sum]
          ring
  -- splitting off the diagonal
  obtain ⟨Sd, hSd_def⟩ : ∃ x, x = ∑ S ∈ P, ∑ l ∈ S, ∑ i ∈ Sᶜ, Tf bF ν S l i i := ⟨_, rfl⟩
  obtain ⟨Soff, hSoff_def⟩ : ∃ x, x = ∑ S ∈ P, ∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i,
      Tf bF ν S l i J := ⟨_, rfl⟩
  have hsplit : ∑ S ∈ P, ∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ, Tf bF ν S l i J = Sd + Soff := by
    rw [hSd_def, hSoff_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact (Finset.add_sum_erase _ _ hi).symm
  have hSd : |Sd| ≤ K * ((j : ℝ) * ((n : ℝ) * c)) := by
    have hperS : ∀ S ∈ P, |∑ l ∈ S, ∑ i ∈ Sᶜ, Tf bF ν S l i i| ≤ (j : ℝ) * ((n : ℝ) * c) := by
      intro S hS
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ S, |∑ i ∈ Sᶜ, Tf bF ν S l i i| ≤ ∑ _l ∈ S, ((n : ℝ) * c) :=
            Finset.sum_le_sum fun l _ => by
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              calc ∑ i ∈ Sᶜ, |Tf bF ν S l i i| ≤ ∑ _i ∈ Sᶜ, c :=
                    Finset.sum_le_sum fun i _ => abs_Tf_le hB ν S l i i
                _ = (n : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul, hSc S hS]
        _ = (j : ℝ) * ((n : ℝ) * c) := by rw [Finset.sum_const, nsmul_eq_mul, hSj S hS]
    rw [hSd_def]
    calc _ ≤ ∑ S ∈ P, |∑ l ∈ S, ∑ i ∈ Sᶜ, Tf bF ν S l i i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ P, (j : ℝ) * ((n : ℝ) * c) := Finset.sum_le_sum hperS
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hPcard]
  -- the main term
  obtain ⟨SE, hSE_def⟩ : ∃ x, x = ∑ S ∈ P, ∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i, E i J l :=
    ⟨_, rfl⟩
  obtain ⟨Se, hSe_def⟩ : ∃ x, x = ∑ S ∈ P, ∑ l ∈ S, ∑ i ∈ Sᶜ, ∑ J ∈ Sᶜ.erase i,
      (Tf bF ν S l i J - E i J l) := ⟨_, rfl⟩
  have hoff : Soff = SE + Se := by
    rw [hSoff_def, hSE_def, hSe_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun J _ => by ring
  have hD3pos : (0 : ℝ) < (N.descFactorial 3 : ℕ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  have hSEval : SE = ((N - 3).choose (j - 1) : ℝ) *
      (((N.descFactorial 3 : ℕ) : ℝ) * globTupleMean ν 3 (A3 bF)) := by
    rw [hSE_def, hP, sum_mixed j hj1 E]
    congr 1
    unfold globTupleMean
    rw [← mul_assoc, mul_inv_cancel₀ hD3pos.ne', one_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have ht : ![t 0, t 1, t 2] = t := by funext a; fin_cases a <;> rfl
    simp only [hE, ht]
  have hC3 : |globTupleMean ν 3 (A3 bF)| ≤ c := by
    unfold globTupleMean
    rw [abs_mul, abs_of_pos (inv_pos.2 hD3pos)]
    have h1 : |∑ J ∈ injTuples N 3, ∫ X, A3 bF (X ∘ J) ∂ν| ≤
        ((N.descFactorial 3 : ℕ) : ℝ) * c := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ J ∈ injTuples N 3, |∫ X, A3 bF (X ∘ J) ∂ν| ≤ ∑ _J ∈ injTuples N 3, c :=
            Finset.sum_le_sum fun J _ => abs_integral_le_of_prob ν _ fun X =>
              abs_sum_mul_le _ _ (fun k => hB.bound _ _ k) (fun k => hB.bound _ _ k)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_injTuples]
    calc _ ≤ ((N.descFactorial 3 : ℕ) : ℝ)⁻¹ * (((N.descFactorial 3 : ℕ) : ℝ) * c) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hD3pos.le)
      _ = c := by field_simp
  -- the Pinsker error
  have hD2pos : (0 : ℝ) < ((n.descFactorial 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  obtain ⟨m, hm⟩ : ∃ m : Finset (Fin N) → ℝ, ∀ S, m S =
      ((n.descFactorial 2 : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S 2, (DRev ν S I).toReal :=
    ⟨_, fun _ => rfl⟩
  have hm0 : ∀ S, 0 ≤ m S := fun S => by
    rw [hm]
    exact mul_nonneg (inv_nonneg.2 hD2pos.le)
      (Finset.sum_nonneg fun I _ => ENNReal.toReal_nonneg)
  have hd : (dRev ν j 2).toReal = K⁻¹ * ∑ S ∈ P, m S := by
    have := dRev_toReal_eq ν μ hH (j := j) (k := 2) (by omega)
    rw [this]
    simp_rw [hm]
    rfl
  have hperS : ∀ S ∈ P, ∑ I ∈ distinctTuples S 2, Real.sqrt (2 * (DRev ν S I).toReal) ≤
      ((n.descFactorial 2 : ℕ) : ℝ) * Real.sqrt (2 * m S) := by
    intro S hS
    have hcard := card_distinctTuples (N := N) (hSj S hS) 2
    have hne : (distinctTuples S 2).Nonempty := by
      rw [← Finset.card_pos, hcard]; exact_mod_cast Nat.descFactorial_pos.2 (by omega)
    have h4 := uniform_sqrt_le (distinctTuples S 2) hne (fun I => 2 * (DRev ν S I).toReal)
      (fun I _ => by positivity)
    rw [hcard] at h4
    have h5 : ((n.descFactorial 2 : ℕ) : ℝ)⁻¹ *
        ∑ I ∈ distinctTuples S 2, 2 * (DRev ν S I).toReal = 2 * m S := by
      rw [hm, ← Finset.mul_sum]; ring
    rw [h5] at h4
    have h6 := mul_le_mul_of_nonneg_left h4 hD2pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hD2pos.ne', one_mul] at h6
  have hSe : |Se| ≤ (j : ℝ) * c * ((n : ℝ) * ((n : ℝ) - 1)) *
      (K * Real.sqrt (2 * (dRev ν j 2).toReal)) := by
    have hD2 : ((n.descFactorial 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := Nat.cast_descFactorial_two ℝ n
    have hSe' : |Se| ≤ ∑ S ∈ P, ((j : ℝ) * (c * (((n.descFactorial 2 : ℕ) : ℝ) *
        Real.sqrt (2 * m S)))) := by
      rw [hSe_def]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hS => ?_)
      refine (perS_err hB ν μ hH S).trans ?_
      rw [hSj S hS]
      gcongr
      · exact hperS S hS
    have hJ := uniform_sqrt_le P (by rw [← Finset.card_pos, hPcard]; exact Nat.choose_pos (by omega))
      (fun S => 2 * m S) (fun S _ => by have := hm0 S; positivity)
    have e3 : (P.card : ℝ)⁻¹ * ∑ S ∈ P, 2 * m S = 2 * (dRev ν j 2).toReal := by
      rw [hd, hPcard, ← Finset.mul_sum, ← hK]; ring
    rw [e3, hPcard, ← hK] at hJ
    have hJ' : ∑ S ∈ P, Real.sqrt (2 * m S) ≤ K * Real.sqrt (2 * (dRev ν j 2).toReal) := by
      have := mul_le_mul_of_nonneg_left hJ hKpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul] at this
    calc |Se| ≤ _ := hSe'
      _ = (j : ℝ) * c * ((n.descFactorial 2 : ℕ) : ℝ) * ∑ S ∈ P, Real.sqrt (2 * m S) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          ring
      _ ≤ (j : ℝ) * c * ((n.descFactorial 2 : ℕ) : ℝ) *
            (K * Real.sqrt (2 * (dRev ν j 2).toReal)) := by
          gcongr
      _ = _ := by rw [hD2]
  -- algebra
  have hid : K * (j : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) =
      ((N - 3).choose (j - 1) : ℝ) * ((N.descFactorial 3 : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) (count_id N j hj1 hj)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_descFactorial_two ℝ] at h
    exact h
  have hQfin : avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ S,
      ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) =
      K⁻¹ * ((N : ℝ)⁻¹ * ((n : ℝ) ^ 2)⁻¹) *
        (Sd + ((N - 3).choose (j - 1) : ℝ) * (((N.descFactorial 3 : ℕ) : ℝ) *
          globTupleMean ν 3 (A3 bF)) + Se) := by
    rw [hQ, hsplit, hoff, hSEval]; ring
  rw [hQfin]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  exact final_alg K (N : ℝ) (n : ℝ) (j : ℝ) _ _ _ _ Sd Se c _ hKpos hNpos hn1
    (Nat.cast_nonneg _) (by exact_mod_cast (by omega : j ≤ N)) hc0 (Real.sqrt_nonneg _)
    hid rfl hSd hSe hC3

end SharpLSI.FL
