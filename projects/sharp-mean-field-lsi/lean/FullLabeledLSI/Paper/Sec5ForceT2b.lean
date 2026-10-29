import FullLabeledLSI.Paper.Sec5ForceMeas
import FullLabeledLSI.Paper.Sec5Products

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

namespace T2bAux

section PiFin

variable {T : Type*} [MeasurableSpace T]

theorem integral_pi_fin_two (m : Fin 2 → Measure T) [∀ i, IsProbabilityMeasure (m i)]
    (g : (Fin 2 → T) → ℝ) (hg : Measurable g) {c : ℝ} (hc : ∀ z, |g z| ≤ c) :
    ∫ z, g z ∂Measure.pi m = ∫ x, ∫ y, g ![x, y] ∂m 1 ∂m 0 := by
  have hmp := measurePreserving_piFinTwo m
  have hsymm : ∀ x y, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => T)).symm (x, y) = ![x, y] :=
    fun x y => by funext i; fin_cases i <;> rfl
  set G : T × T → ℝ := fun p => g ![p.1, p.2] with hG
  have hGm : Measurable G := hg.comp (measurable_pi_iff.2 fun i => by
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd)
  have e1 : ∫ z, g z ∂Measure.pi m = ∫ p, G p ∂(m 0).prod (m 1) := by
    rw [← hmp.integral_comp' G]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG]
    congr 1
    funext i; fin_cases i <;> rfl
  rw [e1, integral_prod]
  exact Integrable.of_bound hGm.aestronglyMeasurable c
    (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hc _)

theorem integral_pi_fin_three (m : Fin 3 → Measure T) [∀ i, IsProbabilityMeasure (m i)]
    (g : (Fin 3 → T) → ℝ) (hg : Measurable g) {c : ℝ} (hc : ∀ z, |g z| ≤ c) :
    ∫ z, g z ∂Measure.pi m = ∫ x, ∫ y, ∫ w, g ![x, y, w] ∂m 2 ∂m 1 ∂m 0 := by
  have hmp := measurePreserving_piFinSuccAbove m 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => T) 0 with he
  set G : T × (Fin 2 → T) → ℝ := fun p => g (e.symm p) with hG
  have hGm : Measurable G := hg.comp e.symm.measurable
  have e1 : ∫ z, g z ∂Measure.pi m = ∫ p, G p ∂(m 0).prod (Measure.pi fun j : Fin 2 => m (Fin.succ j)) := by
    have := hmp.integral_comp' G
    simp only [Fin.succAbove_zero] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [hG]
  have hint : Integrable G ((m 0).prod (Measure.pi fun j : Fin 2 => m (Fin.succ j))) :=
    Integrable.of_bound hGm.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hc _)
  rw [e1, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := integral_pi_fin_two (fun j : Fin 2 => m (Fin.succ j)) (fun z => G (x, z))
    (hGm.comp measurable_prodMk_left) (c := c) (fun z => hc _)
  beta_reduce
  rw [this]
  have hsymm : ∀ x y w, e.symm (x, ![y, w]) = ![x, y, w] := fun x y w => by
    funext i; fin_cases i <;> rfl
  simp only [hG, hsymm]
  rfl

end PiFin


section Aux2

variable {N : ℕ} {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

theorem abs_sum_mul_le {p q : Fin d → ℝ} {B : ℝ} (hp : ∀ k, |p k| ≤ B) (hq : ∀ k, |q k| ≤ B) :
    |∑ k, p k * q k| ≤ d * B ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |p k * q k| ≤ ∑ _k : Fin d, B ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, sq]
        exact mul_le_mul (hp k) (hq k) (abs_nonneg _) ((abs_nonneg _).trans (hp k))
    _ = d * B ^ 2 := by simp

theorem measurable_bF_pair (hB : ForceRep bF bΔ Bb) {ι : Type*} (i j : ι) (k : Fin d) :
    Measurable fun z : ι → Torus d => bF (z i) (z j) k :=
  by
  have h1 : Measurable fun z : ι → Torus d => (z i, z j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact (hB.meas k).comp h1

theorem measurable_integral_bF (hB : ForceRep bF bΔ Bb) (m : Measure (Torus d)) [SFinite m]
    (k : Fin d) : Measurable fun x => ∫ w, bF x w k ∂m :=
  (StronglyMeasurable.integral_prod_right (f := fun x w => bF x w k)
    (hB.meas k).stronglyMeasurable).measurable

theorem measurable_integral_pi_kernel' {α : Type*} [MeasurableSpace α] {k : ℕ}
    (κ : Fin k → Kernel α (Torus d)) [∀ l, IsMarkovKernel (κ l)]
    {A : α → (Fin k → Torus d) → ℝ} (hA : Measurable fun p : α × (Fin k → Torus d) => A p.1 p.2) :
    Measurable fun a => ∫ z, A a z ∂Measure.pi (fun l => κ l a) :=
  (hA.stronglyMeasurable.integral_kernel_prod_right' (κ := kPi κ)).measurable

/-- Reordering lemma at the level of measures (Fubini). -/
theorem integral_pair_expand (hB : ForceRep bF bΔ Bb) (m2 : Fin 2 → Measure (Torus d))
    (m3 : Fin 3 → Measure (Torus d)) [∀ i, IsProbabilityMeasure (m2 i)]
    [∀ i, IsProbabilityMeasure (m3 i)] (h0 : m3 0 = m2 0) (h1 : m3 1 = m2 1) :
    ∫ z, (∑ k, (∫ w, bF (z 0) w k ∂m3 2) * bF (z 0) (z 1) k) ∂Measure.pi m2 =
      ∫ z, A3 bF z ∂Measure.pi m3 := by
  have hm0 : ∀ k, Measurable fun z : Fin 2 → Torus d => ∫ w, bF (z 0) w k ∂m3 2 := fun k =>
    (measurable_integral_bF hB (m3 2) k).comp (measurable_pi_apply 0)
  have hg : Measurable fun z : Fin 2 → Torus d =>
      ∑ k, (∫ w, bF (z 0) w k ∂m3 2) * bF (z 0) (z 1) k :=
    Finset.measurable_sum _ fun k _ => (hm0 k).mul (measurable_bF_pair hB 0 1 k)
  have hgb : ∀ z : Fin 2 → Torus d,
      |∑ k, (∫ w, bF (z 0) w k ∂m3 2) * bF (z 0) (z 1) k| ≤ d * Bb ^ 2 := fun z =>
    abs_sum_mul_le (fun k => abs_integral_le_of_prob _ _ fun w => hB.bound _ w k)
      (fun k => hB.bound _ _ k)
  have hA3m : Measurable (A3 bF : (Fin 3 → Torus d) → ℝ) :=
    Finset.measurable_sum _ fun k _ => (measurable_bF_pair hB 0 1 k).mul
      (measurable_bF_pair hB 0 2 k)
  have hA3b : ∀ z : Fin 3 → Torus d, |A3 bF z| ≤ d * Bb ^ 2 := fun z =>
    abs_sum_mul_le (fun k => hB.bound _ _ k) (fun k => hB.bound _ _ k)
  rw [integral_pi_fin_two m2 _ hg hgb, integral_pi_fin_three m3 _ hA3m hA3b, h0, h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  have hint : ∀ k, Integrable (fun w => bF x w k) (m3 2) := fun k =>
    integrable_of_bdd _ ((hB.meas k).comp measurable_prodMk_left) (fun w => hB.bound _ _ k)
  show ∑ k, (∫ w, bF x w k ∂m3 2) * bF x y k = ∫ w, ∑ k, bF x y k * bF x w k ∂m3 2
  rw [integral_finsetSum _ (fun k _ => (hint k).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, mul_comm]

end Aux2


section PairClaim

variable {N : ℕ} {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

theorem mem_dT_two {S : Finset (Fin N)} {i l : Fin N} (hi : i ∉ S) (hl : l ∉ S) (hil : i ≠ l) :
    (![i, l] : Fin 2 → Fin N) ∈ distinctTuples S 2 := by
  simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun a b hab => ?_, fun m => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp_all
  · fin_cases m <;> simpa

theorem mem_dT_three {S : Finset (Fin N)} {i l J : Fin N} (hi : i ∉ S) (hl : l ∉ S) (hJ : J ∉ S)
    (hil : i ≠ l) (hiJ : i ≠ J) (hlJ : l ≠ J) :
    (![i, l, J] : Fin 3 → Fin N) ∈ distinctTuples S 3 := by
  simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun a b hab => ?_, fun m => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp_all
  · fin_cases m <;> simpa

/-- The test `A¹_a(x,y) = ∑_k B^a_k(x) b_k(x,y)`. -/
noncomputable def A1T (bF : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) : (S → Torus d) → (Fin 2 → Torus d) → ℝ :=
  fun a z => ∑ k, (∫ w, bF (z 0) w k ∂barCondA ν S a) * bF (z 0) (z 1) k

/-- The `J`-th summand of `A1T`. -/
noncomputable def Wfun (bF : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (a : S → Torus d) (J : Fin N)
    (z : Fin 2 → Torus d) : ℝ :=
  ∑ k, (∫ w, bF (z 0) w k ∂condLawS ν S J a) * bF (z 0) (z 1) k

theorem measurable_A1T (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) :
    Measurable fun p : (S → Torus d) × (Fin 2 → Torus d) => A1T bF ν S p.1 p.2 := by
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · have h1 : Measurable fun q : (S → Torus d) × (Fin 2 → Torus d) => (q.1, q.2 0) :=
      measurable_fst.prodMk ((measurable_pi_apply (0 : Fin 2)).comp measurable_snd)
    exact (measurable_BSA hB ν S k).comp h1
  · exact (measurable_bF_pair hB 0 1 k).comp measurable_snd

theorem abs_A1T_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (a : S → Torus d)
    (z : Fin 2 → Torus d) : |A1T bF ν S a z| ≤ d * Bb ^ 2 := by
  have := isProbabilityMeasure_barCondA ν S hS a
  exact abs_sum_mul_le (fun k => abs_integral_le_of_prob _ _ fun w => hB.bound _ w k)
    (fun k => hB.bound _ _ k)

theorem abs_Wfun_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (a : S → Torus d) (J : Fin N)
    (z : Fin 2 → Torus d) : |Wfun bF ν S a J z| ≤ d * Bb ^ 2 :=
  abs_sum_mul_le (fun k => abs_integral_le_of_prob _ _ fun w => hB.bound _ w k)
    (fun k => hB.bound _ _ k)

theorem measurable_Wfun (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (a : S → Torus d) (J : Fin N) :
    Measurable (Wfun bF ν S a J) :=
  Finset.measurable_sum _ fun k _ => Measurable.mul
    ((measurable_integral_bF hB (condLawS ν S J a) k).comp (measurable_pi_apply 0))
    (measurable_bF_pair hB 0 1 k)

theorem A1T_eq_sum (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (a : S → Torus d) (z : Fin 2 → Torus d) :
    A1T bF ν S a z = ((Sᶜ.card : ℝ)⁻¹) * ∑ J ∈ Sᶜ, Wfun bF ν S a J z := by
  have h : ∀ k, ∫ w, bF (z 0) w k ∂barCondA ν S a =
      ((Sᶜ.card : ℝ)⁻¹) * ∑ J ∈ Sᶜ, ∫ w, bF (z 0) w k ∂condLawS ν S J a := fun k =>
    integral_barCondA ν S a _ ((hB.meas k).comp measurable_prodMk_left) (c := Bb)
      (fun w => hB.bound _ w k)
  simp only [A1T, Wfun, h]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem Wint_eq (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (a : S → Torus d) (i l J : Fin N) :
    ∫ z, Wfun bF ν S a J z ∂Measure.pi (fun m => condLawS ν S (![i, l] m) a) =
      ∫ z, A3 bF z ∂Measure.pi (fun m => condLawS ν S (![i, l, J] m) a) :=
  integral_pair_expand hB (fun m => condLawS ν S (![i, l] m) a)
    (fun m => condLawS ν S (![i, l, J] m) a) rfl rfl


theorem pair_claim (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) (S : Finset (Fin N))
    (hS : 3 ≤ Sᶜ.card) (i l : Fin N) (hi : i ∈ Sᶜ) (hl : l ∈ Sᶜ.erase i) :
    |(∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) -
      ((Sᶜ.card : ℝ)⁻¹ * ∑ J ∈ (Sᶜ.erase i).erase l, ∫ X, A3 bF (X ∘ ![i, l, J]) ∂ν)| ≤
    (d * Bb ^ 2) * (Real.sqrt (2 * (DRev ν S ![i, l]).toReal) +
      (Sᶜ.card : ℝ)⁻¹ * ∑ J ∈ (Sᶜ.erase i).erase l,
        Real.sqrt (2 * (DRev ν S ![i, l, J]).toReal) + 2 / (Sᶜ.card : ℝ)) := by
  classical
  set n : ℝ := (Sᶜ.card : ℝ) with hn
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hS
  have hn0 : 0 < n := by linarith
  set c : ℝ := d * Bb ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hS1 : 1 ≤ Sᶜ.card := by omega
  set R' := (Sᶜ.erase i).erase l with hR'
  have hiS : i ∉ S := by simpa using hi
  have hlne : l ≠ i := (Finset.mem_erase.1 hl).1
  have hlS : l ∉ S := by simpa using (Finset.mem_erase.1 hl).2
  have hI2 : (![i, l] : Fin 2 → Fin N) ∈ distinctTuples S 2 :=
    mem_dT_two hiS hlS (Ne.symm hlne)
  have hA3m : Measurable (A3 bF : (Fin 3 → Torus d) → ℝ) :=
    Finset.measurable_sum _ fun k _ => (measurable_bF_pair hB 0 1 k).mul
      (measurable_bF_pair hB 0 2 k)
  have hA3b : ∀ z : Fin 3 → Torus d, |A3 bF z| ≤ c := fun z =>
    abs_sum_mul_le (fun k => hB.bound _ _ k) (fun k => hB.bound _ _ k)
  -- Test `A1`
  set F1 : (S → Torus d) → ℝ := fun a =>
    ∫ z, A1T bF ν S a z ∂Measure.pi (fun m => condLawS ν S (![i, l] m) a) with hF1
  have hF1m : Measurable F1 :=
    measurable_integral_pi_kernel' (fun m => condLawS ν S (![i, l] m)) (measurable_A1T hB ν S)
  have hF1b : ∀ a, |F1 a| ≤ c := fun a =>
    abs_integral_le_of_prob _ _ (abs_A1T_le hB ν S hS1 a)
  have hP1 : |(∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) -
      ∫ X, F1 (restrictS S X) ∂ν| ≤ c * Real.sqrt (2 * (DRev ν S ![i, l]).toReal) := by
    have := condPinsker_tuple ν S ![i, l] (A1T bF ν S) (measurable_A1T hB ν S)
      (abs_A1T_le hB ν S hS1) (DRev_ne_top ν μ hH S _ hI2)
    rw [abs_sub_comm]
    exact this
  -- Tests `A3`
  set G3 : Fin N → (S → Torus d) → ℝ := fun J a =>
    ∫ z, A3 bF z ∂Measure.pi (fun m => condLawS ν S (![i, l, J] m) a) with hG3
  have hG3m : ∀ J, Measurable (G3 J) := fun J =>
    measurable_integral_pi_kernel' (fun m => condLawS ν S (![i, l, J] m))
      (A := fun _ z => A3 bF z) (hA3m.comp measurable_snd)
  have hG3b : ∀ J a, |G3 J a| ≤ c := fun J a => abs_integral_le_of_prob _ _ hA3b
  have hJmem : ∀ J ∈ R', J ∈ Sᶜ ∧ J ≠ i ∧ J ≠ l := fun J hJ => by
    simp only [hR', Finset.mem_erase] at hJ
    exact ⟨hJ.2.2, hJ.2.1, hJ.1⟩
  have hP3 : ∀ J ∈ R', |∫ X, G3 J (restrictS S X) ∂ν - ∫ X, A3 bF (X ∘ ![i, l, J]) ∂ν| ≤
      c * Real.sqrt (2 * (DRev ν S ![i, l, J]).toReal) := fun J hJ => by
    obtain ⟨hJS, hJi, hJl⟩ := hJmem J hJ
    have hJS' : J ∉ S := by simpa using hJS
    have hI3 := mem_dT_three hiS hlS hJS' (Ne.symm hlne) (Ne.symm hJi) (Ne.symm hJl)
    exact condPinsker_tuple ν S ![i, l, J] (fun _ z => A3 bF z) (hA3m.comp measurable_snd)
      (fun _ z => hA3b z) (DRev_ne_top ν μ hH S _ hI3)
  -- pointwise decomposition of `F1`
  set Gf : (S → Torus d) → Fin N → ℝ := fun a J =>
    ∫ z, Wfun bF ν S a J z ∂Measure.pi (fun m => condLawS ν S (![i, l] m) a) with hGf
  have hGfb : ∀ a J, |Gf a J| ≤ c := fun a J =>
    abs_integral_le_of_prob _ _ (abs_Wfun_le hB ν S a J)
  have hdec : ∀ a, F1 a = n⁻¹ * ∑ J ∈ R', G3 J a + n⁻¹ * (Gf a i + Gf a l) := by
    intro a
    have h1 : F1 a = n⁻¹ * ∑ J ∈ Sᶜ, Gf a J := by
      simp only [hF1, hGf, A1T_eq_sum hB ν S a]
      rw [integral_const_mul, integral_finsetSum]
      intro J _
      exact integrable_of_bdd _ (measurable_Wfun hB ν S a J) (abs_Wfun_le hB ν S a J)
    have h2 : ∑ J ∈ Sᶜ, Gf a J = Gf a i + (Gf a l + ∑ J ∈ R', Gf a J) := by
      rw [Finset.add_sum_erase _ _ hl, Finset.add_sum_erase _ _ hi]
    have h3 : ∑ J ∈ R', Gf a J = ∑ J ∈ R', G3 J a :=
      Finset.sum_congr rfl fun J _ => Wint_eq hB ν S a i l J
    rw [h1, h2, h3]
    ring
  have hint1 : Integrable (fun X : Config N d => F1 (restrictS S X)) ν :=
    integrable_of_bdd ν (hF1m.comp (measurable_restrictS S)) (fun X => hF1b _)
  have hint3 : ∀ J, Integrable (fun X : Config N d => G3 J (restrictS S X)) ν := fun J =>
    integrable_of_bdd ν ((hG3m J).comp (measurable_restrictS S)) (fun X => hG3b J _)
  set g : Config N d → ℝ := fun X => n⁻¹ * ∑ J ∈ R', G3 J (restrictS S X) with hg
  have hintg : Integrable g ν := (integrable_finsetSum _ (fun J _ => hint3 J)).const_mul _
  have hgint : ∫ X, g X ∂ν = n⁻¹ * ∑ J ∈ R', ∫ X, G3 J (restrictS S X) ∂ν := by
    simp only [hg]
    rw [integral_const_mul, integral_finsetSum _ (fun J _ => hint3 J)]
  have hdiff : |∫ X, F1 (restrictS S X) ∂ν - ∫ X, g X ∂ν| ≤ 2 * c / n := by
    rw [← integral_sub hint1 hintg]
    have hpt : ∀ X, |F1 (restrictS S X) - g X| ≤ 2 * c / n := fun X => by
      have h : F1 (restrictS S X) - g X =
          n⁻¹ * (Gf (restrictS S X) i + Gf (restrictS S X) l) := by
        simp only [hg]; rw [hdec]; ring
      rw [h, abs_mul, abs_of_pos (inv_pos.2 hn0)]
      calc n⁻¹ * |Gf (restrictS S X) i + Gf (restrictS S X) l| ≤ n⁻¹ * (c + c) :=
            mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
              (add_le_add (hGfb _ _) (hGfb _ _))) (inv_nonneg.2 hn0.le)
        _ = 2 * c / n := by field_simp; ring
    exact abs_integral_le_of_prob ν _ hpt
  set M : ℝ := n⁻¹ * ∑ J ∈ R', ∫ X, A3 bF (X ∘ ![i, l, J]) ∂ν with hM
  have h3 : |n⁻¹ * ∑ J ∈ R', ∫ X, G3 J (restrictS S X) ∂ν - M| ≤
      c * (n⁻¹ * ∑ J ∈ R', Real.sqrt (2 * (DRev ν S ![i, l, J]).toReal)) := by
    simp only [hM]
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hn0)]
    calc n⁻¹ * |∑ J ∈ R', (∫ X, G3 J (restrictS S X) ∂ν - ∫ X, A3 bF (X ∘ ![i, l, J]) ∂ν)|
        ≤ n⁻¹ * ∑ J ∈ R', c * Real.sqrt (2 * (DRev ν S ![i, l, J]).toReal) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum hP3)) (inv_nonneg.2 hn0.le)
      _ = c * (n⁻¹ * ∑ J ∈ R', Real.sqrt (2 * (DRev ν S ![i, l, J]).toReal)) := by
          rw [← Finset.mul_sum]; ring
  rw [hgint] at hdiff
  have e1 := abs_sub_le (∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν)
    (∫ X, F1 (restrictS S X) ∂ν) M
  have e2 := abs_sub_le (∫ X, F1 (restrictS S X) ∂ν)
    (n⁻¹ * ∑ J ∈ R', ∫ X, G3 J (restrictS S X) ∂ν) M
  have e3 : c * (2 / n) = 2 * c / n := by ring
  nlinarith [e1, e2, hP1, hdiff, h3, e3]

end PairClaim


section Counting

variable {N : ℕ}

/-- Real-valued uniform average over `(S, I)`, `|S| = j`, `I` a distinct `k`-tuple in `Sᶜ`. -/
noncomputable def avgR (N j k : ℕ) (h : Finset (Fin N) → (Fin k → Fin N) → ℝ) : ℝ :=
  ((Nat.choose N j : ℕ) : ℝ)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    (((N - j).descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, h S I

theorem conv2 (S : Finset (Fin N)) (f : (Fin 2 → Fin N) → ℝ) :
    ∑ i ∈ Sᶜ, ∑ l ∈ Sᶜ.erase i, f ![i, l] = ∑ I ∈ distinctTuples S 2, f I := by
  classical
  rw [Finset.sum_sigma' (s := Sᶜ) (t := fun i => Sᶜ.erase i)
    (f := fun i l => f ![i, l])]
  refine Finset.sum_nbij' (fun x => ![x.1, x.2]) (fun I => ⟨I 0, I 1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, l⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_compl] at hx
    exact mem_dT_two hx.1 hx.2.2 (Ne.symm hx.2.1)
  · intro I hI
    simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_compl]
    refine ⟨hI.2 0, ?_, hI.2 1⟩
    intro h
    have := hI.1 h
    exact absurd this (by decide)
  · rintro ⟨i, l⟩ _
    rfl
  · intro I _
    funext m
    fin_cases m <;> rfl
  · intro x _
    rfl

theorem conv3 (S : Finset (Fin N)) (f : (Fin 3 → Fin N) → ℝ) :
    ∑ i ∈ Sᶜ, ∑ l ∈ Sᶜ.erase i, ∑ J ∈ (Sᶜ.erase i).erase l, f ![i, l, J] =
      ∑ I ∈ distinctTuples S 3, f I := by
  classical
  have h1 : ∀ i, ∑ l ∈ Sᶜ.erase i, ∑ J ∈ (Sᶜ.erase i).erase l, f ![i, l, J] =
      ∑ x ∈ (Sᶜ.erase i).sigma (fun l => (Sᶜ.erase i).erase l), f ![i, x.1, x.2] := fun i =>
    Finset.sum_sigma' (s := Sᶜ.erase i) (t := fun l => (Sᶜ.erase i).erase l)
      (f := fun l J => f ![i, l, J])
  simp_rw [h1]
  rw [Finset.sum_sigma' (s := Sᶜ) (t := fun i => (Sᶜ.erase i).sigma (fun l => (Sᶜ.erase i).erase l))
    (f := fun i x => f ![i, x.1, x.2])]
  refine Finset.sum_nbij' (fun x => ![x.1, x.2.1, x.2.2]) (fun I => ⟨I 0, ⟨I 1, I 2⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, l, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_compl] at hx
    obtain ⟨hi, ⟨hli, hl⟩, hJl, hJi, hJ⟩ := hx
    exact mem_dT_three hi hl hJ (Ne.symm hli) (Ne.symm hJi) (Ne.symm hJl)
  · intro I hI
    simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_compl]
    refine ⟨hI.2 0, ⟨?_, hI.2 1⟩, ?_, ?_, hI.2 2⟩
    · intro h; exact absurd (hI.1 h) (by decide)
    · intro h; exact absurd (hI.1 h) (by decide)
    · intro h; exact absurd (hI.1 h) (by decide)
  · rintro ⟨i, l, J⟩ _
    rfl
  · intro I _
    funext m
    fin_cases m <;> rfl
  · intro x _
    rfl


theorem avgR_const_mul (j k : ℕ) (c : ℝ) (h : Finset (Fin N) → (Fin k → Fin N) → ℝ) :
    avgR N j k (fun S I => c * h S I) = c * avgR N j k h := by
  simp only [avgR, ← Finset.mul_sum, mul_left_comm _ c]

theorem avgR_nonneg (j k : ℕ) (h : Finset (Fin N) → (Fin k → Fin N) → ℝ)
    (hh : ∀ S I, 0 ≤ h S I) : 0 ≤ avgR N j k h := by
  unfold avgR
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun S _ =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun I _ => hh S I))

theorem avgR_glob {j k : ℕ} (hjk : j + k ≤ N) (H : (Fin k → Fin N) → ℝ) :
    avgR N j k (fun _ I => H I) =
      (((Nat.descFactorial N k : ℕ) : ℝ)⁻¹) * ∑ J ∈ injTuples N k, H J := by
  set n := N - j with hn
  have hnk : k ≤ n := by omega
  have h1 : ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, H I =
      ((n.descFactorial k : ℕ) : ℝ)⁻¹ * (((N - k).choose j) • ∑ J ∈ injTuples N k, H J) := by
    rw [← Finset.mul_sum]
    congr 1
    exact sum_sum_distinctTuples j k H
  unfold avgR
  rw [← hn, h1, nsmul_eq_mul]
  have key : ((N.choose j : ℕ) : ℝ) * ((n.descFactorial k : ℕ) : ℝ) =
      ((N.descFactorial k : ℕ) : ℝ) * (((N - k).choose j : ℕ) : ℝ) := by
    exact_mod_cast choose_descFactorial_glob hjk
  have hCk : (0 : ℝ) < (((N - k).choose j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hDk : (0 : ℝ) < ((N.descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  have hCj : (0 : ℝ) < ((N.choose j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hdn : (0 : ℝ) < ((n.descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hnk
  field_simp
  linear_combination (-(∑ x ∈ injTuples N k, H x)) * key

theorem avgR_abs_le {j k : ℕ} (hjk : j + k ≤ N) (h : Finset (Fin N) → (Fin k → Fin N) → ℝ)
    {c : ℝ} (hc : ∀ S I, |h S I| ≤ c) : |avgR N j k h| ≤ c := by
  have hdn : (0 : ℝ) < (((N - j).descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  have hCj : (0 : ℝ) < ((N.choose j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  unfold avgR
  rw [abs_mul, abs_of_pos (inv_pos.2 hCj)]
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      |(((N - j).descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, h S I| ≤ c := by
    intro S hS
    rw [abs_mul, abs_of_pos (inv_pos.2 hdn)]
    calc _ ≤ (((N - j).descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, c :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun I _ => hc S I)) (inv_nonneg.2 hdn.le)
      _ = c := by
          rw [Finset.sum_const, card_distinctTuples (Finset.mem_powersetCard.1 hS).2,
            nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdn.ne', one_mul]
  calc _ ≤ ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, c :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum hS)) (inv_nonneg.2 hCj.le)
    _ = c := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hCj.ne', one_mul]

theorem avgR_sqrt_le (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hjk : j + k ≤ N) :
    avgR N j k (fun S I => Real.sqrt (2 * (DRev ν S I).toReal)) ≤
      Real.sqrt (2 * (dRev ν j k).toReal) := by
  set n := N - j with hn
  have hnk : k ≤ n := by omega
  set 𝒮 : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard j with h𝒮
  have h𝒮card : 𝒮.card = N.choose j := by simp [h𝒮]
  have hCj : (0 : ℝ) < ((N.choose j : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hdn : (0 : ℝ) < ((n.descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hnk
  have hdt : ∀ S ∈ 𝒮, (distinctTuples S k).card = n.descFactorial k := fun S hS =>
    card_distinctTuples (Finset.mem_powersetCard.1 hS).2 k
  obtain ⟨D, hD⟩ : ∃ D : Finset (Fin N) → (Fin k → Fin N) → ℝ,
      ∀ S I, D S I = (DRev ν S I).toReal := ⟨_, fun _ _ => rfl⟩
  have hD0 : ∀ S I, 0 ≤ D S I := fun S I => by rw [hD]; exact ENNReal.toReal_nonneg
  obtain ⟨m, hm⟩ : ∃ m : Finset (Fin N) → ℝ, ∀ S,
      m S = ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, D S I :=
    ⟨_, fun _ => rfl⟩
  have hm0 : ∀ S, 0 ≤ m S := fun S => by
    rw [hm]; exact mul_nonneg (inv_nonneg.2 hdn.le) (Finset.sum_nonneg fun I _ => hD0 S I)
  have hd : (dRev ν j k).toReal = ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮, m S := by
    rw [dRev_toReal_eq ν μ hH hjk]
    simp_rw [hm, hD]
    rfl
  have hS_bound : ∀ S ∈ 𝒮, ((n.descFactorial k : ℕ) : ℝ)⁻¹ *
      ∑ I ∈ distinctTuples S k, Real.sqrt (2 * (DRev ν S I).toReal) ≤ Real.sqrt (2 * m S) := by
    intro S hS
    have hne : (distinctTuples S k).Nonempty := by
      rw [← Finset.card_pos, hdt S hS]; exact_mod_cast hdn
    have h4 := uniform_sqrt_le (distinctTuples S k) hne (fun I => 2 * D S I)
      (fun I _ => by have := hD0 S I; positivity)
    rw [hdt S hS] at h4
    have h5 : ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, 2 * D S I =
        2 * m S := by
      rw [hm, ← Finset.mul_sum]; ring
    rw [h5] at h4
    simp only [hD] at h4 ⊢
    exact h4
  have hne𝒮 : 𝒮.Nonempty := by
    rw [← Finset.card_pos, h𝒮card]; exact Nat.choose_pos (by omega)
  have hJ := uniform_sqrt_le 𝒮 hne𝒮 (fun S => 2 * m S) (fun S _ => by
    have := hm0 S; positivity)
  rw [h𝒮card] at hJ
  have e3 : ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮, 2 * m S = 2 * (dRev ν j k).toReal := by
    rw [hd, ← Finset.mul_sum]; ring
  rw [e3] at hJ
  refine le_trans ?_ hJ
  unfold avgR
  rw [← hn]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hCj.le)
  exact Finset.sum_le_sum hS_bound


theorem cast_desc2 (n : ℕ) : ((n.descFactorial 2 : ℕ) : ℝ) = n * (n - 1) :=
  Nat.cast_descFactorial_two ℝ n

theorem cast_desc3 {n : ℕ} (hn : 2 ≤ n) :
    ((n.descFactorial 3 : ℕ) : ℝ) = n * (n - 1) * (n - 2) := by
  have h : n.descFactorial 3 = (n - 2) * n.descFactorial 2 := Nat.descFactorial_succ n 2
  rw [h, Nat.cast_mul, Nat.cast_sub hn, cast_desc2]
  push_cast
  ring

theorem card_compl_pos {S : Finset (Fin N)} {n : ℕ} (hn : Sᶜ.card = n) (h1 : 1 ≤ n) :
    (0 : ℝ) < N := by
  have h2 := Finset.card_le_univ Sᶜ
  simp only [Fintype.card_fin] at h2
  exact_mod_cast (by omega : 0 < N)

theorem slice2 (S : Finset (Fin N)) {n : ℕ} (hn : Sᶜ.card = n) (hn2 : 2 ≤ n)
    (h : (Fin 2 → Fin N) → ℝ) :
    ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, h ![i, l] =
      (((n : ℝ) - 1) / N) *
        (((n.descFactorial 2 : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S 2, h I) := by
  have hN := card_compl_pos hn (by omega)
  have e : ∑ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, h ![i, l] =
      (N : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∑ l ∈ Sᶜ.erase i, h ![i, l] := (Finset.mul_sum _ _ _).symm
  rw [e, conv2, hn, cast_desc2]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := by linarith
  field_simp

theorem slice3 (S : Finset (Fin N)) {n : ℕ} (hn : Sᶜ.card = n) (hn3 : 3 ≤ n)
    (h : (Fin 3 → Fin N) → ℝ) :
    ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i,
        ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ J ∈ (Sᶜ.erase i).erase l, h ![i, l, J] =
      (((n : ℝ) - 1) * ((n : ℝ) - 2) / (N * n)) *
        (((n.descFactorial 3 : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S 3, h I) := by
  have hN := card_compl_pos hn (by omega)
  simp_rw [← Finset.mul_sum]
  rw [conv3, hn, cast_desc3 (by omega)]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := by linarith
  have h3 : (n : ℝ) - 2 ≠ 0 := by linarith
  field_simp

theorem slice1 (S : Finset (Fin N)) {n : ℕ} (hn : Sᶜ.card = n) (hn2 : 2 ≤ n) (c : ℝ) :
    ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ _l ∈ Sᶜ.erase i,
        (c * (2 / ((Sᶜ.card : ℕ) : ℝ))) = (((n : ℝ) - 1) / N) * (c * (2 / n)) := by
  have hN := card_compl_pos hn (by omega)
  have e : ∀ i ∈ Sᶜ, ∑ _l ∈ Sᶜ.erase i, (c * (2 / ((Sᶜ.card : ℕ) : ℝ))) =
      ((n : ℝ) - 1) * (c * (2 / n)) := by
    intro i hi
    rw [Finset.sum_const, Finset.card_erase_of_mem hi, hn, nsmul_eq_mul,
      Nat.cast_sub (by omega), Nat.cast_one]
  rw [Finset.sum_congr rfl (fun i hi => by rw [e i hi]), Finset.sum_const, hn, nsmul_eq_mul]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have h2 : (n : ℝ) ≠ 0 := by linarith
  field_simp


/-- The weighted triple average over `(S, i, l)`. -/
noncomputable def Pq (N j : ℕ) (f : Finset (Fin N) → Fin N → Fin N → ℝ) : ℝ :=
  ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i, f S i l

theorem Pq_sub (j : ℕ) (f g : Finset (Fin N) → Fin N → Fin N → ℝ) :
    Pq N j (fun S i l => f S i l - g S i l) = Pq N j f - Pq N j g := by
  simp only [Pq, Finset.sum_sub_distrib, mul_sub]

theorem Pq_add (j : ℕ) (f g : Finset (Fin N) → Fin N → Fin N → ℝ) :
    Pq N j (fun S i l => f S i l + g S i l) = Pq N j f + Pq N j g := by
  simp only [Pq, Finset.sum_add_distrib, mul_add]

theorem abs_wsum_le {ι : Type*} (s : Finset ι) (w : ℝ) (hw : 0 ≤ w) (f g : ι → ℝ)
    (h : ∀ x ∈ s, |f x| ≤ g x) : |w * ∑ x ∈ s, f x| ≤ w * ∑ x ∈ s, g x := by
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum h)) hw

theorem Pq_abs_le (j : ℕ) (f g : Finset (Fin N) → Fin N → Fin N → ℝ)
    (h : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ, ∀ l ∈ Sᶜ.erase i,
      |f S i l| ≤ g S i l) : |Pq N j f| ≤ Pq N j g := by
  unfold Pq
  refine abs_wsum_le _ _ (by positivity) _ _ fun S hS => ?_
  refine abs_wsum_le _ _ (by positivity) _ _ fun i hi => ?_
  exact abs_wsum_le _ _ (by positivity) _ _ fun l hl => h S hS i hi l hl

theorem hSc_of_mem {j : ℕ} {S : Finset (Fin N)}
    (hS : S ∈ (Finset.univ : Finset (Fin N)).powersetCard j) : Sᶜ.card = N - j := by
  rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hS).2]

theorem Pq_two {j : ℕ} (hj : j + 3 ≤ N) (h : Finset (Fin N) → (Fin 2 → Fin N) → ℝ) :
    Pq N j (fun S i l => h S ![i, l]) =
      ((((N - j : ℕ) : ℝ) - 1) / N) * avgR N j 2 h := by
  unfold Pq avgR
  rw [Finset.sum_congr rfl (fun S hS => slice2 S (hSc_of_mem hS) (by omega) (h S)),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem Pq_three {j : ℕ} (hj : j + 3 ≤ N) (h : Finset (Fin N) → (Fin 3 → Fin N) → ℝ) :
    Pq N j (fun S i l => ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ J ∈ (Sᶜ.erase i).erase l, h S ![i, l, J]) =
      ((((N - j : ℕ) : ℝ) - 1) * (((N - j : ℕ) : ℝ) - 2) / (N * ((N - j : ℕ) : ℝ))) *
        avgR N j 3 h := by
  unfold Pq avgR
  rw [Finset.sum_congr rfl (fun S hS => slice3 S (hSc_of_mem hS) (by omega) (h S)),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem Pq_const {j : ℕ} (hj : j + 3 ≤ N) (c : ℝ) :
    Pq N j (fun S _ _ => c * (2 / ((Sᶜ.card : ℕ) : ℝ))) =
      ((((N - j : ℕ) : ℝ) - 1) / N) * (c * (2 / ((N - j : ℕ) : ℝ))) := by
  unfold Pq
  rw [Finset.sum_congr rfl (fun S hS => slice1 S (hSc_of_mem hS) (by omega) c),
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hCj : (0 : ℝ) < ((N.choose j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp

end Counting


end T2bAux

open T2bAux

/-- Cross term from the unrevealed coordinates: coefficient `(n-1)/N`. -/
theorem T2b_close {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) :
    ∃ C : ℝ, ∀ (N : ℕ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
      (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ → ∀ j, j + 3 ≤ N →
      |avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i,
            ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) -
          (((N - j : ℕ) : ℝ) - 1) / N * globTupleMean ν 3 (A3 bF)| ≤
        C * (1 / ((N - j : ℕ) : ℝ) + Real.sqrt (2 * (dRev ν j 2).toReal) +
          Real.sqrt (2 * (dRev ν j 3).toReal)) := by
  refine ⟨4 * (d * Bb ^ 2), ?_⟩
  intro N μ _ ν _ hH j hj
  classical
  set n : ℕ := N - j with hn
  have hn3 : 3 ≤ n := by omega
  have hnN : n ≤ N := by omega
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith
  have hNn : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN : (0 : ℝ) < N := by linarith
  set c : ℝ := d * Bb ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hA3m : Measurable (A3 bF : (Fin 3 → Torus d) → ℝ) :=
    Finset.measurable_sum _ fun k _ => (measurable_bF_pair hB 0 1 k).mul
      (measurable_bF_pair hB 0 2 k)
  have hA3b : ∀ z : Fin 3 → Torus d, |A3 bF z| ≤ c := fun z =>
    abs_sum_mul_le (fun k => hB.bound _ _ k) (fun k => hB.bound _ _ k)
  set Tt : Finset (Fin N) → Fin N → Fin N → ℝ := fun S i l =>
    ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν with hTt
  set Hh : (Fin 3 → Fin N) → ℝ := fun I => ∫ X, A3 bF (X ∘ I) ∂ν with hHh
  set s2 : Finset (Fin N) → (Fin 2 → Fin N) → ℝ := fun S I =>
    Real.sqrt (2 * (DRev ν S I).toReal) with hs2
  set s3 : Finset (Fin N) → (Fin 3 → Fin N) → ℝ := fun S I =>
    Real.sqrt (2 * (DRev ν S I).toReal) with hs3
  set E : Finset (Fin N) → Fin N → Fin N → ℝ := fun S i l =>
    ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ J ∈ (Sᶜ.erase i).erase l, Hh ![i, l, J] with hE
  set Bd : Finset (Fin N) → Fin N → Fin N → ℝ := fun S i l =>
    c * s2 S ![i, l] + ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ J ∈ (Sᶜ.erase i).erase l, c * s3 S ![i, l, J] +
      c * (2 / ((Sᶜ.card : ℕ) : ℝ)) with hBd
  have hpair : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ,
      ∀ l ∈ Sᶜ.erase i, |Tt S i l - E S i l| ≤ Bd S i l := by
    intro S hS i hi l hl
    have h := pair_claim hB ν μ hH S (by rw [hSc_of_mem hS]; exact hn3) i l hi hl
    refine h.trans (le_of_eq ?_)
    simp only [hBd, hs2, hs3]
    rw [← Finset.mul_sum]
    ring
  have h1 : |Pq N j Tt - Pq N j E| ≤ Pq N j Bd := by
    rw [← Pq_sub]
    exact Pq_abs_le j _ _ hpair
  have h2 : Pq N j Bd = (((n : ℝ) - 1) / N) * (c * avgR N j 2 s2) +
      ((((n : ℝ) - 1) * ((n : ℝ) - 2) / (N * n)) * (c * avgR N j 3 s3)) +
      (((n : ℝ) - 1) / N) * (c * (2 / n)) := by
    have e1 := Pq_two hj (fun S I => c * s2 S I)
    have e2 := Pq_three hj (fun S I => c * s3 S I)
    have e3 := Pq_const hj c
    rw [avgR_const_mul] at e1 e2
    simp only [hBd]
    rw [Pq_add, Pq_add, e1, e2, e3]
  have hE3 : Pq N j E = (((n : ℝ) - 1) * ((n : ℝ) - 2) / (N * n)) *
      globTupleMean ν 3 (A3 bF) := by
    have h := Pq_three hj (fun _ I => Hh I)
    rw [avgR_glob (by omega)] at h
    exact h
  have hC3 : |globTupleMean ν 3 (A3 bF)| ≤ c := by
    have h := avgR_abs_le (N := N) (j := j) (k := 3) (by omega) (fun _ I => Hh I) (c := c)
      (fun S I => abs_integral_le_of_prob ν _ fun X => hA3b _)
    rw [avgR_glob (by omega)] at h
    exact h
  have a2 : avgR N j 2 s2 ≤ Real.sqrt (2 * (dRev ν j 2).toReal) :=
    avgR_sqrt_le ν μ hH (by omega)
  have a3 : avgR N j 3 s3 ≤ Real.sqrt (2 * (dRev ν j 3).toReal) :=
    avgR_sqrt_le ν μ hH (by omega)
  have x2 : 0 ≤ avgR N j 2 s2 := avgR_nonneg j 2 s2 fun S I => Real.sqrt_nonneg _
  have x3 : 0 ≤ avgR N j 3 s3 := avgR_nonneg j 3 s3 fun S I => Real.sqrt_nonneg _
  set r2 := Real.sqrt (2 * (dRev ν j 2).toReal) with hr2
  set r3 := Real.sqrt (2 * (dRev ν j 3).toReal) with hr3
  have hr2' : 0 ≤ r2 := Real.sqrt_nonneg _
  have hr3' : 0 ≤ r3 := Real.sqrt_nonneg _
  set P : ℝ := ((n : ℝ) - 1) / N with hP
  set K : ℝ := ((n : ℝ) - 1) * ((n : ℝ) - 2) / (N * n) with hK
  have hP0 : 0 ≤ P := div_nonneg (by linarith) hN.le
  have hP1 : P ≤ 1 := (div_le_one hN).2 (by linarith)
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hK1 : K ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
  have hA : P * (c * avgR N j 2 s2) ≤ c * r2 := by
    calc P * (c * avgR N j 2 s2) ≤ 1 * (c * r2) :=
          mul_le_mul hP1 (mul_le_mul_of_nonneg_left a2 hc0) (mul_nonneg hc0 x2) zero_le_one
      _ = c * r2 := one_mul _
  have hB' : K * (c * avgR N j 3 s3) ≤ c * r3 := by
    calc K * (c * avgR N j 3 s3) ≤ 1 * (c * r3) :=
          mul_le_mul hK1 (mul_le_mul_of_nonneg_left a3 hc0) (mul_nonneg hc0 x3) zero_le_one
      _ = c * r3 := one_mul _
  have hC' : P * (c * (2 / n)) ≤ c * (2 / n) :=
    mul_le_of_le_one_left (by positivity) hP1
  have hdiff : |K * globTupleMean ν 3 (A3 bF) - P * globTupleMean ν 3 (A3 bF)| ≤
      c * (2 / n) := by
    have e : K * globTupleMean ν 3 (A3 bF) - P * globTupleMean ν 3 (A3 bF) =
        (-(2 * P / n)) * globTupleMean ν 3 (A3 bF) := by
      simp only [hK, hP]
      field_simp
      ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    calc 2 * P / n * |globTupleMean ν 3 (A3 bF)| ≤ 2 * P / n * c :=
          mul_le_mul_of_nonneg_left hC3 (by positivity)
      _ ≤ 2 * 1 / n * c := by gcongr
      _ = c * (2 / n) := by ring
  have hQ : avg1R N j (fun S i => (N : ℝ)⁻¹ * ∑ l ∈ Sᶜ.erase i,
      ∫ X, ∑ k : Fin d, BS bF ν S X (X i) k * bF (X i) (X l) k ∂ν) = Pq N j Tt := rfl
  rw [hQ]
  have e1 := abs_sub_le (Pq N j Tt) (Pq N j E) (P * globTupleMean ν 3 (A3 bF))
  have hdiff2 : |Pq N j E - P * globTupleMean ν 3 (A3 bF)| ≤ c * (2 / n) := by
    rw [hE3]; exact hdiff
  rw [h2] at h1
  have hnn : 0 ≤ c * (1 / (n : ℝ)) := by positivity
  have e4 : c * (2 / (n : ℝ)) = 2 * (c * (1 / n)) := by ring
  have e5 : 4 * c * (1 / (n : ℝ) + r2 + r3) =
      4 * (c * (1 / n)) + 4 * (c * r2) + 4 * (c * r3) := by ring
  have h6 : 0 ≤ c * r2 := mul_nonneg hc0 hr2'
  have h7 : 0 ≤ c * r3 := mul_nonneg hc0 hr3'
  rw [e5]
  linarith [e1, h1, hdiff2, hA, hB', hC', e4]

end SharpLSI.FL
