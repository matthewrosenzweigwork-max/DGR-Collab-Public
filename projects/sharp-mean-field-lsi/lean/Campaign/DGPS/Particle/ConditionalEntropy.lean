import DGPS.Measure.EntropyChain
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Independence.Basic

/-!
# Conditioning entropy identities (LIP043)

Marginal-entropy supermodularity, permutation averaging and the conditioning entropy identities.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace DGPS.Lipschitz

section Pyth

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]

theorem klDiv_pyth (ν : Measure (Y × Z)) [IsProbabilityMeasure ν] (P : Measure Y) (Q : Measure Z)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDiv ν (P.prod Q) = klDiv ν.fst P + klDiv ν (ν.fst.prod Q) := by
  have h := klDiv_compProd_eq_add ν.fst P ν.condKernel (Kernel.const Y Q)
  rw [Measure.disintegrate ν ν.condKernel, Measure.compProd_const] at h
  rw [Measure.compProd_const] at h
  exact h

theorem klDiv_supermod {α : Type*} [MeasurableSpace α] (q : Y → α) (hq : Measurable q)
    (ν : Measure (Y × Z)) [IsProbabilityMeasure ν] (R : Measure Y) [IsProbabilityMeasure R]
    (Pβ : Measure Z) [IsProbabilityMeasure Pβ] :
    klDiv ν.fst R + klDiv (ν.map (Prod.map q id)) ((R.map q).prod Pβ)
      ≤ klDiv ν (R.prod Pβ) + klDiv (ν.fst.map q) (R.map q) := by
  have hg : Measurable (Prod.map q (id : Z → Z)) := hq.prodMap measurable_id
  have P1 := klDiv_pyth ν R Pβ
  have P2 := klDiv_pyth (ν.map (Prod.map q id)) (R.map q) Pβ
  have hfst : (ν.map (Prod.map q id)).fst = ν.fst.map q := by
    simp only [Measure.fst]
    rw [Measure.map_map measurable_fst hg, Measure.map_map hq measurable_fst]
    rfl
  have hmap : (ν.fst.prod Pβ).map (Prod.map q id) = (ν.fst.map q).prod Pβ := by
    have := Measure.map_prod_map ν.fst Pβ hq (measurable_id : Measurable (id : Z → Z))
    simpa using this.symm
  have DPI : klDiv (ν.map (Prod.map q id)) ((ν.map (Prod.map q id)).fst.prod Pβ)
      ≤ klDiv ν (ν.fst.prod Pβ) := by
    rw [hfst, ← hmap]
    exact klDiv_map_le ν (ν.fst.prod Pβ) hg
  rw [hfst] at P2 DPI
  rw [P2, P1]
  calc _ ≤ klDiv ν.fst R + (klDiv (ν.fst.map q) (R.map q) + klDiv ν (ν.fst.prod Pβ)) := by
        gcongr
    _ = _ := by ring

end Pyth


section Marginals

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {N : ℕ}

/-- The product reference law `Q_N = μ^{⊗N}` on `Fin N → X`. -/
noncomputable abbrev refLaw (μ : Measure X) (N : ℕ) : Measure (Fin N → X) :=
  Measure.pi fun _ : Fin N => μ

/-- Coordinate restriction to a finite set of labels. -/
abbrev rst (C : Finset (Fin N)) : (Fin N → X) → (C → X) := fun ω i => ω i

theorem measurable_rst (C : Finset (Fin N)) : Measurable (rst (X := X) C) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- Marginal divergence of `ν` on the labels `C`, in `ℝ≥0∞`. -/
noncomputable def margKL (ν : Measure (Fin N → X)) (C : Finset (Fin N)) : ℝ≥0∞ :=
  klDiv (ν.map (rst C)) ((refLaw μ N).map (rst C))

theorem klDiv_map_comp_eq {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] (T : Ω → A) (F : A → B) (G : B → A) (hT : Measurable T)
    (hF : Measurable F) (hG : Measurable G) (hFG : ∀ ω, G (F (T ω)) = T ω) (ν ρ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    klDiv (ν.map (F ∘ T)) (ρ.map (F ∘ T)) = klDiv (ν.map T) (ρ.map T) := by
  apply le_antisymm
  · have := klDiv_map_le (ν.map T) (ρ.map T) hF
    rwa [Measure.map_map hF hT, Measure.map_map hF hT] at this
  · have := klDiv_map_le (ν.map (F ∘ T)) (ρ.map (F ∘ T)) hG
    have e : G ∘ (F ∘ T) = T := funext fun ω => hFG ω
    rwa [Measure.map_map hG (hF.comp hT), Measure.map_map hG (hF.comp hT), e] at this

/-- independence of disjoint blocks under the product measure -/
theorem pi_map_rst_prod [IsProbabilityMeasure μ] (C D : Finset (Fin N)) (hCD : Disjoint C D) :
    (refLaw μ N).map (fun ω => (rst (X := X) C ω, rst (X := X) D ω))
      = ((refLaw μ N).map (rst C)).prod ((refLaw μ N).map (rst D)) := by
  have hind : iIndepFun (fun (i : Fin N) (ω : Fin N → X) => ω i) (refLaw μ N) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun_finset C D hCD (fun i => measurable_pi_apply i)
  exact (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_rst C).aemeasurable (measurable_rst D).aemeasurable).1 h2


variable {μ}

theorem margKL_pair_eq [IsProbabilityMeasure μ] (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]
    (C D : Finset (Fin N)) :
    klDiv (ν.map (fun ω => (rst (X := X) C ω, rst (X := X) D ω)))
      ((refLaw μ N).map (fun ω => (rst (X := X) C ω, rst (X := X) D ω))) = margKL μ ν (C ∪ D) := by
  classical
  let F : (↥(C ∪ D) → X) → (C → X) × (D → X) := fun w =>
    (fun i => w ⟨i.1, Finset.mem_union_left D i.2⟩, fun i => w ⟨i.1, Finset.mem_union_right C i.2⟩)
  let G : (C → X) × (D → X) → (↥(C ∪ D) → X) := fun w i =>
    if h : i.1 ∈ C then w.1 ⟨i.1, h⟩ else w.2 ⟨i.1, (Finset.mem_union.1 i.2).resolve_left h⟩
  have hF : Measurable F :=
    (Measurable.of_eval fun i => measurable_pi_apply _).prodMk
      (Measurable.of_eval fun i => measurable_pi_apply _)
  have hG : Measurable G := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : i.1 ∈ C
    · simp only [G, h, dite_true]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [G, h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  have key := klDiv_map_comp_eq (rst (X := X) (C ∪ D)) F G (measurable_rst _) hF hG
    (fun ω => by
      funext i
      by_cases h : i.1 ∈ C <;> simp [G, F, h]) ν (refLaw μ N)
  exact key

theorem margKL_le_top_of {N : ℕ} (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (C : Finset (Fin N)) :
    margKL μ ν C ≤ klDiv ν (refLaw μ N) := by
  have := klDiv_map_le ν (refLaw μ N) (measurable_rst (X := X) C)
  exact this

theorem margKL_supermod [StandardBorelSpace X] [Nonempty X] [IsProbabilityMeasure μ]
    (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (A B : Finset (Fin N)) :
    margKL μ ν B + margKL μ ν A ≤ margKL μ ν (A ∪ B) + margKL μ ν (A ∩ B) := by
  classical
  have hdisjA : Disjoint B (A \ B) := Finset.disjoint_sdiff
  have hdisjI : Disjoint (A ∩ B) (A \ B) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    exact (Finset.mem_sdiff.1 hx').2 (Finset.mem_inter.1 hx).2
  let q : (↥B → X) → (↥(A ∩ B) → X) := fun w i => w ⟨i.1, (Finset.mem_inter.1 i.2).2⟩
  have hq : Measurable q := Measurable.of_eval fun i => measurable_pi_apply _
  let ν' : Measure ((↥B → X) × (↥(A \ B) → X)) :=
    ν.map (fun ω => (rst (X := X) B ω, rst (X := X) (A \ B) ω))
  let ρ := refLaw μ N
  have hpair : Measurable (fun ω : Fin N → X => (rst (X := X) B ω, rst (X := X) (A \ B) ω)) :=
    (measurable_rst _).prodMk (measurable_rst _)
  have hq' : Measurable (fun ω : Fin N → X => (q (rst (X := X) B ω), rst (X := X) (A \ B) ω)) :=
    (hq.comp (measurable_rst _)).prodMk (measurable_rst _)
  have main := klDiv_supermod q hq ν' (ρ.map (rst B)) (ρ.map (rst (A \ B)))
  -- identify the four terms
  have e1 : ν'.fst = ν.map (rst (X := X) B) := by
    simp only [ν', Measure.fst]
    rw [Measure.map_map measurable_fst hpair]; rfl
  have e2 : ν'.map (Prod.map q id) =
      ν.map (fun ω => (rst (X := X) (A ∩ B) ω, rst (X := X) (A \ B) ω)) := by
    simp only [ν']
    rw [Measure.map_map (hq.prodMap measurable_id) hpair]; rfl
  have e3 : (ρ.map (rst B)).prod (ρ.map (rst (A \ B))) =
      ρ.map (fun ω => (rst (X := X) B ω, rst (X := X) (A \ B) ω)) :=
    (pi_map_rst_prod μ B (A \ B) hdisjA).symm
  have e4 : ((ρ.map (rst B)).map q).prod (ρ.map (rst (A \ B))) =
      ρ.map (fun ω => (rst (X := X) (A ∩ B) ω, rst (X := X) (A \ B) ω)) := by
    rw [Measure.map_map hq (measurable_rst _)]
    exact (pi_map_rst_prod μ (A ∩ B) (A \ B) hdisjI).symm
  have e5 : (ν.map (rst (X := X) B)).map q = ν.map (rst (X := X) (A ∩ B)) := by
    rw [Measure.map_map hq (measurable_rst _)]; rfl
  have e6 : (ρ.map (rst B)).map q = ρ.map (rst (X := X) (A ∩ B)) := by
    rw [Measure.map_map hq (measurable_rst _)]; rfl
  have u1 : B ∪ (A \ B) = A ∪ B := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have u2 : (A ∩ B) ∪ (A \ B) = A := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [e1, e2, e3, e4, e5, e6] at main
  have p1 := margKL_pair_eq (μ := μ) ν B (A \ B)
  have p2 := margKL_pair_eq (μ := μ) ν (A ∩ B) (A \ B)
  rw [u1] at p1
  rw [u2] at p2
  simp only [ν'] at main
  rw [p1, p2] at main
  exact main

end Marginals

section RealLayer

open Finset

/-- shifted sum telescoping -/
theorem sum_shift_sub (h : ℕ → ℝ) (L a : ℕ) :
    ∑ j ∈ range L, (h (j + a) - h j) = ∑ i ∈ range a, (h (L + i) - h i) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ← ih]
    have : ∑ j ∈ range L, h (j + (a + 1)) = ∑ j ∈ range L, h (j + a) + h (L + a) - h a := by
      have h1 : ∑ j ∈ range (L + 1), h (j + a) = ∑ j ∈ range L, h (j + a) + h (L + a) :=
        sum_range_succ _ _
      have h2 : ∑ j ∈ range (L + 1), h (j + a) = h a + ∑ j ∈ range L, h (j + 1 + a) :=
        by rw [sum_range_succ' (fun j => h (j + a)) L, add_comm]; simp [add_comm]
      have h3 : ∑ j ∈ range L, h (j + (a + 1)) = ∑ j ∈ range L, h (j + 1 + a) :=
        sum_congr rfl fun j _ => by ring_nf
      linarith
    simp only [sum_sub_distrib]
    linarith

theorem sum_range_cast (k : ℕ) : ∑ a ∈ range k, (a : ℝ) = (k : ℝ) * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem real_bound (h : ℕ → ℝ) (N : ℕ) (H : ℝ)
    (hnn : ∀ j, j < N → 0 ≤ h j) (hmono : ∀ j, j + 1 < N → h j ≤ h (j + 1))
    (hsum : ∑ j ∈ range N, h j = H) (k M : ℕ) (hkM : k ≤ M) (hMN : M ≤ N) :
    ∑ j ∈ range (N - M), (∑ a ∈ range k, h (j + a) - k * h j)
      ≤ ((k : ℝ) * (k - 1) / ((M : ℝ) - k + 2)) * H := by
  have hH : 0 ≤ H := hsum ▸ sum_nonneg fun j hj => hnn j (mem_range.1 hj)
  have hmono' : ∀ s t, s ≤ t → t < N → h s ≤ h t := by
    intro s t hst htN
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t hst ih => exact (ih (by omega)).trans (hmono t htN)
  -- (N - t) * h t ≤ H
  have hA : ∀ t, t < N → ((N : ℝ) - t) * h t ≤ H := by
    intro t ht
    have h1 : ∑ u ∈ Ico t N, h t ≤ ∑ u ∈ Ico t N, h u :=
      sum_le_sum fun u hu => hmono' t u (mem_Ico.1 hu).1 (mem_Ico.1 hu).2
    have h2 : ∑ u ∈ Ico t N, h t = ((N : ℝ) - t) * h t := by
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub ht.le]
    have h3 : ∑ u ∈ range t, h u + ∑ u ∈ Ico t N, h u = ∑ u ∈ range N, h u :=
      sum_range_add_sum_Ico _ ht.le
    have h4 : 0 ≤ ∑ u ∈ range t, h u := sum_nonneg fun u hu => hnn u (by have := mem_range.1 hu; omega)
    linarith
  set c : ℝ := (M : ℝ) - k + 2 with hc
  have hcpos : 0 < c := by
    have : (k : ℝ) ≤ M := by exact_mod_cast hkM
    linarith
  -- bound on individual values near the top
  have hB : ∀ t, t < N → c ≤ (N : ℝ) - t → h t ≤ H / c := by
    intro t ht hct
    rw [le_div_iff₀ hcpos]
    calc h t * c ≤ h t * ((N : ℝ) - t) := mul_le_mul_of_nonneg_left hct (hnn t ht)
      _ = ((N : ℝ) - t) * h t := by ring
      _ ≤ H := hA t ht
  -- rewrite the inner term
  have hinner : ∀ j, ∑ a ∈ range k, h (j + a) - k * h j = ∑ a ∈ range k, (h (j + a) - h j) := by
    intro j; rw [sum_sub_distrib]; simp
  simp_rw [hinner]
  rw [sum_comm]
  have hterm : ∀ a ∈ range k, ∑ j ∈ range (N - M), (h (j + a) - h j) ≤ (a : ℝ) * (H / c) := by
    intro a ha
    have ha' := mem_range.1 ha
    rw [sum_shift_sub]
    calc ∑ i ∈ range a, (h (N - M + i) - h i) ≤ ∑ i ∈ range a, h (N - M + i) :=
          sum_le_sum fun i hi => by
            have := hnn i (by have := mem_range.1 hi; omega); linarith
      _ ≤ ∑ i ∈ range a, H / c := by
          refine sum_le_sum fun i hi => ?_
          have hi' := mem_range.1 hi
          have hlt : N - M + i < N := by omega
          apply hB _ hlt
          have : ((N - M + i : ℕ) : ℝ) = (N : ℝ) - M + i := by
            rw [Nat.cast_add, Nat.cast_sub hMN]
          rw [this, hc]
          have : (i : ℝ) + 1 ≤ k - 1 := by
            have : i + 1 ≤ k - 1 := by omega
            have h2 : ((i + 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast this
            rw [Nat.cast_sub (by omega)] at h2; push_cast at h2; linarith
          linarith
      _ = (a : ℝ) * (H / c) := by simp
  calc ∑ a ∈ range k, ∑ j ∈ range (N - M), (h (j + a) - h j)
      ≤ ∑ a ∈ range k, (a : ℝ) * (H / c) := sum_le_sum hterm
    _ = ((∑ a ∈ range k, (a : ℝ))) * (H / c) := by rw [← sum_mul]
    _ = ((k : ℝ) * (k - 1) / 2) * (H / c) := by
        rw [sum_range_cast]
    _ ≤ ((k : ℝ) * (k - 1) / c) * H := by
        have hk : (0:ℝ) ≤ (k : ℝ) * (k - 1) := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · simp [h0]
          · have : (1:ℝ) ≤ k := by exact_mod_cast h0
            nlinarith
        have hc2 : 2 ≤ c := by
          have : (k : ℝ) ≤ M := by exact_mod_cast hkM
          rw [hc]; linarith
        have e : ((k : ℝ) * (k - 1) / c) * H - ((k : ℝ) * (k - 1) / 2) * (H / c)
            = ((k : ℝ) * (k - 1)) * H * (1 / c - 1 / (2 * c)) := by field_simp
        have : 0 ≤ ((k : ℝ) * (k - 1)) * H * (1 / c - 1 / (2 * c)) := by
          apply mul_nonneg (mul_nonneg hk hH)
          rw [sub_nonneg]
          apply one_div_le_one_div_of_le hcpos; linarith
        linarith

end RealLayer

section RealMarg

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {N : ℕ}

/-- Real-valued marginal relative entropy of `ν` on the labels `C`. -/
noncomputable def margEnt (ν : Measure (Fin N → X)) (C : Finset (Fin N)) : ℝ :=
  (margKL μ ν C).toReal

theorem margEnt_nonneg (ν : Measure (Fin N → X)) (C : Finset (Fin N)) : 0 ≤ margEnt μ ν C :=
  ENNReal.toReal_nonneg

theorem margEnt_supermod [StandardBorelSpace X] [Nonempty X] [IsProbabilityMeasure μ]
    (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤)
    (A B : Finset (Fin N)) :
    margEnt μ ν B + margEnt μ ν A ≤ margEnt μ ν (A ∪ B) + margEnt μ ν (A ∩ B) := by
  have h := margKL_supermod (μ := μ) ν A B
  have hne : ∀ C, margKL μ ν C ≠ ⊤ := fun C => ne_top_of_le_ne_top hfin (margKL_le_top_of ν C)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne _, hne _⟩) h
  rw [ENNReal.toReal_add (hne _) (hne _), ENNReal.toReal_add (hne _) (hne _)] at h2
  exact h2

theorem measure_eq_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    (m n : Measure α) [IsProbabilityMeasure m] [IsProbabilityMeasure n] : m = n := by
  ext s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
    simp [this]

theorem margEnt_empty [IsProbabilityMeasure μ] (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] :
    margEnt μ ν ∅ = 0 := by
  unfold margEnt margKL
  rw [measure_eq_of_subsingleton (ν.map (rst (X := X) ∅)) ((refLaw μ N).map (rst (X := X) ∅)),
    klDiv_self]
  rfl

theorem margEnt_univ [IsProbabilityMeasure μ] (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] :
    margEnt μ ν Finset.univ = (klDiv ν (refLaw μ N)).toReal := by
  unfold margEnt margKL
  congr 1
  let G : (↥(Finset.univ : Finset (Fin N)) → X) → (Fin N → X) := fun w i => w ⟨i, Finset.mem_univ _⟩
  have hG : Measurable G := Measurable.of_eval fun i => measurable_pi_apply _
  have key := klDiv_map_comp_eq (id : (Fin N → X) → (Fin N → X)) (rst (X := X) Finset.univ) G
    measurable_id (measurable_rst _) hG (fun ω => rfl) ν (refLaw μ N)
  rw [Measure.map_id, Measure.map_id] at key
  exact key

end RealMarg


section PermAvg

open Finset Equiv

/-- Average over all permutations of `Fin N` (uniform random ordering of the labels). -/
noncomputable def permAvg (N : ℕ) (g : Perm (Fin N) → ℝ) : ℝ := (∑ σ, g σ) / (N.factorial : ℝ)

theorem permAvg_sub {N : ℕ} (f g : Perm (Fin N) → ℝ) :
    permAvg N (fun σ => f σ - g σ) = permAvg N f - permAvg N g := by
  simp [permAvg, sum_sub_distrib, sub_div]

theorem permAvg_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Perm (Fin N) → ℝ) :
    permAvg N (fun σ => ∑ a ∈ s, f a σ) = ∑ a ∈ s, permAvg N (f a) := by
  simp only [permAvg]
  rw [sum_comm, sum_div]

theorem permAvg_const (N : ℕ) (c : ℝ) : permAvg N (fun _ => c) = c := by
  have : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  simp [permAvg, Fintype.card_perm]
  field_simp

theorem permAvg_nonneg {N : ℕ} (f : Perm (Fin N) → ℝ) (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ permAvg N f :=
  div_nonneg (sum_nonneg fun σ _ => hf σ) (Nat.cast_nonneg _)

/-- Labels among the first `m` positions of the ordering `σ`. -/
def revealed {N : ℕ} (σ : Perm (Fin N)) (m : ℕ) : Finset (Fin N) :=
  univ.filter fun i => ((σ.symm i : Fin N) : ℕ) < m

/-- Labels among the first `j` positions of `σ`, together with the label at position `j + a`. -/
def revealedPlus {N : ℕ} (σ : Perm (Fin N)) (j a : ℕ) : Finset (Fin N) :=
  univ.filter fun i => ((σ.symm i : Fin N) : ℕ) < j ∨ ((σ.symm i : Fin N) : ℕ) = j + a

theorem revealedPlus_zero {N : ℕ} (σ : Perm (Fin N)) (j : ℕ) :
    revealedPlus σ j 0 = revealed σ (j + 1) := by
  ext i; simp only [revealedPlus, revealed, mem_filter, mem_univ, true_and]; omega

theorem revealed_zero {N : ℕ} (σ : Perm (Fin N)) : revealed σ 0 = ∅ := by
  ext i; simp [revealed]

theorem revealed_full {N : ℕ} (σ : Perm (Fin N)) : revealed σ N = univ := by
  ext i; simp only [revealed, mem_filter, mem_univ, true_and, iff_true]; exact (σ.symm i).2

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {N : ℕ} (ν : Measure (Fin N → X))

/-- Entropy of the label at position `j + a` given the first `j` labels (marginal-difference form). -/
noncomputable def condEnt (σ : Perm (Fin N)) (j a : ℕ) : ℝ :=
  margEnt μ ν (revealedPlus σ j a) - margEnt μ ν (revealed σ j)

/-- Joint entropy of the labels at positions `j, ..., j+k-1` given the first `j` labels. -/
noncomputable def jointCondEnt (σ : Perm (Fin N)) (j k : ℕ) : ℝ :=
  margEnt μ ν (revealed σ (j + k)) - margEnt μ ν (revealed σ j)

/-- Total correlation of the labels at positions `j, ..., j+k-1` given the first `j` labels. -/
noncomputable def totalCorr (σ : Perm (Fin N)) (j k : ℕ) : ℝ :=
  jointCondEnt μ ν σ j k - ∑ a ∈ range k, condEnt μ ν σ j a

/-- `h_j`. -/
noncomputable def condEntAvg (j : ℕ) : ℝ := permAvg N fun σ => condEnt μ ν σ j 0

/-- `d_{j,k}`. -/
noncomputable def totalCorrAvg (j k : ℕ) : ℝ := permAvg N fun σ => totalCorr μ ν σ j k

/-- Average marginal entropy of the first `m` labels. -/
noncomputable def revAvg (m : ℕ) : ℝ := permAvg N fun σ => margEnt μ ν (revealed σ m)

theorem condEntAvg_eq (j : ℕ) : condEntAvg μ ν j = revAvg μ ν (j + 1) - revAvg μ ν j := by
  unfold condEntAvg revAvg
  rw [← permAvg_sub]
  congr 1
  funext σ
  simp only [condEnt, revealedPlus_zero]

theorem condEnt_shift (j a : ℕ) (hja : j + a < N) :
    permAvg N (fun σ => condEnt μ ν σ j a) = permAvg N (fun σ => condEnt μ ν σ j 0) := by
  have hj : j < N := by omega
  let p : Fin N := ⟨j, hj⟩
  let q : Fin N := ⟨j + a, hja⟩
  have h1 : ∀ x : Fin N, (((swap p q) x : Fin N) : ℕ) < j ↔ (x : ℕ) < j := by
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp_all [p, q, Fin.ext_iff]
  have h2 : ∀ x : Fin N, ((((swap p q) x : Fin N) : ℕ) < j ∨ (((swap p q) x : Fin N) : ℕ) = j + 0)
      ↔ ((x : ℕ) < j ∨ (x : ℕ) = j + a) := by
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp_all [p, q, Fin.ext_iff]
  have hs : ∀ (σ : Perm (Fin N)) i, (σ * swap p q).symm i = swap p q (σ.symm i) := by
    intro σ i
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  have key : ∀ σ : Perm (Fin N), condEnt μ ν σ j a = condEnt μ ν (σ * swap p q) j 0 := by
    intro σ
    have e1 : revealed (σ * swap p q) j = revealed σ j := by
      ext i; simp only [revealed, mem_filter, mem_univ, true_and, hs]; exact h1 _
    have e2 : revealedPlus (σ * swap p q) j 0 = revealedPlus σ j a := by
      ext i; simp only [revealedPlus, mem_filter, mem_univ, true_and, hs]; exact h2 _
    simp only [condEnt, e1, e2]
  unfold permAvg
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight (swap p q)) _ _ key

theorem totalCorrAvg_eq (j k : ℕ) (hjk : j + k ≤ N) :
    totalCorrAvg μ ν j k = ∑ a ∈ range k, condEntAvg μ ν (j + a) - k * condEntAvg μ ν j := by
  have step1 : totalCorrAvg μ ν j k
      = (revAvg μ ν (j + k) - revAvg μ ν j)
        - ∑ a ∈ range k, permAvg N (fun σ => condEnt μ ν σ j a) := by
    unfold totalCorrAvg totalCorr
    rw [permAvg_sub, permAvg_sum]
    unfold jointCondEnt revAvg
    rw [permAvg_sub]
  have step2 : ∑ a ∈ range k, permAvg N (fun σ => condEnt μ ν σ j a)
      = k * condEntAvg μ ν j := by
    rw [sum_congr rfl (g := fun _ => condEntAvg μ ν j)]
    · simp
    · intro a ha
      exact condEnt_shift μ ν j a (by have := mem_range.1 ha; omega)
  have step3 : revAvg μ ν (j + k) - revAvg μ ν j = ∑ a ∈ range k, condEntAvg μ ν (j + a) := by
    have := sum_range_sub (fun a => revAvg μ ν (j + a)) k
    simp only [add_zero] at this
    rw [← this]
    refine sum_congr rfl fun a _ => ?_
    rw [condEntAvg_eq, ← Nat.add_assoc]
  rw [step1, step2, step3]

variable [StandardBorelSpace X] [Nonempty X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem totalCorr_two_nonneg (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (σ : Perm (Fin N)) (j : ℕ) :
    0 ≤ totalCorr μ ν σ j 2 := by
  have hs := margEnt_supermod μ ν hfin (revealed σ (j + 1)) (revealedPlus σ j 1)
  have hU : revealed σ (j + 1) ∪ revealedPlus σ j 1 = revealed σ (j + 2) := by
    ext i; simp only [revealed, revealedPlus, mem_union, mem_filter, mem_univ, true_and]; omega
  have hI : revealed σ (j + 1) ∩ revealedPlus σ j 1 = revealed σ j := by
    ext i; simp only [revealed, revealedPlus, mem_inter, mem_filter, mem_univ, true_and]; omega
  rw [hU, hI] at hs
  simp only [totalCorr, condEnt, jointCondEnt, sum_range_succ, sum_range_zero, revealedPlus_zero]
  linarith

theorem condEntAvg_succ_sub (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (j : ℕ) (hj : j + 2 ≤ N) :
    condEntAvg μ ν (j + 1) - condEntAvg μ ν j = totalCorrAvg μ ν j 2 ∧ 0 ≤ totalCorrAvg μ ν j 2 := by
  have e := totalCorrAvg_eq μ ν j 2 hj
  have e2 : ∑ a ∈ range 2, condEntAvg μ ν (j + a) = condEntAvg μ ν j + condEntAvg μ ν (j + 1) := by
    simp [sum_range_succ]
  refine ⟨?_, permAvg_nonneg _ fun σ => totalCorr_two_nonneg μ ν hfin σ j⟩
  rw [e, e2]; push_cast; ring

omit [StandardBorelSpace X] [Nonempty X] in
theorem revAvg_zero : revAvg μ ν 0 = 0 := by
  unfold revAvg
  simp only [revealed_zero, margEnt_empty]
  exact permAvg_const N 0

omit [StandardBorelSpace X] [Nonempty X] in
theorem revAvg_full : revAvg μ ν N = (klDiv ν (refLaw μ N)).toReal := by
  unfold revAvg
  simp only [revealed_full, margEnt_univ]
  exact permAvg_const N _

theorem condEntAvg_nonneg (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (j : ℕ) (hj : j < N) :
    0 ≤ condEntAvg μ ν j := by
  induction j with
  | zero =>
    rw [condEntAvg_eq, revAvg_zero]
    simp only [zero_add]
    have : 0 ≤ revAvg μ ν 1 :=
      permAvg_nonneg _ fun σ => margEnt_nonneg μ ν _
    linarith
  | succ j ih =>
    have := (condEntAvg_succ_sub μ ν hfin j (by omega)).1
    have h2 := (condEntAvg_succ_sub μ ν hfin j (by omega)).2
    have := ih (by omega)
    linarith

omit [StandardBorelSpace X] [Nonempty X] in
theorem condEntAvg_sum :
    ∑ j ∈ range N, condEntAvg μ ν j = (klDiv ν (refLaw μ N)).toReal := by
  have := sum_range_sub (fun j => revAvg μ ν j) N
  rw [revAvg_zero, revAvg_full] at this
  rw [← sub_zero (klDiv ν (refLaw μ N)).toReal, ← this]
  exact sum_congr rfl fun j _ => condEntAvg_eq μ ν j

end PermAvg

section Main

open Finset

/-- **Conditioning entropy identities.** -/
theorem conditioning_entropy_identities {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty X] (μ : Measure X) [IsProbabilityMeasure μ] {N : ℕ}
    (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]
    (hν : DGPS.relativeEntropy ν (refLaw μ N) ≠ ⊤) :
    (∑ j ∈ range N, condEntAvg μ ν j = (DGPS.relativeEntropy ν (refLaw μ N)).toReal) ∧
    (∀ j, j + 2 ≤ N →
      condEntAvg μ ν (j + 1) - condEntAvg μ ν j = totalCorrAvg μ ν j 2 ∧
        0 ≤ totalCorrAvg μ ν j 2) ∧
    (∀ j k, j + k ≤ N →
      totalCorrAvg μ ν j k = ∑ a ∈ range k, condEntAvg μ ν (j + a) - k * condEntAvg μ ν j) ∧
    (∀ k M, k ≤ M → M ≤ N →
      ∑ j ∈ range (N - M), totalCorrAvg μ ν j k
        ≤ ((k : ℝ) * (k - 1) / ((M : ℝ) - k + 2)) * (DGPS.relativeEntropy ν (refLaw μ N)).toReal) := by
  have hKL : DGPS.relativeEntropy ν (refLaw μ N) = klDiv ν (refLaw μ N) :=
    DGPS.Analysis.relativeEntropy_eq_klDiv
  have hfin : klDiv ν (refLaw μ N) ≠ ⊤ := hKL ▸ hν
  have hsum : ∑ j ∈ range N, condEntAvg μ ν j = (DGPS.relativeEntropy ν (refLaw μ N)).toReal := by
    rw [hKL]; exact condEntAvg_sum μ ν
  refine ⟨hsum, fun j hj => condEntAvg_succ_sub μ ν hfin j hj,
    fun j k hjk => totalCorrAvg_eq μ ν j k hjk, ?_⟩
  intro k M hkM hMN
  have := real_bound (condEntAvg μ ν) N _ (fun j hj => condEntAvg_nonneg μ ν hfin j hj)
    (fun j hj => by have := (condEntAvg_succ_sub μ ν hfin j (by omega)); linarith [this.1, this.2])
    hsum k M hkM hMN
  refine le_trans (le_of_eq (sum_congr rfl fun j hj => ?_)) this
  exact totalCorrAvg_eq μ ν j k (by have := mem_range.1 hj; omega)

end Main

end DGPS.Lipschitz
