import DGRHS.Concentration.SourceCutoffRate

noncomputable section
open Filter
open scoped Topology BigOperators
namespace DGRHS.Concentration

lemma sourceRieszRateCutoff_le (C s n η₀ : ℝ) (hC : 0<C) (hs : 0<s)
    (hn : 1<n) (hη₀ : 0<η₀) (hlog : 2*C*η₀^(-s)≤Real.log n) :
    sourceRieszRateCutoff C s n≤η₀ := by
  have hl : 0<Real.log n := Real.log_pos hn
  have hb : 0<Real.log n/(2*C) := div_pos hl (by positivity)
  have hbase : η₀^(-s)≤Real.log n/(2*C) := by
    apply (le_div_iff₀ (by positivity : 0<2*C)).2
    nlinarith
  have hlogs := Real.log_le_log (Real.rpow_pos_of_pos hη₀ (-s)) hbase
  rw [Real.log_rpow hη₀] at hlogs
  have hneg : -1/s≤0 := by
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg zero_le_one hs.le)
  have hm := mul_le_mul_of_nonpos_right hlogs hneg
  have he : (-s*Real.log η₀)*(-1/s)=Real.log η₀ := by field_simp
  rw [he] at hm
  unfold sourceRieszRateCutoff
  rw [Real.rpow_def_of_pos hb,← Real.exp_log hη₀]
  exact Real.exp_le_exp.mpr hm

/-- The actual source cutoff is eligible for every sufficiently large particle
number, with no chosen-scale smallness as a premise. -/
lemma sourceRieszRateCutoff_eventually_small (C s η₀ : ℝ)
    (hC : 0<C) (hs : 0<s) (hη₀ : 0<η₀) :
    ∃ N₀ : ℕ,∀ n : ℕ,N₀≤n→2≤n ∧
      0<sourceRieszRateCutoff C s (n:ℝ) ∧ sourceRieszRateCutoff C s (n:ℝ)≤η₀ := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : ∀ᶠ n : ℕ in atTop,2*C*η₀^(-s)≤Real.log (n:ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have hEligible : ∀ᶠ n : ℕ in atTop,2≤n ∧
      0<sourceRieszRateCutoff C s (n:ℝ) ∧ sourceRieszRateCutoff C s (n:ℝ)≤η₀ := by
    filter_upwards [eventually_ge_atTop 2,hL] with n hn hlog
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    exact ⟨hn,sourceRieszRateCutoff_pos C s n hC hn',sourceRieszRateCutoff_le C s n η₀ hC hs hn' hη₀ hlog⟩
  exact eventually_atTop.1 hEligible

lemma sourceLogRateCutoff_eventually_small (C η₀ : ℝ) (hC : 0<C) (hη₀ : 0<η₀) :
    ∃ N₀ : ℕ,∀ n : ℕ,N₀≤n→1≤n ∧
      0<sourceLogRateCutoff C (n:ℝ) ∧ sourceLogRateCutoff C (n:ℝ)≤η₀ := by
  obtain ⟨ha,_,_⟩ := sourceLogRatePower_bounds C hC
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : ∀ᶠ n : ℕ in atTop,(-Real.log η₀)/sourceLogRatePower C≤Real.log (n:ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have hEligible : ∀ᶠ n : ℕ in atTop,1≤n ∧
      0<sourceLogRateCutoff C (n:ℝ) ∧ sourceLogRateCutoff C (n:ℝ)≤η₀ := by
    filter_upwards [eventually_ge_atTop 1,hL] with n hn hlog
    have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have hm := mul_le_mul_of_nonneg_right hlog ha.le
    rw [div_mul_cancel₀ _ ha.ne'] at hm
    have hη : 0<sourceLogRateCutoff C (n:ℝ) := Real.rpow_pos_of_pos hn0 _
    refine ⟨hn,hη,?_⟩
    unfold sourceLogRateCutoff
    rw [Real.rpow_def_of_pos hn0,← Real.exp_log hη₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact eventually_atTop.1 hEligible

/-- An explicit finite sum absorbs every small particle number. Proper
partition integrability is discharged by the source factory before this
arithmetic lemma is instantiated. -/
theorem partition_rate_all_positive (Z : ℕ→ℝ) (z : ℝ) (f : ℕ→ℝ)
    (hf : ∀ n,0<f n) (K : ℝ) (N₀ : ℕ)
    (hLarge : ∀ n,1≤n→N₀≤n→|Z n-z|≤K*f n) :
    let C := max K 0+∑ j ∈ Finset.range N₀,|Z j-z|/f j
    0≤C ∧ ∀ n,1≤n→|Z n-z|≤C*f n := by
  classical
  let S := ∑ j ∈ Finset.range N₀,|Z j-z|/f j
  have hS : 0≤S := Finset.sum_nonneg fun j _ ↦ div_nonneg (abs_nonneg _) (hf j).le
  refine ⟨add_nonneg (le_max_right _ _) hS,?_⟩
  intro n hn
  by_cases hN : N₀≤n
  · exact (hLarge n hn hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [S] at hS ⊢; linarith [le_max_left K 0]) (hf n).le)
  · have hmem : n∈Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hOne : |Z n-z|/f n≤S := Finset.single_le_sum (f := fun j ↦ |Z j-z|/f j)
      (fun j _ ↦ div_nonneg (abs_nonneg _) (hf j).le) hmem
    apply (div_le_iff₀ (hf n)).1
    dsimp [S] at hOne ⊢
    linarith [le_max_right K 0]

#print axioms DGRHS.Concentration.sourceRieszRateCutoff_le
#print axioms DGRHS.Concentration.sourceRieszRateCutoff_eventually_small
#print axioms DGRHS.Concentration.sourceLogRateCutoff_eventually_small
#print axioms DGRHS.Concentration.partition_rate_all_positive
#check @DGRHS.Concentration.sourceRieszRateCutoff_eventually_small
#check @DGRHS.Concentration.sourceLogRateCutoff_eventually_small
#check @DGRHS.Concentration.partition_rate_all_positive
end DGRHS.Concentration
