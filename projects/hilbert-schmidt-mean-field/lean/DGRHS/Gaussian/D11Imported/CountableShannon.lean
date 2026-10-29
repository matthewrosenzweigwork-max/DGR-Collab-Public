import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-! The countable relative-entropy comparison needed for lattice labels.
Cross-entropy integrability implies entropy integrability, rather than being
silently assumed when rearranging infinite sums. -/
noncomputable section
namespace DGRHS.Gaussian.D11Imported.CountableShannon

lemma entropy_term_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    -p * Real.log p ≤ -p * Real.log q + q-p := by
  by_cases hp0 : p = 0
  · simp [hp0, hq.le]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq hp')) hp
  rw [Real.log_div hq.ne' hp0] at h
  have he : p*(q/p-1)=q-p := by field_simp
  rw [he] at h
  nlinarith

theorem entropy_comparison {ι : Type*} (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hps : HasSum p 1) (hqs : HasSum q 1)
    (hcross : Summable (fun i => p i * Real.log (q i))) :
    Summable (fun i => p i * Real.log (p i)) ∧
      -(∑' i, p i * Real.log (p i)) ≤ -(∑' i, p i * Real.log (q i)) := by
  have hp1 (i : ι) : p i ≤ 1 := by
    simpa only [hps.tsum_eq] using hps.summable.le_tsum i (fun j _ => hp j)
  have hpn (i : ι) : p i * Real.log (p i) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hp i) (Real.log_nonpos (hp i) (hp1 i))
  have hent : Summable (fun i => p i * Real.log (p i)) := by
    apply (hqs.summable.add hcross.abs).of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_of_nonpos (hpn i)]
    have h := entropy_term_le (hp i) (hq i)
    have hab := neg_le_abs (p i * Real.log (q i))
    nlinarith [hp i]
  refine ⟨hent, ?_⟩
  have h := hent.neg.tsum_le_tsum (fun i => by
      simpa only [neg_mul] using entropy_term_le (hp i) (hq i))
    (hcross.neg.add hqs.summable |>.sub hps.summable)
  simpa only [tsum_neg, Summable.tsum_sub (hcross.neg.add hqs.summable) hps.summable,
    Summable.tsum_add hcross.neg hqs.summable, hps.tsum_eq, hqs.tsum_eq, add_sub_cancel_right] using h

#print axioms entropy_comparison
end DGRHS.Gaussian.D11Imported.CountableShannon
