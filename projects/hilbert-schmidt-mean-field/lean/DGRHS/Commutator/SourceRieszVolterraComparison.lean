import DGRHS.Commutator.SourceRieszVolterraScalar
import Mathlib.Analysis.Complex.Basic

/-
DGR arXiv:2609.02743v1, source3971--3997. Proper scalar Volterra support.
Original source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
The finite integral identity is explicit; it is not a terminal factorization or
limit hypothesis. Absolute continuity and the AE equation are derived by native
Lebesgue differentiation and the AC primitive theorem. Stochastic admissibility
and actual physical instantiation remain separate.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval
namespace DGRHS.Commutator

/-- Proper finite scalar Volterra identity implies quantitative decay comparison;
no derivative or absolute continuity premise on chi is supplied. -/
theorem sourceRiesz_real_volterra_comparison {chi m f : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hm : IntervalIntegrable m volume 0 T)
    (hp : IntervalIntegrable (fun t => m t * chi t) volume 0 T)
    (hf : IntervalIntegrable f volume 0 T)
    (hmb : ∀ t ∈ Icc 0 T, 0 ≤ m t ∧ m t ≤ C)
    (hchi : ∀ t ∈ Icc 0 T,
      chi t = chi 0 - ∫ r in 0..t, m r * chi r + f r) :
    |chi T - chi 0 * Real.exp (-(∫ t in 0..T, m t))| ≤
      Real.exp (C * T) * ∫ t in 0..T, |f t| := by
  let I : ℝ → ℝ := fun t => ∫ r in 0..t, m r
  let J : ℝ → ℝ := fun t => ∫ r in 0..t, m r * chi r + f r
  let e : ℝ → ℝ := fun t => chi 0 - J t - chi 0 * Real.exp (-I t)
  have hI : AbsolutelyContinuousOnInterval I 0 T :=
    hm.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hJ : AbsolutelyContinuousOnInterval J 0 T :=
    (hp.add hf).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => chi 0) 0 T :=
    by
      simp [AbsolutelyContinuousOnInterval]
      exact tendsto_const_nhds
  have hg := DGRHS.Dynamics.absolutelyContinuous_exp hI.neg
  have he : AbsolutelyContinuousOnInterval e 0 T :=
    (hc.sub hJ).sub (hg.const_mul (chi 0))
  have hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → deriv e t = -m t * e t + (-f t) := by
    filter_upwards [hm.ae_hasDerivAt_integral, (hp.add hf).ae_hasDerivAt_integral]
      with t hmt hpt htT
    have ht' : t ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using htT
    have hmi := hmt ht' 0 (by simp)
    have hji := hpt ht' 0 (by simp)
    have heder := ((hasDerivAt_const t (chi 0)).sub hji).sub
      (hmi.neg.exp.const_mul (chi 0))
    have hde : deriv e t = 0 - (m t * chi t + f t) -
        chi 0 * (Real.exp (-I t) * (-m t)) := heder.deriv
    rw [hde]
    dsimp [e, J, I]
    rw [hchi t htT]
    ring
  have hbound := sourceRiesz_scalar_forced_decay_bound hT hC he hm hf.neg hmb
    (by simp [e, I, J]) hd
  have heT : e T = chi T - chi 0 * Real.exp (-(∫ t in 0..T, m t)) := by
    dsimp [e, J, I]
    rw [← hchi T ⟨hT, le_rfl⟩]
  simpa [heT] using hbound

#check sourceRiesz_real_volterra_comparison
#print axioms sourceRiesz_real_volterra_comparison
end DGRHS.Commutator
