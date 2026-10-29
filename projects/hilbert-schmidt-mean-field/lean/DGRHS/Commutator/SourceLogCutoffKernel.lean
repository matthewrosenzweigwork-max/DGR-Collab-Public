import DGRHS.Commutator.SourceLogTransportKernel
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.GroupWithZero

/-! RECORDS-ONLY UNCHECKED. A continuous approximation to the actual n=1
logarithmic canceled kernel. It preserves the Lipschitz bound and has error
bounded by that same constant on the epsilon diagonal band. No uncanceled
force integrability or continuity of the original diagonal representative is
assumed. Compiler HOLD: none of the declarations below has a Lean verdict. -/
noncomputable section
open Set Filter
open scoped NNReal RealInnerProductSpace Topology
namespace DGRHS.Commutator
variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceLogCutoffKernel (ε : ℝ) (v : E→E) (p : E×E) : ℝ :=
  -⟪p.1-p.2,v p.1-v p.2⟫ / max (ε^2) (‖p.1-p.2‖^2)

lemma sourceLogTransportNumerator_abs_le {v : E→E} {K : ℝ≥0}
    (hv : LipschitzWith K v) (p : E×E) :
    |⟪p.1-p.2,v p.1-v p.2⟫|≤(K:ℝ)*‖p.1-p.2‖^2 := by
  have hw : ‖v p.1-v p.2‖≤(K:ℝ)*‖p.1-p.2‖ := by
    simpa only [dist_eq_norm] using hv.dist_le_mul p.1 p.2
  calc
    _≤‖p.1-p.2‖*‖v p.1-v p.2‖ := abs_real_inner_le_norm _ _
    _≤‖p.1-p.2‖*((K:ℝ)*‖p.1-p.2‖) :=
      mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _=(K:ℝ)*‖p.1-p.2‖^2 := by ring

lemma continuous_sourceLogCutoffKernel [TopologicalSpace A]
    (ε : ℝ) (hε : 0<ε) (v : A→E→E)
    (hv : Continuous (fun p:A×E=>v p.1 p.2)) :
    Continuous (fun p:A×(E×E)=>sourceLogCutoffKernel ε (v p.1) p.2) := by
  have hz : Continuous (fun p:A×(E×E)=>p.2.1-p.2.2) :=
    (continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)
  have hw : Continuous (fun p:A×(E×E)=>v p.1 p.2.1-v p.1 p.2.2) :=
    (hv.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).sub
      (hv.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hd : Continuous (fun p:A×(E×E)=>max (ε^2) (‖p.2.1-p.2.2‖^2)) :=
    continuous_const.max (hz.norm.pow 2)
  have hn (p:A×(E×E)) : max (ε^2) (‖p.2.1-p.2.2‖^2)≠0 :=
    (lt_of_lt_of_le (sq_pos_of_pos hε) (le_max_left _ _)).ne'
  apply ((hz.inner hw).neg.div hd hn).congr
  intro p
  rfl

lemma abs_sourceLogCutoffKernel_le (ε : ℝ) (hε : 0<ε)
    {v : E→E} {K : ℝ≥0} (hv : LipschitzWith K v) (p : E×E) :
    |sourceLogCutoffKernel ε v p|≤(K:ℝ) := by
  have hd : 0<max (ε^2) (‖p.1-p.2‖^2) :=
    lt_of_lt_of_le (sq_pos_of_pos hε) (le_max_left _ _)
  rw [sourceLogCutoffKernel,abs_div,abs_neg,abs_of_nonneg hd.le]
  apply (div_le_iff₀ hd).mpr
  exact (sourceLogTransportNumerator_abs_le hv p).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) K.coe_nonneg)

lemma sourceLogCutoffKernel_eq_off_band (ε : ℝ) (hε : 0<ε)
    (v : E→E) (p : E×E) (hp : ε≤‖p.1-p.2‖) :
    sourceLogCutoffKernel ε v p=sourceLogTransportKernel 1 v p := by
  have he : ε^2≤‖p.1-p.2‖^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hp)
      (add_nonneg (norm_nonneg (p.1-p.2)) hε.le)
    nlinarith
  rw [sourceLogCutoffKernel,max_eq_right he,sourceLogTransportKernel_one]

lemma abs_sourceLogTransportKernel_sub_cutoff_le (ε : ℝ) (hε : 0<ε)
    {v : E→E} {K : ℝ≥0} (hv : LipschitzWith K v) (p : E×E) :
    |sourceLogTransportKernel 1 v p-sourceLogCutoffKernel ε v p|≤(K:ℝ) := by
  by_cases hp : p.1=p.2
  · simpa [sourceLogTransportKernel,sourceLogCutoffKernel,hp] using K.coe_nonneg
  let u : ℝ := ‖p.1-p.2‖^2
  let d : ℝ := max (ε^2) u
  have hu : 0<u := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  have hd : 0<d := lt_of_lt_of_le (sq_pos_of_pos hε) (le_max_left _ _)
  have hq0 : 0≤u/d := div_nonneg hu.le hd.le
  have hq1 : u/d≤1 := (div_le_iff₀ hd).mpr (by simpa [d] using le_max_right (ε^2) u)
  have hf0 : 0≤1-u/d := sub_nonneg.mpr hq1
  have hf1 : 1-u/d≤1 := by linarith
  have he : sourceLogTransportKernel 1 v p-sourceLogCutoffKernel ε v p=
      (1-u/d)*sourceLogTransportKernel 1 v p := by
    rw [sourceLogTransportKernel_one]
    change (-⟪p.1-p.2,v p.1-v p.2⟫)/u -
        (-⟪p.1-p.2,v p.1-v p.2⟫)/d =
      (1-u/d)*((-⟪p.1-p.2,v p.1-v p.2⟫)/u)
    field_simp [hu.ne',hd.ne']
    <;> ring
  rw [he,abs_mul,abs_of_nonneg hf0]
  calc
    _≤(1-u/d)*(K:ℝ) :=
      mul_le_mul_of_nonneg_left (abs_sourceLogTransportKernel_one_le hv p) hf0
    _≤1*(K:ℝ) := mul_le_mul_of_nonneg_right hf1 K.coe_nonneg
    _=(K:ℝ) := one_mul _

lemma abs_sourceLogTransportKernel_sub_cutoff_le_band (ε : ℝ) (hε : 0<ε)
    {v : E→E} {K : ℝ≥0} (hv : LipschitzWith K v) (p : E×E) :
    |sourceLogTransportKernel 1 v p-sourceLogCutoffKernel ε v p|≤
      if ‖p.1-p.2‖<ε then (K:ℝ) else 0 := by
  by_cases hp : ‖p.1-p.2‖<ε
  · rw [if_pos hp]
    exact abs_sourceLogTransportKernel_sub_cutoff_le ε hε hv p
  · rw [if_neg hp,sourceLogCutoffKernel_eq_off_band ε hε v p (le_of_not_gt hp)]
    simp only [sub_self,abs_zero,le_refl]

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceLogCutoffKernel
#print axioms DGRHS.Commutator.sourceLogCutoffKernel
#check @DGRHS.Commutator.sourceLogTransportNumerator_abs_le
#print axioms DGRHS.Commutator.sourceLogTransportNumerator_abs_le
#check @DGRHS.Commutator.continuous_sourceLogCutoffKernel
#print axioms DGRHS.Commutator.continuous_sourceLogCutoffKernel
#check @DGRHS.Commutator.abs_sourceLogCutoffKernel_le
#print axioms DGRHS.Commutator.abs_sourceLogCutoffKernel_le
#check @DGRHS.Commutator.sourceLogCutoffKernel_eq_off_band
#print axioms DGRHS.Commutator.sourceLogCutoffKernel_eq_off_band
#check @DGRHS.Commutator.abs_sourceLogTransportKernel_sub_cutoff_le
#print axioms DGRHS.Commutator.abs_sourceLogTransportKernel_sub_cutoff_le
#check @DGRHS.Commutator.abs_sourceLogTransportKernel_sub_cutoff_le_band
#print axioms DGRHS.Commutator.abs_sourceLogTransportKernel_sub_cutoff_le_band
