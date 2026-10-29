import DGRHS.Commutator.SourceRieszFiniteTerminalCF
import DGRHS.Commutator.SourceRieszInitialCharacteristic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Source4015--4024: vanishing actual finite-N physical errors plus the
proved literal initial-Gibbs characteristic limit. This helper only performs
the final sequence algebra; the physical consumer supplies its inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace DGRHS.Commutator

lemma sourceRiesz_sqrt_rate_CF_limit (F I : ℕ→ℂ) (I₀ e : ℂ) (C : ℝ)
    (hI : Tendsto I atTop (𝓝 I₀))
    (hb : ∀ N,1≤N → ‖F N-I N*e‖≤C/Real.sqrt N) :
    Tendsto F atTop (𝓝 (I₀*e)) := by
  have hs : Tendsto (fun N : ℕ=>Real.sqrt (N:ℝ)) atTop atTop := by
    have hn : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp hn
  have hc : Tendsto (fun N : ℕ=>C/Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hn : Tendsto (fun N=>‖F N-I N*e‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun N=>norm_nonneg _)
      ((eventually_ge_atTop (1:ℕ)).mono fun N hN=>hb N hN) hc
  have hz : Tendsto (fun N=>F N-I N*e) atTop (𝓝 (0:ℂ)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (by simpa only [sub_zero] using hn)
  have he : Tendsto (fun _ : ℕ=>e) atTop (𝓝 e) := tendsto_const_nhds
  simpa only [sub_add_cancel,zero_add] using hz.add (hI.mul he)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_sqrt_rate_CF_limit
#print axioms DGRHS.Commutator.sourceRiesz_sqrt_rate_CF_limit
