import LeanResearch.PeriodicAttractiveLogGas.StationaryCumulative
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! The one-dimensional rearrangement regularity steps in the supplied
stationary proof. Critical-value inverse images are not assumed to be null.
Source correspondence and actual checks are recorded in the development note.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PeriodicAttractiveLogGas.RearrangementRegularity

open StationaryCumulative

/-- The image formula is applied only on a measurable set of genuine
differentiability points. Its image is contained in a measurable null cover
of the prescribed value set; its inverse image need not be null. -/
theorem deriv_zero_ae_null_preimage_of_antitone {q : ℝ → ℝ}
    (hq : Antitone q) (hc : Continuous q)
    (hac : AbsolutelyContinuousOnInterval q 0 1)
    {C : Set ℝ} (hC : volume C = 0) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), q s ∈ C → deriv q s = 0 := by
  let B : Set ℝ := {x | x ∈ uIcc (0 : ℝ) 1 ∧ ¬DifferentiableAt ℝ q x}
  have hB : volume B = 0 := by
    have hh := hac.ae_differentiableAt
    rw [ae_iff] at hh
    simpa only [not_imp] using hh
  let D : Set ℝ := toMeasurable volume B
  let V : Set ℝ := toMeasurable volume C
  let S : Set ℝ := (Ioo (0 : ℝ) 1 ∩ q ⁻¹' V) \ D
  have hV : volume V = 0 := by
    dsimp only [V]
    rw [measure_toMeasurable, hC]
  have hS : MeasurableSet S :=
    (measurableSet_Ioo.inter ((measurableSet_toMeasurable volume C).preimage hc.measurable)).diff
      (measurableSet_toMeasurable volume B)
  have hd (x : ℝ) (hx : x ∈ S) : DifferentiableAt ℝ q x := by
    by_contra hn
    apply hx.2
    apply subset_toMeasurable volume B
    refine ⟨?_, hn⟩
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.1.1.le, hx.1.1.2.le⟩)
  have himage : volume (q '' S) = 0 := by
    apply measure_mono_null _ hV
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1.2
  have hj := lintegral_deriv_eq_volume_image_of_antitoneOn hS
    (fun x hx ↦ (hd x hx).hasDerivAt.hasDerivWithinAt) (hq.antitoneOn (s := S))
  have hz : (∫⁻ x in S, ENNReal.ofReal (-deriv q x)) = 0 := hj.trans himage
  have hae : ∀ᵐ x ∂volume.restrict S, ENNReal.ofReal (-deriv q x) = 0 :=
    (lintegral_eq_zero_iff ((measurable_deriv q).neg.ennreal_ofReal)).mp hz
  have hzero := (ae_restrict_iff' hS).mp hae
  have hD : ∀ᵐ x ∂volume, x ∉ D := by
    apply ae_iff.mpr
    rw [show {a : ℝ | ¬a ∉ D} = D by ext a; simp]
    exact (measure_toMeasurable (μ := volume) B).trans hB
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_of_ae hD,
    ae_restrict_mem measurableSet_Ioo] with x hz hd hx
  intro hxc
  have hs : x ∈ S := ⟨⟨hx, subset_toMeasurable volume C hxc⟩, hd⟩
  have hp : -deriv q x ≤ 0 := ENNReal.ofReal_eq_zero.mp (hz hs)
  have hn : deriv q x ≤ 0 := hq.deriv_nonpos
  linarith

/-- The source interval statement, including flat pieces. Only the set of
values is null; no nullity of its rank inverse image is required. -/
theorem deriv_zero_ae_null_preimage {q : ℝ → ℝ}
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hac : AbsolutelyContinuousOnInterval q 0 1)
    {C : Set ℝ} (hC : volume C = 0) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), q s ∈ C → deriv q s = 0 := by
  have hc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hac.continuousOn
  have hh := deriv_zero_ae_null_preimage_of_antitone (antitone_extendProfile hq)
    (continuous_extendProfile hc) (ac_extendProfile hac) hC
  filter_upwards [hh, ae_restrict_mem measurableSet_Ioo] with s hs hi
  intro hv
  have he : extendProfile q s ∈ C := by
    simpa only [extendProfile_eq ⟨hi.1.le, hi.2.le⟩] using hv
  simpa only [deriv_extendProfile_eq hi] using hs he

/-- Monotonicity first supplies genuine integrability of the derivative.
The local FTC identifies the integral primitive on the open interval;
continuity extends that equality to both endpoints. -/
theorem ac_of_monotone_of_interior_ac {q : ℝ → ℝ}
    (hc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hloc : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval q a b) :
    AbsolutelyContinuousOnInterval q 0 1 := by
  have hm : MonotoneOn q (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hq
  have hd : IntervalIntegrable (deriv q) volume 0 1 := hm.intervalIntegrable_deriv
  let P : ℝ → ℝ := fun x ↦ q (1 / 2) + ∫ t in (1 / 2 : ℝ)..x, deriv q t
  have hI : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in (1 / 2 : ℝ)..x, deriv q t) 0 1 :=
    hd.absolutelyContinuousOnInterval_intervalIntegral (by norm_num)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ q (1 / 2)) 0 1 :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval P 0 1 := by
    simpa only [P, Pi.add_apply] using! hconst.add hI
  have hPc : ContinuousOn P (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hP.continuousOn
  have heq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : P x = q x := by
    have hh := (hloc (1 / 2) (by norm_num) x hx).integral_deriv_eq_sub
    change q (1 / 2) + (∫ t in (1 / 2 : ℝ)..x, deriv q t) = q x
    rw [hh]
    ring
  have hs : IsClosed {x : ℝ | extendProfile q x = extendProfile P x} :=
    isClosed_eq (continuous_extendProfile hc) (continuous_extendProfile hPc)
  have hsub : Ioo (0 : ℝ) 1 ⊆ {x : ℝ | extendProfile q x = extendProfile P x} := by
    intro x hx
    change extendProfile q x = extendProfile P x
    rw [extendProfile_eq ⟨hx.1.le, hx.2.le⟩, extendProfile_eq ⟨hx.1.le, hx.2.le⟩]
    exact (heq x hx).symm
  have hclosed := closure_minimal hsub hs
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hclosed
  apply hP.congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hh := hclosed hx'
  change extendProfile q x = extendProfile P x at hh
  rw [extendProfile_eq hx', extendProfile_eq hx'] at hh
  exact hh.symm

/-- The endpoint passage for the actual decreasing interval profile.
The local hypothesis means absolute continuity on every compact subinterval
of the open unit interval; no endpoint FTC or integrability is assumed. -/
theorem ac_of_antitone_of_interior_ac {q : ℝ → ℝ}
    (hc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hloc : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval q a b) :
    AbsolutelyContinuousOnInterval q 0 1 := by
  have hn := ac_of_monotone_of_interior_ac hc.neg hq.neg
    (fun a ha b hb ↦ (hloc a ha b hb).neg)
  simpa only [Pi.neg_apply, neg_neg] using hn.neg

/-- The exact closed-interval decrease identity is a conclusion of the
endpoint passage, rather than an input to it. -/
theorem endpoint_integral_deriv {q : ℝ → ℝ}
    (hc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hloc : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval q a b) :
    IntervalIntegrable (deriv q) volume 0 1 ∧
      (∫ s in (0 : ℝ)..1, -deriv q s) = q 0 - q 1 := by
  have h := ac_of_antitone_of_interior_ac hc hq hloc
  refine ⟨h.intervalIntegrable_deriv, ?_⟩
  rw [intervalIntegral.integral_neg, h.integral_deriv_eq_sub]
  ring

/-- The literal restriction to the critical-rank set. That set is not
assumed measurable or null; only its set of values is null. -/
theorem deriv_zero_ae_critical_ranks {q : ℝ → ℝ}
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hac : AbsolutelyContinuousOnInterval q 0 1)
    {C : Set ℝ} (hC : volume C = 0) :
    ∀ᵐ s ∂volume.restrict {s : ℝ | s ∈ Ioo (0 : ℝ) 1 ∧ q s ∈ C},
      deriv q s = 0 := by
  have hh := (ae_restrict_iff' measurableSet_Ioo).mp
    (deriv_zero_ae_null_preimage hq hac hC)
  apply (ae_restrict_iff ((measurableSet_singleton (0 : ℝ)).preimage (measurable_deriv q))).mpr
  filter_upwards [hh] with s hs
  exact fun hm ↦ hs hm.1 hm.2

/-- The source's Lipschitz bounds on each central rank interval imply the
local-AC premise of the endpoint theorem, with no uniform endpoint bound. -/
theorem ac_of_antitone_of_central_lipschitz {q : ℝ → ℝ}
    (hc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hLip : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ K : NNReal, LipschitzOnWith K q (Icc ε (1 - ε))) :
    AbsolutelyContinuousOnInterval q 0 1 := by
  apply ac_of_antitone_of_interior_ac hc hq
  intro a ha b hb
  let d : ℝ := min (min a b) (min (1 - a) (1 - b))
  have hd : 0 < d := lt_min (lt_min ha.1 hb.1)
    (lt_min (sub_pos.mpr ha.2) (sub_pos.mpr hb.2))
  have hda : d ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hdb : d ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have hda' : d ≤ 1 - a := (min_le_right _ _).trans (min_le_left _ _)
  have hdb' : d ≤ 1 - b := (min_le_right _ _).trans (min_le_right _ _)
  have he : 0 < d / 2 := by positivity
  have he' : d / 2 < 1 / 2 := by linarith [ha.2]
  obtain ⟨K, hK⟩ := hLip (d / 2) he he'
  have hs : uIcc a b ⊆ Icc (d / 2) (1 - d / 2) := by
    intro x hx
    rcases le_total a b with hab | hba
    · rw [uIcc_of_le hab] at hx
      constructor <;> linarith [hx.1, hx.2]
    · rw [uIcc_of_ge hba] at hx
      constructor <;> linarith [hx.1, hx.2]
  exact (hK.mono hs).absolutelyContinuousOnInterval

/-- On critical ranks the actual cumulative second derivative vanishes.
This supplies the zero left-hand side in the source differential inequality. -/
theorem critical_rank_curvature_zero {q : ℝ → ℝ}
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hac : AbsolutelyContinuousOnInterval q 0 1)
    {C : Set ℝ} (hC : volume C = 0) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), q s ∈ C →
      deriv (deriv (cumulative (extendProfile q))) s = 0 := by
  have hh := (ae_restrict_iff' measurableSet_Ioc).mp (second_deriv_extendProfile_ae hac)
  filter_upwards [deriv_zero_ae_null_preimage hq hac hC, ae_restrict_of_ae hh,
    ae_restrict_mem measurableSet_Ioo] with s hz hd hs
  intro hv
  rw [hd ⟨hs.1, hs.2.le⟩, hz hv, mul_zero]

/-- Both requested one-dimensional conclusions from primitive interval
regularity. Sard's nullity and the construction of q remain separate inputs. -/
theorem source_interval_regularity {q : ℝ → ℝ}
    (hc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq : AntitoneOn q (Icc (0 : ℝ) 1))
    (hloc : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval q a b)
    {C : Set ℝ} (hC : volume C = 0) :
    AbsolutelyContinuousOnInterval q 0 1 ∧
      IntervalIntegrable (deriv q) volume 0 1 ∧
      (∫ s in (0 : ℝ)..1, -deriv q s) = q 0 - q 1 ∧
      (∀ᵐ s ∂volume.restrict {s : ℝ | s ∈ Ioo (0 : ℝ) 1 ∧ q s ∈ C}, deriv q s = 0) := by
  have hac := ac_of_antitone_of_interior_ac hc hq hloc
  have hi := endpoint_integral_deriv hc hq hloc
  exact ⟨hac, hi.1, hi.2, deriv_zero_ae_critical_ranks hq hac hC⟩

end PeriodicAttractiveLogGas.RearrangementRegularity
