import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarRateSqueeze

/-! Actual scalar-rate convergence as coupling tends to zero at fixed field.
Both the ENNReal limit and the finite real rate limit are derived from the
proved all-H1 bounds, uniformly over the genuine drift providers. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- No scalar rate limit or attainment premise is imposed. Finiteness is proved
on the coupling tail before composing the real-rate limit map. -/
theorem elementaryModel_scalarRate_tendsto_ordinary (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
        ∀ b : (n : ℕ) → AbsoluteDrift (modelData h (ε n)),
          Tendsto (fun n => scalarRate (modelData h (ε n)) (b n)) atTop
              (𝓝 (ordinaryLSRate (ordinaryReference h))) ∧
          (∀ᶠ n in atTop, scalarRate (modelData h (ε n)) (b n) ≠ ⊤) ∧
          Tendsto (fun n => (scalarRate (modelData h (ε n)) (b n)).toReal) atTop
              (𝓝 (ordinaryLSRate (ordinaryReference h)).toReal) := by
  obtain ⟨δ, hδ, hδr, hbound⟩ := elementaryModel_scalarRate_coupling_squeeze D
  refine ⟨δ, hδ, hδr, fun h hh hhd ε hε hεlim b => ?_⟩
  obtain ⟨ε0, K, hε0, _, _, hsqueeze⟩ := hbound h hh hhd
  obtain ⟨σ, _, hpos, hquot, _⟩ := D.roots h hh (hhd.trans_le hδr)
  have hfin : ordinaryLSRate (ordinaryReference h) ≠ ⊤ := by
    rw [← hquot 0]
    unfold str025_quot
    exact ENNReal.div_ne_top (str025_fisher_ne_top h (σ 0))
      (mul_ne_zero (by norm_num) (hpos 0).ne')
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : ENNReal.ofReal a = ordinaryLSRate (ordinaryReference h) :=
    ENNReal.ofReal_toReal hfin
  have hevent : ∀ᶠ n in atTop, ε n < ε0 :=
    hεlim.eventually (gt_mem_nhds hε0)
  have hbounds : ∀ᶠ n in atTop,
      ENNReal.ofReal (a - K * ε n) ≤ scalarRate (modelData h (ε n)) (b n) ∧
        scalarRate (modelData h (ε n)) (b n) ≤ ENNReal.ofReal (a + K * ε n) := by
    filter_upwards [hevent] with n hn
    exact hsqueeze (ε n) (hε n) hn (b n)
  have hlow : Tendsto (fun n => ENNReal.ofReal (a - K * ε n)) atTop
      (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
    have ht := (ENNReal.continuous_ofReal.tendsto a).comp
      (show Tendsto (fun n => a - K * ε n) atTop (𝓝 a) by
        simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hεlim.const_mul K))
    rwa [ha] at ht
  have hupp : Tendsto (fun n => ENNReal.ofReal (a + K * ε n)) atTop
      (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
    have ht := (ENNReal.continuous_ofReal.tendsto a).comp
      (show Tendsto (fun n => a + K * ε n) atTop (𝓝 a) by
        simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hεlim.const_mul K))
    rwa [ha] at ht
  have hlim : Tendsto (fun n => scalarRate (modelData h (ε n)) (b n)) atTop
      (𝓝 (ordinaryLSRate (ordinaryReference h))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
      (hbounds.mono fun _ hn => hn.1) (hbounds.mono fun _ hn => hn.2)
  have htailfin : ∀ᶠ n in atTop, scalarRate (modelData h (ε n)) (b n) ≠ ⊤ := by
    filter_upwards [hbounds] with n hn
    exact ne_of_lt (hn.2.trans_lt (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top))
  exact ⟨hlim, htailfin, (ENNReal.tendsto_toReal hfin).comp hlim⟩

end DGPS.Examples.ThreeSpeciesCircle
