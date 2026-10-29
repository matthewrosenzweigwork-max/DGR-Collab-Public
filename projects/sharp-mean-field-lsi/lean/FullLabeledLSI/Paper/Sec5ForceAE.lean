import FullLabeledLSI.Paper.Sec5ForceMeas
import FullLabeledLSI.Paper.PermAvg

/-!
# Lemma 5.5: `condForceS` agrees with `B_S` computed from the bounded representative
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- The joint coordinate projection `(X_S, X_j)` for `j ∉ S` is volume preserving. -/
theorem mp_proj (S : Finset (Fin N)) (j : Fin N) (hj : j ∉ S) :
    MeasurePreserving (fun X : Config N d => (restrictS S X, X j))
      (volume : Measure (Config N d))
      ((volume : Measure (S → Torus d)).prod (volume : Measure (Torus d))) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => (volume : Measure (Torus d))) (· ∈ S)
  have h2 : MeasurePreserving (Function.eval (⟨j, hj⟩ : {i // ¬ i ∈ S}))
      (volume : Measure ({i // ¬ i ∈ S} → Torus d)) (volume : Measure (Torus d)) :=
    measurePreserving_eval (fun _ => (volume : Measure (Torus d))) _
  have h3 := (MeasurePreserving.id (volume : Measure (S → Torus d))).prod h2
  have h1' : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Torus d) (· ∈ S))
      (volume : Measure (Config N d))
      ((volume : Measure (S → Torus d)).prod (volume : Measure ({i // ¬ i ∈ S} → Torus d))) := by
    have h := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => Torus d) (· ∈ S)
    rw [Measure.volume_eq_prod] at h
    convert h
  exact MeasurePreserving.comp (g := Prod.map id (Function.eval (⟨j, hj⟩ : {i // ¬ i ∈ S}))) h3 h1'

theorem mp_restrict (S : Finset (Fin N)) (j : Fin N) (hj : j ∉ S) :
    MeasurePreserving (restrictS (d := d) S) (volume : Measure (Config N d))
      (volume : Measure (S → Torus d)) :=
  (measurePreserving_fst (μ := (volume : Measure (S → Torus d)))
    (ν := (volume : Measure (Torus d)))).comp (mp_proj S j hj)

/-- For `j ∉ S`, `ρ_{S,j}(X_S) ≪ haar` for `ν`-a.e. `X`. -/
theorem condLawS_ac (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hac : ν ≪ (volume : Measure (Config N d))) (hpos : (volume : Measure (Config N d)) ≪ ν)
    (S : Finset (Fin N)) (j : Fin N) (hj : j ∉ S) :
    ∀ᵐ X ∂ν, condLawS ν S j (restrictS S X) ≪ SharpLSI.haar d := by
  set P0 : Measure (S → Torus d) := ν.map (restrictS S) with hP0
  have hlaw : ν.map (fun X => (restrictS S X, X j)) = P0 ⊗ₘ condLawS ν S j :=
    (compProd_map_condDistrib (measurable_restrictS S).aemeasurable
      (measurable_pi_apply j).aemeasurable).symm
  have hT := (mp_proj (d := d) S j hj)
  have hvS : (volume : Measure (S → Torus d)) ≪ P0 := by
    have := hpos.map (measurable_restrictS (d := d) S)
    rwa [(mp_restrict (d := d) S j hj).map_eq] at this
  have hA : P0 ⊗ₘ condLawS ν S j ≪ P0 ⊗ₘ Kernel.const _ (SharpLSI.haar d) := by
    rw [← hlaw, Measure.compProd_const]
    have h1 := hac.map hT.measurable
    rw [hT.map_eq] at h1
    exact h1.trans (Measure.AbsolutelyContinuous.prod hvS (Measure.AbsolutelyContinuous.refl _))
  have h := hA.kernel_of_compProd
  simp only [Kernel.const_apply] at h
  exact ae_of_ae_map (measurable_restrictS S).aemeasurable h

theorem barCond_ac (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hac : ν ≪ (volume : Measure (Config N d))) (hpos : (volume : Measure (Config N d)) ≪ ν)
    (S : Finset (Fin N)) :
    ∀ᵐ X ∂ν, barCond ν S X ≪ SharpLSI.haar d := by
  have h : ∀ᵐ X ∂ν, ∀ j : (Sᶜ : Finset (Fin N)),
      condLawS ν S j (restrictS S X) ≪ SharpLSI.haar d :=
    ae_all_iff.2 fun j => condLawS_ac ν hac hpos S j (Finset.mem_compl.mp j.2)
  filter_upwards [h] with X hX
  intro s hs
  simp only [barCond, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_zero, mul_zero]
  intro j hj
  exact hX ⟨j, hj⟩ hs

/-- General version: `ν ≪ volume` and `volume ≪ ν`. -/
theorem condForce_ae_eq_of_ac {bg bF : Torus d → Torus d → Fin d → ℝ}
    (hbg : ∀ᵐ p ∂(SharpLSI.haar d).prod (SharpLSI.haar d), ∀ k, bg p.1 p.2 k = bF p.1 p.2 k)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hac : ν ≪ (volume : Measure (Config N d))) (hpos : (volume : Measure (Config N d)) ≪ ν)
    (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) :
    ∀ᵐ X ∂ν, ∀ k, ∫ y, bg (X i) y k ∂barCond ν S X = ∫ y, bF (X i) y k ∂barCond ν S X := by
  have hZ := Measure.ae_ae_of_ae_prod hbg
  have hev : (ν.map (fun X : Config N d => X i)) ≪ SharpLSI.haar d := by
    have h1 := hac.map (measurable_pi_apply i : Measurable fun X : Config N d => X i)
    have h2 : (volume : Measure (Config N d)).map (fun X => X i) = (volume : Measure (Torus d)) :=
      (measurePreserving_eval (fun _ : Fin N => (volume : Measure (Torus d))) i).map_eq
    rwa [h2] at h1
  have hX : ∀ᵐ X ∂ν, ∀ᵐ y ∂SharpLSI.haar d, ∀ k, bg (X i) y k = bF (X i) y k :=
    ae_of_ae_map (measurable_pi_apply i).aemeasurable (hev.ae_le hZ)
  filter_upwards [hX, barCond_ac ν hac hpos S] with X h1 h2 k
  exact integral_congr_ae (by
    have := ae_iff.mpr (h2 (ae_iff.mp h1))
    exact this.mono fun y hy => by simp [hy k])

theorem ac_of_smooth {ν : Measure (Config N d)} (hν : HasSmoothPosDensity ν) :
    ν ≪ (volume : Measure (Config N d)) ∧ (volume : Measure (Config N d)) ≪ ν := by
  obtain ⟨u, hus, hu0, rfl⟩ := hν
  have hum : Measurable u := (continuous_of_isSmoothC hus).measurable
  refine ⟨withDensity_absolutelyContinuous _ _, ?_⟩
  exact withDensity_absolutelyContinuous' (hum.ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun X => by simpa using hu0 X)

/-- If `bg = bF` a.e. for `m ⊗ m` and `ν` has a smooth positive density, then for `i ∉ S` and
ν-a.e. `X`, `∫ bg(X_i, y) dρ̄_S(y) = ∫ bF(X_i, y) dρ̄_S(y)`. -/
theorem condForce_ae_eq {bg bF : Torus d → Torus d → Fin d → ℝ}
    (hbg : ∀ᵐ p ∂(SharpLSI.haar d).prod (SharpLSI.haar d), ∀ k, bg p.1 p.2 k = bF p.1 p.2 k)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hν : HasSmoothPosDensity ν)
    (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) :
    ∀ᵐ X ∂ν, ∀ k, ∫ y, bg (X i) y k ∂barCond ν S X = ∫ y, bF (X i) y k ∂barCond ν S X :=
  condForce_ae_eq_of_ac hbg ν (ac_of_smooth hν).1 (ac_of_smooth hν).2 S i hi

end SharpLSI.FL
