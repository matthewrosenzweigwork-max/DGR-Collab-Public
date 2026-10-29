import DGPS.SingularCounterexample.Cutoff
import DGPS.SingularCounterexample.BarrierGeometry
import DGPS.SingularCounterexample.Particle.WellPosed
import DGPS.SingularCounterexample.Particle.TestFunction
import DGPS.Examples.PositiveH1.Nonlinear
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace DGPS.SingularCounterexample

noncomputable section

private def particleBoxRadius (N : ℕ) : ℝ := 1 / (100 * (N : ℝ))

private def particleBoxFixedWidth (N : ℕ) : ℝ := 1 / (50 * (N : ℝ))

private def particleBoxCenter (N : ℕ) (i : Fin N) : ℝ :=
  if i.val = 0 then 1 / 8 else 3 / 8 + ((i.val : ℝ) - 2) / (12 * (N : ℝ))

private def particleBoxLower (N : ℕ) (n : ℕ) (i : Fin N) : ℝ :=
  if i.val = 1 then -(2 * separation n / 3)
  else particleBoxCenter N i - particleBoxRadius N

private def particleBoxUpper (N : ℕ) (n : ℕ) (i : Fin N) : ℝ :=
  if i.val = 1 then -(separation n / 3)
  else particleBoxCenter N i + particleBoxRadius N

/-- One relative coordinate lies in the middle valley; all other coordinates lie in fixed arcs. -/
private def particleParameterBox (N n : ℕ) : Set (Fin N → ℝ) :=
  Set.univ.pi fun i => Set.Icc (particleBoxLower N n i) (particleBoxUpper N n i)

def particleIndex0 (N : ℕ) (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩

def particleIndex1 (N : ℕ) (hN : 2 ≤ N) : Fin N := ⟨1, by omega⟩

private def particleShear (N : ℕ) (hN : 2 ≤ N) : (Fin N → ℝ) → (Fin N → ℝ) :=
  Matrix.toLin' ((Matrix.TransvectionStruct.mk (⟨1, by omega⟩ : Fin N)
    (⟨0, by omega⟩ : Fin N) (by norm_num) (1 : ℝ)).toMatrix)

private theorem particleShear_volumePreserving {N : ℕ} (hN : 2 ≤ N) :
    MeasurePreserving (particleShear N hN) (volume : Measure (Fin N → ℝ)) volume := by
  exact Real.volume_preserving_transvectionStruct
    (Matrix.TransvectionStruct.mk (⟨1, by omega⟩ : Fin N)
      (⟨0, by omega⟩ : Fin N) (by norm_num) (1 : ℝ))

private theorem particleShear_apply {N : ℕ} (hN : 2 ≤ N) (y : Fin N → ℝ) (i : Fin N) :
    particleShear N hN y i =
      if i.val = 1 then y i + y (particleIndex0 N hN) else y i := by
  classical
  rw [particleShear, Matrix.TransvectionStruct.toMatrix_mk,
    Matrix.toLin'_apply, Matrix.transvection, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  by_cases hi : i.val = 1 <;>
    simp [particleIndex0, hi, Function.update_apply, Fin.ext_iff]

private def particleConfigLift (N : ℕ) (y : Fin N → ℝ) : SharpLSI.Config N 1 :=
  fun i => Examples.PositiveH1.Nonlinear.lift1 (y i)

private theorem particleConfigLift_map (N : ℕ) :
    Measure.map (particleConfigLift N)
      ((volume : Measure (Fin N → ℝ)).restrict (SharpLSI.unitBox (Fin N))) =
        (volume : Measure (SharpLSI.Config N 1)) := by
  classical
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hbox : (volume : Measure (Fin N → ℝ)).restrict (SharpLSI.unitBox (Fin N)) =
      Measure.pi fun _ : Fin N => μ := by
    rw [SharpLSI.volume_restrict_unitBox]
  have hmap : Measure.map (particleConfigLift N) (Measure.pi fun _ : Fin N => μ) =
      Measure.pi fun _ : Fin N => Measure.map Examples.PositiveH1.Nonlinear.lift1 μ := by
    exact Measure.pi_map_pi
      (fun _ => Examples.PositiveH1.Nonlinear.continuous_lift1.measurable.aemeasurable)
  rw [hbox, hmap]
  have hμ : Measure.map Examples.PositiveH1.Nonlinear.lift1 μ = DGPS.haar 1 := by
    simpa [μ] using Examples.PositiveH1.Nonlinear.haar1_eq_map.symm
  simp_rw [hμ]
  rw [volume_pi]

def particleFavorableBox (N : ℕ) (hN : 2 ≤ N) (n : ℕ) :
    Set (SharpLSI.Config N 1) :=
  particleConfigLift N '' (particleShear N hN '' particleParameterBox N n)

def particleBoxConstant (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (1 / 3 : ℝ) * ∏ i ∈ (Finset.univ.erase (particleIndex1 N hN)), particleBoxFixedWidth N

private theorem particleBoxConstant_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < particleBoxConstant N hN := by
  unfold particleBoxConstant particleBoxFixedWidth
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  apply mul_pos (by norm_num)
  exact Finset.prod_pos fun i hi => by positivity

private theorem particleBoxParameter_compact (N n : ℕ) :
    IsCompact (particleParameterBox N n) := by
  unfold particleParameterBox
  exact isCompact_univ_pi fun _ => isCompact_Icc

private theorem particleShear_continuous {N : ℕ} (hN : 2 ≤ N) :
    Continuous (particleShear N hN) := by
  classical
  refine continuous_pi fun i => ?_
  by_cases hi : i.val = 1
  · have hEqFun : (fun x => particleShear N hN x i) =
        (fun x => x i + x (particleIndex0 N hN)) := by
      funext x
      rw [particleShear_apply]
      simp [hi]
    rw [hEqFun]
    exact (continuous_apply i).add (continuous_apply (particleIndex0 N hN))
  · simpa [particleShear_apply, hi] using continuous_apply i

private theorem particleConfigLift_continuous (N : ℕ) :
    Continuous (particleConfigLift N) := by
  refine continuous_pi fun i => ?_
  exact Examples.PositiveH1.Nonlinear.continuous_lift1.comp (continuous_apply i)

private theorem particleFavorableBox_compact {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    IsCompact (particleFavorableBox N hN n) := by
  unfold particleFavorableBox
  exact ((particleBoxParameter_compact N n).image (particleShear_continuous hN)).image
    (particleConfigLift_continuous N)

private theorem particleShear_mem_unitBox {N : ℕ} (hN : 2 ≤ N) (n : ℕ)
    {y : Fin N → ℝ} (hy : y ∈ particleParameterBox N n) :
    particleShear N hN y ∈ SharpLSI.unitBox (Fin N) := by
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr : particleBoxRadius N ≤ (1 : ℝ) / 200 := by
    unfold particleBoxRadius
    apply (div_le_iff₀ (by positivity : 0 < 100 * (N : ℝ))).2
    nlinarith [hNreal]
  have ha : separation n ≤ (1 : ℝ) / 10000 := by
    have h := separation_le_ten_neg_four n
    norm_num [Real.rpow_neg, Real.rpow_natCast] at h ⊢
    exact h
  rw [SharpLSI.unitBox, Set.mem_univ_pi]
  intro i
  have hyi : y i ∈ Set.Icc (particleBoxLower N n i) (particleBoxUpper N n i) :=
    Set.mem_univ_pi.mp hy i
  by_cases hi0 : i.val = 0
  · have hi : i = particleIndex0 N hN := Fin.ext hi0
    subst i
    have hcoord : y (particleIndex0 N hN) ∈
        Set.Icc (1 / 8 - particleBoxRadius N) (1 / 8 + particleBoxRadius N) := by
      simpa [particleBoxLower, particleBoxUpper, particleBoxCenter,
        particleIndex0, particleIndex1] using hyi
    have hz : particleShear N hN y (particleIndex0 N hN) = y (particleIndex0 N hN) := by
      rw [particleShear_apply]
      simp [particleIndex0, particleIndex1]
    rw [hz]
    constructor <;> dsimp [particleBoxRadius] at * <;> nlinarith [hr, hcoord.1, hcoord.2]
  · by_cases hi1 : i.val = 1
    · have hi : i = particleIndex1 N hN := Fin.ext hi1
      subst i
      have hy0 : y (particleIndex0 N hN) ∈
          Set.Icc (1 / 8 - particleBoxRadius N) (1 / 8 + particleBoxRadius N) := by
        have h := Set.mem_univ_pi.mp hy (particleIndex0 N hN)
        simpa [particleBoxLower, particleBoxUpper, particleBoxCenter,
          particleIndex0, particleIndex1] using h
      have hy1 : y (particleIndex1 N hN) ∈
          Set.Icc (-(2 * separation n / 3)) (-(separation n / 3)) := by
        simpa [particleBoxLower, particleBoxUpper, particleIndex1] using hyi
      have hz : particleShear N hN y (particleIndex1 N hN) =
          y (particleIndex1 N hN) + y (particleIndex0 N hN) := by
        rw [particleShear_apply]
        simp [particleIndex0, particleIndex1]
      rw [hz]
      constructor <;> dsimp [particleBoxRadius] at * <;>
        nlinarith [hr, ha, hy0.1, hy0.2, hy1.1, hy1.2]
    · have hi2 : 2 ≤ i.val := by omega
      have hiN : i.val < N := i.isLt
      have hidx : (2 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hi2
      have hidxN : (i.val : ℝ) < (N : ℝ) := by exact_mod_cast hiN
      have hcoord : y i ∈ Set.Icc (particleBoxCenter N i - particleBoxRadius N)
          (particleBoxCenter N i + particleBoxRadius N) := by
        simpa [particleBoxLower, particleBoxUpper, hi1] using hyi
      simp only [particleBoxCenter, if_neg hi0] at hcoord
      have hterm0 : 0 ≤ ((i.val : ℝ) - 2) / (12 * (N : ℝ)) :=
        div_nonneg (by linarith [hidx]) (by positivity)
      have hterm1 : ((i.val : ℝ) - 2) / (12 * (N : ℝ)) < 1 / 12 := by
        rw [div_lt_iff₀ (by positivity : 0 < 12 * (N : ℝ))]
        nlinarith [hidxN]
      have hz : particleShear N hN y i = y i := by
        rw [particleShear_apply]
        simp [hi1]
      rw [hz]
      constructor
      · nlinarith [hterm0, hr, hcoord.1]
      · nlinarith [hterm1, hr, hcoord.2]

private theorem particleParameterBox_volume {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    volume (particleParameterBox N n) =
      ENNReal.ofReal (separation n / 3) *
        ∏ i ∈ (Finset.univ.erase (particleIndex1 N hN)),
          ENNReal.ofReal (particleBoxFixedWidth N) := by
  classical
  rw [particleParameterBox, Set.pi_univ_Icc, Real.volume_Icc_pi]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i : Fin N => ENNReal.ofReal (particleBoxUpper N n i - particleBoxLower N n i))
    (Finset.mem_univ (particleIndex1 N hN))]
  have hspecial : particleBoxUpper N n (particleIndex1 N hN) -
      particleBoxLower N n (particleIndex1 N hN) = separation n / 3 := by
    simp [particleBoxLower, particleBoxUpper, particleIndex1]
    ring
  rw [hspecial]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hiNe : i ≠ particleIndex1 N hN := (Finset.mem_erase.mp hi).1
  have hiVal : i.val ≠ 1 := by
    intro hv
    apply hiNe
    exact Fin.ext hv
  have hwidth : particleBoxUpper N n i - particleBoxLower N n i =
      particleBoxFixedWidth N := by
    simp [particleBoxLower, particleBoxUpper, particleBoxCenter,
      particleBoxRadius, particleBoxFixedWidth, hiVal]
    ring
  rw [hwidth]

/-- The favorable set has Haar volume bounded below by a positive constant times `a_n`. -/
theorem particle_favorable_box_volume_lower {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    ENNReal.ofReal (particleBoxConstant N hN * separation n) ≤
      (volume : Measure (SharpLSI.Config N 1)) (particleFavorableBox N hN n) := by
  classical
  have hboxCompact := particleFavorableBox_compact hN n
  rw [← particleConfigLift_map]
  rw [Measure.map_apply (particleConfigLift_continuous N).measurable hboxCompact.measurableSet]
  have hsubset : particleShear N hN '' particleParameterBox N n ⊆
      SharpLSI.unitBox (Fin N) ∩ particleConfigLift N ⁻¹' particleFavorableBox N hN n := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨particleShear_mem_unitBox hN n hy, ?_⟩
    exact ⟨particleShear N hN y, ⟨y, hy, rfl⟩, rfl⟩
  have hcompact : IsCompact (particleShear N hN '' particleParameterBox N n) :=
    (particleBoxParameter_compact N n).image (particleShear_continuous hN)
  have hmeasure :
      volume (particleShear N hN '' particleParameterBox N n) =
        volume (particleParameterBox N n) := by
    have hinj : Function.Injective (particleShear N hN) := by
      intro x y hxy
      funext i
      have h0 : x (particleIndex0 N hN) = y (particleIndex0 N hN) := by
        have hi := congrFun hxy (particleIndex0 N hN)
        simpa [particleShear_apply, particleIndex0, particleIndex1] using hi
      have h1 : x (particleIndex1 N hN) = y (particleIndex1 N hN) := by
        have hi := congrFun hxy (particleIndex1 N hN)
        have hi' : x (particleIndex1 N hN) + x (particleIndex0 N hN) =
            y (particleIndex1 N hN) + y (particleIndex0 N hN) := by
          simpa [particleShear_apply, particleIndex0, particleIndex1] using hi
        rw [h0] at hi'
        exact add_right_cancel hi'
      by_cases hi : i = particleIndex1 N hN
      · subst i
        exact h1
      · have hi' : i.val ≠ 1 := by
          intro hv
          apply hi
          exact Fin.ext hv
        simpa [particleShear_apply, hi'] using congrFun hxy i
    have hpre : (particleShear N hN) ⁻¹'
        (particleShear N hN '' particleParameterBox N n) = particleParameterBox N n := by
      ext y
      constructor
      · intro hy
        change particleShear N hN y ∈ particleShear N hN '' particleParameterBox N n at hy
        rcases (Set.mem_image _ _ _).mp hy with ⟨w, hw, hwy⟩
        have hyw : y = w := hinj hwy.symm
        simpa [hyw] using hw
      · intro hy
        change particleShear N hN y ∈ particleShear N hN '' particleParameterBox N n
        exact Set.mem_image_of_mem _ hy
    rw [← (particleShear_volumePreserving hN).measure_preimage
      hcompact.measurableSet.nullMeasurableSet, hpre]
  have hrestrict :
      (volume.restrict (SharpLSI.unitBox (Fin N)))
        (particleConfigLift N ⁻¹' particleFavorableBox N hN n) =
        volume (SharpLSI.unitBox (Fin N) ∩
          particleConfigLift N ⁻¹' particleFavorableBox N hN n) := by
    rw [Measure.restrict_apply
      ((particleConfigLift_continuous N).measurable hboxCompact.measurableSet)]
    rw [Set.inter_comm]
  rw [hrestrict]
  calc
    ENNReal.ofReal (particleBoxConstant N hN * separation n) ≤
        volume (particleParameterBox N n) := by
      rw [particleParameterBox_volume hN]
      have hreal : separation n / 3 *
          (∏ i ∈ Finset.univ.erase (particleIndex1 N hN), particleBoxFixedWidth N) =
            particleBoxConstant N hN * separation n := by
        unfold particleBoxConstant
        ring
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hwpos : 0 < particleBoxFixedWidth N := by
        unfold particleBoxFixedWidth
        apply div_pos
        · norm_num
        · exact mul_pos (by norm_num) hNpos
      rw [← ENNReal.ofReal_prod_of_nonneg
        (s := Finset.univ.erase (particleIndex1 N hN))
        (f := fun _ : Fin N => particleBoxFixedWidth N)
        (by intro i hi; exact le_of_lt hwpos)]
      rw [← ENNReal.ofReal_mul
        (le_of_lt (div_pos (separation_pos n) (by norm_num))), hreal]
    _ = volume (particleShear N hN '' particleParameterBox N n) := hmeasure.symm
    _ ≤ volume (SharpLSI.unitBox (Fin N) ∩
          particleConfigLift N ⁻¹' particleFavorableBox N hN n) :=
      measure_mono hsubset

/-- The real coordinates of the sheared box stay in fixed separated arcs, except for the valley
pair. -/
private theorem particleFavorableBox_position_bounds {N : ℕ} (hN : 2 ≤ N) (n : ℕ)
    {y : Fin N → ℝ} (hy : y ∈ particleParameterBox N n) (i : Fin N) :
    (if i.val < 2 then
      particleShear N hN y i ∈ Set.Icc (1 / 10 : ℝ) (1 / 5)
    else particleShear N hN y i ∈ Set.Icc (1 / 3 : ℝ) (1 / 2)) := by
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha : separation n ≤ (1 : ℝ) / 10000 := by
    have h := separation_le_ten_neg_four n
    norm_num [Real.rpow_neg, Real.rpow_natCast] at h ⊢
    exact h
  have hr : particleBoxRadius N ≤ (1 : ℝ) / 200 := by
    unfold particleBoxRadius
    apply (div_le_iff₀ (by positivity : 0 < 100 * (N : ℝ))).2
    nlinarith [hNreal]
  have hcoord (k : Fin N) :
      y k ∈ Set.Icc (particleBoxLower N n k) (particleBoxUpper N n k) :=
    Set.mem_univ_pi.mp hy k
  by_cases hi0 : i.val = 0
  · have hi : i = particleIndex0 N hN := Fin.ext hi0
    subst i
    have hy0 : y (particleIndex0 N hN) ∈
        Set.Icc (1 / 8 - particleBoxRadius N) (1 / 8 + particleBoxRadius N) := by
      simpa [particleBoxLower, particleBoxUpper, particleBoxCenter,
        particleIndex0, particleIndex1] using hcoord (particleIndex0 N hN)
    have hz : particleShear N hN y (particleIndex0 N hN) = y (particleIndex0 N hN) := by
      rw [particleShear_apply]
      simp [particleIndex0, particleIndex1]
    simp only [particleIndex0, Fin.val_mk, Nat.zero_lt_two, if_pos]
    change particleShear N hN y (particleIndex0 N hN) ∈ _
    rw [hz]
    constructor <;> nlinarith [hr, hy0.1, hy0.2]
  · by_cases hi1 : i.val = 1
    · have hi : i = particleIndex1 N hN := Fin.ext hi1
      subst i
      have hy0 : y (particleIndex0 N hN) ∈
          Set.Icc (1 / 8 - particleBoxRadius N) (1 / 8 + particleBoxRadius N) := by
        simpa [particleBoxLower, particleBoxUpper, particleBoxCenter,
          particleIndex0, particleIndex1] using hcoord (particleIndex0 N hN)
      have hy1 : y (particleIndex1 N hN) ∈
          Set.Icc (-(2 * separation n / 3)) (-(separation n / 3)) := by
        simpa [particleBoxLower, particleBoxUpper, particleIndex1] using hcoord (particleIndex1 N hN)
      have hz : particleShear N hN y (particleIndex1 N hN) =
          y (particleIndex1 N hN) + y (particleIndex0 N hN) := by
        rw [particleShear_apply]
        simp [particleIndex0, particleIndex1]
      simp only [particleIndex1, Fin.val_mk, Nat.reduceLT, if_pos]
      change particleShear N hN y (particleIndex1 N hN) ∈ _
      rw [hz]
      constructor <;> nlinarith [hr, ha, hy0.1, hy0.2, hy1.1, hy1.2]
    · have hidxloNat : 2 ≤ i.val := by omega
      have hidxlo : (2 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hidxloNat
      have hidxhi : (i.val : ℝ) < (N : ℝ) := by exact_mod_cast i.isLt
      have hterm0 : 0 ≤ ((i.val : ℝ) - 2) / (12 * (N : ℝ)) :=
        div_nonneg (by linarith [hidxlo]) (by positivity)
      have hterm1 : ((i.val : ℝ) - 2) / (12 * (N : ℝ)) < 1 / 12 := by
        rw [div_lt_iff₀ (by positivity : 0 < 12 * (N : ℝ))]
        nlinarith [hidxhi]
      have hyi : y i ∈
          Set.Icc (particleBoxCenter N i - particleBoxRadius N)
            (particleBoxCenter N i + particleBoxRadius N) := by
        simpa [particleBoxLower, particleBoxUpper, hi1] using hcoord i
      have hz : particleShear N hN y i = y i := by
        rw [particleShear_apply]
        simp [hi1]
      simp only [if_neg (Nat.not_lt.mpr hidxloNat)]
      rw [hz]
      simp only [particleBoxCenter, if_neg hi0] at hyi
      constructor
      · nlinarith [hterm0, hr, hyi.1]
      · nlinarith [hterm1, hr, hyi.2]

/-- The valley coordinate is realized by a distinguished particle pair. -/
theorem particle_favorable_box_pair_cutoff {N : ℕ} (hN : 2 ≤ N) (n : ℕ)
    {X : SharpLSI.Config N 1} (hX : X ∈ particleFavorableBox N hN n) :
    pairCutoff n (circleDiff (X (particleIndex0 N hN)) (X (particleIndex1 N hN))) = 1 := by
  rcases hX with ⟨z, ⟨y, hy, rfl⟩, rfl⟩
  have hy1 : y (particleIndex1 N hN) ∈
      Set.Icc (-(2 * separation n / 3)) (-(separation n / 3)) := by
    exact Set.mem_univ_pi.mp hy (particleIndex1 N hN)
  have hplateau : -y (particleIndex1 N hN) ∈
      Set.Icc (separation n / 3) (2 * separation n / 3) := by
    constructor <;> linarith [hy1.1, hy1.2]
  have h0 : particleShear N hN y (particleIndex0 N hN) = y (particleIndex0 N hN) := by
    rw [particleShear_apply]
    simp [particleIndex0, particleIndex1]
  have h1 : particleShear N hN y (particleIndex1 N hN) =
      y (particleIndex1 N hN) + y (particleIndex0 N hN) := by
    rw [particleShear_apply]
    simp [particleIndex0, particleIndex1]
  rw [show circleDiff
      (particleConfigLift N (particleShear N hN y) (particleIndex0 N hN))
      (particleConfigLift N (particleShear N hN y) (particleIndex1 N hN)) =
        torusPoint (-y (particleIndex1 N hN)) by
          rw [circleDiff]
          simp only [particleConfigLift, h0, h1]
          rw [← Examples.PositiveH1.Nonlinear.lift1_sub]
          congr 1
          ring]
  exact pairCutoff_one_on_positive_plateau hplateau

private theorem torusDist_point_eq_abs {t : ℝ} (ht : |t| ≤ 1 / 2) :
    torusDist (torusPoint t) 0 = |t| := by
  have h := DGPS.torusDist_liftT_eq (x := fun _ : Fin 1 => t)
    (y := fun _ : Fin 1 => (0 : ℝ)) (by intro j; simpa using ht)
  have hzero : torusPoint (0 : ℝ) = 0 := by
    ext j
    simp [torusPoint, torusLift, SharpLSI.liftT]
  rw [← hzero]
  simpa [torusPoint, torusLift, SharpLSI.liftT, Real.sqrt_sq_eq_abs] using h

theorem particle_favorable_box_distinguished_barrier_upper
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) {X : SharpLSI.Config N 1}
    (hX : X ∈ particleFavorableBox N hN n) :
    barrier (X (particleIndex0 N hN) - X (particleIndex1 N hN)) ≤ valleyCost n := by
  rcases hX with ⟨z, ⟨y, hy, rfl⟩, rfl⟩
  have hy1 : y (particleIndex1 N hN) ∈
      Set.Icc (-(2 * separation n / 3)) (-(separation n / 3)) :=
    Set.mem_univ_pi.mp hy (particleIndex1 N hN)
  have hplateau : -y (particleIndex1 N hN) ∈
      Set.Icc (separation n / 3) (2 * separation n / 3) := by
    constructor <;> linarith [hy1.1, hy1.2]
  have h0 : particleShear N hN y (particleIndex0 N hN) = y (particleIndex0 N hN) := by
    rw [particleShear_apply]
    simp [particleIndex0, particleIndex1]
  have h1 : particleShear N hN y (particleIndex1 N hN) =
      y (particleIndex1 N hN) + y (particleIndex0 N hN) := by
    rw [particleShear_apply]
    simp [particleIndex0, particleIndex1]
  rw [show particleConfigLift N (particleShear N hN y) (particleIndex0 N hN) -
      particleConfigLift N (particleShear N hN y) (particleIndex1 N hN) =
        torusPoint (-y (particleIndex1 N hN)) by
          change Examples.PositiveH1.Nonlinear.lift1
              (particleShear N hN y (particleIndex0 N hN)) -
            Examples.PositiveH1.Nonlinear.lift1
              (particleShear N hN y (particleIndex1 N hN)) = _
          rw [h0, h1]
          rw [← Examples.PositiveH1.Nonlinear.lift1_sub]
          congr 1
          ring]
  exact barrier_valley_upper n hplateau

theorem particle_favorable_box_offpair_distance_lower {N : ℕ}
    (hN : 2 ≤ N) (n : ℕ) {X : SharpLSI.Config N 1}
    (hX : X ∈ particleFavorableBox N hN n) {i j : Fin N} (hij : i ≠ j)
    (hnot01 : ¬ (i = particleIndex0 N hN ∧ j = particleIndex1 N hN))
    (hnot10 : ¬ (i = particleIndex1 N hN ∧ j = particleIndex0 N hN)) :
    1 / (100 * (N : ℝ)) ≤ torusDist (X i - X j) 0 := by
  rcases hX with ⟨z, ⟨y, hy, rfl⟩, rfl⟩
  let si : ℝ := particleShear N hN y i
  let sj : ℝ := particleShear N hN y j
  have hsi := particleFavorableBox_position_bounds hN n hy i
  have hsj := particleFavorableBox_position_bounds hN n hy j
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hdelta : 1 / (100 * (N : ℝ)) ≤ (1 : ℝ) / 200 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 100 * (N : ℝ))
      (by norm_num : (0 : ℝ) < 200)]
    nlinarith [hNreal]
  have hlow_pair_impossible : ¬ (i.val < 2 ∧ j.val < 2) := by
    intro hboth
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hij (Fin.ext (by omega))
    · have hieq : i = particleIndex0 N hN := by
        apply Fin.ext
        simpa [particleIndex0] using hi
      have hjeq : j = particleIndex1 N hN := by
        apply Fin.ext
        simpa [particleIndex1] using hj
      exact hnot01 ⟨hieq, hjeq⟩
    · have hieq : i = particleIndex1 N hN := by
        apply Fin.ext
        simpa [particleIndex1] using hi
      have hjeq : j = particleIndex0 N hN := by
        apply Fin.ext
        simpa [particleIndex0] using hj
      exact hnot10 ⟨hieq, hjeq⟩
    · exact hij (Fin.ext (by omega))
  have hcoord_diff_le : |si - sj| ≤ 1 / 2 := by
    by_cases hilow : i.val < 2
    · have hjhigh : ¬ j.val < 2 := fun hjlow => hlow_pair_impossible ⟨hilow, hjlow⟩
      have hsi' : si ∈ Set.Icc (1 / 10 : ℝ) (1 / 5) := by
        simpa [si, hilow] using hsi
      have hsj' : sj ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
        simpa [sj, hjhigh] using hsj
      rw [abs_of_nonpos (by linarith [hsi'.2, hsj'.1])]
      linarith [hsi'.1, hsj'.2]
    · by_cases hjlow : j.val < 2
      · have hsi' : si ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
          simpa [si, hilow] using hsi
        have hsj' : sj ∈ Set.Icc (1 / 10 : ℝ) (1 / 5) := by
          simpa [sj, hjlow] using hsj
        rw [abs_of_nonneg (by linarith [hsi'.1, hsj'.2])]
        linarith [hsi'.2, hsj'.1]
      · have hsi' : si ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
          simpa [si, hilow] using hsi
        have hsj' : sj ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
          simpa [sj, hjlow] using hsj
        rw [abs_le]
        constructor <;> linarith [hsi'.1, hsi'.2, hsj'.1, hsj'.2]
  have hcoordinate_gap : 1 / (100 * (N : ℝ)) ≤ |si - sj| := by
    by_cases hilow : i.val < 2
    · have hjhigh : ¬ j.val < 2 := fun hjlow => hlow_pair_impossible ⟨hilow, hjlow⟩
      have hsi' : si ∈ Set.Icc (1 / 10 : ℝ) (1 / 5) := by
        simpa [si, hilow] using hsi
      have hsj' : sj ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
        simpa [sj, hjhigh] using hsj
      rw [abs_of_nonpos (by linarith [hsi'.2, hsj'.1])]
      linarith [hsi'.2, hsj'.1, hdelta]
    · by_cases hjlow : j.val < 2
      · have hsi' : si ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
          simpa [si, hilow] using hsi
        have hsj' : sj ∈ Set.Icc (1 / 10 : ℝ) (1 / 5) := by
          simpa [sj, hjlow] using hsj
        rw [abs_of_nonneg (by linarith [hsi'.1, hsj'.2])]
        linarith [hsi'.1, hsj'.2, hdelta]
      · have hi2 : 2 ≤ i.val := by omega
        have hj2 : 2 ≤ j.val := by omega
        have hival0 : i.val ≠ 0 := by omega
        have hjval0 : j.val ≠ 0 := by omega
        have hival1 : i.val ≠ 1 := by omega
        have hjval1 : j.val ≠ 1 := by omega
        have hcoordi : y i ∈ Set.Icc
            (particleBoxCenter N i - particleBoxRadius N)
            (particleBoxCenter N i + particleBoxRadius N) := by
          simpa [particleBoxLower, particleBoxUpper, hival1] using
            Set.mem_univ_pi.mp hy i
        have hcoordj : y j ∈ Set.Icc
            (particleBoxCenter N j - particleBoxRadius N)
            (particleBoxCenter N j + particleBoxRadius N) := by
          simpa [particleBoxLower, particleBoxUpper, hjval1] using
            Set.mem_univ_pi.mp hy j
        have hsi_eq : si = y i := by
          dsimp [si]
          rw [particleShear_apply]
          simp [hival1]
        have hsj_eq : sj = y j := by
          dsimp [sj]
          rw [particleShear_apply]
          simp [hjval1]
        have hval_ne : i.val ≠ j.val := by
          intro heq
          exact hij (Fin.ext heq)
        have hvalgap : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
          rcases Nat.lt_or_gt_of_ne hval_ne with hlt | hgt
          · have hnat : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
            have hreal : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hnat
            rw [abs_of_neg (by linarith)]
            linarith
          · have hnat : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hgt
            have hreal : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hnat
            rw [abs_of_pos (by linarith)]
            linarith
        have hcenter_gap : 1 / (12 * (N : ℝ)) ≤
            |particleBoxCenter N i - particleBoxCenter N j| := by
          have hinside : particleBoxCenter N i - particleBoxCenter N j =
              ((i.val : ℝ) - (j.val : ℝ)) / (12 * (N : ℝ)) := by
            simp [particleBoxCenter, hival0, hjval0]
            ring
          rw [hinside, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 12 * (N : ℝ))]
          exact (div_le_div_iff_of_pos_right (by positivity)).2 hvalgap
        have hradius : 2 * particleBoxRadius N + 1 / (100 * (N : ℝ)) ≤
            1 / (12 * (N : ℝ)) := by
          unfold particleBoxRadius
          have hNpos' : 0 < (N : ℝ) := hNpos
          field_simp
          nlinarith
        by_cases horder : particleBoxCenter N i ≤ particleBoxCenter N j
        · have hcenter : 1 / (12 * (N : ℝ)) ≤
              particleBoxCenter N j - particleBoxCenter N i := by
            rw [abs_of_nonpos (sub_nonpos.mpr horder)] at hcenter_gap
            simpa [sub_eq_add_neg] using hcenter_gap
          have hfar : 2 * particleBoxRadius N + 1 / (100 * (N : ℝ)) ≤
              particleBoxCenter N j - particleBoxCenter N i := hradius.trans hcenter
          have hcoord : 1 / (100 * (N : ℝ)) ≤ y j - y i := by
            linarith [hcoordi.2, hcoordj.1]
          have hδpos : 0 < 1 / (100 * (N : ℝ)) := by positivity
          rw [hsi_eq, hsj_eq, abs_of_nonpos (by linarith [hcoord, hδpos])]
          simpa [sub_eq_add_neg] using hcoord
        · have horder' : particleBoxCenter N j ≤ particleBoxCenter N i := le_of_not_ge horder
          have hcenter : 1 / (12 * (N : ℝ)) ≤
              particleBoxCenter N i - particleBoxCenter N j := by
            rw [abs_of_nonneg (sub_nonneg.mpr horder')] at hcenter_gap
            exact hcenter_gap
          have hfar : 2 * particleBoxRadius N + 1 / (100 * (N : ℝ)) ≤
              particleBoxCenter N i - particleBoxCenter N j := hradius.trans hcenter
          have hcoord : 1 / (100 * (N : ℝ)) ≤ y i - y j := by
            linarith [hcoordi.1, hcoordj.2]
          have hδpos : 0 < 1 / (100 * (N : ℝ)) := by positivity
          rw [hsi_eq, hsj_eq, abs_of_nonneg (by linarith [hcoord, hδpos])]
          exact hcoord
  have hdiff : particleConfigLift N (particleShear N hN y) i -
      particleConfigLift N (particleShear N hN y) j = torusPoint (si - sj) := by
    change Examples.PositiveH1.Nonlinear.lift1 (particleShear N hN y i) -
      Examples.PositiveH1.Nonlinear.lift1 (particleShear N hN y j) = _
    rw [← Examples.PositiveH1.Nonlinear.lift1_sub]
    congr 1 <;> simp [si, sj]
  rw [hdiff]
  rw [torusDist_point_eq_abs hcoord_diff_le]
  exact hcoordinate_gap

private theorem particle_favorable_box_barrier_upper {N : ℕ} (hN : 2 ≤ N)
    (n : ℕ) {X : SharpLSI.Config N 1} (hX : X ∈ particleFavorableBox N hN n)
    (Caway : ℝ) (hCaway : 0 ≤ Caway)
    (hbarAway : ∀ x : Circle, 1 / (100 * (N : ℝ)) ≤ torusDist x 0 → barrier x ≤ Caway)
    (i j : Fin N) :
    barrier (X i - X j) ≤ Caway + valleyCost n := by
  by_cases hij : i = j
  · subst j
    simp only [sub_self, barrier_zero]
    exact add_nonneg hCaway (valleyCost_nonneg n)
  · by_cases hpair01 : i = particleIndex0 N hN ∧ j = particleIndex1 N hN
    · rcases hpair01 with ⟨rfl, rfl⟩
      calc
        barrier (X (particleIndex0 N hN) - X (particleIndex1 N hN)) ≤ valleyCost n :=
          particle_favorable_box_distinguished_barrier_upper hN n hX
        _ ≤ Caway + valleyCost n := le_add_of_nonneg_left hCaway
    · by_cases hpair10 : i = particleIndex1 N hN ∧ j = particleIndex0 N hN
      · rcases hpair10 with ⟨rfl, rfl⟩
        have hswap : X (particleIndex1 N hN) - X (particleIndex0 N hN) =
            -(X (particleIndex0 N hN) - X (particleIndex1 N hN)) := by abel
        rw [hswap, barrier_even]
        calc
          barrier (X (particleIndex0 N hN) - X (particleIndex1 N hN)) ≤ valleyCost n :=
            particle_favorable_box_distinguished_barrier_upper hN n hX
          _ ≤ Caway + valleyCost n := le_add_of_nonneg_left hCaway
      · have hdist := particle_favorable_box_offpair_distance_lower hN n hX hij hpair01 hpair10
        have hbar' := hbarAway (X i - X j) hdist
        exact hbar'.trans (le_add_of_nonneg_right (valleyCost_nonneg n))

/-- SLC-N018: the Hamiltonian is bounded above on the favorable box, with its explicit
`(N/2) β η valleyCost n` dependence retained. -/
theorem particle_favorable_box_hamiltonian_upper {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ X : SharpLSI.Config N 1,
      X ∈ particleFavorableBox N hN n →
      SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X ≤
        C + (N : ℝ) / 2 * β * η * valleyCost n := by
  rcases B.bounded_g with ⟨G, hG, hGb⟩
  rcases barrier_bound_away_zero (show 0 < 1 / (100 * (N : ℝ)) by positivity) with
    ⟨Caway, hCaway, hbarAway⟩
  let C : ℝ := (N : ℝ) / 2 * β * (G + η * Caway)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro n X hX
    have hpair (i j : Fin N) :
        perturbedInteraction B β η (X i) (X j) ≤
          β * (G + η * Caway) + β * η * valleyCost n := by
      have hg : B.g (X i - X j) ≤ G := (abs_le.mp (hGb (X i - X j))).2
      have hs := particle_favorable_box_barrier_upper hN n hX Caway hCaway hbarAway i j
      unfold perturbedInteraction perturbedKernel
      calc
        β * (B.g (X i - X j) + η * barrier (X i - X j)) ≤
            β * (G + η * (Caway + valleyCost n)) :=
          mul_le_mul_of_nonneg_left (add_le_add hg (mul_le_mul_of_nonneg_left hs hη.le)) hβ.le
        _ = β * (G + η * Caway) + β * η * valleyCost n := by ring
    have hsum : (∑ i : Fin N, ∑ j : Fin N,
        perturbedInteraction B β η (X i) (X j)) ≤
        (N : ℝ) ^ 2 * (β * (G + η * Caway) + β * η * valleyCost n) := by
      calc
        _ ≤ ∑ i : Fin N, ∑ j : Fin N,
              (β * (G + η * Caway) + β * η * valleyCost n) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
        _ = (N : ℝ) ^ 2 * (β * (G + η * Caway) + β * η * valleyCost n) := by
          simp
          ring
    unfold SharpLSI.hamiltonian
    simp only [Finset.sum_const_zero, zero_add]
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    calc
      1 / (2 * (N : ℝ)) *
          (∑ i : Fin N, ∑ j : Fin N, perturbedInteraction B β η (X i) (X j)) ≤
        1 / (2 * (N : ℝ)) *
          ((N : ℝ) ^ 2 * (β * (G + η * Caway) + β * η * valleyCost n)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = C + (N : ℝ) / 2 * β * η * valleyCost n := by
        dsimp [C]
        field_simp [ne_of_gt hNpos]

private def particleTestTerm {N : ℕ} (n : ℕ) (X : SharpLSI.Config N 1)
    (i j : Fin N) : ℝ :=
  if i = j then 0 else pairCutoff n (X i - X j)

/-- The two oriented plateau interactions contribute one to the pair test. -/
private theorem particle_favorable_box_test_ge_one {N : ℕ} (hN : 2 ≤ N) (n : ℕ)
    {X : SharpLSI.Config N 1} (hX : X ∈ particleFavorableBox N hN n) :
    1 ≤ particleTest n X := by
  let i0 := particleIndex0 N hN
  let i1 := particleIndex1 N hN
  have hne : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i0, i1, particleIndex0, particleIndex1] at hv
  have hcut01 : pairCutoff n (X i0 - X i1) = 1 := by
    simpa [i0, i1, circleDiff] using particle_favorable_box_pair_cutoff hN n hX
  have hcut10 : pairCutoff n (X i1 - X i0) = 1 := by
    have hswap : X i1 - X i0 = -(X i0 - X i1) := by abel
    rw [hswap, pairCutoff_even, hcut01]
  have hterm01 : particleTestTerm n X i0 i1 = 1 := by
    simp [particleTestTerm, hne, hcut01]
  have hterm10 : particleTestTerm n X i1 i0 = 1 := by
    simp [particleTestTerm, hne.symm, hcut10]
  have hterm_nonneg (i j : Fin N) : 0 ≤ particleTestTerm n X i j := by
    by_cases hij : i = j
    · simp [particleTestTerm, hij]
    · simp [particleTestTerm, hij, pairCutoff_nonneg]
  have hinner (i : Fin N) :
      (if i = i0 then (1 : ℝ) else 0) + (if i = i1 then 1 else 0) ≤
        ∑ j : Fin N, particleTestTerm n X i j := by
    by_cases hi0 : i = i0
    · subst i
      have hsingle : particleTestTerm n X i0 i1 ≤
          ∑ j : Fin N, particleTestTerm n X i0 j :=
        Finset.single_le_sum (fun j _ => hterm_nonneg i0 j) (Finset.mem_univ i1)
      simpa [hterm01, hne] using hsingle
    · by_cases hi1 : i = i1
      · subst i
        have hsingle : particleTestTerm n X i1 i0 ≤
            ∑ j : Fin N, particleTestTerm n X i1 j :=
          Finset.single_le_sum (fun j _ => hterm_nonneg i1 j) (Finset.mem_univ i0)
        simpa [hterm10, hi0] using hsingle
      · simp [hi0, hi1]
        exact Finset.sum_nonneg fun j _ => hterm_nonneg i j
  have hsum :
      ∑ i : Fin N, ((if i = i0 then (1 : ℝ) else 0) + (if i = i1 then 1 else 0)) ≤
        ∑ i : Fin N, ∑ j : Fin N, particleTestTerm n X i j :=
    Finset.sum_le_sum fun i _ => hinner i
  have hsum_id :
      ∑ i : Fin N, ((if i = i0 then (1 : ℝ) else 0) + (if i = i1 then 1 else 0)) = 2 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq', hne]
    norm_num
  have htwice : 2 ≤ ∑ i : Fin N, ∑ j : Fin N, particleTestTerm n X i j := by
    rw [← hsum_id]
    exact hsum
  change 1 ≤ (1 / 2 : ℝ) *
    ∑ i : Fin N, ∑ j : Fin N, particleTestTerm n X i j
  nlinarith [htwice]

private theorem n019_withDensity_second_moment_lower
    {X : Type*} [MeasurableSpace X] {μ P : Measure X}
    {A : Set X} (hA : MeasurableSet A) {ρ : X → ℝ≥0∞}
    (hP : P = μ.withDensity ρ) {c : ℝ}
    (hρ : ∀ x ∈ A, ENNReal.ofReal c ≤ ρ x)
    {f : X → ℝ} (hfA : ∀ x ∈ A, 1 ≤ f x)
    (hf2 : Integrable (fun x => f x ^ 2) P) :
    ENNReal.ofReal c * μ A ≤ ENNReal.ofReal (∫ x, f x ^ 2 ∂P) := by
  have hset : ENNReal.ofReal c * μ A ≤ P A := by
    rw [hP, withDensity_apply _ hA]
    calc
      ENNReal.ofReal c * μ A =
          ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal c) x ∂μ :=
        (lintegral_indicator_const hA (ENNReal.ofReal c)).symm
      _ ≤ ∫⁻ x in A, ρ x ∂μ := by
        rw [← lintegral_indicator hA]
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ A
        · simp only [Set.indicator_of_mem hx]
          exact hρ x hx
        · simp [hx]
  have hmoment : P A ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P := by
    calc
      P A = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂P := by
        rw [lintegral_indicator_const hA]
        simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx]
          calc
            (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by norm_num
            _ ≤ ENNReal.ofReal (f x ^ 2) :=
              ENNReal.ofReal_le_ofReal (by nlinarith [hfA x hx])
        · simp [hx]
  have hnn : 0 ≤ᵐ[P] fun x => f x ^ 2 := Filter.Eventually.of_forall fun x => sq_nonneg _
  have hfin : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnn).1 hf2.hasFiniteIntegral
  have hcast :
      ENNReal.ofReal (∫ x, f x ^ 2 ∂P) = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hf2.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal (ne_of_lt hfin)
  calc
    ENNReal.ofReal c * μ A ≤ P A := hset
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P := hmoment
    _ = ENNReal.ofReal (∫ x, f x ^ 2 ∂P) := hcast.symm

private theorem n019_gibbs_second_moment_lower_real_volume
    {X : Type*} [MeasurableSpace X] {μ P : Measure X} [IsFiniteMeasure μ]
    {A : Set X} (hA : MeasurableSet A) {H f : X → ℝ} {C Z : ℝ}
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (Z⁻¹ * Real.exp (-H x))))
    (hZ : 0 < Z) (hH : ∀ x ∈ A, H x ≤ C)
    (hfA : ∀ x ∈ A, 1 ≤ f x)
    (hf2 : Integrable (fun x => f x ^ 2) P) :
    ENNReal.ofReal (Real.exp (-C) / Z) * ENNReal.ofReal (μ.real A) ≤
      ENNReal.ofReal (∫ x, f x ^ 2 ∂P) := by
  have hAfinite : μ A ≠ ⊤ := ne_of_lt (measure_lt_top μ A)
  have hAreal : ENNReal.ofReal (μ.real A) = μ A := by
    rw [Measure.real_def]
    exact ENNReal.ofReal_toReal hAfinite
  rw [hAreal]
  apply n019_withDensity_second_moment_lower hA hP
  · intro x hx
    apply ENNReal.ofReal_le_ofReal
    calc
      Real.exp (-C) / Z ≤ Real.exp (-H x) / Z :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hH x hx])) hZ.le
      _ = Z⁻¹ * Real.exp (-H x) := by simp [div_eq_mul_inv, mul_comm]
  · exact hfA
  · exact hf2

private theorem n019_gibbs_second_moment_lower_box
    {X : Type*} [MeasurableSpace X] {μ P : Measure X} [IsFiniteMeasure μ]
    {A : Set X} (hA : MeasurableSet A) {H f : X → ℝ} {C₀ κ cost Z d a : ℝ}
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (Z⁻¹ * Real.exp (-H x))))
    (hZ : 0 < Z) (hH : ∀ x ∈ A, H x ≤ C₀ + κ * cost)
    (hfA : ∀ x ∈ A, 1 ≤ f x) (hf2 : Integrable (fun x => f x ^ 2) P)
    (hvolume : d * a ≤ μ.real A) :
    ENNReal.ofReal ((d / Z) * a * Real.exp (-(C₀ + κ * cost))) ≤
      ENNReal.ofReal (∫ x, f x ^ 2 ∂P) := by
  have hbase := n019_gibbs_second_moment_lower_real_volume hA hP hZ hH hfA hf2
  have hq : 0 ≤ Real.exp (-(C₀ + κ * cost)) / Z :=
    (div_pos (Real.exp_pos _) hZ).le
  have hvol : ENNReal.ofReal (d * a) ≤ ENNReal.ofReal (μ.real A) :=
    ENNReal.ofReal_le_ofReal hvolume
  have hmul :
      ENNReal.ofReal ((Real.exp (-(C₀ + κ * cost)) / Z) * (d * a)) ≤
        ENNReal.ofReal (Real.exp (-(C₀ + κ * cost)) / Z) * ENNReal.ofReal (μ.real A) := by
    rw [ENNReal.ofReal_mul hq]
    exact mul_le_mul_of_nonneg_left hvol bot_le
  have heq :
      (d / Z) * a * Real.exp (-(C₀ + κ * cost)) =
        (Real.exp (-(C₀ + κ * cost)) / Z) * (d * a) := by ring
  rw [heq]
  exact hmul.trans hbase

/-- SLC-N019: the favorable box gives a second-moment lower bound with constants uniform in
`n`; the full valley cost remains in the exponential. -/
theorem particle_favorable_box_second_moment_lower {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 < d ∧ ∀ n : ℕ,
      d * separation n * Real.exp (-(C + (N : ℝ) / 2 * β * η * valleyCost n)) ≤
        ∫ X, particleTest n X ^ 2 ∂SharpLSI.gibbs (fun _ => 0)
          (perturbedInteraction B β η) N := by
  rcases particle_favorable_box_hamiltonian_upper hN B hβ hη with ⟨C, hC, hHam⟩
  have hNpos : 0 < N := by omega
  let Z := SharpLSI.partitionFn (fun _ => 0) (perturbedInteraction B β η) N
  let H := SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N
  let P := SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N
  have hZ : 0 < Z := by
    dsimp [Z]
    exact singular_partition_pos B hβ hη hNpos
  have hP : P = (volume : Measure (SharpLSI.Config N 1)).withDensity
      (fun X => ENNReal.ofReal (Z⁻¹ * Real.exp (-H X))) := by
    dsimp [P, SharpLSI.gibbs, Z, H, SharpLSI.partitionFn]
    congr 1
    funext X
    simp [div_eq_mul_inv, mul_comm]
  have : IsProbabilityMeasure P := singular_gibbs_isProbabilityMeasure B hβ hη hNpos
  refine ⟨C, particleBoxConstant N hN / Z, hC, div_pos (particleBoxConstant_pos hN) hZ, ?_⟩
  intro n
  let A := particleFavorableBox N hN n
  have hA : MeasurableSet A := (particleFavorableBox_compact hN n).measurableSet
  have hAvolENN : ENNReal.ofReal (particleBoxConstant N hN * separation n) ≤
      (volume : Measure (SharpLSI.Config N 1)) A := particle_favorable_box_volume_lower hN n
  have hAfinite : (volume : Measure (SharpLSI.Config N 1)) A ≠ ⊤ :=
    ne_of_lt (measure_lt_top _ A)
  have hAvol : particleBoxConstant N hN * separation n ≤
      (volume : Measure (SharpLSI.Config N 1)).real A := by
    have h := ENNReal.toReal_mono hAfinite hAvolENN
    simpa [Measure.real_def, ENNReal.toReal_ofReal
      (mul_nonneg (particleBoxConstant_pos hN).le (separation_pos n).le)] using h
  have hHupper : ∀ X ∈ A,
      H X ≤ C + (N : ℝ) / 2 * β * η * valleyCost n := by
    intro X hX
    exact hHam n X hX
  have hFupper : ∀ X ∈ A, 1 ≤ particleTest n X := by
    intro X hX
    exact particle_favorable_box_test_ge_one hN n hX
  have hFmem : MemLp (particleTest n) 2 P := by
    refine MemLp.of_bound (particleTest_measurable n).aestronglyMeasurable
      ((N : ℝ) ^ 2 / 2) ?_
    exact Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (particleTest_nonneg n X)]
      exact particleTest_le n X
  have hbound := n019_gibbs_second_moment_lower_box hA hP hZ hHupper hFupper
    hFmem.integrable_sq hAvol
  have hbound' :
      ENNReal.ofReal ((particleBoxConstant N hN / Z) * separation n *
        Real.exp (-(C + (N : ℝ) / 2 * β * η * valleyCost n))) ≤
      ENNReal.ofReal (∫ X, particleTest n X ^ 2 ∂P) := by
    convert hbound using 1
  have hIntNN : 0 ≤ ∫ X, particleTest n X ^ 2 ∂P :=
    integral_nonneg fun X => sq_nonneg _
  exact (ENNReal.ofReal_le_ofReal_iff hIntNN).mp hbound'

private theorem pairDifference_measurePreserving {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun X : SharpLSI.Config N 1 => X i - X j) volume (haar 1) := by
  have hpair : MeasurePreserving (fun X : SharpLSI.Config N 1 => (X i, X j)) volume
      ((haar 1).prod (haar 1)) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    change (Measure.pi (fun _ : Fin N => haar 1)).map (fun X => (X i, X j)) = _
    have hind := iIndepFun_pi (μ := fun _ : Fin N => haar 1)
      (X := fun _ => id) (fun _ => aemeasurable_id)
    have hm := (indepFun_iff_map_prod_eq_prod_map_map
      (μ := Measure.pi (fun _ : Fin N => haar 1))
      (f := fun X => X i) (g := fun X => X j)
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp
      (hind.indepFun hij)
    rw [hm, (measurePreserving_eval (fun _ : Fin N => haar 1) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N => haar 1) j).map_eq]
  exact measurePreserving_fst.comp ((measurePreserving_sub_prod (haar 1) (haar 1)).comp hpair)

theorem particleTest_support_haar_le {N : ℕ} (n : ℕ) :
    (volume : Measure (SharpLSI.Config N 1)) {X | particleTest n X ≠ 0} ≤
      ENNReal.ofReal (2 * (N : ℝ) ^ 2 * separation n) := by
  let E (p : Fin N × Fin N) : Set (SharpLSI.Config N 1) :=
    {X | p.1 ≠ p.2 ∧ pairCutoff n (X p.1 - X p.2) ≠ 0}
  have hsub : {X : SharpLSI.Config N 1 | particleTest n X ≠ 0} ⊆ ⋃ p, E p := by
    intro X hX
    by_contra hnot
    have hz : particleTest n X = 0 := by
      change (1 / 2 : ℝ) * (∑ i, ∑ j,
        if i = j then 0 else pairCutoff n (X i - X j)) = 0
      have hterms (i j : Fin N) : (if i = j then 0 else pairCutoff n (X i - X j)) = 0 := by
        split_ifs with hij
        · rfl
        · by_contra hne
          exact hnot (mem_iUnion.mpr ⟨(i, j), hij, hne⟩)
      simp only [hterms, Finset.sum_const_zero, mul_zero]
    exact hX hz
  have hbound (p : Fin N × Fin N) : volume (E p) ≤ ENNReal.ofReal (2 * separation n) := by
    by_cases hp : p.1 = p.2
    · simp [E, hp]
    · have hs : MeasurableSet {x : Circle | pairCutoff n x ≠ 0} :=
        ((measurableSet_singleton (0 : ℝ)).preimage (pairCutoff_measurable n)).compl
      have heq := (pairDifference_measurePreserving hp).measure_preimage hs.nullMeasurableSet
      have hE : E p = (fun X : SharpLSI.Config N 1 => X p.1 - X p.2) ⁻¹'
          {x | pairCutoff n x ≠ 0} := by ext X; simp [E, hp]
      rw [hE, heq]
      exact pairCutoff_support_measure_le n
  calc
    volume {X : SharpLSI.Config N 1 | particleTest n X ≠ 0} ≤ volume (⋃ p, E p) :=
      measure_mono hsub
    _ ≤ ∑' p : Fin N × Fin N, volume (E p) := measure_iUnion_le E
    _ ≤ ∑' _p : Fin N × Fin N, ENNReal.ofReal (2 * separation n) :=
      ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ 2 * separation n) := by
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

theorem variance_half_secondMoment_of_support_small
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) {A : Set Ω} (hA : MeasurableSet A)
    (hsupp : ∀ x, x ∉ A → f x = 0) (hsmall : P.real A ≤ 1 / 2) :
    ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x, f x ^ 2 ∂P) ≤ SharpLSI.var P f := by
  let m := ∫ x, f x ∂P
  let I := A.indicator (fun _ : Ω => (1 : ℝ))
  have hi : Integrable I P := (integrable_const (1 : ℝ)).indicator hA
  have hfi := hf.integrable (by norm_num)
  have hform (x : Ω) :
      (f x - 2 * m * I x) ^ 2 = f x ^ 2 - 4 * m * f x + 4 * m ^ 2 * I x := by
    by_cases hx : x ∈ A
    · simp only [I, indicator_of_mem hx]
      ring
    · simp only [I, indicator_of_notMem hx, hsupp x hx]
      ring
  have hnonneg : 0 ≤ ∫ x, (f x ^ 2 - 4 * m * f x + 4 * m ^ 2 * I x) ∂P := by
    apply integral_nonneg
    intro x
    change (0 : ℝ) ≤ f x ^ 2 - 4 * m * f x + 4 * m ^ 2 * I x
    rw [← hform]
    exact sq_nonneg _
  rw [integral_add (f := fun x => f x ^ 2 - 4 * m * f x)
      (g := fun x => 4 * m ^ 2 * I x)
      (hf.integrable_sq.sub (hfi.const_mul _)) (hi.const_mul _),
    integral_sub (f := fun x => f x ^ 2) (g := fun x => 4 * m * f x)
      hf.integrable_sq (hfi.const_mul _), integral_const_mul,
    integral_const_mul] at hnonneg
  have hiint : ∫ x, I x ∂P = P.real A := by
    simpa only [I, smul_eq_mul, mul_one] using integral_indicator_const (1 : ℝ) hA
  rw [hiint] at hnonneg
  have hprod := mul_le_mul_of_nonneg_left hsmall (sq_nonneg m)
  have hmean : m ^ 2 ≤ (1 / 2 : ℝ) * ∫ x, f x ^ 2 ∂P := by
    change 0 ≤ (∫ x, f x ^ 2 ∂P) - 4 * m * m + 4 * m ^ 2 * P.real A at hnonneg
    nlinarith
  change _ ≤ ProbabilityTheory.evariance f P
  rw [← hf.ofReal_variance_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [ProbabilityTheory.variance_eq_sub hf]
  change (1 / 2 : ℝ) * (∫ x, f x ^ 2 ∂P) ≤ (∫ x, f x ^ 2 ∂P) - m ^ 2
  linarith

theorem particleTest_support_probability_upper (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N)
        {X | particleTest n X ≠ 0} ≤ ENNReal.ofReal (C * separation n) := by
  obtain ⟨D, hD⟩ := singular_gibbs_density_upper_bound B hβ hη hN
  let K : ℝ := max D 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right D 1)
  have hD' (X : SharpLSI.Config N 1) :
      ENNReal.ofReal (Real.exp (-SharpLSI.hamiltonian (fun _ => 0)
        (perturbedInteraction B β η) N X) /
          SharpLSI.partitionFn (fun _ => 0) (perturbedInteraction B β η) N) ≤
        ENNReal.ofReal K := (hD X).trans (ENNReal.ofReal_le_ofReal (le_max_left D 1))
  refine ⟨K * (2 * (N : ℝ) ^ 2), by positivity, fun n => ?_⟩
  have hs : MeasurableSet {X : SharpLSI.Config N 1 | particleTest n X ≠ 0} :=
    ((measurableSet_singleton (0 : ℝ)).preimage (particleTest_measurable n)).compl
  unfold SharpLSI.gibbs
  rw [withDensity_apply _ hs]
  calc
    _ ≤ ∫⁻ _X : SharpLSI.Config N 1 in {X | particleTest n X ≠ 0}, ENNReal.ofReal K :=
      lintegral_mono hD'
    _ = ENNReal.ofReal K * volume {X : SharpLSI.Config N 1 | particleTest n X ≠ 0} := by simp
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * (N : ℝ) ^ 2 * separation n) := by
      gcongr
      exact particleTest_support_haar_le n
    _ = ENNReal.ofReal (K * (2 * (N : ℝ) ^ 2) * separation n) := by
      rw [← ENNReal.ofReal_mul hK.le]
      congr 1
      ring

theorem particleTest_support_probability_tendsto_zero (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    Tendsto (fun n : ℕ =>
      (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N)
        {X | particleTest n X ≠ 0}) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := particleTest_support_probability_upper B hβ hη hN
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (C * separation n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (separation_tendsto_zero.const_mul C)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hC

theorem particleTest_variance_eventually_lower (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 0 < N) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((1 / 2 : ℝ) * ∫ X, (particleTest n X : ℝ) ^ 2
        ∂SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N) ≤
      SharpLSI.var (SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N)
        (particleTest n) := by
  let P := SharpLSI.gibbs (fun _ => 0) (perturbedInteraction B β η) N
  have : IsProbabilityMeasure P := singular_gibbs_isProbabilityMeasure B hβ hη hN
  have ht := particleTest_support_probability_tendsto_zero B hβ hη hN
  have hev : ∀ᶠ n : ℕ in atTop,
      P {X | particleTest n X ≠ 0} < ENNReal.ofReal (1 / 2 : ℝ) :=
    ht.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hev] with n hn
  have hf : MemLp (particleTest n) 2 P := by
    refine MemLp.of_bound (particleTest_measurable n).aestronglyMeasurable ((N : ℝ) ^ 2 / 2) ?_
    exact Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (particleTest_nonneg n X)]
      exact particleTest_le n X
  apply variance_half_secondMoment_of_support_small (A := {X | particleTest n X ≠ 0}) hf
    (((measurableSet_singleton (0 : ℝ)).preimage (particleTest_measurable n)).compl)
    (fun X hx => by simpa using hx)
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 / 2 : ℝ) ≠ ∞) hn.le
  change (P {X | particleTest n X ≠ 0}).toReal ≤ (1 / 2 : ℝ)
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hreal

end

end DGPS.SingularCounterexample
