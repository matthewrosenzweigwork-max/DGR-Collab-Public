import LeanResearch.PeriodicAttractiveLogGas.CellGridFourierCoercivity
import LeanResearch.PeriodicAttractiveLogGas.OccupationCentralRates
import LeanResearch.PeriodicAttractiveLogGas.OccupationAbsoluteMass

/-! Near-uniform imbalance of the actual outer occupation rates, source
lines 1987--2005. The development record distinguishes source construction,
serialized diagnostics, integration and independent review. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PeriodicAttractiveLogGas.OccupationNearImbalance
open MeshCells MeshAdjacentCells LabelOccupations LabelRatioTransport
  DiscreteOccupationIdentities ConditionalLawEstimates OccupationNearContraction
  OccupationChemicalCoercivity OccupationCentralRates OccupationReverseRates
  OccupationDrift OccupationCoordinates LabelGroundState

theorem exp_half_separation_lower {d : ℝ} (hd : |d| ≤ 1) :
    |d| / 4 ≤ |1 - Real.exp (-d / 2)| := by
  by_cases hp : 0 ≤ d
  · have he : Real.exp (-d / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hl : 1 / 2 ≤ Real.exp (-d / 2) := by
      have hh := Real.add_one_le_exp (-d / 2)
      have := (abs_le.mp hd).2
      linarith
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (d / 2))
      (Real.exp_pos (-d / 2)).le
    have hz : Real.exp (d / 2) * Real.exp (-d / 2) = 1 := by
      rw [← Real.exp_add, show d / 2 + -d / 2 = 0 by ring, Real.exp_zero]
    rw [hz] at hh
    rw [abs_of_nonneg hp, abs_of_nonneg (sub_nonneg.mpr he)]
    nlinarith
  · have hn : d ≤ 0 := le_of_not_ge hp
    have he : 1 ≤ Real.exp (-d / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hh := Real.add_one_le_exp (-d / 2)
    rw [abs_of_nonpos hn, abs_of_nonpos (sub_nonpos.mpr he)]
    linarith

theorem exp_half_separation_upper {d : ℝ} (hd : |d| ≤ 1) :
    |1 - Real.exp (-d / 2)| ≤ |d| := by
  have hx : |-d / 2| ≤ 1 := by rw [abs_div, abs_neg]; norm_num; linarith
  have hh := Real.abs_exp_sub_one_le hx
  rw [abs_sub_comm, abs_div, abs_neg] at hh
  norm_num at hh
  linarith

theorem sqrt_exp_ratio {u v d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : v = u * Real.exp (-d)) :
    Real.sqrt v = Real.sqrt u * Real.exp (-d / 2) := by
  have he : Real.exp (-d / 2) ^ 2 = Real.exp (-d) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_eq_sq₀ (Real.sqrt_nonneg v) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hv, he, h]

theorem true_reverse_root_lower {u v d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : v = u * Real.exp (-d)) (hd : |d| ≤ 1) :
    u / 16 * d ^ 2 ≤ (Real.sqrt u - Real.sqrt v) ^ 2 := by
  have hh := (sq_le_sq₀ (by positivity : 0 ≤ |d| / 4)
    (abs_nonneg (1 - Real.exp (-d / 2)))).mpr (exp_half_separation_lower hd)
  have hp := mul_le_mul_of_nonneg_left hh hu
  rw [sqrt_exp_ratio hu hv h]
  have he : (Real.sqrt u - Real.sqrt u * Real.exp (-d / 2)) ^ 2 =
      u * (1 - Real.exp (-d / 2)) ^ 2 := by
    calc
      _ = Real.sqrt u ^ 2 * (1 - Real.exp (-d / 2)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hu]
  rw [he]
  calc
    _ = u * (d ^ 2 / 4 ^ 2) := by ring
    _ ≤ _ := by simpa only [div_pow, sq_abs] using hp

theorem true_reverse_root_upper {u v d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : v = u * Real.exp (-d)) (hd : |d| ≤ 1) :
    (Real.sqrt u - Real.sqrt v) ^ 2 ≤ u * d ^ 2 := by
  have hh := (sq_le_sq₀ (abs_nonneg (1 - Real.exp (-d / 2)))
    (abs_nonneg d)).mpr (exp_half_separation_upper hd)
  have hp := mul_le_mul_of_nonneg_left hh hu
  rw [sqrt_exp_ratio hu hv h]
  have he : (Real.sqrt u - Real.sqrt u * Real.exp (-d / 2)) ^ 2 =
      u * (1 - Real.exp (-d / 2)) ^ 2 := by
    calc
      _ = Real.sqrt u ^ 2 * (1 - Real.exp (-d / 2)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hu]
  rw [he]
  simpa only [sq_abs] using hp

/-- A genuine lower rate scale turns an additive rate error into the
required squared square-root error. -/
theorem root_perturbation_sq_le {u v κ E : ℝ} (hκ : 0 < κ) (hu : κ ≤ u)
    (hv : 0 ≤ v) (hE : 0 ≤ E) (he : |u - v| ≤ E) :
    (Real.sqrt u - Real.sqrt v) ^ 2 ≤ E ^ 2 / κ := by
  have hu0 := hκ.le.trans hu
  have hsu := Real.sq_sqrt hu0
  have hsv := Real.sq_sqrt hv
  have hs : κ ≤ (Real.sqrt u + Real.sqrt v) ^ 2 := by
    nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v]
  have hh := (sq_le_sq₀ (abs_nonneg (u - v)) hE).mpr he
  rw [sq_abs] at hh
  apply (le_div_iff₀ hκ).mpr
  calc
    _ ≤ (Real.sqrt u - Real.sqrt v) ^ 2 * (Real.sqrt u + Real.sqrt v) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (Real.sqrt u ^ 2 - Real.sqrt v ^ 2) ^ 2 := by ring
    _ = (u - v) ^ 2 := by rw [hsu, hsv]
    _ ≤ _ := hh

theorem square_difference_lower (x y : ℝ) : x ^ 2 / 2 - (x - y) ^ 2 ≤ y ^ 2 := by
  nlinarith only [sq_nonneg (x - 2 * y)]

theorem square_difference_upper (x y : ℝ) : y ^ 2 ≤ 2 * x ^ 2 + 2 * (x - y) ^ 2 := by
  nlinarith only [sq_nonneg (2 * x - y)]

theorem log_near_one_bound {x ρ : ℝ} (hρ : 0 ≤ ρ) (hsmall : ρ ≤ 1 / 2)
    (hx : |x - 1| ≤ ρ) : |Real.log x| ≤ 2 * ρ := by
  have hh := logRemainder_bound hρ hsmall hx
  have he : (x - 1) - logRemainder (x - 1) = Real.log x := by
    unfold logRemainder
    rw [show 1 + (x - 1) = x by ring]
    ring
  rw [← he]
  have ht := abs_sub (x - 1) (logRemainder (x - 1))
  nlinarith [abs_nonneg (x - 1)]

def chemicalDifferenceConstant (β₀ : ℝ) : ℝ :=
  4 + (8 / 3 : ℝ) * potentialDifferenceConstant β₀

theorem chemicalDifferenceConstant_pos (β₀ : ℝ) : 0 < chemicalDifferenceConstant β₀ := by
  have := potentialDifferenceConstant_nonneg β₀
  unfold chemicalDifferenceConstant
  positivity

def nearNeighborhood (β₀ : ℝ) : ℝ :=
  min (OccupationChemicalCoercivity.neighborhood β₀) (1 / (4 * chemicalDifferenceConstant β₀))

theorem nearNeighborhood_pos {β₀ : ℝ} (hsub : β₀ < 4) : 0 < nearNeighborhood β₀ :=
  lt_min (neighborhood_pos hsub) (by have := chemicalDifferenceConstant_pos β₀; positivity)

theorem fixedPoint_chemical_difference_bound {J : ℕ} (hJ : 0 < J)
    {θ : MeshIndex J → ℝ} {β β₀ : ℝ} (h : NearParameters θ β β₀)
    (hnear : profileDeviation θ ≤ OccupationChemicalCoercivity.neighborhood β₀)
    (a b : MeshIndex J) :
    |coefficient hJ θ β (nearFixedPoint hJ h).val a -
      coefficient hJ θ β (nearFixedPoint hJ h).val b| ≤
        chemicalDifferenceConstant β₀ * profileDeviation θ := by
  let f := (nearFixedPoint hJ h).val
  let ρ := profileDeviation θ
  have hρ : 0 ≤ ρ := profileDeviation_nonneg θ
  have hsmall : ρ ≤ 1 / 2 := (hnear.trans (min_le_left _ _)).trans (by norm_num)
  have hJp : (0 : ℝ) < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast hJ) 2
  have hθ (c : MeshIndex J) := profile_positive hJ hnear c
  have hl (c : MeshIndex J) : |Real.log ((J : ℝ) ^ 2 * θ c)| ≤ 2 * ρ :=
    log_near_one_bound hρ hsmall (profileDeviation_apply_le θ c)
  have hm : |Real.log (θ a) - Real.log (θ b)| ≤ 4 * ρ := by
    have ha := Real.log_mul hJp.ne' (hθ a).ne'
    have hb := Real.log_mul hJp.ne' (hθ b).ne'
    have he : Real.log (θ a) - Real.log (θ b) =
        Real.log ((J : ℝ) ^ 2 * θ a) - Real.log ((J : ℝ) ^ 2 * θ b) := by
      linarith only [ha, hb]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hl a) (hl b)).trans_eq (by ring))
  have hz : cellIntegral hJ (scaledPotential β oneL4) b /
      cellIntegral hJ (scaledPotential β oneL4) a = 1 := by
    rw [← cellNormalizer_ratio_eq_haar hJ (continuous_scaledPotential β oneL4)]
    simp only [scaledPotential_one, OccupationNearContraction.cellNormalizer, Real.exp_zero, integral_const,
      probReal_univ, one_smul, div_self (by norm_num : (1 : ℝ) ≠ 0)]
  have hi := cellIntegral_log_ratio_difference hJ h.beta_nonneg h.beta_le f oneL4 a b
  rw [hz, Real.log_one, sub_zero] at hi
  have hn := nearFixedPoint_L4_bound hJ h
  have hi' := hi.trans (mul_le_mul_of_nonneg_left hn
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (potentialDifferenceConstant_nonneg β₀)))
  have he : coefficient hJ θ β f a - coefficient hJ θ β f b =
      (Real.log (θ a) - Real.log (θ b)) +
        Real.log (cellIntegral hJ (scaledPotential β f) b / cellIntegral hJ (scaledPotential β f) a) := by
    rw [coefficient, coefficient,
      Real.log_div (hθ a).ne' (cellIntegral_pos hJ (continuous_scaledPotential β f) a).ne',
      Real.log_div (hθ b).ne' (cellIntegral_pos hJ (continuous_scaledPotential β f) b).ne',
      Real.log_div (cellIntegral_pos hJ (continuous_scaledPotential β f) b).ne'
        (cellIntegral_pos hJ (continuous_scaledPotential β f) a).ne']
    ring
  change |coefficient hJ θ β f a - coefficient hJ θ β f b| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hm hi').trans_eq (by
    unfold chemicalDifferenceConstant
    ring))

def stateProfile {J N : ℕ} {t : ℝ} (m : OccupationState J N t) : MeshIndex J → ℝ :=
  occupationProfile (labelOfState m).val

theorem stateProfile_apply {J N : ℕ} {t : ℝ} (m : OccupationState J N t) (a : MeshIndex J) :
    stateProfile m a = (m.val a : ℝ) / N := by
  simp only [stateProfile, occupationProfile, labelOfState, OccupationProbability.occupation_labelOfProfile]

theorem stateProfile_nonneg {J N : ℕ} {t : ℝ} (m : OccupationState J N t) (a : MeshIndex J) :
    0 ≤ stateProfile m a := occupationProfile_nonneg (labelOfState m).val a

theorem stateProfile_mass {J N : ℕ} {t : ℝ} (hN : 0 < N) (m : OccupationState J N t) :
    ∑ a, stateProfile m a = 1 := occupationProfile_mass hN (labelOfState m).val

theorem stateParameters {J N : ℕ} {t β β₀ : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hnearJ : nearMeshThreshold β₀ ≤ J)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8) :
    NearParameters (stateProfile m) β β₀ :=
  nearProfileParameters hβ hβ₀ hnearJ (stateProfile_nonneg m) (stateProfile_mass (by omega) m) hnear

def stateFixedPoint {J N : ℕ} {t β β₀ : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hnearJ : nearMeshThreshold β₀ ≤ J)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8) : L4 :=
  (nearFixedPoint hJ (stateParameters hN hβ hβ₀ hnearJ m hnear)).val

theorem near_count_lower {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8)
    (a : MeshIndex J) : (N : ℝ) / (2 * (J : ℝ) ^ 2) ≤ (m.val a : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJr : (0 : ℝ) < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast hJ) 2
  have hh := (abs_le.mp ((profileDeviation_apply_le (stateProfile m) a).trans hnear)).1
  rw [stateProfile_apply] at hh
  have hl : (1 / 2 : ℝ) ≤ (J : ℝ) ^ 2 * ((m.val a : ℝ) / N) := by linarith
  have hp := mul_le_mul_of_nonneg_right hl hNr.le
  have he : (J : ℝ) ^ 2 * ((m.val a : ℝ) / N) * N = (J : ℝ) ^ 2 * m.val a := by
    field_simp
  rw [he] at hp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (J : ℝ) ^ 2)).mpr
  linarith

theorem near_count_positive {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8)
    (a : MeshIndex J) : 1 ≤ m.val a := by
  have hp := near_count_lower hJ hN m hnear a
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJr : (0 : ℝ) < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast hJ) 2
  have hh : (0 : ℝ) < m.val a := (div_pos hNr (by positivity)).trans_le hp
  exact Nat.succ_le_of_lt (by exact_mod_cast hh)

/-- Transfer of the proved original-label Q estimate to a true occupation
move; the selected label has exactly the given occupation, without a
multinomial factor inside Q. -/
theorem state_Q_log_ratio {J N : ℕ} {t β β₀ : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hnearN : nearParticleThreshold J β₀ ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8)
    {m' : OccupationState J N t} {a b : MeshIndex J}
    (hm : PermittedMove (mesh_pos hmesh) m m' a b) :
    |Real.log (qWeight (mesh_pos hmesh) β m' / qWeight (mesh_pos hmesh) β m) -
      Real.log (cellIntegral (mesh_pos hmesh)
        (scaledPotential β (stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear)) b /
        cellIntegral (mesh_pos hmesh)
          (scaledPotential β (stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear)) a)| ≤
      nearRateConstant J β₀ / Real.sqrt (N : ℝ) := by
  cases N with
  | zero => omega
  | succ n =>
    have hocc : occupation (labelOfState m).val = m.val :=
      congrArg Subtype.val (profile_labelOfState m)
    have ha : 1 ≤ occupation (labelOfState m).val a := by rw [hocc]; exact hm.2.1
    have hh := actual_near_Q_log_ratio hβ hβ₀ hsub htC hmesh (labelOfState m).val
      (labelOfState m).property hnearJ hnearN hnear a b ha
    change |Real.log _ - Real.log (cellIntegral (mesh_pos hmesh)
        (scaledPotential β (stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear)) b /
        cellIntegral (mesh_pos hmesh)
          (scaledPotential β (stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear)) a)| ≤ _ at hh
    rw [hocc, hm.2.2] at hh
    have hC : OccupationPartitionTransport.logarithmicRatioConstant J β₀ +
        (8 / 3 : ℝ) * potentialDifferenceConstant β₀ *
          OccupationFieldApproximation.approximationConstant J β₀ ≤ nearRateConstant J β₀ := by
      unfold nearRateConstant
      have := approximationConstant_nonneg J (hβ.trans hβ₀)
      linarith
    simpa only [qWeight, Nat.cast_add, Nat.cast_one] using!
      hh.trans (div_le_div_of_nonneg_right hC (Real.sqrt_nonneg ((n : ℝ) + 1)))

def logIncrement {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m m' : OccupationState J N t) : ℝ :=
  Real.log (occupationWeight hJ β m') - Real.log (occupationWeight hJ β m)

def logErrorConstant (J : ℕ) (β₀ : ℝ) : ℝ := nearRateConstant J β₀ + 2 * (J : ℝ) ^ 2

theorem logErrorConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ logErrorConstant J β₀ := by
  unfold logErrorConstant
  exact add_nonneg (nearRateConstant_nonneg J hβ₀) (by positivity)

theorem chemical_difference_count_identity {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hN : 2 ≤ N) (m : OccupationState J N t)
    (hnear : profileDeviation (stateProfile m) ≤ 1 / 8) (f : L4) (a b : MeshIndex J) :
    coefficient hJ (stateProfile m) β f a - coefficient hJ (stateProfile m) β f b =
      Real.log ((m.val a : ℝ) / m.val b) +
        Real.log (cellIntegral hJ (scaledPotential β f) b / cellIntegral hJ (scaledPotential β f) a) := by
  have ha : (0 : ℝ) < m.val a := by
    have := near_count_positive hJ hN m hnear a
    exact_mod_cast (show 0 < m.val a by omega)
  have hb : (0 : ℝ) < m.val b := by
    have := near_count_positive hJ hN m hnear b
    exact_mod_cast (show 0 < m.val b by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hIa := cellIntegral_pos hJ (continuous_scaledPotential β f) a
  have hIb := cellIntegral_pos hJ (continuous_scaledPotential β f) b
  rw [coefficient, coefficient, stateProfile_apply, stateProfile_apply,
    Real.log_div (div_pos ha hn).ne' hIa.ne', Real.log_div (div_pos hb hn).ne' hIb.ne',
    Real.log_div ha.ne' hn.ne', Real.log_div hb.ne' hn.ne',
    Real.log_div ha.ne' hb.ne', Real.log_div hIb.ne' hIa.ne']
  ring

theorem actual_log_increment_error {J N : ℕ} {t β β₀ : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hnearN : nearParticleThreshold J β₀ ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8)
    {m' : OccupationState J N t} {a b : MeshIndex J}
    (hm : PermittedMove (mesh_pos hmesh) m m' a b) :
    |logIncrement (mesh_pos hmesh) β m m' -
      (coefficient (mesh_pos hmesh) (stateProfile m) β
          (stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear) a -
        coefficient (mesh_pos hmesh) (stateProfile m) β
          (stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear) b)| ≤
      logErrorConstant J β₀ / Real.sqrt (N : ℝ) := by
  let f := stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m hnear
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJr : (0 : ℝ) < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast mesh_pos hmesh) 2
  have hb := near_count_lower (mesh_pos hmesh) hN m hnear b
  have hp := abs_log_sub_le_of_unit (div_pos hNr (by positivity : (0 : ℝ) < 2 * (J : ℝ) ^ 2))
    (show (N : ℝ) / (2 * (J : ℝ) ^ 2) ≤ (m.val b : ℝ) + 1 by linarith)
    hb (show |((m.val b : ℝ) + 1) - m.val b| ≤ 1 by norm_num)
  have hκ : 1 / ((N : ℝ) / (2 * (J : ℝ) ^ 2)) = 2 * (J : ℝ) ^ 2 / N := by field_simp
  rw [hκ] at hp
  have ha : (0 : ℝ) < m.val a := by
    have := near_count_positive (mesh_pos hmesh) hN m hnear a
    exact_mod_cast (show 0 < m.val a by omega)
  have hb0 : (0 : ℝ) < m.val b := by
    have := near_count_positive (mesh_pos hmesh) hN m hnear b
    exact_mod_cast (show 0 < m.val b by omega)
  have hq := state_Q_log_ratio hN hβ hβ₀ hsub htC hmesh hnearJ hnearN m hnear hm
  have he : logIncrement (mesh_pos hmesh) β m m' -
      (coefficient (mesh_pos hmesh) (stateProfile m) β f a -
        coefficient (mesh_pos hmesh) (stateProfile m) β f b) =
      -(Real.log ((m.val b : ℝ) + 1) - Real.log (m.val b : ℝ)) +
        (Real.log (qWeight (mesh_pos hmesh) β m' / qWeight (mesh_pos hmesh) β m) -
          Real.log (cellIntegral (mesh_pos hmesh) (scaledPotential β f) b /
            cellIntegral (mesh_pos hmesh) (scaledPotential β f) a)) := by
    rw [logIncrement, occupation_log_increment (mesh_pos hmesh) (mesh_two_le hmesh) hN hβ
      (hβ₀.trans_lt hsub) hm, chemical_difference_count_identity (mesh_pos hmesh) hN m hnear f a b,
      Real.log_div ha.ne' (show (m.val b : ℝ) + 1 ≠ 0 by positivity), Real.log_div ha.ne' hb0.ne']
    ring
  change |logIncrement (mesh_pos hmesh) β m m' -
      (coefficient (mesh_pos hmesh) (stateProfile m) β f a -
        coefficient (mesh_pos hmesh) (stateProfile m) β f b)| ≤ _
  rw [he]
  have hs : Real.sqrt (N : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith [Real.sq_sqrt hNr.le, Real.sqrt_nonneg (N : ℝ)]
  calc
    _ ≤ |Real.log ((m.val b : ℝ) + 1) - Real.log (m.val b : ℝ)| +
        |Real.log (qWeight (mesh_pos hmesh) β m' / qWeight (mesh_pos hmesh) β m) -
          Real.log (cellIntegral (mesh_pos hmesh) (scaledPotential β f) b /
            cellIntegral (mesh_pos hmesh) (scaledPotential β f) a)| := by
      simpa only [abs_neg] using abs_add_le
        (-(Real.log ((m.val b : ℝ) + 1) - Real.log (m.val b : ℝ))) _
    _ ≤ 2 * (J : ℝ) ^ 2 / N + nearRateConstant J β₀ / Real.sqrt (N : ℝ) := add_le_add hp hq
    _ ≤ 2 * (J : ℝ) ^ 2 / Real.sqrt (N : ℝ) + nearRateConstant J β₀ / Real.sqrt (N : ℝ) :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hNr) hs) le_rfl
    _ = _ := by unfold logErrorConstant; ring

def rateScale (J : ℕ) (β₀ : ℝ) : ℝ := lowerBound β₀ / (4 * (J : ℝ) ^ 2)

theorem rateScale_pos {J : ℕ} (hJ : 0 < J) (β₀ : ℝ) : 0 < rateScale J β₀ := by
  unfold rateScale
  exact div_pos (lowerBound_pos β₀) (by
    have : (0 : ℝ) < J := by exact_mod_cast hJ
    positivity)

def reverseError (J : ℕ) (β₀ : ℝ) : ℝ :=
  1 + OccupationSecondDifferences.secondDifferenceConstant J β₀ / 4

theorem reverseError_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) : 0 ≤ reverseError J β₀ := by
  have := OccupationSecondDifferences.secondDifferenceConstant_nonneg J hβ₀
  unfold reverseError
  positivity

/-- One threshold for the original Q approximation, the original reverse-rate
comparison, the move margin, the small log odds and the rounded center. -/
def particleThreshold (J : ℕ) (β₀ t : ℝ) : ℕ :=
  max (nearParticleThreshold J β₀)
    (max (OccupationSecondDifferences.secondDifferenceThreshold J β₀)
      (max (8 * J ^ 2) ⌈max (4 / t)
        (max ((4 * logErrorConstant J β₀) ^ 2) ((J : ℝ) ^ 2 / nearNeighborhood β₀))⌉₊))

theorem particleThreshold_bounds {J N : ℕ} {β₀ t : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (hlarge : particleThreshold J β₀ t ≤ N) :
    nearParticleThreshold J β₀ ≤ N ∧
      OccupationSecondDifferences.secondDifferenceThreshold J β₀ ≤ N ∧
      8 * J ^ 2 ≤ N ∧ 2 ≤ N ∧ 4 ≤ t * N ∧
      logErrorConstant J β₀ / Real.sqrt (N : ℝ) ≤ 1 / 4 ∧
      (J : ℝ) ^ 2 / N ≤ nearNeighborhood β₀ := by
  have hn : nearParticleThreshold J β₀ ≤ N := (le_max_left _ _).trans hlarge
  have hr := (le_max_right _ _).trans hlarge
  have hs : OccupationSecondDifferences.secondDifferenceThreshold J β₀ ≤ N := (le_max_left _ _).trans hr
  have hr' := (le_max_right _ _).trans hr
  have h8 : 8 * J ^ 2 ≤ N := (le_max_left _ _).trans hr'
  have hmax : max (4 / t)
      (max ((4 * logErrorConstant J β₀) ^ 2) ((J : ℝ) ^ 2 / nearNeighborhood β₀)) ≤ (N : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hr')
  have hN := (nearParticleThreshold_bounds hn).2.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : 4 / t ≤ (N : ℝ) := (le_max_left _ _).trans hmax
  have hsq : (4 * logErrorConstant J β₀) ^ 2 ≤ (N : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have he : (J : ℝ) ^ 2 / nearNeighborhood β₀ ≤ (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmax)
  refine ⟨hn, hs, h8, hN, ?_, ?_, ?_⟩
  · have hh := (div_le_iff₀ ht).mp hm
    nlinarith only [hh]
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).mpr
    have hD := logErrorConstant_nonneg J hβ₀
    nlinarith [Real.sq_sqrt hNr.le, Real.sqrt_nonneg (N : ℝ)]
  · apply (div_le_iff₀ hNr).mpr
    have hh := (div_le_iff₀ (nearNeighborhood_pos hsub)).mp he
    nlinarith only [hh]

theorem nearNeighborhood_le_eighth (β₀ : ℝ) : nearNeighborhood β₀ ≤ 1 / 8 :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- Detailed balance is used with the literal occupation probability, so the
exponent is the full log increment, including the multinomial correction. -/
theorem actual_true_reverse {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (hm : PermittedMove hJ m m' a b) :
    occupationRate hJ β m' m = occupationRate hJ β m m' * Real.exp (-logIncrement hJ β m m') := by
  have hp := occupationWeight_pos hJ hN hβ hsub m
  have hp' := occupationWeight_pos hJ hN hβ hsub m'
  have he : Real.exp (-logIncrement hJ β m m') = occupationWeight hJ β m / occupationWeight hJ β m' := by
    rw [logIncrement, neg_sub, Real.exp_sub, Real.exp_log hp, Real.exp_log hp']
  rw [he]
  have hh := occupation_detailed_balance_of_move hJ hJ2 β hm
  calc
    _ = (occupationWeight hJ β m * occupationRate hJ β m m') / occupationWeight hJ β m' := by
      apply (eq_div_iff hp'.ne').mpr
      simpa only [mul_comm] using hh.symm
    _ = _ := by ring

theorem actual_log_increment_small {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ nearNeighborhood β₀)
    {m' : OccupationState J N t} {a b : MeshIndex J}
    (hm : PermittedMove (mesh_pos hmesh) m m' a b) :
    |logIncrement (mesh_pos hmesh) β m m'| ≤ 1 := by
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have h8 := hnear.trans (nearNeighborhood_le_eighth β₀)
  let f := stateFixedPoint (mesh_pos hmesh) hb.2.2.2.1 hβ hβ₀ hnearJ m h8
  let c := coefficient (mesh_pos hmesh) (stateProfile m) β f a -
    coefficient (mesh_pos hmesh) (stateProfile m) β f b
  have he : |logIncrement (mesh_pos hmesh) β m m' - c| ≤ 1 / 4 :=
    (actual_log_increment_error hb.2.2.2.1 hβ hβ₀ hsub htC hmesh hnearJ hb.1 m h8 hm).trans hb.2.2.2.2.2.1
  have hc : |c| ≤ chemicalDifferenceConstant β₀ * profileDeviation (stateProfile m) :=
    fixedPoint_chemical_difference_bound (mesh_pos hmesh)
      (stateParameters hb.2.2.2.1 hβ hβ₀ hnearJ m h8) (hnear.trans (min_le_left _ _)) a b
  have hH := chemicalDifferenceConstant_pos β₀
  have hρ : profileDeviation (stateProfile m) ≤ 1 / (4 * chemicalDifferenceConstant β₀) :=
    hnear.trans (min_le_right _ _)
  have hc' : |c| ≤ 1 / 4 := hc.trans ((mul_le_mul_of_nonneg_left hρ hH.le).trans_eq (by field_simp))
  have ha := abs_add_le (logIncrement (mesh_pos hmesh) β m m' - c) c
  rw [sub_add_cancel] at ha
  linarith only [ha, he, hc']

/-- Scalar assembly of the source two square-root comparisons. All its
inputs are discharged for the actual outer rates below. -/
theorem root_log_error_lower {u v w d c κ E D n : ℝ}
    (hκ : 0 < κ) (hn : 1 ≤ n) (hu : κ * n ≤ u) (hw : κ * n ≤ w)
    (hv : 0 ≤ v) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hr : v = u * Real.exp (-d)) (hd : |d| ≤ 1)
    (he : |v - w| ≤ E) (hc : |d - c| ≤ D / Real.sqrt n) :
    κ * n / 64 * c ^ 2 - (κ * D ^ 2 / 32 + E ^ 2 / κ) ≤
      (Real.sqrt u - Real.sqrt w) ^ 2 := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hκn := mul_pos hκ hn0
  have hu0 : 0 ≤ u := hκn.le.trans hu
  have hp := true_reverse_root_lower hu0 hv hr hd
  have hp' : κ * n / 16 * d ^ 2 ≤ (Real.sqrt u - Real.sqrt v) ^ 2 :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hu (by norm_num)) (sq_nonneg d)).trans hp
  have hr' : (Real.sqrt w - Real.sqrt v) ^ 2 ≤ E ^ 2 / κ := by
    have hh := root_perturbation_sq_le hκn hw hv hE (by rwa [abs_sub_comm])
    exact hh.trans (div_le_div_of_nonneg_left (sq_nonneg E) hκ (by nlinarith only [hn, hκ]))
  have hsq : (d - c) ^ 2 ≤ D ^ 2 / n := by
    have hh := (sq_le_sq₀ (abs_nonneg (d - c)) (by positivity : 0 ≤ D / Real.sqrt n)).mpr hc
    simpa only [sq_abs, div_pow, Real.sq_sqrt hn0.le] using hh
  have hdc := square_difference_lower c d
  have hdc' : c ^ 2 / 2 - D ^ 2 / n ≤ d ^ 2 := by
    rw [show (c - d) ^ 2 = (d - c) ^ 2 by ring] at hdc
    linarith only [hdc, hsq]
  have hmul := mul_le_mul_of_nonneg_left hdc' (show 0 ≤ κ * n / 32 by positivity)
  have hid : κ * n / 32 * (c ^ 2 / 2 - D ^ 2 / n) = κ * n / 64 * c ^ 2 - κ * D ^ 2 / 32 := by
    field_simp
    ring
  rw [hid] at hmul
  have hs := square_difference_lower (Real.sqrt u - Real.sqrt v) (Real.sqrt u - Real.sqrt w)
  have hdif : (Real.sqrt u - Real.sqrt v) - (Real.sqrt u - Real.sqrt w) = Real.sqrt w - Real.sqrt v := by ring
  rw [hdif] at hs
  linarith only [hmul, hs, hr', hp']

theorem root_log_error_upper {u v w d κ E L n : ℝ}
    (hκ : 0 < κ) (hn : 1 ≤ n) (hu : 0 ≤ u) (hun : u ≤ n)
    (hw : κ * n ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hr : v = u * Real.exp (-d)) (hd : |d| ≤ 1)
    (he : |v - w| ≤ E) (hl : |d| ≤ L / Real.sqrt n) :
    (Real.sqrt u - Real.sqrt w) ^ 2 ≤ 2 * L ^ 2 + 2 * E ^ 2 / κ := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hsq : d ^ 2 ≤ L ^ 2 / n := by
    have hh := (sq_le_sq₀ (abs_nonneg d) (by positivity : 0 ≤ L / Real.sqrt n)).mpr hl
    simpa only [sq_abs, div_pow, Real.sq_sqrt hn0.le] using hh
  have hp := true_reverse_root_upper hu hv hr hd
  have hp' : (Real.sqrt u - Real.sqrt v) ^ 2 ≤ L ^ 2 := by
    calc
      _ ≤ u * d ^ 2 := hp
      _ ≤ n * (L ^ 2 / n) := mul_le_mul hun hsq (sq_nonneg d) hn0.le
      _ = L ^ 2 := by field_simp
  have hr' : (Real.sqrt w - Real.sqrt v) ^ 2 ≤ E ^ 2 / κ := by
    have hh := root_perturbation_sq_le (mul_pos hκ hn0) hw hv hE (by rwa [abs_sub_comm])
    exact hh.trans (div_le_div_of_nonneg_left (sq_nonneg E) hκ (by nlinarith only [hn, hκ]))
  have hs := square_difference_upper (Real.sqrt u - Real.sqrt v) (Real.sqrt u - Real.sqrt w)
  have hdif : (Real.sqrt u - Real.sqrt v) - (Real.sqrt u - Real.sqrt w) = Real.sqrt w - Real.sqrt v := by ring
  rw [hdif] at hs
  calc
    _ ≤ 2 * (Real.sqrt u - Real.sqrt v) ^ 2 + 2 * (Real.sqrt w - Real.sqrt v) ^ 2 := hs
    _ ≤ 2 * L ^ 2 + 2 * (E ^ 2 / κ) := by linarith only [hp', hr']
    _ = _ := by ring

/-- Uniform scale for each of the two genuine departures from a central
occupation. No lower estimate for an invented comparison chain is used. -/
theorem actual_direction_lower {J N : ℕ} {t β β₀ : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ 1 / 8)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) :
    rateScale J β₀ * N ≤ directionRate (mesh_pos hmesh) β m hm hmargin a b := by
  have ha := near_count_positive (mesh_pos hmesh) hN m hnear a
  rw [directionRate, dite_eq_left ha]
  have hp : PermittedMove (mesh_pos hmesh) m (movedState m hm hmargin a b ha) a b := ⟨hab, ha, rfl⟩
  have hh := central_rate_lower hN hβ hβ₀ hsub ht htC hmesh hp
    (by simpa only [Nat.cast_pow] using near_count_lower (mesh_pos hmesh) hN m hnear a)
  simpa only [rateScale, Nat.cast_pow] using hh

theorem actual_direction_upper {J N : ℕ} {t β : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
    (hmargin : 4 ≤ t * N) (a b : MeshIndex J) (hab : EdgeAdjacent J hJ a b) :
    directionRate hJ β m hm hmargin a b ≤ N := by
  by_cases ha : 1 ≤ m.val a
  · rw [directionRate, dite_eq_left ha]
    have hp : PermittedMove hJ m (movedState m hm hmargin a b ha) a b := ⟨hab, ha, rfl⟩
    exact (OccupationAbsoluteMass.occupationRate_le_source hJ hJ2 β hp).trans
      (by exact_mod_cast count_le_total m a)
  · rw [directionRate, dite_eq_right ha]
    exact Nat.cast_nonneg _

def edgeError (J : ℕ) (β₀ : ℝ) : ℝ :=
  rateScale J β₀ * logErrorConstant J β₀ ^ 2 / 32 + reverseError J β₀ ^ 2 / rateScale J β₀

/-- The single unordered-edge estimate for the original direction rates.
Every rate, log increment and comparison input is proved from source gates. -/
theorem actual_edge_imbalance_lower {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ nearNeighborhood β₀)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) :
    let hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
    let f := stateFixedPoint (mesh_pos hmesh) hb.2.2.2.1 hβ hβ₀ hnearJ m
      (hnear.trans (nearNeighborhood_le_eighth β₀))
    rateScale J β₀ * N / 64 *
        (coefficient (mesh_pos hmesh) (stateProfile m) β f a -
          coefficient (mesh_pos hmesh) (stateProfile m) β f b) ^ 2 - edgeError J β₀ ≤
      (Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin a b) -
        Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin b a)) ^ 2 := by
  dsimp only
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hN := hb.2.2.2.1
  have h8 := hnear.trans (nearNeighborhood_le_eighth β₀)
  have ha := near_count_positive (mesh_pos hmesh) hN m h8 a
  have hc := near_count_positive (mesh_pos hmesh) hN m h8 b
  let mp := movedState m hm hmargin a b ha
  have hp : PermittedMove (mesh_pos hmesh) m mp a b := ⟨hab, ha, rfl⟩
  have hu := actual_direction_lower hN hβ hβ₀ hsub ht htC hmesh m h8 hm hmargin a b hab
  have hw := actual_direction_lower hN hβ hβ₀ hsub ht htC hmesh m h8 hm hmargin b a hab.symm
  have he := reverse_rate_comparison hβ hβ₀ hsub ht htC hmesh hb.2.1 hmargin m hm a b hab ha hc
  have hl := actual_log_increment_error hN hβ hβ₀ hsub htC hmesh hnearJ hb.1 m h8 hp
  have hd := actual_log_increment_small hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hnear hp
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  simp only [directionRate, dite_eq_left ha, dite_eq_left hc] at hu hw ⊢
  exact root_log_error_lower (rateScale_pos (mesh_pos hmesh) β₀) hn hu hw
    (occupationRate_nonneg (mesh_pos hmesh) β mp m) (reverseError_nonneg J (hβ.trans hβ₀))
    (logErrorConstant_nonneg J (hβ.trans hβ₀))
    (actual_true_reverse (mesh_pos hmesh) (mesh_two_le hmesh) hN hβ (hβ₀.trans_lt hsub) hp)
    hd he hl

theorem unordered_mono {J : ℕ} (hJ : 0 < J) {F G : MeshIndex J → MeshIndex J → ℝ}
    (h : ∀ a b, EdgeAdjacent J hJ a b → F a b ≤ G a b) : unorderedSum hJ F ≤ unorderedSum hJ G := by
  classical
  unfold unorderedSum
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  split_ifs with he
  · exact h a b he.2
  · exact le_rfl

theorem unordered_affine {J : ℕ} (hJ : 0 < J) (F : MeshIndex J → MeshIndex J → ℝ) (A B : ℝ) :
    unorderedSum hJ (fun a b => A * F a b - B) =
      A * unorderedSum hJ F - B * unorderedSum hJ (fun _ _ => 1) := by
  classical
  unfold unorderedSum
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

def coercivityConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  rateScale J β₀ * GreenL2Coercivity.gap β₀ ^ 2 * (J : ℝ) ^ 2 / 16

def additiveConstant (J : ℕ) (β₀ : ℝ) : ℝ := 2 * (J : ℝ) ^ 2 * edgeError J β₀

theorem coercivityConstant_pos {J : ℕ} (hJ : 0 < J) {β₀ : ℝ} (hsub : β₀ < 4) :
    0 < coercivityConstant J β₀ := by
  have := rateScale_pos hJ β₀
  have := GreenL2Coercivity.gap_pos hsub
  have : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold coercivityConstant
  positivity

/-- The near-uniform part of source quadratic imbalance, for the literal
outer occupation rates and their original unordered cell graph. -/
theorem near_uniform_imbalance {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ nearNeighborhood β₀)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) :
    let hmargin := (particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge).2.2.2.2.1
    coercivityConstant J β₀ * N *
        (∑ a, (stateProfile m a - ((J : ℝ) ^ 2)⁻¹) ^ 2) - additiveConstant J β₀ ≤
      imbalance (mesh_pos hmesh) β m hm hmargin := by
  dsimp only
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  let hmargin := hb.2.2.2.2.1
  have h8 := hnear.trans (nearNeighborhood_le_eighth β₀)
  let f := stateFixedPoint (mesh_pos hmesh) hb.2.2.2.1 hβ hβ₀ hnearJ m h8
  let c := coefficient (mesh_pos hmesh) (stateProfile m) β f
  have he := unordered_mono (mesh_pos hmesh) (fun a b hab =>
    actual_edge_imbalance_lower hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hnear hm hmargin a b hab)
  change unorderedSum (mesh_pos hmesh) (fun a b => rateScale J β₀ * N / 64 * (c a - c b) ^ 2 - edgeError J β₀) ≤
    imbalance (mesh_pos hmesh) β m hm hmargin at he
  rw [unordered_affine, unordered_cell_edge_count (mesh_pos hmesh) (mesh_three_le hmesh)] at he
  have hg := CellGridFourierCoercivity.chemical_edge_coercivity (mesh_pos hmesh) (mesh_three_le hmesh)
    (stateParameters hb.2.2.2.1 hβ hβ₀ hnearJ m h8) (hnear.trans (min_le_left _ _)) hsub
  have hs : 0 ≤ rateScale J β₀ * N / 64 := by
    have := (rateScale_pos (mesh_pos hmesh) β₀).le
    positivity
  have hp := mul_le_mul_of_nonneg_left hg hs
  have hid : rateScale J β₀ * N / 64 *
      (4 * GreenL2Coercivity.gap β₀ ^ 2 * (J : ℝ) ^ 2 *
        (∑ a, (stateProfile m a - ((J : ℝ) ^ 2)⁻¹) ^ 2)) =
      coercivityConstant J β₀ * N * (∑ a, (stateProfile m a - ((J : ℝ) ^ 2)⁻¹) ^ 2) := by
    unfold coercivityConstant
    ring
  rw [hid] at hp
  change _ ≤ rateScale J β₀ * N / 64 * unorderedSum (mesh_pos hmesh) (fun a b => (c a - c b) ^ 2) at hp
  have hce : edgeError J β₀ * (2 * (J ^ 2 : ℕ)) = additiveConstant J β₀ := by
    simp only [Nat.cast_pow, additiveConstant]
    ring
  rw [hce] at he
  exact (sub_le_sub_right hp (additiveConstant J β₀)).trans he

/-- Rounding error in the literal probability profile, without a chosen
representative of the occupation fiber. -/
theorem rounded_profile_error {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 0 < N)
    (m : OccupationState J N t) (hround : m.val = rounded J N) (a : MeshIndex J) :
    |stateProfile m a - ((J : ℝ) ^ 2)⁻¹| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hh := rounded_close hJ N a
  simp only [Nat.cast_pow] at hh
  rw [stateProfile_apply, hround]
  have he : (rounded J N a : ℝ) / N - ((J : ℝ) ^ 2)⁻¹ =
      ((rounded J N a : ℝ) - (N : ℝ) / (J : ℝ) ^ 2) / N := by
    field_simp
  rw [he, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right hh hNr.le

theorem rounded_profile_deviation_le {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 0 < N)
    (m : OccupationState J N t) (hround : m.val = rounded J N) :
    profileDeviation (stateProfile m) ≤ (J : ℝ) ^ 2 / N := by
  unfold profileDeviation
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  rw [Real.norm_eq_abs]
  have hJr : (J : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hJ.ne')
  have he : (J : ℝ) ^ 2 * stateProfile m a - 1 =
      (J : ℝ) ^ 2 * (stateProfile m a - ((J : ℝ) ^ 2)⁻¹) := by
    field_simp
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (rounded_profile_error hJ hN m hround a) (sq_nonneg _)).trans_eq (by ring)

/-- The rounded center is in the actual inner cap by the proved rounding
construction. The smallness gate is precisely the source cell-size gate. -/
theorem rounded_inner {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hcounts : 8 * J ^ 2 ≤ N)
    (hsmall : 1 / (J ^ 2 : ℕ) < t / 8)
    (m : OccupationState J N t) (hround : m.val = rounded J N) :
    m.val ∈ cappedOccupations J N (3 * t / 4) := by
  rw [hround]
  refine ⟨rounded_sum hJ N, fun a => ?_⟩
  have hh := (rounded_capped hJ hcounts hsmall).2 a
  have hz : (0 : ℝ) ≤ rounded J N a := Nat.cast_nonneg _
  nlinarith only [hh, hz]

def roundedLogConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  chemicalDifferenceConstant β₀ * (J : ℝ) ^ 2 + logErrorConstant J β₀

theorem roundedLogConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ roundedLogConstant J β₀ := by
  unfold roundedLogConstant
  exact add_nonneg (mul_nonneg (chemicalDifferenceConstant_pos β₀).le (sq_nonneg _))
    (logErrorConstant_nonneg J hβ₀)

theorem actual_log_increment_rounded {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hround : m.val = rounded J N)
    {m' : OccupationState J N t} {a b : MeshIndex J}
    (hm : PermittedMove (mesh_pos hmesh) m m' a b) :
    |logIncrement (mesh_pos hmesh) β m m'| ≤ roundedLogConstant J β₀ / Real.sqrt (N : ℝ) := by
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hN := hb.2.2.2.1
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hρ := rounded_profile_deviation_le (mesh_pos hmesh) hN0 m hround
  have hnear := hρ.trans hb.2.2.2.2.2.2
  have h8 := hnear.trans (nearNeighborhood_le_eighth β₀)
  let f := stateFixedPoint (mesh_pos hmesh) hN hβ hβ₀ hnearJ m h8
  let c := coefficient (mesh_pos hmesh) (stateProfile m) β f a -
    coefficient (mesh_pos hmesh) (stateProfile m) β f b
  have he : |logIncrement (mesh_pos hmesh) β m m' - c| ≤ logErrorConstant J β₀ / Real.sqrt (N : ℝ) :=
    actual_log_increment_error hN hβ hβ₀ hsub htC hmesh hnearJ hb.1 m h8 hm
  have hc : |c| ≤ chemicalDifferenceConstant β₀ * profileDeviation (stateProfile m) :=
    fixedPoint_chemical_difference_bound (mesh_pos hmesh)
      (stateParameters hN hβ hβ₀ hnearJ m h8) (hnear.trans (min_le_left _ _)) a b
  have hs : Real.sqrt (N : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith [Real.sq_sqrt hNr.le, Real.sqrt_nonneg (N : ℝ)]
  have hc' : |c| ≤ chemicalDifferenceConstant β₀ * (J : ℝ) ^ 2 / Real.sqrt (N : ℝ) := by
    calc
      _ ≤ chemicalDifferenceConstant β₀ * ((J : ℝ) ^ 2 / N) :=
        hc.trans (mul_le_mul_of_nonneg_left hρ (chemicalDifferenceConstant_pos β₀).le)
      _ = (chemicalDifferenceConstant β₀ * (J : ℝ) ^ 2) / N := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by have := (chemicalDifferenceConstant_pos β₀).le; positivity)
        (Real.sqrt_pos.mpr hNr) hs
  have ha := abs_add_le (logIncrement (mesh_pos hmesh) β m m' - c) c
  rw [sub_add_cancel] at ha
  exact ha.trans ((add_le_add he hc').trans_eq (by unfold roundedLogConstant; ring))

def roundedConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  4 * (J : ℝ) ^ 2 * (roundedLogConstant J β₀ ^ 2 + reverseError J β₀ ^ 2 / rateScale J β₀)

theorem roundedConstant_nonneg {J : ℕ} (hJ : 0 < J) (β₀ : ℝ) : 0 ≤ roundedConstant J β₀ := by
  have := (rateScale_pos hJ β₀).le
  unfold roundedConstant
  positivity

theorem actual_edge_rounded_upper {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hround : m.val = rounded J N)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) :
    (Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin a b) -
      Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin b a)) ^ 2 ≤
        2 * roundedLogConstant J β₀ ^ 2 + 2 * reverseError J β₀ ^ 2 / rateScale J β₀ := by
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hN := hb.2.2.2.1
  have hnear := (rounded_profile_deviation_le (mesh_pos hmesh) (by omega) m hround).trans hb.2.2.2.2.2.2
  have h8 := hnear.trans (nearNeighborhood_le_eighth β₀)
  have ha := near_count_positive (mesh_pos hmesh) hN m h8 a
  have hc := near_count_positive (mesh_pos hmesh) hN m h8 b
  let mp := movedState m hm hmargin a b ha
  have hp : PermittedMove (mesh_pos hmesh) m mp a b := ⟨hab, ha, rfl⟩
  have hu := actual_direction_upper (β := β) (mesh_pos hmesh) (mesh_two_le hmesh) m hm hmargin a b hab
  have hw := actual_direction_lower hN hβ hβ₀ hsub ht htC hmesh m h8 hm hmargin b a hab.symm
  have he := reverse_rate_comparison hβ hβ₀ hsub ht htC hmesh hb.2.1 hmargin m hm a b hab ha hc
  have hl := actual_log_increment_rounded hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hround hp
  have hd := actual_log_increment_small hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hnear hp
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  simp only [directionRate, dite_eq_left ha, dite_eq_left hc] at hu hw ⊢
  exact root_log_error_upper (rateScale_pos (mesh_pos hmesh) β₀) hn
    (occupationRate_nonneg (mesh_pos hmesh) β m mp) hu hw
    (occupationRate_nonneg (mesh_pos hmesh) β mp m) (reverseError_nonneg J (hβ.trans hβ₀))
    (roundedLogConstant_nonneg J (hβ.trans hβ₀))
    (actual_true_reverse (mesh_pos hmesh) (mesh_two_le hmesh) hN hβ (hβ₀.trans_lt hsub) hp)
    hd he hl

theorem unordered_const {J : ℕ} (hJ : 0 < J) (B : ℝ) :
    unorderedSum hJ (fun _ _ => B) = B * unorderedSum hJ (fun _ _ => 1) := by
  classical
  unfold unorderedSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

/-- The actual rounded-center bound required by the central log-gradient
argument. The state may be any subtype proof of the literal rounded counts. -/
theorem rounded_imbalance_upper {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (hsmall : 1 / (J ^ 2 : ℕ) < t / 8)
    (m : OccupationState J N t) (hround : m.val = rounded J N) :
    let hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
    imbalance (mesh_pos hmesh) β m (rounded_inner (mesh_pos hmesh) hb.2.2.1 hsmall m hround)
      hb.2.2.2.2.1 ≤ roundedConstant J β₀ := by
  dsimp only
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  let hm := rounded_inner (mesh_pos hmesh) hb.2.2.1 hsmall m hround
  let hmargin := hb.2.2.2.2.1
  have he := unordered_mono (mesh_pos hmesh) (fun a b hab =>
    actual_edge_rounded_upper hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hround hm hmargin a b hab)
  change imbalance (mesh_pos hmesh) β m hm hmargin ≤
    unorderedSum (mesh_pos hmesh) (fun _ _ =>
      2 * roundedLogConstant J β₀ ^ 2 + 2 * reverseError J β₀ ^ 2 / rateScale J β₀) at he
  rw [unordered_const, unordered_cell_edge_count (mesh_pos hmesh) (mesh_three_le hmesh)] at he
  exact he.trans_eq (by simp only [Nat.cast_pow, roundedConstant]; ring)

/-- The Euclidean rounding cost, with the original particle count. -/
theorem rounded_profile_square_sum {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) :
    (∑ a : MeshIndex J, ((rounded J N a : ℝ) / N - ((J : ℝ) ^ 2)⁻¹) ^ 2) ≤
      (J : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hh (a : MeshIndex J) : |(rounded J N a : ℝ) / N - ((J : ℝ) ^ 2)⁻¹| ≤ 1 / N := by
    have hr := rounded_close hJ N a
    simp only [Nat.cast_pow] at hr
    have he : (rounded J N a : ℝ) / N - ((J : ℝ) ^ 2)⁻¹ =
        ((rounded J N a : ℝ) - (N : ℝ) / (J : ℝ) ^ 2) / N := by field_simp
    rw [he, abs_div, abs_of_pos hNr]
    exact div_le_div_of_nonneg_right hr hNr.le
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (MeshIndex J))) (fun a _ =>
    (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (1 : ℝ) / N)).mpr (hh a))
  simpa only [sq_abs, Finset.sum_const, Finset.card_univ, card_meshIndex, nsmul_eq_mul,
    Nat.cast_pow, div_pow, one_pow, mul_one_div] using hs

def translatedConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  additiveConstant J β₀ + coercivityConstant J β₀ * (J : ℝ) ^ 2

/-- Replacement of the uniform profile by the literal rounded profile costs
only a bounded additive term. This remains the near-region theorem; the
far-profile compactness argument is not invoked or assumed. -/
theorem near_rounded_imbalance {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hlarge : particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hnear : profileDeviation (stateProfile m) ≤ nearNeighborhood β₀)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) :
    let hmargin := (particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge).2.2.2.2.1
    coercivityConstant J β₀ / 2 * N *
        (∑ a, (stateProfile m a - (rounded J N a : ℝ) / N) ^ 2) - translatedConstant J β₀ ≤
      imbalance (mesh_pos hmesh) β m hm hmargin := by
  dsimp only
  have hb := particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hN := hb.2.2.2.1
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc := (coercivityConstant_pos (mesh_pos hmesh) hsub).le
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (MeshIndex J))) (fun a _ =>
    square_difference_upper (stateProfile m a - ((J : ℝ) ^ 2)⁻¹)
      (stateProfile m a - (rounded J N a : ℝ) / N))
  have hid (a : MeshIndex J) :
      (stateProfile m a - ((J : ℝ) ^ 2)⁻¹) -
        (stateProfile m a - (rounded J N a : ℝ) / N) = (rounded J N a : ℝ) / N - ((J : ℝ) ^ 2)⁻¹ := by ring
  simp only [hid, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hr := rounded_profile_square_sum (mesh_pos hmesh) hN0
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ coercivityConstant J β₀ / 2 * N by positivity)
  have hr' : (N : ℝ) * (∑ a : MeshIndex J, ((rounded J N a : ℝ) / N - ((J : ℝ) ^ 2)⁻¹) ^ 2) ≤ (J : ℝ) ^ 2 := by
    calc
      _ ≤ N * ((J : ℝ) ^ 2 / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hr hNr.le
      _ = (J : ℝ) ^ 2 / N := by field_simp
      _ ≤ (J : ℝ) ^ 2 := (div_le_iff₀ hNr).mpr (by nlinarith only [hN1, sq_nonneg (J : ℝ)])
  have hr'' := mul_le_mul_of_nonneg_left hr' hc
  have hu := near_uniform_imbalance hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hnear hm
  dsimp only at hu
  unfold translatedConstant
  nlinarith only [hp, hr'', hu]

theorem edgeError_nonneg {J : ℕ} (hJ : 0 < J) (β₀ : ℝ) : 0 ≤ edgeError J β₀ := by
  have := (rateScale_pos hJ β₀).le
  unfold edgeError
  positivity

theorem additiveConstant_nonneg {J : ℕ} (hJ : 0 < J) (β₀ : ℝ) : 0 ≤ additiveConstant J β₀ := by
  have := edgeError_nonneg hJ β₀
  unfold additiveConstant
  positivity

theorem translatedConstant_nonneg {J : ℕ} (hJ : 0 < J) {β₀ : ℝ} (hsub : β₀ < 4) :
    0 ≤ translatedConstant J β₀ := by
  unfold translatedConstant
  exact add_nonneg (additiveConstant_nonneg hJ β₀)
    (mul_nonneg (coercivityConstant_pos hJ hsub).le (sq_nonneg _))

end PeriodicAttractiveLogGas.OccupationNearImbalance
