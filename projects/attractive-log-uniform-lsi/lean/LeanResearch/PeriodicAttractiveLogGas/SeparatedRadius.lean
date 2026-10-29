import LeanResearch.PeriodicAttractiveLogGas.HeavyScales
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialCutoffs

/-! The actual counting argument in `lem:separated-radius`. All radial masses,
ratios, and cutoff values below are evaluations of the constructed functions.
The last radius is used only in the finite count, with no smallness assumption
and no collective test attached to it. -/

noncomputable section
open Set Filter Metric
open scoped BigOperators Topology ContDiff NNReal

namespace PeriodicAttractiveLogGas.SeparatedRadius

open MeshCells SmoothOccupations HeavyScales LocalizedVirialCutoffs

/-- The actual smoothed particle count for an arbitrary center and radius. -/
def mass {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin N, phi ξ s (X i)

/-- The actual annular mass, with particles counted with their labels. -/
def shellMass {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin N, omega ξ s K (X i)

/-- A strict-radius ball count; repeated positions count as distinct labels. -/
def ballCount {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : ℕ :=
  (Finset.univ.filter fun i : Fin N ↦ torusEuclideanDist (X i) ξ < s).card

/-- The denominator floor is the exact source value `delta*N/4`. -/
def rho {N : ℕ} (β₀ δ : ℝ) (ξ : Torus) (s : ℝ) (X : Configuration N) : ℝ :=
  shellMass ξ s (separationRadius β₀) X / max (mass ξ s X) (δ * N / 4)

/-- The actual separation cutoff, using the fixed source `c` and `K`. -/
def sigma {N : ℕ} (β₀ δ : ℝ) (ξ : Torus) (s : ℝ) (X : Configuration N) : ℝ :=
  1 - H ((rho β₀ δ ξ s X - separationConstant β₀ * (4 - β₀)) /
    (separationConstant β₀ * (4 - β₀)))

theorem mass_nonneg {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    0 ≤ mass ξ s X := Finset.sum_nonneg fun i _ ↦ (phi_mem_Icc ξ s (X i)).1

theorem mass_le_N {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : mass ξ s X ≤ N := by
  calc
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (phi_mem_Icc ξ s (X i)).2
    _ = N := by simp

theorem shellMass_nonneg {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) :
    0 ≤ shellMass ξ s K X := Finset.sum_nonneg fun i _ ↦ (omega_mem_Icc ξ s K (X i)).1

theorem shellMass_le_N {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) :
    shellMass ξ s K X ≤ N := by
  calc
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (omega_mem_Icc ξ s K (X i)).2
    _ = N := by simp

theorem ballCount_real_eq {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    (ballCount ξ s X : ℝ) =
      ∑ i : Fin N, if torusEuclideanDist (X i) ξ < s then (1 : ℝ) else 0 := by
  simpa only [ballCount] using!
    (Finset.natCast_card_filter (R := ℝ)
      (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < s) Finset.univ)

theorem ballCount_le_N {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    ballCount ξ s X ≤ N := by
  simpa only [ballCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset
      (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < s) Finset.univ)

theorem ballCount_le_mass {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N) :
    (ballCount ξ s X : ℝ) ≤ mass ξ s X := by
  rw [ballCount_real_eq]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · rw [phi_eq_one hs (by linarith : torusEuclideanDist (X i) ξ ≤ 2 * s)]
  · exact (phi_mem_Icc ξ s (X i)).1

/-- The inner ball and annular cutoff are disjoint pointwise. This inequality
includes equality at the inner and outer radii, where omega is zero. -/
theorem ballCount_add_shellMass_le {N : ℕ} {s K : ℝ}
    (hs : 0 < s) (hK : 1 ≤ K) (ξ : Torus) (X : Configuration N) :
    (ballCount ξ s X : ℝ) + shellMass ξ s K X ≤ (ballCount ξ (2 * K * s) X : ℝ) := by
  rw [ballCount_real_eq, ballCount_real_eq, shellMass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : torusEuclideanDist (X i) ξ < s
  · have hlarge : torusEuclideanDist (X i) ξ < 2 * K * s := by
      have hmul := mul_le_mul_of_nonneg_right hK hs.le
      nlinarith
    rw [ite_eq_left hi, ite_eq_left hlarge, omega_eq_zero_inner hs hi.le]
    norm_num
  · rw [ite_eq_right hi]
    by_cases ho : torusEuclideanDist (X i) ξ < 2 * K * s
    · rw [ite_eq_left ho, zero_add]
      exact (omega_mem_Icc ξ s K (X i)).2
    · rw [ite_eq_right ho, omega_eq_zero_outer hs (by linarith) (le_of_not_gt ho)]
      norm_num

theorem continuous_mass {N : ℕ} (ξ : Torus) (s : ℝ) : Continuous (mass (N := N) ξ s) :=
  continuous_finsetSum Finset.univ fun i _ ↦ (continuous_phi ξ s).comp (continuous_apply i)

theorem continuous_shellMass {N : ℕ} (ξ : Torus) (s K : ℝ) :
    Continuous (shellMass (N := N) ξ s K) :=
  continuous_finsetSum Finset.univ fun i _ ↦ (continuous_omega ξ s K).comp (continuous_apply i)

theorem denominator_pos {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (ξ : Torus) (s : ℝ) (X : Configuration N) : 0 < max (mass ξ s X) (δ * N / 4) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

theorem rho_nonneg {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (β₀ : ℝ) (ξ : Torus) (s : ℝ) (X : Configuration N) : 0 ≤ rho β₀ δ ξ s X :=
  div_nonneg (shellMass_nonneg _ _ _ _) (denominator_pos hN hδ ξ s X).le

theorem continuous_rho {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (β₀ : ℝ) (ξ : Torus) (s : ℝ) : Continuous (rho (N := N) β₀ δ ξ s) :=
  (continuous_shellMass ξ s (separationRadius β₀)).div
    ((continuous_mass ξ s).max continuous_const)
    (fun X ↦ (denominator_pos hN hδ ξ s X).ne')

theorem continuous_sigma {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (β₀ : ℝ) (ξ : Torus) (s : ℝ) : Continuous (sigma (N := N) β₀ δ ξ s) :=
  continuous_const.sub (contDiff_H.continuous.comp
    (((continuous_rho hN hδ β₀ ξ s).sub continuous_const).div_const _))

theorem sigma_mem_Icc {N : ℕ} (β₀ δ : ℝ) (ξ : Torus) (s : ℝ) (X : Configuration N) :
    sigma β₀ δ ξ s X ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := H_mem_Icc
    ((rho β₀ δ ξ s X - separationConstant β₀ * (4 - β₀)) /
      (separationConstant β₀ * (4 - β₀)))
  constructor <;> dsimp [sigma] <;> linarith

theorem separation_threshold_pos {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) :
    0 < separationConstant β₀ * (4 - β₀) :=
  mul_pos (separationConstant_pos hβ₀) (sub_pos.mpr hβ)

theorem sigma_eq_one_of_rho_le {N : ℕ} {β₀ δ s : ℝ} {ξ : Torus} {X : Configuration N}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4)
    (hr : rho β₀ δ ξ s X ≤ separationConstant β₀ * (4 - β₀)) :
    sigma β₀ δ ξ s X = 1 := by
  unfold sigma
  rw [H_eq_zero_of_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr)
    (separation_threshold_pos hβ₀ hβ).le)]
  ring

theorem rho_lt_twice_threshold_of_sigma_pos {N : ℕ} {β₀ δ s : ℝ} {ξ : Torus}
    {X : Configuration N} (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4)
    (hσ : 0 < sigma β₀ δ ξ s X) :
    rho β₀ δ ξ s X < 2 * (separationConstant β₀ * (4 - β₀)) := by
  by_contra h
  have he : 1 ≤ (rho β₀ δ ξ s X - separationConstant β₀ * (4 - β₀)) /
      (separationConstant β₀ * (4 - β₀)) := by
    apply (le_div_iff₀ (separation_threshold_pos hβ₀ hβ)).2
    linarith
  have hz : sigma β₀ δ ξ s X = 0 := by simp only [sigma, H_eq_one_of_one_le he, sub_self]
  linarith

/-- The actual resolution threshold in particular supplies the mesh condition
needed by the already constructed smooth occupations. -/
theorem source_mesh_ge_three {β₀ δ : ℝ} {J : ℕ}
    (hJ : sourceResolution β₀ δ ≤ J) : 3 ≤ J := by
  have hK := separationRadius_ge_eight β₀
  have hp : 1 ≤ (2 * separationRadius β₀) ^
      (sourceScaleCount β₀ δ - 1) := one_le_pow₀ (by linarith)
  have hfirst : 16 * separationRadius β₀ *
      (2 * separationRadius β₀) ^ (sourceScaleCount β₀ δ - 1) ≤ (J : ℝ) :=
    (le_max_left _ _).trans hJ
  have hprod := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 16 * separationRadius β₀ by linarith)
  have hreal : (3 : ℝ) ≤ J := by nlinarith
  exact_mod_cast hreal

theorem source_mesh_pos {β₀ δ : ℝ} {J : ℕ}
    (hJ : sourceResolution β₀ δ ≤ J) : 0 < J := by
  have := source_mesh_ge_three hJ
  omega

theorem source_radius_pos {β₀ δ : ℝ} {J : ℕ}
    (hJ : sourceResolution β₀ δ ≤ J) (m : ℕ) :
    0 < scaleRadius J (separationRadius β₀) m :=
  scaleRadius_pos (source_mesh_pos hJ) (by linarith [separationRadius_ge_eight β₀]) m

/-- The full topological support of the actual cell cutoff fits strictly
inside the initial counting ball, and hence every later plateau ball. -/
theorem cell_support_lt_scale {β₀ δ : ℝ} {J : ℕ}
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ) {z : Torus}
    (hz : z ∈ tsupport (cellCutoff J (source_mesh_pos hJ) a)) :
    torusEuclideanDist z (cellCenter J a) < scaleRadius J (separationRadius β₀) m := by
  have hb := cellCutoff_tsupport_ball J (source_mesh_ge_three hJ) a hz
  have hi := cutoff_ball_lt_initial_scale (source_mesh_pos hJ) (separationRadius β₀)
  have hm : scaleRadius J (separationRadius β₀) 0 ≤
      scaleRadius J (separationRadius β₀) m :=
    scaleRadius_mono (by linarith [separationRadius_ge_eight β₀]) (Nat.zero_le m)
  exact (hb.trans_lt hi).trans_le hm

theorem cell_support_phi_eq_one {β₀ δ : ℝ} {J : ℕ}
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ) {z : Torus}
    (hz : z ∈ tsupport (cellCutoff J (source_mesh_pos hJ) a)) :
    phi (cellCenter J a) (scaleRadius J (separationRadius β₀) m) z = 1 := by
  apply phi_eq_one (source_radius_pos hJ m)
  have hr := cell_support_lt_scale hJ a m hz
  linarith [source_radius_pos hJ m]

theorem cellCutoff_le_phi {β₀ δ : ℝ} {J : ℕ}
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ) (z : Torus) :
    cellCutoff J (source_mesh_pos hJ) a z ≤
      phi (cellCenter J a) (scaleRadius J (separationRadius β₀) m) z := by
  by_cases hz : cellCutoff J (source_mesh_pos hJ) a z = 0
  · rw [hz]
    exact (phi_mem_Icc _ _ _).1
  · rw [cell_support_phi_eq_one hJ a m (subset_tsupport _ hz)]
    exact cellCutoff_le_one J (source_mesh_ge_three hJ) a z

theorem N_mul_occupationFraction {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    (a : MeshIndex J) (X : Configuration N) :
    (N : ℝ) * occupationFraction N J hJ a X = ∑ i : Fin N, cellCutoff J hJ a (X i) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold occupationFraction
  field_simp

theorem occupation_mass_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ) (X : Configuration N) :
    (N : ℝ) * occupationFraction N J (source_mesh_pos hJ) a X ≤
      mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
  rw [N_mul_occupationFraction hN]
  exact Finset.sum_le_sum fun i _ ↦ cellCutoff_le_phi hJ a m (X i)

theorem occupation_initial_count_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (X : Configuration N) :
    (N : ℝ) * occupationFraction N J (source_mesh_pos hJ) a X ≤
      (ballCount (cellCenter J a) (scaleRadius J (separationRadius β₀) 0) X : ℝ) := by
  rw [N_mul_occupationFraction hN, ballCount_real_eq]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : cellCutoff J (source_mesh_pos hJ) a (X i) = 0
  · rw [hi]
    split_ifs <;> norm_num
  · rw [ite_eq_left (cell_support_lt_scale hJ a 0 (subset_tsupport _ hi))]
    exact cellCutoff_le_one J (source_mesh_ge_three hJ) a (X i)

theorem mass_gt_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (X : Configuration N)
    (hheavy : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a X) (m : ℕ) :
    δ * N / 2 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := occupation_mass_le hN hJ a m X
  have hh := mul_lt_mul_of_pos_left hheavy hNr
  nlinarith

theorem denominator_eq_mass_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hδ : 0 < δ) (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (X : Configuration N)
    (hheavy : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a X) (m : ℕ) :
    max (mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X) (δ * N / 4) =
      mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
  apply max_eq_left
  have hm := mass_gt_of_heavy hN hJ a X hheavy m
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith [mul_pos hδ hNr]

theorem rho_eq_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hδ : 0 < δ) (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (X : Configuration N)
    (hheavy : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a X) (m : ℕ) :
    rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X =
      shellMass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) (separationRadius β₀) X /
        mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
  unfold rho
  rw [denominator_eq_mass_of_heavy hN hδ hJ a X hheavy m]

/-- The actual separated-radius lemma. The proof applies the checked finite
growth contradiction to the actual strict ball counts, including the final
counting-only radius. No collision exclusion or symmetry is assumed. -/
theorem separated_radius {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (X : Configuration N)
    (hheavy : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a X) :
    (∀ m < sourceScaleCount β₀ δ,
      δ * N / 2 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X) ∧
    ∃ m < sourceScaleCount β₀ δ,
      sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X = 1 := by
  refine ⟨fun m _ ↦ mass_gt_of_heavy hN hJ a X hheavy m, ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let count : ℕ → ℝ := fun m ↦
    (ballCount (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X : ℝ)
  have hstart : δ * N / 2 < count 0 := by
    have hi := occupation_initial_count_le hN hJ a X
    have hh := mul_lt_mul_of_pos_left hheavy hNr
    dsimp [count]
    nlinarith
  have hfinal : count (sourceScaleCount β₀ δ) ≤ N := by
    dsimp [count]
    exact_mod_cast ballCount_le_N (cellCenter J a)
      (scaleRadius J (separationRadius β₀) (sourceScaleCount β₀ δ)) X
  obtain ⟨m, hm, hcount⟩ := exists_nonexpanding_scale hβ hδ
    (separationConstant_pos hβ₀) count hstart hfinal
  refine ⟨m, hm, sigma_eq_one_of_rho_le hβ₀ hβ ?_⟩
  have hs := source_radius_pos hJ m
  have hK := separationRadius_ge_eight β₀
  have hinc := ballCount_add_shellMass_le hs (by linarith : 1 ≤ separationRadius β₀)
    (cellCenter J a) X
  have hcountmass := ballCount_le_mass hs (cellCenter J a) X
  have hshell : shellMass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (separationRadius β₀) X ≤
      separationConstant β₀ * (4 - β₀) *
        mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
    have he : 2 * separationRadius β₀ * scaleRadius J (separationRadius β₀) m =
        scaleRadius J (separationRadius β₀) (m + 1) := by
      rw [scaleRadius_succ]
    rw [he] at hinc
    change count m + shellMass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (separationRadius β₀) X ≤ count (m + 1) at hinc
    have hb := mul_le_mul_of_nonneg_left hcountmass
      (separation_threshold_pos hβ₀ hβ).le
    change separationConstant β₀ * (4 - β₀) * count m ≤ _ at hb
    nlinarith
  rw [rho_eq_of_heavy hN hδ hJ a X hheavy m]
  apply (div_le_iff₀ (lt_trans (by positivity : (0 : ℝ) < δ * N / 2)
    (mass_gt_of_heavy hN hJ a X hheavy m))).2
  exact hshell

/-- The actual open set used in the next localization lemma. -/
def separatedOpenSet (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ) (a : MeshIndex J) (m : ℕ) :
    Set (Configuration N) :=
  {X | δ / 2 < occupationFraction N J hJ a X ∧
    0 < sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X}

theorem isOpen_separatedOpenSet {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) (a : MeshIndex J) (m : ℕ) :
    IsOpen (separatedOpenSet N J hJ β₀ δ a m) :=
  (isOpen_lt continuous_const (occupationFraction_continuous N J hJ a)).inter
    (isOpen_lt continuous_const (continuous_sigma hN hδ β₀ (cellCenter J a)
      (scaleRadius J (separationRadius β₀) m)))

theorem separatedOpenSet_conditions {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ) {X : Configuration N}
    (hX : X ∈ separatedOpenSet N J (source_mesh_pos hJ) β₀ δ a m) :
    δ * N / 2 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X ∧
    shellMass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) (separationRadius β₀) X <
      2 * (separationConstant β₀ * (4 - β₀)) *
        mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
  have hm := mass_gt_of_heavy hN hJ a X hX.1 m
  refine ⟨hm, ?_⟩
  have hr := rho_lt_twice_threshold_of_sigma_pos hβ₀ hβ hX.2
  rw [rho_eq_of_heavy hN hδ hJ a X hX.1 m] at hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_lt_iff₀ (lt_trans (by positivity : (0 : ℝ) < δ * N / 2) hm)).mp hr

/-- An explicit global Lipschitz constant for the actual radial mass. -/
def massLipschitzConstant (N : ℕ) (s : ℝ) : ℝ≥0 :=
  N * Real.toNNReal (1 / s)

/-- The exact single-particle omega bound supplies this finite-sum constant. -/
def shellLipschitzConstant (N : ℕ) (s : ℝ) : ℝ≥0 :=
  N * Real.toNNReal (2 / s)

/-- The denominator floor gives a global constant, including configurations
outside the heavy region. This bound is qualitative; no sharpness is used. -/
def rhoLipschitzConstant (N : ℕ) (δ s : ℝ) : ℝ≥0 :=
  Real.toNNReal ((shellLipschitzConstant N s : ℝ) / (δ * N / 4) +
    N * (massLipschitzConstant N s : ℝ) / (δ * N / 4) ^ 2)

def sigmaLipschitzConstant (N : ℕ) (β₀ δ s : ℝ) : ℝ≥0 :=
  2 * Real.toNNReal (1 / (separationConstant β₀ * (4 - β₀))) *
    rhoLipschitzConstant N δ s

private theorem norm_particleProjection_le (N : ℕ) (i : Fin N) (y : Gradient N) :
    ‖particleProjection N i y‖ ≤ ‖y‖ := by
  have hs : ‖particleProjection N i y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [← sum_particleProjection_norm_sq N y]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖particleProjection N j y‖)
      (Finset.mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

private theorem configuration_sum_lipschitz {N : ℕ} {f : Torus → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C (fun y : PlanarSpace ↦ f (torusQuotient y))) :
    ConfigurationEuclideanLipschitzWith (N * C)
      (fun X : Configuration N ↦ ∑ i : Fin N, f (X i)) := by
  apply configurationEuclideanLipschitzWith_iff_lift.mpr
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, ← Finset.sum_sub_distrib, dist_eq_norm]
  calc
    _ ≤ ∑ i : Fin N, |f (configurationQuotient N y i) -
        f (configurationQuotient N z i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (C : ℝ) * ‖y - z‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hf.dist_le_mul (particleProjection N i y) (particleProjection N i z)
      simp only [quotient_particleProjection, dist_eq_norm, ← map_sub] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left (norm_particleProjection_le N i (y - z))
        C.coe_nonneg)
    _ = _ := by simp [NNReal.coe_mul, mul_assoc]

theorem mass_physical_lipschitz {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) : ConfigurationEuclideanLipschitzWith (massLipschitzConstant N s)
      (mass (N := N) ξ s) := by
  apply configuration_sum_lipschitz
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_phi_lift hs hsmall ξ).differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)) x‖ ≤
    (Real.toNNReal (1 / s) : ℝ)
  rw [Real.toNNReal_of_nonneg (by positivity)]
  exact norm_fderiv_phi_lift_le hs hsmall ξ x

theorem shellMass_physical_lipschitz {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (houter : 2 * K * s ≤ 1 / 4) (ξ : Torus) :
    ConfigurationEuclideanLipschitzWith (shellLipschitzConstant N s)
      (shellMass (N := N) ξ s K) := by
  apply configuration_sum_lipschitz
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_omega_lift hs (by linarith : 0 < K) houter ξ).differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ (fun y : PlanarSpace ↦ omega ξ s K (torusQuotient y)) x‖ ≤
    (Real.toNNReal (2 / s) : ℝ)
  rw [Real.toNNReal_of_nonneg (by positivity)]
  exact norm_fderiv_omega_lift_le hs hK houter ξ x

private theorem lipschitz_div_of_positive_floor {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Cf Cg : ℝ≥0} {B ε : ℝ}
    (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g)
    (hB : 0 ≤ B) (hε : 0 < ε) (hb : ∀ x, |f x| ≤ B) (hl : ∀ x, ε ≤ g x) :
    LipschitzWith (Real.toNNReal ((Cf : ℝ) / ε + B * (Cg : ℝ) / ε ^ 2))
      (fun x ↦ f x / g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < g x := hε.trans_le (hl x)
  have hy : 0 < g y := hε.trans_le (hl y)
  have hp : ε ^ 2 ≤ g x * g y := by
    simpa only [sq] using mul_le_mul (hl x) (hl y) hε.le hx.le
  have hdf : |f x - f y| ≤ (Cf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hf.dist_le_mul x y
  have hdg : |g y - g x| ≤ (Cg : ℝ) * dist x y := by
    calc
      _ = |g x - g y| := abs_sub_comm _ _
      _ ≤ _ := by simpa only [Real.dist_eq] using hg.dist_le_mul x y
  have he : f x / g x - f y / g y =
      (f x - f y) / g x + f y * (g y - g x) / (g x * g y) := by
    field_simp [hx.ne', hy.ne']
    ring
  rw [Real.dist_eq, he]
  calc
    _ ≤ |(f x - f y) / g x| + |f y * (g y - g x) / (g x * g y)| := abs_add_le _ _
    _ = |f x - f y| / g x + |f y| * |g y - g x| / (g x * g y) := by
      simp only [abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy]
    _ ≤ ((Cf : ℝ) * dist x y) / ε + (B * ((Cg : ℝ) * dist x y)) / ε ^ 2 := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right hdf hx.le).trans
          (div_le_div_of_nonneg_left (by positivity) hε (hl x))
      · have hn : |f y| * |g y - g x| ≤ B * ((Cg : ℝ) * dist x y) :=
          mul_le_mul (hb y) hdg (abs_nonneg _) hB
        exact (div_le_div_of_nonneg_right hn (mul_pos hx hy).le).trans
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hε) hp)
    _ = _ := by
      rw [Real.toNNReal_of_nonneg (by positivity)]
      change ((Cf : ℝ) * dist x y) / ε + (B * ((Cg : ℝ) * dist x y)) / ε ^ 2 =
        ((Cf : ℝ) / ε + B * (Cg : ℝ) / ε ^ 2) * dist x y
      ring

/-- Global physical Lipschitz regularity of the actual ratio. Positivity is
provided by the explicit floor, not by a restriction to the heavy set. -/
theorem rho_physical_lipschitz {N : ℕ} (hN : 0 < N) {β₀ δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (houter : 2 * separationRadius β₀ * s ≤ 1 / 4) (ξ : Torus) :
    ConfigurationEuclideanLipschitzWith (rhoLipschitzConstant N δ s)
      (rho (N := N) β₀ δ ξ s) := by
  apply configurationEuclideanLipschitzWith_iff_lift.mpr
  have hM := (mass_physical_lipschitz (N := N) hs hsmall ξ).lift
  have hS := (shellMass_physical_lipschitz (N := N) hs
    (by linarith [separationRadius_ge_eight β₀]) houter ξ).lift
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply lipschitz_div_of_positive_floor hS (hM.max_const (δ * N / 4))
    (Nat.cast_nonneg N) (by positivity : 0 < δ * N / 4)
  · intro y
    rw [abs_of_nonneg (shellMass_nonneg _ _ _ _)]
    exact shellMass_le_N _ _ _ _
  · intro y
    exact le_max_right _ _

theorem H_lipschitz : LipschitzWith 2 H := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun r ↦ (hasDerivAt_H r).differentiableAt)
  intro r
  change |deriv H r| ≤ (2 : ℝ)
  rw [deriv_H, abs_of_nonneg (b_nonneg r)]
  exact b_le_two r

private theorem threshold_argument_lipschitz {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal (1 / t)) (fun r : ℝ ↦ (r - t) / t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq,
    show (x - t) / t - (y - t) / t = (x - y) / t by ring,
    abs_div, abs_of_pos ht, Real.toNNReal_of_nonneg (by positivity)]
  change |x - y| / t ≤ (1 / t) * |x - y|
  exact le_of_eq (by ring)

theorem sigma_physical_lipschitz {N : ℕ} (hN : 0 < N) {β₀ δ s : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hs : 0 < s)
    (hsmall : s ≤ 1 / 64) (houter : 2 * separationRadius β₀ * s ≤ 1 / 4) (ξ : Torus) :
    ConfigurationEuclideanLipschitzWith (sigmaLipschitzConstant N β₀ δ s)
      (sigma (N := N) β₀ δ ξ s) := by
  apply configurationEuclideanLipschitzWith_iff_lift.mpr
  have hr := (rho_physical_lipschitz hN hδ hs hsmall houter ξ).lift
  have ha := threshold_argument_lipschitz (separation_threshold_pos hβ₀ hβ)
  have h := (LipschitzWith.const (1 : ℝ)).sub (H_lipschitz.comp (ha.comp hr))
  simpa only [sigma, sigmaLipschitzConstant, Function.comp_def, zero_add, mul_assoc] using h

/-- Both localization factors are globally Lipschitz for every actual source
test scale; the final counting-only radius is deliberately excluded here. -/
theorem source_rho_sigma_physical_lipschitz {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) :
    ConfigurationEuclideanLipschitzWith
      (rhoLipschitzConstant N δ (scaleRadius J (separationRadius β₀) m))
      (rho (N := N) β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)) ∧
    ConfigurationEuclideanLipschitzWith
      (sigmaLipschitzConstant N β₀ δ (scaleRadius J (separationRadius β₀) m))
      (sigma (N := N) β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)) := by
  obtain ⟨hsmall, hKsmall, houter, _⟩ := source_scale_admissibility hβ₀ hβ hJ hm
  have hs := source_radius_pos hJ m
  exact ⟨rho_physical_lipschitz hN hδ hs (hsmall.trans hKsmall) houter _,
    sigma_physical_lipschitz hN hβ₀ hβ hδ hs (hsmall.trans hKsmall) houter _⟩

end PeriodicAttractiveLogGas.SeparatedRadius
