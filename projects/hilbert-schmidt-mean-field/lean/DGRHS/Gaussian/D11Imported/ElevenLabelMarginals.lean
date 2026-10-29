import DGRHS.Gaussian.D11Imported.ElevenJointLabel

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma translated_insertNth (i : Fin 11) (t : ℝ) (y : Fin 10 → ℝ)
    (n : ℤ) (m : Fin 10 → ℤ) :
    (fun j : Fin 11 => (i.insertNth t y : Fin 11 → ℝ) j + ((i.insertNth n m : Frequency 11) j:ℝ)) =
      (i.insertNth (t+(n:ℝ)) (fun j => y j+(m j:ℝ)) : Fin 11 → ℝ) := by
  apply funext
  refine (Fin.forall_iff_succAbove i (P := fun j : Fin 11 =>
    (i.insertNth t y : Fin 11 → ℝ) j + ((i.insertNth n m : Frequency 11) j:ℝ) =
      (i.insertNth (t+(n:ℝ)) (fun j => y j+(m j:ℝ)) : Fin 11 → ℝ) j)).mpr ?_
  constructor
  · simp
  · intro j
    simp

lemma profile_slice_lintegral (t : ℝ) :
    (∫⁻ y : Fin 10 → ℝ, ENNReal.ofReal (euclideanProfile (Fin.cons t y))) =
      ENNReal.ofReal (coordinateProfile t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (euclideanProfile_marginal_integrable t)
    (ae_of_all _ (fun _ => (euclideanProfile_pos _).le)), euclideanProfile_marginal]
  rfl

lemma profile_slice_unfold (t : ℝ) :
    (∑' m : Frequency 10, ∫⁻ y in PeriodizationCube.cube 10,
      ENNReal.ofReal (euclideanProfile (Fin.cons t (fun j => y j+(m j:ℝ))))) =
        ENNReal.ofReal (coordinateProfile t) := by
  have hm : Measurable (fun y : Fin 10 → ℝ => ENNReal.ofReal (euclideanProfile (Fin.cons t y))) :=
    euclideanProfile_continuous.measurable.ennreal_ofReal.comp (by fun_prop)
  rw [← lintegral_tsum (f := fun (m : Frequency 10) (y : Fin 10 → ℝ) =>
      ENNReal.ofReal (euclideanProfile (Fin.cons t (fun j => y j+(m j:ℝ)))))
    (fun m => (hm.comp (by fun_prop)).aemeasurable)]
  exact (PeriodizationCube.unfold_lintegral 10 _ hm).trans (profile_slice_lintegral t)

lemma coordinateLabelProbability_ofReal (n : ℤ) :
    ENNReal.ofReal (coordinateLabelProbability n) =
      ∫⁻ t in Ico (-(1/2:ℝ)) (1/2), ENNReal.ofReal (coordinateProfile (t+(n:ℝ))) := by
  have hi : Integrable (fun t : ℝ => coordinateProfile (t+(n:ℝ))) :=
    (measurePreserving_add_right volume (n:ℝ)).integrable_comp_of_integrable coordinateProfile_integrable
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (ae_of_all _ (fun _ => (coordinateProfile_pos _).le))]
  congr 1
  rw [coordinateLabelProbability_interval, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ)≤1/2),
    intervalIntegral.integral_comp_add_right]
  congr 1 <;> ring

lemma labelProbability_coordinate_lsum (i : Fin 11) (n : ℤ) :
    (∑' m : Frequency 10, ENNReal.ofReal (labelProbability (i.insertNth n m))) =
      ENNReal.ofReal (coordinateLabelProbability n) := by
  have he (m : Frequency 10) : ENNReal.ofReal (labelProbability (i.insertNth n m)) =
      ∫⁻ t in Ico (-(1/2:ℝ)) (1/2), ∫⁻ y in PeriodizationCube.cube 10,
        ENNReal.ofReal (euclideanProfile (Fin.cons (t+(n:ℝ)) (fun j => y j+(m j:ℝ)))) := by
    rw [labelProbability_ofReal]
    change (∫⁻ x in PeriodizationCube.cube 11, _) = _
    rw [PeriodizationCube.lintegral_cube_split 10 i
      (fun x : Fin 11 → ℝ => ENNReal.ofReal (euclideanProfile (fun j => x j+((i.insertNth n m : Frequency 11) j:ℝ))))
      (euclideanProfile_continuous.measurable.ennreal_ofReal.comp (by fun_prop))]
    apply lintegral_congr
    intro t
    apply lintegral_congr
    intro y
    rw [translated_insertNth, euclideanProfile_insertNth]
  simp_rw [he]
  have hm (m : Frequency 10) : Measurable (fun t : ℝ =>
      ∫⁻ y in PeriodizationCube.cube 10,
        ENNReal.ofReal (euclideanProfile (Fin.cons (t+(n:ℝ)) (fun j => y j+(m j:ℝ))))) := by
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (PeriodizationCube.cube 10))
      (f := fun z : ℝ × (Fin 10 → ℝ) =>
        ENNReal.ofReal (euclideanProfile (Fin.cons (z.1+(n:ℝ)) (fun j => z.2 j+(m j:ℝ)))))
      (euclideanProfile_continuous.measurable.ennreal_ofReal.comp (by fun_prop))
  rw [← lintegral_tsum (fun m => (hm m).aemeasurable)]
  simp_rw [profile_slice_unfold]
  exact (coordinateLabelProbability_ofReal n).symm

#print axioms labelProbability_coordinate_lsum
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
