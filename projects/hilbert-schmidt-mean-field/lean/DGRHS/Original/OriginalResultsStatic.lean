import Batteries.Tactic.Alias
import DGRHS.CLT.EquilibriumSplitting
import DGRHS.CLT.SourceLogEquilibriumOriginal
import DGRHS.CLT.SourceLogLiteralStatic
import DGRHS.CLT.SourceLogSingularWeight
import DGRHS.CLT.SourceRieszLiteralStatic
import DGRHS.CLT.SourceRieszStatic
import DGRHS.CLT.SourceRieszThermalEquilibrium
import DGRHS.CLT.SourceRieszUniform
import DGRHS.CLT.SourceStaticCovarianceBounds
import DGRHS.Entropy.SourceRieszTemperatureGrowth
import DGRHS.Entropy.SourceTemperatureScaling
import DGRHS.Entropy.SourceTemperatureWindow
import DGRHS.Gaussian.GaussianLogSourceMoment
import DGRHS.Gaussian.SharpnessCompressionFactory
import DGRHS.Gaussian.SharpnessCompressionLower
import DGRHS.Gaussian.SharpnessLiteralPartition
import DGRHS.Gaussian.SourceRepulsiveLogRate
import DGRHS.Gaussian.SourceRepulsiveLogRateCutoff
import DGRHS.Gaussian.SourceRepulsiveRieszRate
import DGRHS.Kinetic.SourceLogKineticTransfer
import DGRHS.Kinetic.SourceRieszKinetic
import DGRHS.Kinetic.SpatialTensorization

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). Source-facing export suite, area: Static.

Each `alias` creates a new declaration with EXACTLY the type of an existing
root declaration (no premise added or removed). The source label, lines and the
row disposition from reports/DISPOSITIONS_253.json are recorded beside it; a
row marked SOURCE_DISCREPANCY or UNRESOLVED exports only the valid corrected or
partial statement named in that row's qualification, never the printed
auxiliary claim. Target bytes/status are bound by the gate records cited in the
disposition, not by this file. -/

/-- rem:torus-kinetic-variants (source 492–496); row disposition UNRESOLVED. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_sourceLog_kinetic_entropic_transfer := DGRHS.Kinetic.sourceLog_kinetic_entropic_transfer

/-- rem:torus-kinetic-variants (source 492–496); row disposition UNRESOLVED. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_sourceRiesz_kinetic_finiteKL_entropic := DGRHS.Kinetic.sourceRiesz_kinetic_finiteKL_entropic

/-- rem:torus-kinetic-variants (source 492–496); row disposition UNRESOLVED. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_spatial_partition_tensor := DGRHS.Kinetic.spatial_partition_tensor

/-- thm:partitionFunctionBound (source 504–529); row disposition REUSED. -/
alias DGRHS.Original.thm_partitionFunctionBound.CLT_sourceRieszPartition_uniform := DGRHS.CLT.sourceRieszPartition_uniform

/-- thm:partitionFunctionBound (source 504–529); row disposition REUSED. -/
alias DGRHS.Original.thm_partitionFunctionBound.CLT_sourceLogSingularPartition_uniform := DGRHS.CLT.sourceLogSingularPartition_uniform

/-- thm:partitionFunctionBound (source 504–529); row disposition REUSED. -/
alias DGRHS.Original.thm_partitionFunctionBound.SourceRepulsiveRieszRate_exists_source_partition_rate := DGRHS.SourceRepulsiveRieszRate.exists_source_partition_rate

/-- thm:partitionFunctionBound (source 504–529); row disposition REUSED. -/
alias DGRHS.Original.thm_partitionFunctionBound.SourceRepulsiveLogRate_exists_source_partition_rate := DGRHS.SourceRepulsiveLogRate.exists_source_partition_rate

/-- cor:equilibriumFreeEnergyCorrection (source 558–586); row disposition REUSED. -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.CLT_sourceLog_equilibrium_correction_original := DGRHS.CLT.sourceLog_equilibrium_correction_original

/-- cor:equilibriumFreeEnergyCorrection (source 558–586); row disposition REUSED. -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.CLT_sourceLog_equilibrium_macroscopic_original := DGRHS.CLT.sourceLog_equilibrium_macroscopic_original

/-- cor:equilibriumFreeEnergyCorrection (source 558–586); row disposition REUSED. -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.CLT_sourceRiesz_thermal_equilibrium_correction := DGRHS.CLT.sourceRiesz_thermal_equilibrium_correction

/-- cor:equilibriumFreeEnergyCorrection (source 558–586); row disposition REUSED. -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.CLT_sourceRiesz_thermal_equilibrium_macroscopic := DGRHS.CLT.sourceRiesz_thermal_equilibrium_macroscopic

/-- prop:linearEmpiricalFluctuationCLT (source 805–830); row disposition REUSED. -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.CLT_exists_sourceRieszStatic := DGRHS.CLT.exists_sourceRieszStatic

/-- prop:linearEmpiricalFluctuationCLT (source 805–830); row disposition REUSED. -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.CLT_exists_sourceRieszSingularStatic := DGRHS.CLT.exists_sourceRieszSingularStatic

/-- prop:linearEmpiricalFluctuationCLT (source 805–830); row disposition REUSED. -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.CLT_exists_sourceLogSingularStatic := DGRHS.CLT.exists_sourceLogSingularStatic

/-- rem:staticCLTInterpretation (source 832–845); row disposition REUSED. -/
alias DGRHS.Original.rem_staticCLTInterpretation.CLT_equilibrium_modulated_eq_canonical := DGRHS.CLT.equilibrium_modulated_eq_canonical

/-- rem:staticCLTInterpretation (source 832–845); row disposition REUSED. -/
alias DGRHS.Original.rem_staticCLTInterpretation.CLT_exists_sourceRieszCovarianceBounds := DGRHS.CLT.exists_sourceRieszCovarianceBounds

/-- rem:staticCLTInterpretation (source 832–845); row disposition REUSED. -/
alias DGRHS.Original.rem_staticCLTInterpretation.CLT_exists_sourceLogCovarianceBounds := DGRHS.CLT.exists_sourceLogCovarianceBounds

/-- prop:uniformBoundRepulsive (source 1523–1532); row disposition REUSED. -/
alias DGRHS.Original.prop_uniformBoundRepulsive.Gaussian_logPhysicalSource_uniform_exponential := DGRHS.Gaussian.logPhysicalSource_uniform_exponential

/-- prop:uniformBoundRepulsive (source 1523–1532); row disposition REUSED. -/
alias DGRHS.Original.prop_uniformBoundRepulsive.CLT_sourceRieszPartition_uniform := DGRHS.CLT.sourceRieszPartition_uniform

/-- prop:rieszLaplaceLogFallback (source 1941–1952); row disposition REUSED. -/
alias DGRHS.Original.prop_rieszLaplaceLogFallback.SourceRepulsiveRieszRate_exists_canonical_partition_rate := DGRHS.SourceRepulsiveRieszRate.exists_canonical_partition_rate

/-- prop:rieszLaplaceLogFallback (source 1941–1952); row disposition REUSED. -/
alias DGRHS.Original.prop_rieszLaplaceLogFallback.SourceRepulsiveLogRate_exists_cutoff_partition_rate := DGRHS.SourceRepulsiveLogRate.exists_cutoff_partition_rate

/-- cor:partitionFunctionTemperatureInterpolation (source 2168–2196); row disposition REUSED. -/
alias DGRHS.Original.cor_partitionFunctionTemperatureInterpolation.Entropy_sourceLogPartition_fixed_temperature_window := DGRHS.Entropy.sourceLogPartition_fixed_temperature_window

/-- cor:partitionFunctionTemperatureInterpolation (source 2168–2196); row disposition REUSED. -/
alias DGRHS.Original.cor_partitionFunctionTemperatureInterpolation.Entropy_sourceRieszPartition_all_temperature_growth := DGRHS.Entropy.sourceRieszPartition_all_temperature_growth

/-- cor:partitionFunctionTemperatureInterpolation (source 2168–2196); row disposition REUSED. -/
alias DGRHS.Original.cor_partitionFunctionTemperatureInterpolation.Entropy_sourceLogPartition_temperature_scaling := DGRHS.Entropy.sourceLogPartition_temperature_scaling

/-- rem:LebleSerfatyComparison (source 2198–2200); row disposition REUSED. -/
alias DGRHS.Original.rem_LebleSerfatyComparison.Entropy_sourceLogPartition_temperature_scaling := DGRHS.Entropy.sourceLogPartition_temperature_scaling

/-- rem:LebleSerfatyComparison (source 2198–2200); row disposition REUSED. -/
alias DGRHS.Original.rem_LebleSerfatyComparison.Entropy_sourceRieszPartition_temperature_scaling := DGRHS.Entropy.sourceRieszPartition_temperature_scaling

/-- lem:quantitativeDyadicCompression (source 2238–2267); row disposition REUSED. -/
alias DGRHS.Original.lem_quantitativeDyadicCompression.Gaussian_sharpness_exists_critical_compression_factory := DGRHS.Gaussian.sharpness_exists_critical_compression_factory

/-- lem:quantitativeDyadicCompression (source 2238–2267); row disposition REUSED. -/
alias DGRHS.Original.lem_quantitativeDyadicCompression.Gaussian_sharpness_compression_good_annulus_lower := DGRHS.Gaussian.sharpness_compression_good_annulus_lower

/-- prop:partition-function-sharpness (source 2355–2367); row disposition REUSED. -/
alias DGRHS.Original.prop_partition_function_sharpness.Gaussian_sharpness_riesz_literal_partition_rate := DGRHS.Gaussian.sharpness_riesz_literal_partition_rate
