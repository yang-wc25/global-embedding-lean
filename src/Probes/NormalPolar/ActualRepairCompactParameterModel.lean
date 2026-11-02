import Mathlib.Geometry.Manifold.Instances.Sphere
import Smoothing.ParameterRound2CompactAtlas
import NormalPolar.ActualRepairGlobalParameterProfiles

/-!
# A genuine nonempty compact parameter model in every dimension

The unit sphere supplies a concrete smooth compact parameter manifold,
including dimension zero. Its actual finite buffered atlas comes from the
accepted compact chart-cover construction. This produces the parameter
manifold, atlas, compact samples and global local-coordinate extension; it
does not assert existence of the remaining repair packet or raw wave data.
-/

noncomputable section
open Set Metric Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation

abbrev ActualRepairCompactParameter (d : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

def actualRepairCompactParameterBase (d : ℕ) : ActualRepairCompactParameter d :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

theorem actualRepairCompactParameter_nonempty (d : ℕ) :
    Nonempty (ActualRepairCompactParameter d) :=
  ⟨actualRepairCompactParameterBase d⟩

/-- All compact samples and the full cover are actually constructed on the
same nonempty smooth compact parameter manifold. -/
theorem exists_actual_compact_parameter_atlas (d : ℕ) :
    ∃ A : BufferedAtlas (ActualRepairCompactParameter d) (EuclideanSpace ℝ (Fin d)),
      IsSmoothBufferedAtlas A ∧
      ∃ Q : Fin A.count → Set (EuclideanSpace ℝ (Fin d)),
        (∀ i, IsCompact (Q i) ∧ Q i ⊆ (A.chart i).target ∧
          closure (bufferedSamplingCoordinates A i) ⊆ Q i) ∧
        ∃ b : Fin A.count, actualRepairCompactParameterBase d ∈ A.inner b := by
  obtain ⟨A, hA, Q, hQ⟩ := parameterRound2_exists_compact_bufferedAtlas
    (E := EuclideanSpace ℝ (Fin d)) (P := ActualRepairCompactParameter d)
  exact ⟨A, hA, Q, hQ, A.cover (actualRepairCompactParameterBase d)⟩

/-- A concrete full compact parameter model with an actual globally smooth
bounded parameter, equal to the original parameter on its entire chosen
ball. The radius is positive and all coordinate norm costs remain explicit. -/
theorem exists_actual_compact_parameter_globalization (d : ℕ) :
    ∃ A : BufferedAtlas (ActualRepairCompactParameter d) (EuclideanSpace ℝ (Fin d)),
      IsSmoothBufferedAtlas A ∧ ∃ b : Fin A.count,
      let B := tensorChartFamilyOfAtlas A
      let p₀ := actualRepairCompactParameterBase d
      let u := actualRepairGlobalParameter B b p₀
      p₀ ∈ B.inner b ∧ 0 < actualRepairParameterRadius B ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, Fin d → ℝ) ∞ u ∧
      (∀ p, ‖u p‖ ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖ * B.buffer) ∧
      (∀ v : Fin d → ℝ, ‖v‖ < actualRepairParameterRadius B →
        u (actualRepairParameterMap B b p₀ v) = v) := by
  obtain ⟨A, hA, Q, hQ, b, hb⟩ := exists_actual_compact_parameter_atlas d
  refine ⟨A, hA, b, hb, actualRepairParameterRadius_pos _, ?_, ?_, ?_⟩
  · exact actualRepairGlobalParameter_smooth (tensorChartFamilyOfAtlas A)
      (fun i => hA.chart_mem i) b (actualRepairCompactParameterBase d) hb
  · exact actualRepairGlobalParameter_norm_le (tensorChartFamilyOfAtlas A) b
      (actualRepairCompactParameterBase d)
  · exact actualRepairGlobalParameter_local_identity (tensorChartFamilyOfAtlas A) b
      (actualRepairCompactParameterBase d) hb

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_actual_compact_parameter_atlas
#print axioms GlobalEmbedding.NormalPolar.exists_actual_compact_parameter_globalization
