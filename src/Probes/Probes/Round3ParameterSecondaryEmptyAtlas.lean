import Probes.Round3ParameterPreparedSecondaryFamily
import Probes.Round3ParameterNativeFamily
import Probes.Round3ParameterRawAtlasData

/-! The genuine empty-atlas branch. The buffered cover forces M to be
empty, while the original primary and secondary Sigma indices are empty.
Every native record is constructed directly, including its physical geometry;
no spatial base chart or nonempty-manifold assumption is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  {Β : Type uPrimary} {SubSecondary : Type uSecondary}
  [Fintype Β] [Fintype SubSecondary] [IsEmpty Β] [IsEmpty SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def round3Parameter_secondary_empty_atlas_native_family
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hEmpty : Data.atlas.count = 0)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W G : Set (Ep × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
      ActualOriginalSecondaryChoice Ep M m) :
    Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data F hF g q ell W G Mrest Kcut Tinv Tobs Rsecondary S := by
  letI : IsEmpty (Fin Data.atlas.count) := ⟨fun i => by have hi := i.isLt; omega⟩
  letI : IsEmpty M := ⟨fun x => by obtain ⟨i,hi⟩ := Data.atlas.cover x; exact isEmptyElim i⟩
  refine {
    choice := choice
    geometry := fun _ _ a => isEmptyElim a
    hCoordinate := fun _ _ a => isEmptyElim a
    hChart := fun _ _ a => isEmptyElim a
    hPhase := fun _ _ a => isEmptyElim a
    hHost := fun _ a => isEmptyElim a
    hHostInv := fun _ a => isEmptyElim a
    hHostSource := fun _ _ a => isEmptyElim a
    hSupport := fun _ _ a => isEmptyElim a
    hPair := fun _ _ a => isEmptyElim a
    hPartition := fun _ y => isEmptyElim y.2
    hCut := fun _ _ a => isEmptyElim a
    hInv := fun _ _ a => isEmptyElim a
    hCutJets := fun _ _ a => isEmptyElim a
    hInvJets := fun _ _ a => isEmptyElim a
    hostIndex := fun _ a => isEmptyElim a
    hHostIndex := fun _ a => isEmptyElim a
    hNativeSamples := fun _ _ a => isEmptyElim a
    primaryGeometry := {
      slices := fun _ a => isEmptyElim a
      maximal := fun _ a => isEmptyElim a
      inverse := fun _ a => isEmptyElim a
      target := fun _ a => isEmptyElim a
      immersion := fun _ a => isEmptyElim a
      gram := fun _ a => isEmptyElim a
      normalKernel := fun _ a => isEmptyElim a
      adaptation := fun _ a => isEmptyElim a }
    hOriginal := ?_
    hChartInv := fun _ _ a => isEmptyElim a
    hObserverNativeSamples := fun _ _ _ a => isEmptyElim a
    hObserverJets := fun _ _ _ a => isEmptyElim a
    hObserverCount := fun _ i => isEmptyElim i.1 }
  intro y
  exact isEmptyElim y.2

theorem round3Parameter_secondary_empty_atlas_families
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hEmpty : Data.atlas.count = 0)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W : Set (P × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (m+1+d) → ℝ))
    (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
      Round3ParameterSecondaryChoice P M m) :
    ∃ family : ∀ ip : Fin Data.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Data.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        Mrest Kcut Tinv Tobs Rsecondary
        (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip)),
      ∀ ip, (family ip).choice = round3ParameterNativeChoices choice (Data.parameterChart ip) := by
  refine ⟨fun ip => round3Parameter_secondary_empty_atlas_native_family Data hEmpty
    (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
    (round3ParameterNativePrimary F g (Data.parameterChart ip)) q ell
    (round3ParameterNativeDomain (Data.parameterChart ip) W)
    (round3ParameterNativeDomain (Data.parameterChart ip) W) Mrest Kcut Tinv Tobs Rsecondary
    (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip))
    (round3ParameterNativeChoices choice (Data.parameterChart ip)),fun _ => rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_empty_atlas_native_family
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_empty_atlas_families
