import Probes.Round3ParameterSecondaryEmptyAtlas

/-! A real spatial base chart is used only when one exists. Original Sigma
indices carry their original host index, so an empty atlas makes both index
types empty and the already proved empty construction applies. This removes
the implementation's base-chart argument from the global primary/secondary
consumer without adding nonemptiness to the original theorem. -/
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
  {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def Round3ParameterCoherentSecondaryOutput
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W : Set (P × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (m+1+d) → ℝ)) : Prop :=
    ∃ choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
      Round3ParameterSecondaryChoice P M m,
      (∀ r a, Round3ParameterChartPreserves (choice r a).chart) ∧
    ∃ family : ∀ ip : Fin Data.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Data.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        Mrest Kcut Tinv Tobs Rsecondary
        (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip)),
      ∀ ip, (family ip).choice = round3ParameterNativeChoices choice (Data.parameterChart ip)

theorem round3Parameter_secondary_factory_without_base_chart
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (primaryHost : Β → Fin Data.atlas.count)
    (secondaryHost : SubSecondary → Fin Data.atlas.count)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W : Set (P × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (m+1+d) → ℝ))
    (nonemptyFactory : ∀ base : Fin Data.atlas.count,
      Round3ParameterCoherentSecondaryOutput (SubSecondary := SubSecondary) Data F hF g q ell W
        Mrest Kcut Tinv Tobs Rsecondary S) :
    Round3ParameterCoherentSecondaryOutput (SubSecondary := SubSecondary) Data F hF g q ell W
      Mrest Kcut Tinv Tobs Rsecondary S := by
  by_cases hEmpty : Data.atlas.count = 0
  · letI : IsEmpty (Fin Data.atlas.count) := ⟨fun i => by have hi := i.isLt; omega⟩
    letI : IsEmpty Β := ⟨fun a => isEmptyElim (primaryHost a)⟩
    letI : IsEmpty SubSecondary := ⟨fun a => isEmptyElim (secondaryHost a)⟩
    let choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
        Round3ParameterSecondaryChoice P M m := fun _ a => isEmptyElim a
    obtain ⟨family,hChoice⟩ := round3Parameter_secondary_empty_atlas_families Data hEmpty F hF g
      q ell W Mrest Kcut Tinv Tobs Rsecondary S choice
    exact ⟨choice,fun _ a => isEmptyElim a,family,hChoice⟩
  · exact nonemptyFactory ⟨0,Nat.pos_of_ne_zero hEmpty⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_factory_without_base_chart
