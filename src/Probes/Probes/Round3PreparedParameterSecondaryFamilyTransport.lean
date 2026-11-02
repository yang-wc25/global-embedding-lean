import Probes.Round3ParameterSecondaryCommonFamily
import Probes.Round3ParameterCrossNativeFamily

/-! Exact transport between the original open slice and the same physical
map in a canonical observer chart. Equality elimination changes only the
dependent map type; the full primary and secondary choices are preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
universe uM uP uB uS
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  {Β : Type uB} {SubSecondary : Type uS} [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 def round3PreparedPrimaryAtMap
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F F' : Ep → M → Ey) (hEq : F = F')
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F') :
    IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F := by
  cases hEq
  exact g

 theorem round3_prepared_primary_at_map_fields
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F F' : Ep → M → Ey) (hEq : F = F')
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F') :
    HEq (round3PreparedPrimaryAtMap Data F F' hEq g) g ∧
    (round3PreparedPrimaryAtMap Data F F' hEq g).phase = g.phase ∧
    (round3PreparedPrimaryAtMap Data F F' hEq g).cutoff = g.cutoff := by
  cases hEq
  exact ⟨HEq.rfl,rfl,rfl⟩

 def round3PreparedPrimaryPhysicalAtMap
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F F' : Ep → M → Ey) (hEq : F = F')
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (hF' : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F')
    (geometry : ActualOriginalPrimaryPhysicalGeometry F' hF' g) :
    ActualOriginalPrimaryPhysicalGeometry F hF (round3PreparedPrimaryAtMap Data F F' hEq g) := by
  cases hEq
  exact geometry

 theorem round3_prepared_secondary_family_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F F' : Ep → M → Ey) (hEq : F = F')
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (hF' : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F') (hg : HEq g g')
    (q : ℕ) (ell : ℝ) (W G : Set (Ep × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (Samples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X)
    (family : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary)
      Data F hF g q ell W G Mrest Kcut Tinv Tobs Rsecondary Samples) :
    ∃ out : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary)
      Data F' hF' g' q ell W G Mrest Kcut Tinv Tobs Rsecondary Samples,
      out.choice = family.choice := by
  cases hEq
  cases eq_of_heq hg
  exact ⟨family,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_secondary_family_transport
