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

theorem round3Parameter_secondary_domain_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W W' : Set (Ep × M)) (hW : W=W')
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Ep × D))
    (family : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data F hF g q ell
      W W Mrest Kcut Tinv Tobs Rsecondary S) :
    ∃ out : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data F hF g q ell
      W' W' Mrest Kcut Tinv Tobs Rsecondary S, out.choice=family.choice := by
  cases hW
  exact ⟨family,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_domain_transport
