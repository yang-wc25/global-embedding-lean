import Probes.Round3ParameterPreparedSecondaryFamily
import Probes.ActualSecondaryGeometryBudgets

/-! Prescribed reference profiles can dominate the actual prepared profiles
without choosing another chart, cutoff, support, sample or increment. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def Round3ParameterPreparedSecondaryFamily.round3Repair_enlargeProfiles
    {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {F : Ep → M → V} {hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t)}
    {g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F}
    {q : ℕ} {ell : ℝ} {W G : Set (Ep × M)}
    {Mrest Kcut Tinv Tobs : ℕ → ℝ} {Rsecondary : ℕ}
    {NativeSamples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    (old : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data F hF g q ell W G
      Mrest Kcut Tinv Tobs Rsecondary NativeSamples)
    (Mnew Knew Tnew Onew : ℕ → ℝ) (Rnew : ℕ)
    (hM : ∀ j, Mrest j ≤ Mnew j) (hK : ∀ j, Kcut j ≤ Knew j)
    (hT : ∀ j, Tinv j ≤ Tnew j) (hO : ∀ j, Tobs j ≤ Onew j)
    (hR : Rsecondary ≤ Rnew) :
    Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data F hF g q ell W G
      Mnew Knew Tnew Onew Rnew NativeSamples := {
    old with
    geometry := fun j r a => (old.geometry j r a).enlargeBudget (hM j)
    hCutJets := fun j r a k hk z hz => (old.hCutJets j r a k hk z hz).trans (hK j)
    hInvJets := fun j r a k hk hkj z hz => (old.hInvJets j r a k hk hkj z hz).trans (hT k)
    hObserverJets := fun j i r a z hz k hk hkj => (old.hObserverJets j i r a z hz k hk hkj).trans (hO k)
    hObserverCount := fun j i r z hz => (old.hObserverCount j i r z hz).trans hR }

theorem Round3ParameterPreparedSecondaryFamily.round3Repair_enlargeProfiles_choice
    {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {F : Ep → M → V} {hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t)}
    {g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F}
    {q : ℕ} {ell : ℝ} {W G : Set (Ep × M)}
    {Mrest Kcut Tinv Tobs : ℕ → ℝ} {Rsecondary : ℕ}
    {NativeSamples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    (old : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data F hF g q ell W G
      Mrest Kcut Tinv Tobs Rsecondary NativeSamples)
    (Mnew Knew Tnew Onew : ℕ → ℝ) (Rnew : ℕ)
    (hM : ∀ j, Mrest j ≤ Mnew j) (hK : ∀ j, Kcut j ≤ Knew j)
    (hT : ∀ j, Tinv j ≤ Tnew j) (hO : ∀ j, Tobs j ≤ Onew j)
    (hR : Rsecondary ≤ Rnew) :
    (old.round3Repair_enlargeProfiles Mnew Knew Tnew Onew Rnew hM hK hT hO hR).choice = old.choice := rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.Round3ParameterPreparedSecondaryFamily.round3Repair_enlargeProfiles
