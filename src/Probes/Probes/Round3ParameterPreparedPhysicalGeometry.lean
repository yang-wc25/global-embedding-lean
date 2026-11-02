import Probes.ActualIncrementOriginalPhysicalGeometry
import Smoothing.Round3ParameterCanonicalMeanReserveSupply
import Smoothing.Round3ParameterOriginalCanonicalMeanAtlas
import Probes.Round3ParameterOriginalMeanPreparation
import Probes.Round3ParameterOriginalActiveRawProfiles
import Probes.Round3ParameterOriginalActiveMeanPrimitives
import Smoothing.Round3ParameterOriginalClosedMeanAtlas
import Smoothing.Round3ParameterMeanReserveSupply
import Smoothing.ParameterRound2OriginalGermReserveBall
import Smoothing.ParameterRound2IdentityRefinementSamples
import Smoothing.ParameterRound2IdentityRawCosts
/-! Original C0 closeness constructs a common genuine positive neighborhood
for a finite list of actual native tensors. The same actual original primary
family, restricted to this one neighborhood, then supplies every mean
primitive for every input. No computed mean/source/output estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
variable {Β : Type*} [Fintype Β]

local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance meanPrimitiveSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance meanPrimitiveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance meanPrimitiveGeometryFirstNormed : NormedAddCommGroup (Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFirstSpace : NormedSpace ℝ (Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryHessianNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryHessianSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryT0Normed : NormedAddCommGroup (Es →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveGeometryT0Space : NormedSpace ℝ (Es →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCjetNormed : NormedAddCommGroup (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCjetSpace : NormedSpace ℝ (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCANormed : NormedAddCommGroup
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCASpace : NormedSpace ℝ
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance finiteArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance finiteArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance finiteArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private theorem preparedPhysical_restricted_heq
    {Sub Label : Type*} [Fintype Sub] [Fintype Label]
    {F F' : Ep → M → V} (hEq : F = F')
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (hF' : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F')
    (hg : HEq g g') (W : Set (Ep × M)) (hW : IsOpen W) :
    Nonempty (ActualOriginalPrimaryPhysicalGeometry F hF
      (parameterRound2_restrictPrimaryFamily F g W hW)) ↔
    Nonempty (ActualOriginalPrimaryPhysicalGeometry F' hF'
      (parameterRound2_restrictPrimaryFamily F' g' W hW)) := by
  cases hEq
  cases eq_of_heq hg
  rfl

theorem round3Parameter_prepared_native_physical_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hAll : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lprimary : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (z : Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT
      Tinv Forward Meta Rsub Lprimary i) :
    Nonempty (ActualOriginalPrimaryPhysicalGeometry
      (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
      (fun p => hF ((Data.parameterChart i.2).symm p))
      (round3ParameterNativePrimary (fun p x => Data.F (p,x))
        (round3Parameter_restrictPrimaryFamily (fun p x => Data.F (p,x)) g univ isOpen_univ)
        (Data.parameterChart i.2))) := by
  let F := actualOriginalOpenParameterSlice Data i
  let hFn := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
  let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)
  let g0 := actualOriginalPrimaryFamily Data hd hs hn i z.host z.native z.slices z.data gN.eta z.active
  let W := actualOriginalParameterNeighborhood Data i.2 univ
  let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 univ isOpen_univ
  have phys := actualOriginalPrimaryFamily_physical_geometry Data hd hs hn i z.host z.native
    z.slices z.data gN.eta z.active hImm univ isOpen_univ cT hcT z.transverse
  have h' := (preparedPhysical_restricted_heq
    (round3Parameter_original_open_slice_eq_global Data hd hAll i) hFn
    (fun p => hF ((Data.parameterChart i.2).symm p)) g0 gN z.same W hW).mp phys
  rw [round3Parameter_native_primary_restriction_commutes]
  have hW' : W = round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)) := by
    ext w
    simp only [W,actualOriginalParameterNeighborhood,round3ParameterNativeDomain,mem_inter_iff,
      mem_prod,mem_univ,mem_preimage,mem_setOf_eq,and_true]
  simpa only [gN,hW'] using h'

#print axioms round3Parameter_prepared_native_physical_geometry
end GlobalEmbedding.Continuation
