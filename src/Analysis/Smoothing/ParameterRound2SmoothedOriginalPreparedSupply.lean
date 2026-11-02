import Smoothing.ParameterRound2SmoothedOriginalPreparedStatement
import Smoothing.ParameterRound2OriginalSmoothingStageData
import Smoothing.ParameterRound2IdentityParameterJets
import Smoothing.ParameterRound2ActualFinalRawProfiles
import Smoothing.ParameterRound2MeanRawFixedNeighborhoodSupply
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

variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
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

theorem exists_uniform_parameterRound2_smoothed_original_prepared_supply
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (smoothingRadius : ℝ) (hSmoothingRadius : 0 < smoothingRadius) (q : ℕ) (hq : 1 ≤ q) :
    ∃ Cmap : ℕ → ℝ, ∃ hCmap : ∀ j, 0 ≤ Cmap j,
    ∃ Ctarget : ℕ → ℝ, ∃ hCtarget : ∀ j, 0 ≤ Ctarget j,
    ParameterRound2SmoothedOriginalPreparedStatement (m := m) (d := d) (N := N) (M := M) (Β := Β)
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp smoothingRadius hSmoothingRadius q hq
      Cmap hCmap Ctarget hCtarget := by
  obtain ⟨Cmap,hCmap,Ctarget,hCtarget,hstageProducer⟩ :=
    exists_uniform_parameterRound2_original_stage_data_profiles
      (n := m+1) (d := d) (N := N) (M := M) (P := Ep)
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp smoothingRadius hSmoothingRadius q
  refine ⟨Cmap,hCmap,Ctarget,hCtarget,?_⟩
  unfold ParameterRound2SmoothedOriginalPreparedStatement
  intro Data budget reference givenPacket stage hd hs hn hp i hId hOne host b e hdata eta hactive hImm hsource
    c cT Bnative hEll hcT hBnative hnative hTreserve hLinear hDecompOriginal rho hReserve Vprep hVprep hKVprep
    Rsub Lprimary Tinv Forward Meta hTinv hForward hMeta
    ell hS B0 Packet ML hPacket0 F hF g0 hRef S W0 p radius Bnd Mg Dinput Tfixed
  obtain ⟨H,hH,hHbudget,hProfiles⟩ := hstageProducer Data budget reference givenPacket stage
  have hfinite : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hProfiles 0).1 (actualOriginalGivenInputProfile_core_le Data 0 ell)
  have hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hProfiles 0).1 (actualOriginalGivenInputProfile_linear_le Data 0 ell)
  have hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML :=
    (ENNReal.toReal_mono (hProfiles 0).1 (actualOriginalGivenInputProfile_linear_le Data 0 ell)).trans (hProfiles 0).2
  have hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤ := fun n => (hProfiles n).1
  have hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n := fun n => (hProfiles n).2
  have hSupply := parameterRound2_identity_original_prepared_canonical_supply Data hd hs hn hp i hId hOne
    host b e hdata eta hactive hImm hsource ell c cT Bnative stage.ell_pos (stage.ell_le_t.trans stage.t_le_one)
    hEll hcT hBnative hfinite hnative hTreserve hLinear hDecompOriginal rho hReserve Vprep hVprep hKVprep
    hS ML hProfile hML q Rsub Lprimary Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket hRef
  exact ⟨hSupply.1,H,hH,hHbudget,hSupply.2 H hH⟩

#print axioms exists_uniform_parameterRound2_smoothed_original_prepared_supply
end GlobalEmbedding.Continuation
