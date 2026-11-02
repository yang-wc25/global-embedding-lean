import OriginalIncrements.AlgebraicChosenPhaseGood
import OriginalIncrements.NativePhaseOperatorSmooth
import OriginalIncrements.CompactNativeRestrictionReserve
import Probes.Round3PreparedPrimaryPhase

/-! The original chosen primary Good condition gives a genuine coordinate
kernel reserve on a compact neighborhood, without imposing a reserve on
unused portions of the original primary domain and without any auxiliary
norm or RiemannianBundle premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation.OriginalIncrements
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance primaryCompactRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance primaryCompactSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_primary_native_good
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (z : X) (hz : z∈actualOriginalPrimaryNativeOpen Data nu i) :
    LinearSecondFormGoodCovector
      (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
        (fun _=>Data.atlas.chart i.1) z).toLinearMap
      (fderiv ℝ (fun x : D => Data.phase nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2).toLinearMap := by
  have hActive := round3_prepared_native_primary_active Data i nu hz
  let F := actualOriginalOpenParameterSlice Data i
  let host := Data.atlas.chart i.1
  let psi := fun x : M=>Data.phase nu ((Data.parameterChart i.2).symm z.1,x)
  have hGood : GoodCovector (F z.1) (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
      (host.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (host.symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2))) := by
    have htransport (f : M → V) (hf : ContMDiff 𝓙 𝓘(ℝ,V) ∞ f)
        (heq : f=fun x=>Data.F ((Data.parameterChart i.2).symm z.1,x)) :
        GoodCovector f hf (host.symm z.2)
          ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (host.symm z.2))).toContinuousLinearMap.comp
            (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2))) := by
      subst f
      exact hp.primary_good nu _ hActive
    exact htransport _ _ (actualOriginalOpenParameterSlice_eq Data i z.1 hActive.2.1)
  have hNative := round3_prepared_primary_native_subset Data i nu hz
  exact original_good_phase_native_operator_algebraic F
    (actualOriginalOpenParameterSlice_contMDiff Data hd hs i) host (hd.atlas_smooth.chart_mem i.1)
    (actualOriginalNativeOpen Data i) (actualOriginalNativeOpen_isOpen Data hd i)
    (actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i)
    z hNative (actualOriginalNativeMap_source_target Data i hNative.1) psi hGood

theorem original_primary_compact_reserve
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (K : Set X) (hK : IsCompact K)
    (hKPrimary : K⊆actualOriginalPrimaryNativeOpen Data nu i) :
    ∃ (kernel : ℝ) (O : Set X), 0<kernel ∧ IsOpen O ∧ K⊆O ∧
      O⊆actualOriginalPrimaryNativeOpen Data nu i ∧
      ∀z∈O, ∀v, kernel*‖v‖ ≤ ‖covectorRestriction
        (round4ActualPhaseOperatorInChart
          (fun p x=>Data.F ((Data.parameterChart i.2).symm p,x))
          (fun _=>Data.atlas.chart i.1) z)
        (fderiv ℝ (fun x : D => Data.phase nu
          ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2) v‖ := by
  let U := actualOriginalPrimaryNativeOpen Data nu i
  let B := round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
    (fun _=>Data.atlas.chart i.1)
  let phase := fun z : X=>Data.phase nu ((Data.parameterChart i.2).symm z.1,
    (Data.atlas.chart i.1).symm z.2)
  let xi := fun z : X=>fderiv ℝ (fun x : D=>phase (z.1,x)) z.2
  have hU : IsOpen U := actualOriginalPrimaryNativeOpen_isOpen Data hd nu i
  have hNative : U⊆actualOriginalNativeOpen Data i := round3_prepared_primary_native_subset Data i nu
  have hB : ContinuousOn B U :=
    ((original_native_phase_operator_contDiffOn Data hd hs hImm i).mono hNative).continuousOn
  have hPhase : ContDiffOn ℝ ∞ phase U := round3_actual_original_primary_native_phase_smooth Data hd hs nu i
  have hxi : ContinuousOn xi U := (incrementsJointSpatialJets_bridge phase U hU hPhase).2.1.continuousOn
  obtain ⟨kernel,O,hKernel,hO,hKO,hOU,hLower⟩ := compact_native_restriction_reserve B xi K U
    hK hU hKPrimary hB hxi (fun z hz=>original_primary_native_good Data hd hs hp i nu z (hKPrimary hz))
  refine ⟨kernel,O,hKernel,hO,hKO,hOU,?_⟩
  intro z hz v
  have hSlice : actualOriginalOpenParameterSlice Data i z.1 =
      fun x=>Data.F ((Data.parameterChart i.2).symm z.1,x) :=
    actualOriginalOpenParameterSlice_eq Data i z.1
      (actualOriginalNativeOpen_parameter Data i (hNative (hOU hz)))
  have hOperator : B z = round4ActualPhaseOperatorInChart
      (fun p x=>Data.F ((Data.parameterChart i.2).symm p,x))
      (fun _=>Data.atlas.chart i.1) z :=
    congrArg (fun f : M → V => round4ActualPhaseOperatorInChart
      (fun _ : Ep=>f) (fun _=>Data.atlas.chart i.1) z) hSlice
  have h := hLower z hz v
  rw [hOperator] at h
  exact h


end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_native_good
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_compact_reserve
