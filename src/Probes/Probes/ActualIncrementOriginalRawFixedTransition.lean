import Probes.ActualIncrementOriginalRawProducer
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle Filter
open scoped ContDiff Topology BigOperators TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance marginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance marginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance marginCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance marginCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance marginCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace

private local instance rawCoeffInnerNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffInnerSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance rawCoeffOuterNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffOuterSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {Β : Type*} [Fintype Β]


private theorem original_native_differentiation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X)
    (hp : z.1 ∈ (Data.parameterChart i.2).target) (hx : z.2 ∈ (Data.atlas.chart i.1).target) :
    parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i := by
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) = z :=
    (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
  have hp' := congrArg Prod.fst hprod
  have hx' := congrArg Prod.snd hprod
  dsimp only at hp' hx'
  exact ⟨hx'.symm ▸ hx,hp'.symm ▸ hp⟩

theorem actualOriginalPrimaryFamily_raw_profiles_fixed_transition
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (G : Set (P × M)) (hG : IsOpen G)
    (observer : Fin Data.atlas.count)
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (Told : ℕ → ℝ)
    (ell tau Delta : ℝ) (hell : 0 < ell)
    (Packet Forward : ℕ → ℝ) (hForward0 : ∀ r, 0 ≤ Forward r)
    (hGiven : ∀ r, actualOriginalGivenInputProfile Data r ell ≠ ⊤)
    (hPacket : ∀ r, (actualOriginalGivenInputProfile Data r ell).toReal ≤ Packet r) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let g := parameterRound2_restrictPrimaryFamily F g0 W hW
    let primary := fun nu => W ∩
      (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu
    let obs := Data.atlas.chart observer
    let oi := (observer,i.2)
    let a := parameterTensorModelEquiv (m+1) d
    let kappa := fun z : X => (z.1,obs.symm z.2)
    let O := actualRawObserverOpen obs W
    let S := a ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet oi
    let R := fun nu => S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff nu)
    let Rloc := fun nu beta => R nu ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta nu beta z*g.cutoff nu z)
    let Tfixed := fun k => actualFastChartTransferCost
      (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d k*Packet k) k*Forward k
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) →
    (hForward : ∀ r nu beta k, 1 ≤ k → k ≤ r+1 → ∀ z ∈ Rloc nu beta,
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta) (actualOriginalObserverHostTransition Data oi (host nu beta) z)‖ ≤ Forward r) →
    ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary reserve Bnd Mg Told
      F hF g input inputbar W primary obs O S tau ell Delta →
    (∀ k, 0 ≤ Tfixed k) ∧ Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ)
      n length j Rsub Lprimary reserve Bnd Mg Tfixed
      F hF g input inputbar W primary obs O S tau ell Delta) := by
  intro F hF g0 W hW g primary obs oi a kappa O S R Rloc Tfixed input inputbar hForward data
  have hObsInv := contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem observer)
  have dom := actual_raw_observer_domains F hF g input W primary data.prim obs hObsInv S data.hSO
  let U := fun nu beta => O ∩ kappa ⁻¹' (g.chart nu beta).source
  have hRlocU (nu) (beta) : Rloc nu beta ⊆ U nu beta := by
    intro z hz
    exact (dom.2.2.2.2 nu beta).2.1 ⟨(dom.2.2.2.1 nu).2.1 hz.1,hz.2⟩
  have hOverlap (nu) (beta) : U nu beta ⊆
      actualOriginalNativeGivenTransitionDomain Data (oi,(host nu beta,i.2)) := by
    intro z hz
    refine ⟨original_native_differentiation Data oi z hz.1.2.1.1 hz.1.1.2,?_⟩
    simp only [mem_preimage]
    rw [actual_original_jointPoint_native]
    exact ⟨(Data.parameterChart i.2).map_target hz.1.2.1.1,hz.2.1.1.2⟩
  have hObserver (r) (nu) (beta) := actual_original_observer_adapted_positive_jets Data hd oi (host nu beta)
    (b nu beta) ((actual_host_slice_geometry_inputs _ (hd.atlas_smooth.chart_mem (host nu beta))
      _ _ _ (hdata nu beta)).2.1)
    (U nu beta) (Rloc nu beta) (dom.2.2.2.2 nu beta).1 (hRlocU nu beta) (hOverlap nu beta)
    (fun z hz => hz.2.1.2) (fun z hz => ⟨hz.1.1,hOverlap nu beta (hRlocU nu beta hz)⟩)
    r ell (Packet r) (Forward r) hell (hForward0 r) (hGiven r) (hPacket r) (hForward r nu beta)
  refine ⟨?_,⟨{ data with hphib := ?_ }⟩⟩
  · intro k
    apply mul_nonneg _ (hForward0 k)
    apply actualFastChartTransferCost_nonneg
    intro r
    exact mul_nonneg (actualOriginalNativeGivenTransitionJetCost_nonneg _ _ _) (ENNReal.toReal_nonneg.trans (hPacket k))
  · intro nu beta k hk hkj z hz
    exact (hObserver k nu beta).2 k hk (by omega) z hz

#print axioms actualOriginalPrimaryFamily_raw_profiles_fixed_transition
end GlobalEmbedding.Continuation
