import Probes.Round3PreparedParameterSecondaryChartProfiles
import Probes.Round3PreparedParameterSecondaryStableFamily
import Probes.Round3ParameterStageFamilyFunctions

/-! The all-B reference profiles are retained by the actual current stable
signed pieces. No compact maximum is taken on the current SF. Source/target
membership is proved anew on the SAME effective carrier; all derivative
functions are transported by literal full-function equalities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 theorem round3_prepared_parameter_secondary_stable_functions
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (old : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3PreparedParameterStableSecondaryPiece Ref hd hs i r W old F hF)
    (observer : Fin Ref.parameterCount) :
    let choice0 := round3PreparedParameterSecondaryChoice Ref hd hs i r W old
    let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r W stable.piece
    let c0 := (choice0.pullback (Ref.parameterChart observer)).toNative
    let c := (choice.pullback (Ref.parameterChart observer)).toNative
    choice.cutoff = choice0.cutoff ∧ c.cutoff = c0.cutoff ∧
      (c.chart : Ep × M → X) = c0.chart ∧ (c.chart.symm : X → Ep × M) = c0.chart.symm := by
  intro choice0 choice c0 c
  have hEta : choice.cutoff = choice0.cutoff := by
    change round3ParameterSupportedPullback _ stable.piece.cutoff = round3ParameterSupportedPullback _ old.cutoff
    rw [stable.cutoff]
  have hAdapt :
      ((actualHostAdaptedChart (Ref.atlas.chart i.1) stable.piece.native : Ep × M → X) =
        actualHostAdaptedChart (Ref.atlas.chart i.1) old.native) ∧
      (((actualHostAdaptedChart (Ref.atlas.chart i.1) stable.piece.native).symm : X → Ep × M) =
        (actualHostAdaptedChart (Ref.atlas.chart i.1) old.native).symm) := by
    constructor
    · funext z
      change stable.piece.native (z.1,Ref.atlas.chart i.1 z.2) = old.native (z.1,Ref.atlas.chart i.1 z.2)
      rw [stable.forward]
    · funext z
      change ((stable.piece.native.symm z).1,(Ref.atlas.chart i.1).symm (stable.piece.native.symm z).2) =
        ((old.native.symm z).1,(Ref.atlas.chart i.1).symm (old.native.symm z).2)
      rw [stable.inverse]
  have hGlobal := round3Parameter_chart_pullback_functions_congr (Ref.parameterChart i.2).symm
    (actualHostAdaptedChart (Ref.atlas.chart i.1) stable.piece.native)
    (actualHostAdaptedChart (Ref.atlas.chart i.1) old.native) hAdapt.1 hAdapt.2
  have hNative := round3Parameter_chart_pullback_functions_congr (Ref.parameterChart observer)
    choice.chart choice0.chart hGlobal.1 hGlobal.2
  exact ⟨hEta,by funext z; exact congrFun hEta _,hNative.1,hNative.2⟩

 theorem round3_prepared_actual_parameter_secondary_stable_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i)) :
    ∃ Forward Inverse Kcut : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Kcut k) ∧
      ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
      ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece
      let native := (choice.pullback (Ref.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart observer.1)).symm.trans native.chart
      let rho := fun z : X => native.cutoff (native.chart.symm z)
      ∀ k z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
        Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet observer →
        ((Ref.parameterChart observer.2).symm z.1,(Ref.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Ref r choice →
        z ∈ t.source ∧ t z ∈ t.target ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k ∧
        ell^k*‖iteratedFDeriv ℝ k rho (t z)‖ ≤ Kcut k := by
  obtain ⟨Tf,Ti,Te,hTf,hTi,hTe,hProfiles⟩ := round3_prepared_actual_parameter_secondary_chart_profiles Ref hd hs theta packet
    (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet)
    hS (fun _ _ hz => hz.1)
  refine ⟨Tf,Ti,Te,hTf,hTi,hTe,?_⟩
  intro F hF stable ell hell hell1 r i a observer choice native t rho k z hz hCarrierZ
  let choice0 := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (packet.piece r i a)
  let native0 := (choice0.pullback (Ref.parameterChart observer.2)).toNative
  let q := (OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart observer.1)
  let t0 := q.symm.trans native0.chart
  have hEqual := round3_prepared_parameter_secondary_stable_functions Ref hd hs i r _ (packet.piece r i a) F hF (stable r i a) observer.2
  have hC : round3PreparedParameterSecondaryCarrier Ref r choice =
      round3PreparedParameterSecondaryCarrier Ref r choice0 := by
    unfold round3PreparedParameterSecondaryCarrier
    rw [hEqual.1]
  have hCarrier0 := hC ▸ hCarrierZ
  have hOld := hProfiles ell hell hell1 r i a observer k z hz hCarrier0
  have hTF : (t : X → X) = t0 := by
    funext y
    exact congrFun hEqual.2.2.1 (q.symm y)
  have hTI : (t.symm : X → X) = t0.symm := by
    funext y
    exact congrArg q (congrFun hEqual.2.2.2 y)
  have hEta : rho = fun y : X => native0.cutoff (native0.chart.symm y) := by
    funext y
    change native.cutoff (native.chart.symm y) = _
    rw [hEqual.2.1,hEqual.2.2.2]
  have hParent : tsupport choice.cutoff ⊆ tsupport (theta i) := by
    rw [hEqual.1]
    exact packet.parent r i a
  have hSource := (round3_prepared_parameter_secondary_carrier_source Ref hd hs i r (stable r i a).piece
    (theta i) (hSupport i) hParent).1
  have hNativeEval := (actual_original_native_evaluation_iff Ref hd observer z).mp hz
  have hp : z.1 ∈ (Ref.parameterChart observer.2).target := hd.parameter_norm_subset observer.2 hNativeEval.2.1
  have hx : z.2 ∈ (Ref.atlas.chart observer.1).target := hd.source_norm_subset observer.1 hNativeEval.1
  have hsrc : z ∈ t.source := by
    refine ⟨⟨mem_univ _,hx⟩,?_⟩
    apply (round3ParameterChartPullback_source_iff (Ref.parameterChart observer.2) choice.chart
      (round3_prepared_parameter_secondary_preserves Ref hd hs i r _ (stable r i a).piece)
      (z.1,(Ref.atlas.chart observer.1).symm z.2) hp).mpr
    exact hSource hCarrierZ
  refine ⟨hsrc,t.map_source hsrc,?_⟩
  simpa only [hTF,hTI,hEta] using hOld.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_parameter_secondary_stable_profiles
