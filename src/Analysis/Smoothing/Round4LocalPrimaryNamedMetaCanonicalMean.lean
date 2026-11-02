import Smoothing.Round3OuterOriginalAdmissibleParameterFactory
import Smoothing.Round4LocalPrimaryNamedMetaPhysicalFactory
import Probes.Round4ParameterStageDataProfiles
import Smoothing.Round3OuterStageDataProfiles
import Smoothing.Round3RepairNormalStage

/-! The ordinary reference cutoff profile is used numerically in the actual
canonical raw reserve supply; the whole fixed-carrier profile remains separate
geometric evidence. Both refer to the same reference and physical family.

The actual admissible normal stage produces its mean operator and raw
canonical reserve supply on the same physical family, retaining every exact
original observer set and the true native physical geometry for secondary
assembly. All native charts and frame
reserves are recovered from the SAME stable reference witness. The actual
smoother internally supplies every given-input budget, including the linear
zero-order bound. No mean, solver, or new-map derivative estimate is a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal TensorProduct
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
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance outerStableMeanSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance outerStableMeanSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance outerStableMeanGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance outerStableMeanGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance outerStableMeanCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance outerStableMeanCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance outerStableMeanCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableMeanCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance outerStableMeanCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableMeanCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance outerStableMeanCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableMeanCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance outerStableArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance outerStableArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round4_local_primary_named_meta_canonical_mean_from_stable
    (BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC GeometryMeta MetaC : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hInverseC : ∀ j, 0 ≤ InverseC j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (q : ℕ) (budget lower : ℝ) :
    let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∀ (Ref : IncrementsOriginalNativeData (m+1) d N M P)
      (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
      (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
      (hAll : Ref.parameterSet = univ) (hLinearRef : IncrementsOriginalLinearSmoothInputs Ref)
      (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
      (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (F : P × M → Ey)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius q budget reference Given),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference Given stage) p
    ∀ stable : Round3ParameterWholeStableReference Ref hdRef hsRef theta packet profiles
        (fun p x => F (p,x)) hF,
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterStablePrimaryPacket Ref hdRef hsRef theta packet profiles (fun p x => F (p,x)) hF stable)
    ∀ (R Lprimary : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
      (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
      (hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g0.eta nu)))
      (hProfiles : Round3ParameterOriginalChartProfiles Ref
        (round3ParameterFixedCarrierFamily Ref g0 hOpen) ForwardC InverseC GeometryMeta)
      (hNamedProfiles : Round3ParameterOriginalChartProfiles Ref g0 ForwardC InverseC MetaC)
      (normal : Fin Ref.primaryCount → P × M → Ey),
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    let E := round3RepairRebindNormalData Data normal domain
    ∀ (rebound : Round3RepairNormalRebound stage normal domain Cnormal)
      (hImm : IncrementsOriginalSliceImmersionInputs E)
      (hp : IncrementsOriginalPhaseConditions E rebound.domain_conditions rebound.smooth_inputs)
      (hEll : IncrementsOriginalCoordinateEllipticityInputs E lower)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
      (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho),
    ∃ g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Ref.primaryCount) (Β := Round3ParameterWholePrimaryIndex Ref theta packet)
        (fun p x => F (p,x)),
      g.eta = (round3ParameterFixedCarrierFamily Ref g0 hOpen).eta ∧
      (∀ nu a, ((g.chart nu a) : P × M → P × D) =
        (round3ParameterFixedCarrierFamily Ref g0 hOpen).chart nu a) ∧
      (∀ nu a, ((g.chart nu a).symm : P × D → P × M) =
        ((round3ParameterFixedCarrierFamily Ref g0 hOpen).chart nu a).symm) ∧
      Round3ParameterOriginalPrimaryGeometry E g R ∧
      Round3ParameterOriginalChartProfiles E g ForwardC InverseC GeometryMeta ∧
      Round4ParameterOriginalGeneratedCanonicalSupply E hF g stage.samples_compact
        stage.ell lower (profiles.cT/16) rho (Packet 0) q R Lprimary Packet ForwardC InverseC MetaC ∧
      (∀ i : Fin E.atlas.count × Fin E.parameterCount,
        Nonempty (ActualOriginalPrimaryPhysicalGeometry
          (fun p x => E.F ((E.parameterChart i.2).symm p,x))
          (fun p => hF ((E.parameterChart i.2).symm p))
          (round3ParameterNativePrimary (fun p x => E.F (p,x))
            (round3Parameter_restrictPrimaryFamily (fun p x => E.F (p,x)) g univ isOpen_univ)
            (E.parameterChart i.2)))) := by
  intro Cmap Ctarget
  obtain ⟨hCmap,hCtarget,hBudget⟩ :=
    round4Parameter_actual_stage_data_named_profiles
      (n := m+1) (d := d) (N := N) (M := M) (P := P)
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q
  refine ⟨hCmap,hCtarget,?_⟩
  intro Packet Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles F H neighborhood Data stage hF
    stable g0 R Lprimary geom hLocal hOpen hProfiles hNamedProfiles normal domain E rebound hImm hp hEll hDecomp rho hReserve
  obtain ⟨e,hData,hNative,hActive,hInner,hChart,hFirst,hFrame,hRaw,hSlices⟩ :=
    round3_stable_primary_all_observer_data Ref hdRef hsRef hnRef theta packet profiles
      (fun p x => F (p,x)) hF stable
  let ps := round3OuterStablePrimaryPacket Ref hdRef hsRef theta packet profiles (fun p x => F (p,x)) hF stable
  let piece := round3ParameterWholePrimaryPiece Ref hdRef theta ps
  let host := fun nu (_ : Fin Ref.parameterCount) (a : Round3ParameterWholePrimaryIndex Ref theta packet) => (piece nu a).host
  let b := fun nu ip (a : Round3ParameterWholePrimaryIndex Ref theta packet) => round3ParameterCrossNativeChart
    (Ref.parameterChart a.1.2) (Ref.parameterChart ip) (piece nu a).native
  obtain ⟨hOpen',hCover,hSub,hNonzero,hGeom,rest⟩ := round3_parameter_original_fixed_carrier Ref g0 R geom
  have hLinearData : IncrementsOriginalLinearSmoothInputs Data := ⟨hLinearRef.linear_coordinates⟩
  have hLinear := round3_repair_rebind_linear Data normal domain
    (fun nu z hz => (hSub nu hz).1) hLinearData
  have hdec := round3_repair_rebind_decomposition Data normal domain hDecomp
  have hres := round3_repair_rebind_reserve Data normal domain rho hReserve
  obtain ⟨Kt,hKt,hKtBound,hGiven⟩ := hBudget E budget reference
    (fun j => max (Given j) (Cnormal j)) rebound.stage
  have hProfile (j : ℕ) : actualOriginalGivenInputProfile E j stage.ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile E j stage.ell).toReal ≤ Packet j := by
    rw [← rebound.ell_eq]
    exact hGiven j
  have hLinearFinite : incrementsOriginalInputProfileWithLinear E 0 stage.ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hProfile 0).1 (actualOriginalGivenInputProfile_linear_le E 0 stage.ell)
  have hML : (incrementsOriginalInputProfileWithLinear E 0 stage.ell).toReal ≤ Packet 0 :=
    (ENNReal.toReal_mono (hProfile 0).1 (actualOriginalGivenInputProfile_linear_le E 0 stage.ell)).trans
      (hProfile 0).2
  have hTransverse : ∀ (i : Fin Ref.atlas.count × Fin Ref.parameterCount) nu a z,
      z ∈ (b nu i.2 a).target → ∀ v : Tdata, (profiles.cT/16)*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice E i z.1)
        (actualOriginalOpenParameterSlice_contMDiff E rebound.domain_conditions rebound.smooth_inputs i z.1)
        (e nu i.2 a z.1).symm z.2 v‖^2 := by
    intro i nu a z hz v
    simp only [round3Parameter_original_open_slice_eq_global E rebound.domain_conditions hAll i]
    exact hFrame nu i.2 a z hz v
  obtain ⟨hNewActive,hNewGeom,hNewProfiles,hMean,hPhysical⟩ :=
    round4Parameter_fixed_carrier_after_normal_physical_factory_local_named_meta Ref hdRef g0 R Lprimary geom hLocal hOpen
      ForwardC InverseC GeometryMeta hProfiles MetaC hNamedProfiles F H normal neighborhood
      rebound.domain_conditions rebound.smooth_inputs rebound.normal_conditions hAll
      stage.ell lower (profiles.cT/16) stage.ell_pos (stage.ell_le_t.trans stage.t_le_one)
      host b e hData hNative hInner hChart hSlices hTransverse hp hF hImm hEll
      (div_pos profiles.cT_pos (by norm_num)) hLinear hdec rho hres stage.samples_compact
      (Packet 0) hLinearFinite hML q Packet hInverseC (fun j => (hProfile j).1) (fun j => (hProfile j).2)
  let gFixed := round3ParameterFixedCarrierFamily Ref g0 hOpen
  let g := round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood
    rebound.domain_conditions rebound.smooth_inputs rebound.normal_conditions hNewActive
  exact ⟨g,rfl,fun _ _ => rfl,fun _ _ => rfl,hNewGeom,hNewProfiles,hMean,hPhysical⟩

#print axioms round4_local_primary_named_meta_canonical_mean_from_stable
end GlobalEmbedding.Continuation
