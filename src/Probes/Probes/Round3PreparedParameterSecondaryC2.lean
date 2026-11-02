import Probes.Round3PreparedParameterSecondaryPieces
import Probes.Round3PreparedC2Frames
import Smoothing.ParameterRound2OriginalInputs
import Smoothing.Round3OuterC2NativeJets
import Probes.ActualIncrementFreeNormalKernel
import Probes.ActualIncrementOriginalSampling

/-! Fixed actual reference pieces on every parameter chart are sampled in
the original norm.  The old unit normal and beta kernel are derived from
the original free-normal assumptions, without an identity parameter chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
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

theorem round3_prepared_parameter_secondary_carrier_sampling
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (hK : Ref.parameterSet = univ)
    (hParam : ∀ y ∈ piece.carrier, y.1 ∈ Ref.parameterNormDomain i.2)
    (y : Ep × M) (hy : y ∈ piece.carrier) :
    let z := actualHostAdaptedChart (Ref.atlas.chart i.1) piece.native y
    parameterTensorModelEquiv (m+1) d
      (round3OriginalAdaptedTransition Ref.atlas i.1 piece.slices z) ∈
        incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
          Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i := by
  intro z
  let a := actualHostAdaptedChart (Ref.atlas.chart i.1) piece.native
  have hys := piece.carrier_source hy
  have hz : z ∈ piece.native.target := by
    rw [← piece.data.1]
    exact a.map_source hys
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hzp : z.1 = y.1 := (hforw y hys).1
  have hpx : (piece.slices z.1).symm z.2 = y.2 := by
    have hh := a.left_inv hys
    rw [hpair z hz] at hh
    exact congrArg Prod.snd hh
  apply (actual_original_native_evaluation_iff Ref hd i _).mpr
  refine ⟨?_,?_,?_⟩
  · change Ref.atlas.chart i.1 ((piece.slices z.1).symm z.2) ∈ Ref.sourceNormDomain i.1
    rw [hpx]
    exact hd.source_inner_norm i.1 y.2 (piece.source_inner y hys)
  · change z.1 ∈ Ref.parameterNormDomain i.2
    rw [hzp]
    exact hParam y hy
  · change (Ref.parameterChart i.2).symm z.1 ∈ Ref.parameterSet
    rw [hK]
    exact mem_univ _

local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

 theorem round3_prepared_parameter_secondary_C2_pointwise
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (hAll : Ref.parameterSet = univ)
    (hParam : ∀ y ∈ piece.carrier, y.1 ∈ Ref.parameterNormDomain i.2)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∀ y, y ∈ piece.carrier →
      let z := actualHostAdaptedChart (Ref.atlas.chart i.1) piece.native y
      let p := (Ref.parameterChart i.2).symm z.1
      (∀ v : D, (piece.cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F p ∘ (piece.slices z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, (piece.cT/4)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F p) (hF p) (piece.slices z.1).symm z.2 v‖^2) := by
  obtain ⟨epsilon,hepsilon,hStable⟩ := round3_prepared_original_C2_frame_stability
    (m := m) (d := d) (N := N) (M := M) (P := P) (c := Ref.parameterCount)
    piece.Tinv piece.Tinv_nonneg piece.cF piece.cT piece.MH piece.cF_pos piece.cT_pos piece.MH_nonneg
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound y hy z p
  let c := Ref.atlas.chart i.1
  let a := actualHostAdaptedChart c piece.native
  have hys := piece.carrier_source hy
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hz : z ∈ piece.native.target := by rw [← hat]; exact a.map_source hys
  have hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Ref.F (p,x)) :=
    fun p => hF0joint.comp (contMDiff_const.prodMk contMDiff_id)
  have hCoord0 := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Ref.F (by simpa only [modelWithCornersSelf_prod] using hF0joint)
  have hCoord := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth (Function.uncurry F) (by simpa only [modelWithCornersSelf_prod] using hFjoint)
  rcases actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem i.1) piece.native
    _ piece.slices piece.data with ⟨hSource,hBS,hBIS,hPoint,hTransition,hReverse,hMap,hAdapt⟩
  have hParameter (w : X) (hw : w ∈ piece.native.target) : w.1 ∈ (Ref.parameterChart i.2).target := by
    have hsp := actual_host_slice_source_point c piece.native _ piece.slices piece.data w hw
    exact ((round3Parameter_originalNativeOpen_iff Ref i _).mp (piece.native_source hsp.2)).2.1
  have hSample := round3_prepared_parameter_secondary_carrier_sampling Ref hd hs i r W piece hAll hParam y hy
  have hOpen (q : P) : q ∈ Ref.parameterOpen := hd.parameter_subset (by rw [hAll]; exact mem_univ _)
  have hEq : actualOriginalOpenParameterSlice Ref i z.1 = fun x => Ref.F (p,x) :=
    actualOriginalOpenParameterSlice_eq Ref i z.1 (hOpen _)
  have hFirst : ∀ v : D, piece.cF*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => Ref.F (p,x)) ∘
      (piece.slices z.1).symm) z.2 v‖^2 := by simpa only [hEq] using piece.first z hz
  have hFrame : ∀ v : Tdata, piece.cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (fun x => Ref.F (p,x)) (hF0 p) (piece.slices z.1).symm z.2 v‖^2 := by
    simpa only [hEq] using piece.transverse z hz
  have hHessian : ‖fderiv ℝ (fderiv ℝ ((fun x => Ref.F (p,x)) ∘ (piece.slices z.1).symm)) z.2‖ ≤ piece.MH := by
    simpa only [hEq] using piece.hessian z hz
  exact hStable Ref.atlas Ref.parameterChart Ref.F (Function.uncurry F) hF0 hF S
    (fun _ _ h => h.1) hCoord0 hCoord hFinite hBound i piece.slices
    piece.native.target piece.native.open_target hTransition (fun w hw => (hPoint w hw).2) hParameter
    z hz (hPoint z hz).1 (he z.1) hSample
    (fun j _ _ => by
      change ‖iteratedFDeriv ℝ j (actualSourceChartTransition (fun _ => c) piece.slices) z‖ ≤ piece.Tinv j
      rw [hbj j z hz]
      exact piece.inverse_jets j z hz) hFirst hFrame hHessian

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_C2_pointwise
