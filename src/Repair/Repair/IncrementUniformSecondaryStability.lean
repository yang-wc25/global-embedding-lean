import Repair.EntranceUniformGeometryTolerance
import Probes.Round3PreparedParameterSecondaryStableFamily

/-!
# Uniform original C2 stability of the actual secondary packet

One numerical tolerance is fixed from the common reference first/transverse
reserves, Hessian bound and native inverse profile.  Original carrier samples
supply the two-jet discrepancy, and the actual stable target constructor
retains all physical choices and functions.  No finite minimum of piece
stability tolerances or new-map frame assumptions is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
private local instance incrementToleranceFirstNormed (m N : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance incrementToleranceFirstSpace (m N : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance incrementToleranceHessianNormed (m N : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance incrementToleranceHessianSpace (m N : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance incrementToleranceFrameNormed (m N : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance incrementToleranceFrameSpace (m N : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance incrementToleranceColumnsNormed (m N : ℕ) :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance incrementToleranceColumnsSpace (m N : ℕ) :
    NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := ContinuousLinearMap.toNormedSpace

section TwoJet
variable {m N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem increment_uniform_two_jet_frame_stability
    (cF cT MH : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (F0 F : M → V) (hF0 : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F0) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ e.target)
    (hFirst : ∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F0 ∘ e.symm) x v‖^2)
    (hTransverse : ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F0 hF0 e.symm x v‖^2)
    (hHessian : ‖fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤ MH)
    (hD : ‖fderiv ℝ (F0 ∘ e.symm) x-fderiv ℝ (F ∘ e.symm) x‖ ≤
      repairEntranceTwoJetTolerance m N cF cT MH hcF hcT)
    (hH : ‖fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x-fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤
      repairEntranceTwoJetTolerance m N cF cT MH hcF hcT)
:
    (∀ v : D, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F ∘ e.symm) x v‖^2) ∧
    (∀ v : Tdata, (cT/4)*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF e.symm x v‖^2) := by
  let C := repairEntranceTransverseChangeCost m N cF MH
  let en := repairEntranceProjectionTolerance m N cF cT hcF hcT
  let epsilon := repairEntranceTwoJetTolerance m N cF cT MH hcF hcT
  have hEn : 0 < en := repairEntranceProjectionTolerance_pos m N cF cT hcF hcT
  have hC : 0 ≤ C := by dsimp [C,repairEntranceTransverseChangeCost]; positivity
  have hSmallF : epsilon ≤ Real.sqrt cF/2 := min_le_left _ _
  have hSmallT : C*epsilon ≤ Real.sqrt cT/2 := by
    calc
      _ ≤ C*(Real.sqrt cT/(2*(C+1))) :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hC
      _ ≤ (C+1)*(Real.sqrt cT/(2*(C+1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Real.sqrt cT/2 := by field_simp
  have hFrame := actual_original_transverse_frame_two_jet_difference F0 F hF0 hF e he x hx
    cF MH hcF hFirst hHessian (hD.trans hSmallF)
  have hFrameBound : ‖incrementsModeAmbientTransverseFrame F hF e.symm x-
      incrementsModeAmbientTransverseFrame F0 hF0 e.symm x‖ ≤ C*epsilon := by
    apply hFrame.trans
    calc
      _ ≤ ‖actualIncrementTransverseColumns m N‖*(epsilon+(3/Real.sqrt cF)*MH*epsilon) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hH (mul_le_mul_of_nonneg_left hD (by positivity))) (norm_nonneg _)
      _ = C*epsilon := by dsimp [C,repairEntranceTransverseChangeCost]; ring
  exact ⟨actual_first_frame_reserve_perturbation _ _ cF hcF hFirst
      (by simpa only [norm_sub_rev] using hD.trans hSmallF),
    actual_first_frame_reserve_perturbation _ _ cT hcT hTransverse
      (hFrameBound.trans hSmallT)⟩

end TwoJet

section OriginalTransfer
variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem increment_uniform_original_C2_frame_stability
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH) :
    ∀
      (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
      (F0 F : P × M → Ey)
      (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => F0 (p,x)))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
      (S : Fin A.count × Fin c → Set (Fin ((m+1)+d) → ℝ)),
    (∀ i, S i ⊆ incrementsOriginalDifferentiation A B i) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F0 i)
      (incrementsOriginalDifferentiation A B i)) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i)) →
    paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT →
    ∀ (i : Fin A.count × Fin c) (e : Ep → OpenPartialHomeomorph M Es)
      (O : Set X), IsOpen O →
    ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition A i.1 e) O →
    (∀ z ∈ O, (e z.1).symm z.2 ∈ (A.chart i.1).source) →
    (∀ z ∈ O, z.1 ∈ (B i.2).target) →
    ∀ (z : X), z ∈ O → z.2 ∈ (e z.1).target →
    e z.1 ∈ IsManifold.maximalAtlas 𝓙 ∞ M →
    parameterTensorModelEquiv (m+1) d (round3OriginalAdaptedTransition A i.1 e z) ∈ S i →
    (∀ j, 1 ≤ j → j ≤ 2 →
      ‖iteratedFDeriv ℝ j (round3OriginalAdaptedTransition A i.1 e) z‖ ≤ T j) →
    let p := (B i.2).symm z.1
    let f0 := fun x => F0 (p,x)
    let f := fun x => F (p,x)
    (∀ v : Es, cF*‖v‖^2 ≤ ‖fderiv ℝ (f0 ∘ (e z.1).symm) z.2 v‖^2) →
    (∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame f0 (hF0 p) (e z.1).symm z.2 v‖^2) →
    ‖fderiv ℝ (fderiv ℝ (f0 ∘ (e z.1).symm)) z.2‖ ≤ MH →
    (∀ v : Es, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (f ∘ (e z.1).symm) z.2 v‖^2) ∧
    (∀ v : Tdata, (cT/4)*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame f (hF p) (e z.1).symm z.2 v‖^2) := by
  intro A B F0 F hF0 hF S hSO hCoord0 hCoord hFinite hBound i e O hO hTransition
    hSource hParameter z hz heTarget he hSample hChartJets p f0 f hFirst hFrame hHessian
  let eta := repairEntranceTwoJetTolerance m N cF cT MH hcF hcT
  let C := round3OriginalC2AdaptedCost (m+1) d N T
  let epsilon := repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT
  have hC : 0 ≤ C := round3OriginalC2AdaptedCost_nonneg (m+1) d N T hT
  have hepsilon : 0 < epsilon := repairEntranceGeometryTolerance_pos m d N T hT cF cT MH hcF hcT hMH
  have hCost : C*epsilon ≤ eta := by
    calc
      _ ≤ (C+1)*epsilon := mul_le_mul_of_nonneg_right (by linarith) hepsilon.le
      _ = eta := by
        change (C+1)*(eta/(C+1)) = eta
        field_simp [ne_of_gt (show 0 < C+1 by linarith)]
  have hDiff := round3_original_C2_actual_spatial_difference T hT A B F F0 S hSO
    hCoord hCoord0 hFinite epsilon hepsilon.le hBound i e O hO hTransition hSource hParameter
    z hz hSample hChartJets
  apply increment_uniform_two_jet_frame_stability cF cT MH hcF hcT hMH
    f0 f (hF0 p) (hF p) (e z.1) he z.2 heTarget
    hFirst hFrame hHessian _ _
  · rw [norm_sub_rev]
    exact hDiff.1.trans hCost
  · exact hDiff.2.trans hCost

end OriginalTransfer
section OriginalPacket
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
 theorem increment_uniform_secondary_C2_pointwise
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (hAll : Ref.parameterSet = univ)
    (hParam : ∀ y ∈ piece.carrier, y.1 ∈ Ref.parameterNormDomain i.2)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (hFirstValue : piece.cF = cF) (hFrameValue : piece.cT = cT)
    (hHessianBound : piece.MH ≤ MH)
    (hInverseBound : ∀ j, 1 ≤ j → j ≤ 2 → piece.Tinv j ≤ T j) :
    ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT →
    ∀ y, y ∈ piece.carrier →
      let z := actualHostAdaptedChart (Ref.atlas.chart i.1) piece.native y
      let p := (Ref.parameterChart i.2).symm z.1
      (∀ v : D, (piece.cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F p ∘ (piece.slices z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, (piece.cT/4)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F p) (hF p) (piece.slices z.1).symm z.2 v‖^2) := by
  have hStable := increment_uniform_original_C2_frame_stability
    (m := m) (d := d) (N := N) (M := M) (P := P) (c := Ref.parameterCount)
    T hT cF cT MH hcF hcT hMH
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
  have hFirst : ∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => Ref.F (p,x)) ∘
      (piece.slices z.1).symm) z.2 v‖^2 := by simpa only [hEq,hFirstValue] using piece.first z hz
  have hFrame : ∀ v : Tdata, cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (fun x => Ref.F (p,x)) (hF0 p) (piece.slices z.1).symm z.2 v‖^2 := by
    simpa only [hEq,hFrameValue] using piece.transverse z hz
  have hHessian : ‖fderiv ℝ (fderiv ℝ ((fun x => Ref.F (p,x)) ∘ (piece.slices z.1).symm)) z.2‖ ≤ MH := by
    simpa only [hEq] using (piece.hessian z hz).trans hHessianBound
  simpa only [hFirstValue,hFrameValue,Function.uncurry,p] using hStable Ref.atlas Ref.parameterChart Ref.F (Function.uncurry F) hF0 hF S
    (fun _ _ h => h.1) hCoord0 hCoord hFinite hBound i piece.slices
    piece.native.target piece.native.open_target hTransition (fun w hw => (hPoint w hw).2) hParameter
    z hz (hPoint z hz).1 (he z.1) hSample
    (fun j hj hj2 => by
      change ‖iteratedFDeriv ℝ j (actualSourceChartTransition (fun _ => c) piece.slices) z‖ ≤ T j
      rw [hbj j z hz]
      exact (piece.inverse_jets j z hz).trans (hInverseBound j hj hj2)) hFirst hFrame hHessian

/-- Common reference profile values yield one actual stable family with the
named numerical tolerance.  Every later observer sees this same family. -/
theorem increment_uniform_secondary_stable_family
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hParam : ∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (hFirstValue : ∀ r i a, (packet.piece r i a).cF = cF)
    (hFrameValue : ∀ r i a, (packet.piece r i a).cT = cT)
    (hHessianBound : ∀ r i a, (packet.piece r i a).MH ≤ MH)
    (hInverseBound : ∀ r i a j, 1 ≤ j → j ≤ 2 → (packet.piece r i a).Tinv j ≤ T j) :
    ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤
      repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT →
    Nonempty (∀ r i (a : packet.s r i),
      Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF) := by
  intro F hFjoint hF S hFinite hBound
  exact ⟨fun r i a => Classical.choice (round3_prepared_parameter_secondary_stable_piece Ref hd hs i r _
    (packet.piece r i a) F hF hFjoint
    (increment_uniform_secondary_C2_pointwise Ref hd hs i r _ (packet.piece r i a)
      hAll (hParam r i a) hF0joint T hT cF cT MH hcF hcT hMH
      (hFirstValue r i a) (hFrameValue r i a) (hHessianBound r i a) (hInverseBound r i a)
      F hFjoint hF hFinite hBound))⟩

end OriginalPacket
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_uniform_two_jet_frame_stability
#print axioms GlobalEmbedding.Continuation.increment_uniform_original_C2_frame_stability
#print axioms GlobalEmbedding.Continuation.increment_uniform_secondary_C2_pointwise
#print axioms GlobalEmbedding.Continuation.increment_uniform_secondary_stable_family
