import Probes.Round3ParameterCrossNativeData

/-! Actual transverse-frame transport between parameter observers on the
original open parameter region.  The two sides use the existing original
open-slice convention.  They agree because the nonlinear parameter change
represents the same physical parameter.  No global source-slice smoothness,
`parameterSet = univ`, extension of `Data.F`, or change to `Data` is required.
-/

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
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem fullIncrementNov_primary_target_parameter_open
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W)
    (z : X) (hz : z ∈ piece.native.target) :
    (Data.parameterChart ip).symm z.1 ∈ Data.parameterOpen := by
  have hy := piece.native.map_target hz
  have hPreserves := (round3Parameter_primary_native_preserves_phase Data hd ip nu W piece).1
    (piece.native.symm z) hy
  rw [piece.native.right_inv hz] at hPreserves
  have hOpen := actualOriginalNativeOpen_parameter Data (piece.host,ip) (piece.native_source hy)
  rw [← hPreserves] at hOpen
  exact hOpen

theorem fullIncrementNov_original_open_cross_transverse_reserve
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (ip : Fin Data.parameterCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (W : Set (Ep × M)) (piece : Round3PreparedPrimaryPiece Data ip nu W)
    (e : Ep → OpenPartialHomeomorph M D)
    (hSlices : ∀ p x, (e p).symm x =
      (piece.slices ((Data.parameterChart ip) ((Data.parameterChart i.2).symm p))).symm x)
    (cT : ℝ)
    (hNative : ∀ z ∈ piece.native.target, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data (piece.host,ip) z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs (piece.host,ip) z.1)
        (piece.slices z.1).symm z.2 v‖^2) :
    ∀ z ∈ (round3ParameterCrossNativeChart (Data.parameterChart ip)
      (Data.parameterChart i.2) piece.native).target, ∀ v : Tdata,
      (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen ∧
      cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (e z.1).symm z.2 v‖^2 := by
  intro z hz v
  let Bp := Data.parameterChart ip
  let Bo := Data.parameterChart i.2
  have hh := (round3ParameterChartPullback_target (Bp.symm.trans Bo) piece.native z).mp hz
  have hp : Bp.symm (Bp (Bo.symm z.1)) = Bo.symm z.1 := Bp.left_inv hh.1.2
  have hb := hNative (Bp (Bo.symm z.1),z.2) hh.2.1 v
  have hOpen := fullIncrementNov_primary_target_parameter_open Data hd ip nu W piece
    (Bp (Bo.symm z.1),z.2) hh.2.1
  change Bp.symm (Bp (Bo.symm z.1)) ∈ Data.parameterOpen at hOpen
  rw [hp] at hOpen
  have hBase : actualOriginalOpenParameterSlice Data (piece.host,ip) (Bp (Bo.symm z.1)) =
      actualOriginalOpenParameterSlice Data i z.1 := by
    funext x
    simp only [actualOriginalOpenParameterSlice,show
      (Data.parameterChart ip).symm (Bp (Bo.symm z.1)) = (Data.parameterChart i.2).symm z.1 from hp]
  have he : ((e z.1).symm : D → M) = (piece.slices (Bp (Bo.symm z.1))).symm :=
    funext (hSlices z.1)
  refine ⟨hOpen,?_⟩
  simpa only [hBase,he] using hb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_target_parameter_open
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_cross_transverse_reserve
