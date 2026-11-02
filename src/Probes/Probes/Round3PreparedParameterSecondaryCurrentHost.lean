import Probes.Round3PreparedParameterSecondaryStablePiece
import Probes.Round3PreparedParameterSecondaryLift
import Probes.Round3ParameterFixedProfileRebase

/-! One current signed piece supplies every observer's actual host/slice
geometry. The old phase and the physical choice are unchanged; the transverse
reserve is transported at the same physical parameter, with no new maximum. -/
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
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

 theorem round3_prepared_parameter_secondary_current_host
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (old : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3PreparedParameterStableSecondaryPiece Ref hd hs i r W old F hF)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (hdNew : IncrementsOriginalDomainConditions
      (round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood))
    (hsNew : IncrementsOriginalSmoothInputs
      (round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood))
    (observer : Fin Ref.parameterCount) :
    let Data := round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood
    let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r W stable.piece
    let native := (choice.pullback (Ref.parameterChart observer)).toNative
    let b := round3ParameterCrossNativeChart (Ref.parameterChart i.2) (Ref.parameterChart observer) stable.piece.native
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData (Data.atlas.chart i.1) b
        (actualOriginalParameterSignedPhase Data (i.1,observer) r.val) e ∧
      b.source ⊆ actualOriginalNativeOpen Data (i.1,observer) ∧
      (∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
        w.2 ∈ Ref.atlas.inner i.1) ∧
      native = ⟨Data.atlas.chart i.1,actualHostAdaptedChart (Data.atlas.chart i.1) b,
        (fun p x => (e p).symm x),fun z => choice.cutoff ((Ref.parameterChart observer).symm z.1,z.2)⟩ ∧
      ∀ z ∈ b.target, ∀ v : Tdata, (old.cT/16)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Data (i.1,observer) z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hdNew hsNew (i.1,observer) z.1)
          (e z.1).symm z.2 v‖^2 := by
  intro Data choice native b
  let Bp := Ref.parameterChart i.2
  let Bo := Ref.parameterChart observer
  let C := Bp.symm.trans Bo
  obtain ⟨e,hData,hNative,hActive,hSlices⟩ :=
    round3_prepared_signed_cross_native_data Ref hd hs i observer r W stable.piece
  have hSame (p : Ep) : ((e p).symm : D → M) = (stable.piece.slices (Bp (Bo.symm p))).symm :=
    funext (hSlices p)
  have hWhole (p : P) : p ∈ V := hdNew.parameter_subset (by change p ∈ Ref.parameterSet; rw [hAll]; exact mem_univ _)
  have hFsame : actualOriginalOpenParameterSlice Data (i.1,observer) = fun p => F (Bo.symm p) := by
    funext p
    exact actualOriginalOpenParameterSlice_eq Data (i.1,observer) p (hWhole _)
  have hNativeNew : b.source ⊆ actualOriginalNativeOpen Data (i.1,observer) := by
    intro z hz
    have hh := (round3Parameter_originalNativeOpen_iff Ref (i.1,observer) z).mp (hNative hz)
    exact (round3Parameter_originalNativeOpen_iff Data (i.1,observer) z).mpr ⟨hh.1,hh.2.1,hWhole _⟩
  have hCrossInner (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Ref.atlas.chart i.1) b).source) :
      w.2 ∈ Ref.atlas.inner i.1 := by
    have hEq := round3Parameter_cross_host_conjugation Bp Bo (Ref.atlas.chart i.1) stable.piece.native
      (round3_prepared_signed_native_preserves_phase Ref hd hs i r W stable.piece).1
    have hh : w ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm
        (actualHostAdaptedChart (Ref.atlas.chart i.1) stable.piece.native))).source := by rwa [← hEq]
    have ho := (round3ParameterChartPullback_source Bo (round3ParameterChartPullback Bp.symm
      (actualHostAdaptedChart (Ref.atlas.chart i.1) stable.piece.native)) w).mp hh
    have hp := (round3ParameterChartPullback_source Bp.symm
      (actualHostAdaptedChart (Ref.atlas.chart i.1) stable.piece.native) (Bo.symm w.1,w.2)).mp ho.2.1
    exact stable.piece.source_inner (Bp (Bo.symm w.1),w.2) hp.2.1
  have hChart : native.chart = actualHostAdaptedChart (Ref.atlas.chart i.1) b :=
    (round3Parameter_cross_host_conjugation Bp Bo (Ref.atlas.chart i.1) stable.piece.native
      (round3_prepared_signed_native_preserves_phase Ref hd hs i r W stable.piece).1).symm
  have hC : native.c = fun p x => (e p).symm x := by
    funext p x
    exact (hSlices p x).symm
  refine ⟨e,hData,hNativeNew,hCrossInner,?_,?_⟩
  · change ActualOriginalSecondaryChoice.mk native.host native.chart native.c native.cutoff = _
    rw [hChart,hC]
    rfl
  · intro z hz v
    have ht := (round3ParameterChartPullback_target C stable.piece.native z).mp hz
    have hh := stable.transverse (Bp (Bo.symm z.1),z.2) ht.2.1 v
    dsimp only at hh
    rw [Bp.left_inv ht.1.2] at hh
    simpa only [hFsame,hSame] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_current_host
