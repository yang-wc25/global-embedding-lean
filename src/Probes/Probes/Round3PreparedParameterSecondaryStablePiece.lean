import Probes.Round3PreparedParameterSecondaryStableTarget

/-! The whole-parameter stable signed chart is repackaged as an actual
restriction of the fixed reference piece. Every scalar cost and every
all-order reference profile is literally retained. -/
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

 structure Round3PreparedParameterStableSecondaryPiece
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (old : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)) where
  piece : Round3PreparedSignedReferencePiece Ref hd hs i r W
  cutoff : piece.cutoff = old.cutoff
  carrier : piece.carrier = old.carrier
  forward : (piece.native : X → X) = old.native
  inverse : (piece.native.symm : X → X) = old.native.symm
  slices : ∀ p, ((piece.slices p).symm : D → M) = (old.slices p).symm
  source_subset : piece.native.source ⊆ old.native.source
  target_subset : piece.native.target ⊆ old.native.target
  cF_eq : piece.cF = old.cF
  cT_eq : piece.cT = old.cT
  MH_eq : piece.MH = old.MH
  Bnative_eq : piece.Bnative = old.Bnative
  Tinv_eq : piece.Tinv = old.Tinv
  Forward_eq : piece.Forward = old.Forward
  first : ∀ z ∈ piece.native.target, ∀ v : D,
    (old.cF/16)*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart i.2).symm z.1) ∘ (piece.slices z.1).symm) z.2 v‖^2
  transverse : ∀ z ∈ piece.native.target, ∀ v : Tdata,
    (old.cT/16)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (F ((Ref.parameterChart i.2).symm z.1)) (hF ((Ref.parameterChart i.2).symm z.1))
      (piece.slices z.1).symm z.2 v‖^2
  immersion : ∀ z ∈ piece.native.target, Function.Injective (mfderiv 𝓙 𝓘(ℝ,Ey)
    (F ((Ref.parameterChart i.2).symm z.1)) ((piece.slices z.1).symm z.2))

 theorem round3_prepared_parameter_secondary_stable_piece
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (old : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (hJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
    (hPointwise : ∀ y, y ∈ old.carrier →
      let z := actualHostAdaptedChart (Ref.atlas.chart i.1) old.native y
      let p := (Ref.parameterChart i.2).symm z.1
      (∀ v : D, (old.cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F p ∘ (old.slices z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, (old.cT/4)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F p) (hF p) (old.slices z.1).symm z.2 v‖^2)) :
    Nonempty (Round3PreparedParameterStableSecondaryPiece Ref hd hs i r W old F hF) := by
  obtain ⟨b,e,hb,hbi,hSlices,hSource,hTarget,hData,hSupport,hASource,hFirst,hFrame,hImm⟩ :=
    round3_prepared_parameter_secondary_stable_target Ref hd hs i r W old F hF hJoint hPointwise
  let out : Round3PreparedSignedReferencePiece Ref hd hs i r W := {
    old with
    native := b
    slices := e
    data := hData
    native_source := hSource.trans old.native_source
    source_domain := hASource.trans old.source_domain
    active := fun z hz => old.active z (hASource hz)
    source_inner := fun z hz => old.source_inner z (hASource hz)
    carrier_source := hSupport
    native_first := by
      intro z hz
      rw [hb]
      exact old.native_first z (hSource hz)
    first := by
      intro z hz v
      rw [hSlices]
      exact old.first z (hTarget hz) v
    transverse := by
      intro z hz v
      rw [hSlices]
      exact old.transverse z (hTarget hz) v
    hessian := by
      intro z hz
      rw [hSlices]
      exact old.hessian z (hTarget hz)
    inverse_jets := by
      intro j z hz
      rw [hbi]
      exact old.inverse_jets j z (hTarget hz)
    forward_jets := by
      intro j z hz
      rw [hb]
      exact old.forward_jets j z (hSource hz) }
  exact ⟨{
    piece := out
    cutoff := rfl
    carrier := rfl
    forward := hb
    inverse := hbi
    slices := hSlices
    source_subset := hSource
    target_subset := hTarget
    cF_eq := rfl
    cT_eq := rfl
    MH_eq := rfl
    Bnative_eq := rfl
    Tinv_eq := rfl
    Forward_eq := rfl
    first := hFirst
    transverse := hFrame
    immersion := hImm }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_stable_piece
