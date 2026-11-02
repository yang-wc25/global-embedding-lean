import Smoothing.Round3OuterParameterNormalCover

/-! True fixed-reference first/transverse/normal reserves transfer to every
canonical cross-parameter chart without any loss. The sliced inverse is the
same function and both parameter charts represent the same physical point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round3_parameter_actual_cross_reserves
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip observer : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Ref ip nu W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (cF cT mu : ℝ)
    (hInner : ∀ w, w ∈ (actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native).source →
      w.2 ∈ Ref.atlas.inner piece.host)
    (hFirst : ∀ z ∈ piece.native.target, ∀ v : D,
      cF*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart ip).symm z.1) ∘ (piece.slices z.1).symm) z.2 v‖^2)
    (hFrame : ∀ z ∈ piece.native.target, ∀ v : Tdata,
      cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
        (F ((Ref.parameterChart ip).symm z.1)) (hF ((Ref.parameterChart ip).symm z.1))
        (piece.slices z.1).symm z.2 v‖^2)
    (hReserve : ∀ z ∈ piece.native.target, mu ≤
      ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F ((Ref.parameterChart ip).symm z.1) ∘ (piece.slices z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F ((Ref.parameterChart ip).symm z.1))
          (hF ((Ref.parameterChart ip).symm z.1)) (piece.slices z.1).symm z.2)
        (Ref.freeNormal nu ((Ref.parameterChart ip).symm z.1,(piece.slices z.1).symm z.2))‖) :
    let b := round3ParameterCrossNativeChart (Ref.parameterChart ip) (Ref.parameterChart observer) piece.native
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData (Ref.atlas.chart piece.host) b
        (fun w : Ep × M => Ref.phase nu ((Ref.parameterChart observer).symm w.1,w.2)) e ∧
      b.source ⊆ actualOriginalNativeOpen Ref (piece.host,observer) ∧
      (∀ w ∈ (actualHostAdaptedChart (Ref.atlas.chart piece.host) b).source,
        ((Ref.parameterChart observer).symm w.1,w.2) ∈
          Ref.primaryDomain nu ∩ incrementsOriginalParameterRegion Ref) ∧
      (∀ w ∈ (actualHostAdaptedChart (Ref.atlas.chart piece.host) b).source,
        w.2 ∈ Ref.atlas.inner piece.host) ∧
      (∀ z ∈ b.target, ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart observer).symm z.1) ∘ (e z.1).symm) z.2 v‖^2) ∧
      (∀ z ∈ b.target, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F ((Ref.parameterChart observer).symm z.1)) (hF ((Ref.parameterChart observer).symm z.1))
          (e z.1).symm z.2 v‖^2) ∧
      (∀ z ∈ b.target, mu ≤
        ‖actualOriginalFreeNormalFieldRaw (fun p x => F ((Ref.parameterChart observer).symm p) x)
          (fun p => hF ((Ref.parameterChart observer).symm p)) e
          (fun z : X => Ref.freeNormal nu ((Ref.parameterChart observer).symm z.1,(e z.1).symm z.2)) z‖) ∧
      ∀ p x, (e p).symm x =
        (piece.slices ((Ref.parameterChart ip) ((Ref.parameterChart observer).symm p))).symm x := by
  intro b
  obtain ⟨e,hData,hNative,hActive,hSlices⟩ := round3Parameter_actual_cross_native_data Ref hd ip observer nu W piece
  let Bp := Ref.parameterChart ip
  let Bo := Ref.parameterChart observer
  let C := Bp.symm.trans Bo
  have hSame (p : Ep) : ((e p).symm : D → M) = (piece.slices (Bp (Bo.symm p))).symm :=
    funext (hSlices p)
  have hCrossInner (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Ref.atlas.chart piece.host) b).source) :
      w.2 ∈ Ref.atlas.inner piece.host := by
    have hEq := round3Parameter_cross_host_conjugation Bp Bo (Ref.atlas.chart piece.host) piece.native
      (round3Parameter_primary_native_preserves_phase Ref hd ip nu W piece).1
    have hh : w ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm
        (actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native))).source := by rwa [← hEq]
    have ho := (round3ParameterChartPullback_source Bo (round3ParameterChartPullback Bp.symm
      (actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native)) w).mp hh
    have hp := (round3ParameterChartPullback_source Bp.symm
      (actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native) (Bo.symm w.1,w.2)).mp ho.2.1
    exact hInner (Bp (Bo.symm w.1),w.2) hp.2.1
  refine ⟨e,hData,hNative,hActive,hCrossInner,?_,?_,?_,hSlices⟩
  · intro z hz v
    have ht := (round3ParameterChartPullback_target C piece.native z).mp hz
    have hh := hFirst (Bp (Bo.symm z.1),z.2) ht.2.1 v
    dsimp only at hh
    rw [Bp.left_inv ht.1.2] at hh
    rw [hSame]
    exact hh
  · intro z hz v
    have ht := (round3ParameterChartPullback_target C piece.native z).mp hz
    have hh := hFrame (Bp (Bo.symm z.1),z.2) ht.2.1 v
    dsimp only at hh
    rw [Bp.left_inv ht.1.2] at hh
    rw [hSame]
    exact hh
  · intro z hz
    have ht := (round3ParameterChartPullback_target C piece.native z).mp hz
    have hh := hReserve (Bp (Bo.symm z.1),z.2) ht.2.1
    dsimp only at hh
    rw [Bp.left_inv ht.1.2] at hh
    change mu ≤ ‖actualFreeNormalProjectionRaw
      (fderiv ℝ (F (Bo.symm z.1) ∘ (e z.1).symm) z.2)
      (incrementsModeAmbientTransverseFrame (F (Bo.symm z.1)) (hF (Bo.symm z.1))
        (e z.1).symm z.2) (Ref.freeNormal nu (Bo.symm z.1,(e z.1).symm z.2))‖
    rw [hSame]
    exact hh

#print axioms round3_parameter_actual_cross_reserves
end GlobalEmbedding.Continuation
