import Probes.Round3ParameterWholeReferenceConditioning
import Probes.Round3ParameterReferenceC2Pointwise
import Probes.Round3PreparedReferenceTargetProfiles

/-! All parameter charts share one genuine fixed reference geometry packet.
First/transverse reserves, the ordinary reference Hessian bound and complete
chart profiles are outputs of compact conditioning of the original map.
They precede every current map and every smoothing scale. -/

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
private local instance profFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance profFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance profHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance profHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance

structure Round3ParameterWholeReferenceProfiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta) where
  piece : ∀ nu i, packet.s nu i → Round3PreparedPrimaryPiece Ref i.2 nu
    ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))
  host : ∀ nu i a, (piece nu i a).host = (packet.piece nu i a).host
  cutoff : ∀ nu i a, (piece nu i a).cutoff = (packet.piece nu i a).cutoff
  forward : ∀ nu i a, ((piece nu i a).native : X → X) = (packet.piece nu i a).native
  inverse : ∀ nu i a, ((piece nu i a).native.symm : X → X) = (packet.piece nu i a).native.symm
  slices : ∀ nu i a p, (((piece nu i a).slices p).symm : D → M) = ((packet.piece nu i a).slices p).symm
  cF : ℝ
  cT : ℝ
  MH : ℝ
  cF_pos : 0 < cF
  cT_pos : 0 < cT
  MH_nonneg : 0 ≤ MH
  Tinv : ℕ → ℝ
  Tforward : ℕ → ℝ
  Tinv_nonneg : ∀ j, 0 ≤ Tinv j
  Tforward_nonneg : ∀ j, 0 ≤ Tforward j
  first : ∀ nu i a z, z ∈ (piece nu i a).native.target → ∀ v : D,
    cF*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => Ref.F ((Ref.parameterChart i.2).symm z.1,x)) ∘
      ((piece nu i a).slices z.1).symm) z.2 v‖^2
  transverse : ∀ nu i a z, z ∈ (piece nu i a).native.target → ∀ v : Tdata,
    cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (actualOriginalOpenParameterSlice Ref i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Ref hd hs i z.1)
      ((piece nu i a).slices z.1).symm z.2 v‖^2
  hessian : ∀ nu i a z, z ∈ (piece nu i a).native.target →
    ‖fderiv ℝ (fderiv ℝ ((fun x => Ref.F ((Ref.parameterChart i.2).symm z.1,x)) ∘
      ((piece nu i a).slices z.1).symm)) z.2‖ ≤ MH
  inverse_jets : ∀ nu i a j z, z ∈ (piece nu i a).native.target →
    ‖iteratedFDeriv ℝ j (piece nu i a).native.symm z‖ ≤ Tinv j
  forward_jets : ∀ nu i a j z, z ∈ (piece nu i a).native.source →
    ‖iteratedFDeriv ℝ j (piece nu i a).native z‖ ≤ Tforward j
  source_inner : ∀ nu i a y, y ∈ (actualHostAdaptedChart (Ref.atlas.chart (piece nu i a).host) (piece nu i a).native).source →
    y.2 ∈ Ref.atlas.inner (piece nu i a).host

theorem round3Parameter_actual_whole_reference_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref hd hs) (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hK : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (hInner : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
      y.2 ∈ Ref.atlas.inner (packet.piece nu i a).host) :
    Nonempty (Round3ParameterWholeReferenceProfiles Ref hd hs theta packet) := by
  obtain ⟨cF,cT,piece,hcF,hcT,hHost,hCut,hb,hbi,hSlices,hFirst,hFrame⟩ :=
    round3Parameter_actual_whole_reference_conditioning Ref hd hs hp hImm theta packet
  let W := fun i : Fin Ref.atlas.count × Fin Ref.parameterCount =>
    (Ref.parameterChart i.2).target ×ˢ (univ : Set M)
  let Fn := fun (i : Fin Ref.atlas.count × Fin Ref.parameterCount) p x => Ref.F ((Ref.parameterChart i.2).symm p,x)
  have hFn (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry (Fn i)) (W i) :=
    actual_original_parameter_pullback_smooth Ref hd i.2 Ref.F univ hF0joint.contMDiffOn
      (W i) (fun _ h => h.1) (fun _ _ => mem_univ _)
  have hInner' (nu) (i) (a : packet.s nu i) (y : Ep × M) (hy : y ∈ tsupport (piece nu i a).cutoff) :
      y.2 ∈ Ref.atlas.inner (piece nu i a).host := by
    rw [hHost]
    exact hInner nu i a y (by rwa [hCut] at hy)
  have hLocal (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (a : packet.s nu i) :=
    round3_prepared_primary_reference_target_profiled Ref hd i.2 nu (W i) (piece nu i a)
      (hInner' nu i a) (Fn i) (hFn i)
  choose MH out Ti Tf hMH hHost' hCut' hb' hbi' hSlices' hTarget hBN hHessian hTi hTf hInv hForw hSourceInner using hLocal
  let Index := Sigma (fun nu : Fin Ref.primaryCount => Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s nu i)))
  let MHmax := round3PreparedFiniteMaximum (fun a : Index => MH a.1 a.2.1 a.2.2)
  let Tinv := fun j => round3PreparedFiniteMaximum (fun a : Index => Ti a.1 a.2.1 a.2.2 j)
  let Tforward := fun j => round3PreparedFiniteMaximum (fun a : Index => Tf a.1 a.2.1 a.2.2 j)
  have hOpen (p : P) : p ∈ Ref.parameterOpen := hd.parameter_subset (by rw [hK]; exact mem_univ _)
  have hSlice (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (p : Ep) :
      actualOriginalOpenParameterSlice Ref i p = Fn i p :=
    actualOriginalOpenParameterSlice_eq Ref i p (hOpen _)
  refine ⟨{
    piece := out
    host := fun nu i a => (hHost' nu i a).trans (hHost nu i a)
    cutoff := fun nu i a => (hCut' nu i a).trans (hCut nu i a)
    forward := fun nu i a => (hb' nu i a).trans (hb nu i a)
    inverse := fun nu i a => (hbi' nu i a).trans (hbi nu i a)
    slices := fun nu i a p => (hSlices' nu i a p).trans (hSlices nu i a p)
    cF := cF
    cT := cT
    MH := MHmax
    cF_pos := hcF
    cT_pos := hcT
    MH_nonneg := round3PreparedFiniteMaximum_nonneg _
    Tinv := Tinv
    Tforward := Tforward
    Tinv_nonneg := fun _ => round3PreparedFiniteMaximum_nonneg _
    Tforward_nonneg := fun _ => round3PreparedFiniteMaximum_nonneg _
    first := ?_
    transverse := ?_
    hessian := ?_
    inverse_jets := ?_
    forward_jets := ?_
    source_inner := hSourceInner }⟩
  · intro nu i a z hz v
    have hh := hFirst nu i a z (hTarget nu i a hz) v
    rw [hSlice] at hh
    rw [hSlices']
    exact hh
  · intro nu i a z hz v
    rw [hSlices']
    exact hFrame nu i a z (hTarget nu i a hz) v
  · intro nu i a z hz
    exact (hHessian nu i a z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Index => MH a.1 a.2.1 a.2.2) ⟨nu,i,a⟩)
  · intro nu i a j z hz
    exact (hInv nu i a j z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Index => Ti a.1 a.2.1 a.2.2 j) ⟨nu,i,a⟩)
  · intro nu i a j z hz
    exact (hForw nu i a j z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Index => Tf a.1 a.2.1 a.2.2 j) ⟨nu,i,a⟩)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_whole_reference_profiles
