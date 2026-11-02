import Repair.FullIncrementNovOpenReferenceProfiles

/-!
# Retained native-domain certificates for actual reference conditioning

The existing construction restricts its actual partial homeomorphisms, but
its old whole-profile interface retained only equality of the underlying
functions. This companion preserves the source/target inclusions and the
original per-piece first-derivative budget. It does not enlarge the original
parameter region or choose replacement phase, cutoff, or chart functions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_primary_conditioning_with_domains
    {Β : Type*} [Fintype Β]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount) (W : Set (Ep × M))
    (piece : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu W) :
    ∃ (cF cT : ℝ)
      (out : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu W),
      0 < cF ∧ 0 < cT ∧
      (∀ nu a, (out nu a).host = (piece nu a).host) ∧
      (∀ nu a, (out nu a).cutoff = (piece nu a).cutoff) ∧
      (∀ nu a, ((out nu a).native : X → X) = (piece nu a).native) ∧
      (∀ nu a, ((out nu a).native.symm : X → X) = (piece nu a).native.symm) ∧
      (∀ nu a p, (((out nu a).slices p).symm : D → M) = ((piece nu a).slices p).symm) ∧
      (∀ nu a, (out nu a).native.source ⊆ (piece nu a).native.source) ∧
      (∀ nu a, (out nu a).native.target ⊆ (piece nu a).native.target) ∧
      (∀ nu a, (out nu a).Bnative = (piece nu a).Bnative) ∧
      (∀ nu a z, z ∈ (out nu a).native.target → ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ
          (actualOriginalOpenParameterSlice Data baseIndex z.1 ∘ ((out nu a).slices z.1).symm) z.2 v‖^2) ∧
      ∀ nu a z, z ∈ (out nu a).native.target → ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Data baseIndex z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex z.1)
          ((out nu a).slices z.1).symm z.2 v‖^2 := by
  obtain ⟨cF,cT,b,e,hcF,hcT,hout⟩ :=
    actual_original_data_host_family_conditioning Data hd hs hp hImm baseIndex
      (fun nu a => (piece nu a).host) (fun nu a => (piece nu a).native)
      (fun nu a => (piece nu a).slices) (fun nu a => (piece nu a).data)
      (fun nu a => (piece nu a).cutoff) (fun nu a => (piece nu a).compact)
      (fun nu a => (piece nu a).support) (fun nu a => (piece nu a).native_source)
      (fun nu a => (piece nu a).active)
  let out : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu W :=
    fun nu a => {
      host := (piece nu a).host
      native := b nu a
      slices := e nu a
      cutoff := (piece nu a).cutoff
      data := (hout nu a).2.2.2.2.1
      native_source := (hout nu a).1.trans (piece nu a).native_source
      source_domain := (hout nu a).2.2.2.2.2.2.1.trans (piece nu a).source_domain
      active := fun w hw => (piece nu a).active w ((hout nu a).2.2.2.2.2.2.1 hw)
      compact := (piece nu a).compact
      smooth := (piece nu a).smooth
      support := (hout nu a).2.2.2.2.2.1
      Bnative := (piece nu a).Bnative
      positive := (piece nu a).positive
      native_first := by
        intro z hz
        rw [(hout nu a).2.2.1]
        exact (piece nu a).native_first z ((hout nu a).1 hz) }
  refine ⟨cF,cT,out,hcF,hcT,fun _ _ => rfl,fun _ _ => rfl,
    fun nu a => (hout nu a).2.2.1,fun nu a => (hout nu a).2.2.2.1,?_,
    fun nu a => (hout nu a).1,fun nu a => (hout nu a).2.1,
    fun _ _ => rfl,fun nu a => (hout nu a).2.2.2.2.2.2.2.2.1,
    fun nu a => (hout nu a).2.2.2.2.2.2.2.2.2⟩
  intro nu a p
  exact (hout nu a).2.2.2.2.2.2.2.1 p

theorem original_whole_conditioning_with_domains
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref hd hs) (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta) :
    ∃ (cF cT : ℝ)
      (out : ∀ nu i, packet.s nu i → Round3PreparedPrimaryPiece Ref i.2 nu
        ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))),
      0 < cF ∧ 0 < cT ∧
      (∀ nu i a, (out nu i a).host = (packet.piece nu i a).host) ∧
      (∀ nu i a, (out nu i a).cutoff = (packet.piece nu i a).cutoff) ∧
      (∀ nu i a, ((out nu i a).native : X → X) = (packet.piece nu i a).native) ∧
      (∀ nu i a, ((out nu i a).native.symm : X → X) = (packet.piece nu i a).native.symm) ∧
      (∀ nu i a p, (((out nu i a).slices p).symm : D → M) = ((packet.piece nu i a).slices p).symm) ∧
      (∀ nu i a, (out nu i a).native.source ⊆ (packet.piece nu i a).native.source) ∧
      (∀ nu i a, (out nu i a).native.target ⊆ (packet.piece nu i a).native.target) ∧
      (∀ nu i a, (out nu i a).Bnative = (packet.piece nu i a).Bnative) ∧
      (∀ nu i a z, z ∈ (out nu i a).native.target → ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (actualOriginalOpenParameterSlice Ref i z.1 ∘
          ((out nu i a).slices z.1).symm) z.2 v‖^2) ∧
      ∀ nu i a z, z ∈ (out nu i a).native.target → ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Ref i z.1)
          (actualOriginalOpenParameterSlice_contMDiff Ref hd hs i z.1)
          ((out nu i a).slices z.1).symm z.2 v‖^2 := by
  let W := fun i : Fin Ref.atlas.count × Fin Ref.parameterCount =>
    (Ref.parameterChart i.2).target ×ˢ (univ : Set M)
  let part := fun (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (nu : Fin Ref.primaryCount)
      (a : Sigma (fun mu : Fin Ref.primaryCount => ↥(packet.s mu i))) =>
    round3PreparedPrimarySigmaPiece Ref hd i (W i) (fun mu => ↥(packet.s mu i))
      (fun mu b => packet.piece mu i b) nu a
  have hLocal (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :=
    original_primary_conditioning_with_domains Ref hd hs hp hImm i (W i) (part i)
  choose cf ct pieces hcf hct hHost hCut hb hbi hSlices hSource hTarget hBN hFirst hFrame using hLocal
  obtain ⟨cF,hcF,hcFle⟩ := finite_positive_common_lower_bound cf hcf
  obtain ⟨cT,hcT,hcTle⟩ := finite_positive_common_lower_bound ct hct
  let out := fun nu i (a : packet.s nu i) => pieces i nu ⟨nu,a⟩
  have hPart (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
      (a : packet.s nu i) : part i nu ⟨nu,a⟩ = packet.piece nu i a :=
    round3PreparedPrimarySigmaPiece_active Ref hd i (W i) (fun mu => ↥(packet.s mu i))
      (fun mu b => packet.piece mu i b) nu a
  refine ⟨cF,cT,out,hcF,hcT,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro nu i a
    exact (hHost i nu ⟨nu,a⟩).trans (congrArg (fun p => p.host) (hPart nu i a))
  · intro nu i a
    exact (hCut i nu ⟨nu,a⟩).trans (congrArg (fun p => p.cutoff) (hPart nu i a))
  · intro nu i a
    exact (hb i nu ⟨nu,a⟩).trans (congrArg (fun p => (p.native : X → X)) (hPart nu i a))
  · intro nu i a
    exact (hbi i nu ⟨nu,a⟩).trans (congrArg (fun p => (p.native.symm : X → X)) (hPart nu i a))
  · intro nu i a p
    exact (hSlices i nu ⟨nu,a⟩ p).trans (congrArg (fun q => ((q.slices p).symm : D → M)) (hPart nu i a))
  · intro nu i a
    simpa only [out,hPart nu i a] using hSource i nu ⟨nu,a⟩
  · intro nu i a
    simpa only [out,hPart nu i a] using hTarget i nu ⟨nu,a⟩
  · intro nu i a
    exact (hBN i nu ⟨nu,a⟩).trans (congrArg (fun p => p.Bnative) (hPart nu i a))
  · intro nu i a z hz v
    exact (mul_le_mul_of_nonneg_right (hcFle i) (sq_nonneg ‖v‖)).trans (hFirst i nu ⟨nu,a⟩ z hz v)
  · intro nu i a z hz v
    exact (mul_le_mul_of_nonneg_right (hcTle i) (sq_nonneg ‖v‖)).trans (hFrame i nu ⟨nu,a⟩ z hz v)

/-- Source inclusion follows from the retained inverse function and target
inclusion. Equality of chart functions alone would not suffice. -/
theorem native_source_subset_of_target_subset
    (a b : OpenPartialHomeomorph X X)
    (hInverse : (a.symm : X → X) = b.symm) (hTarget : a.target ⊆ b.target) :
    a.source ⊆ b.source := by
  intro z hz
  have hh := b.map_target (hTarget (a.map_source hz))
  rw [← hInverse,a.left_inv hz] at hh
  exact hh

structure RestrictedReferenceGeometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    extends Round3ParameterWholeReferenceProfiles Data hd hs theta packet where
  source_subset : ∀ nu i a, (piece nu i a).native.source ⊆ (packet.piece nu i a).native.source
  target_subset : ∀ nu i a, (piece nu i a).native.target ⊆ (packet.piece nu i a).native.target
  native_bound_eq : ∀ nu i a, (piece nu i a).Bnative = (packet.piece nu i a).Bnative

theorem original_open_restricted_reference_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (hInner : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
      y.2 ∈ Data.atlas.inner (packet.piece nu i a).host) :
    Nonempty (RestrictedReferenceGeometry Data hd hs theta packet) := by
  obtain ⟨cF,cT,piece,hcF,hcT,hHost,hCut,hb,hbi,hSlices,hNativeSource,hNativeTarget,hNativeBound,hFirst,hFrame⟩ :=
    original_whole_conditioning_with_domains Data hd hs hp hImm theta packet
  let W := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  let G := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    actualOriginalParameterNeighborhood Data i.2 (incrementsOriginalParameterRegion Data)
  let Fn := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) p x =>
    Data.F ((Data.parameterChart i.2).symm p,x)
  have hFn (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry (Fn i)) (G i) :=
    actual_original_parameter_pullback_smooth Data hd i.2 Data.F
      (incrementsOriginalParameterRegion Data) hs.F_joint (G i)
      (fun _ hz => hz.1.1) (fun _ hz => hz.2)
  let localPiece := fun nu i (a : packet.s nu i) =>
    fullIncrementNovPrimaryPieceOpenAnnotation Data i.2 nu (piece nu i a)
  have hInner' (nu) (i) (a : packet.s nu i) (y : Ep × M)
      (hy : y ∈ tsupport (localPiece nu i a).cutoff) :
      y.2 ∈ Data.atlas.inner (localPiece nu i a).host := by
    change y.2 ∈ Data.atlas.inner (piece nu i a).host
    rw [hHost]
    exact hInner nu i a y (by change y ∈ tsupport (piece nu i a).cutoff at hy; rwa [hCut] at hy)
  have hLocal (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (a : packet.s nu i) :=
    round3_prepared_primary_reference_target_profiled Data hd i.2 nu (G i) (localPiece nu i a)
      (hInner' nu i a) (Fn i) (hFn i)
  choose MH out Ti Tf hMH hHost' hCut' hb' hbi' hSlices' hTarget hBN hHessian hTi hTf hInv hForw hSourceInner using hLocal
  let final := fun nu i (a : packet.s nu i) =>
    fullIncrementNovPrimaryPieceEnlarge Data i.2 nu (G i) (W i) (out nu i a) inter_subset_left
  let Index := Sigma (fun nu : Fin Data.primaryCount =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s nu i)))
  let MHmax := round3PreparedFiniteMaximum (fun a : Index => MH a.1 a.2.1 a.2.2)
  let Tinv := fun j => round3PreparedFiniteMaximum (fun a : Index => Ti a.1 a.2.1 a.2.2 j)
  let Tforward := fun j => round3PreparedFiniteMaximum (fun a : Index => Tf a.1 a.2.1 a.2.2 j)
  refine ⟨{
    piece := final
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
    source_inner := hSourceInner
    source_subset := ?_
    target_subset := ?_
    native_bound_eq := ?_ }⟩
  · intro nu i a z hz v
    have hh := hFirst nu i a z (hTarget nu i a hz) v
    have hOpen := fullIncrementNov_primary_target_parameter_open Data hd i.2 nu (G i)
      (out nu i a) z hz
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 hOpen] at hh
    change cF*‖v‖^2 ≤ ‖fderiv ℝ ((Fn i z.1) ∘ ((out nu i a).slices z.1).symm) z.2 v‖^2
    rw [hSlices']
    exact hh
  · intro nu i a z hz v
    change cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
      ((out nu i a).slices z.1).symm z.2 v‖^2
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

  · intro nu i a
    exact (native_source_subset_of_target_subset (out nu i a).native (localPiece nu i a).native
      (hbi' nu i a) (hTarget nu i a)).trans (hNativeSource nu i a)
  · intro nu i a
    exact (hTarget nu i a).trans (hNativeTarget nu i a)
  · intro nu i a
    exact (hBN nu i a).trans (hNativeBound nu i a)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.original_primary_conditioning_with_domains
#print axioms GlobalEmbedding.Continuation.original_whole_conditioning_with_domains
#print axioms GlobalEmbedding.Continuation.native_source_subset_of_target_subset
#print axioms GlobalEmbedding.Continuation.original_open_restricted_reference_profiles
