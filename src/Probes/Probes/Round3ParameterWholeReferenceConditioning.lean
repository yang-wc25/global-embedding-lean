import Probes.Round3ParameterPrimarySigma
import Probes.Round3PreparedPrimaryConditioning

/-! The genuine all-parameter-chart primary packet has common positive
reference reserves. Every original cutoff and every native chart function
is retained. Finite minima are taken only over fixed reference geometry,
before any perturbed map, smoothing scale or derivative order. -/

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

theorem round3Parameter_actual_whole_reference_conditioning
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
    round3_prepared_primary_common_conditioning Ref hd hs hp hImm i (W i) (part i)
  choose cf ct bn pieces hcf hct hbn hHost hCut hb hbi hSlices hBN hFirst hFrame using hLocal
  obtain ⟨cF,hcF,hcFle⟩ := finite_positive_common_lower_bound cf hcf
  obtain ⟨cT,hcT,hcTle⟩ := finite_positive_common_lower_bound ct hct
  let out := fun nu i (a : packet.s nu i) => pieces i nu ⟨nu,a⟩
  have hPart (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
      (a : packet.s nu i) : part i nu ⟨nu,a⟩ = packet.piece nu i a :=
    round3PreparedPrimarySigmaPiece_active Ref hd i (W i) (fun mu => ↥(packet.s mu i))
      (fun mu b => packet.piece mu i b) nu a
  refine ⟨cF,cT,out,hcF,hcT,?_,?_,?_,?_,?_,?_,?_⟩
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
  · intro nu i a z hz v
    exact (mul_le_mul_of_nonneg_right (hcFle i) (sq_nonneg ‖v‖)).trans (hFirst i nu ⟨nu,a⟩ z hz v)
  · intro nu i a z hz v
    exact (mul_le_mul_of_nonneg_right (hcTle i) (sq_nonneg ‖v‖)).trans (hFrame i nu ⟨nu,a⟩ z hz v)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_whole_reference_conditioning
