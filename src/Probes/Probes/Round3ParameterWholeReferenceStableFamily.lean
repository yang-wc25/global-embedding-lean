import Probes.Round3ParameterOriginalPrimarySamples

/-! A single original C2 tolerance for the actual all-chart reference packet.
Every later whole-parameter stage retains the same cutoff, native forward
function, inverse function and sliced inverse function.  Only genuine stable
target domains change. All fixed reference chart profiles remain valid.
The numerical new-map reserves are outputs, not supplied stage assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
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

structure Round3ParameterWholeStableReference
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)) where
  piece : ∀ nu i, packet.s nu i → Round3PreparedPrimaryPiece Ref i.2 nu
    ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))
  host : ∀ nu i a, (piece nu i a).host = (profiles.piece nu i a).host
  cutoff : ∀ nu i a, (piece nu i a).cutoff = (profiles.piece nu i a).cutoff
  forward : ∀ nu i a, ((piece nu i a).native : X → X) = (profiles.piece nu i a).native
  inverse : ∀ nu i a, ((piece nu i a).native.symm : X → X) = (profiles.piece nu i a).native.symm
  slices : ∀ nu i a p, (((piece nu i a).slices p).symm : D → M) = ((profiles.piece nu i a).slices p).symm
  source_subset : ∀ nu i a, (piece nu i a).native.source ⊆ (profiles.piece nu i a).native.source
  target_subset : ∀ nu i a, (piece nu i a).native.target ⊆ (profiles.piece nu i a).native.target
  first : ∀ nu i a z, z ∈ (piece nu i a).native.target → ∀ v : D,
    (profiles.cF/16)*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart i.2).symm z.1) ∘
      ((piece nu i a).slices z.1).symm) z.2 v‖^2
  transverse : ∀ nu i a z, z ∈ (piece nu i a).native.target → ∀ v : Tdata,
    (profiles.cT/16)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (F ((Ref.parameterChart i.2).symm z.1)) (hF ((Ref.parameterChart i.2).symm z.1))
      ((piece nu i a).slices z.1).symm z.2 v‖^2
  normal : ∀ nu i a z, z ∈ (piece nu i a).native.target → (1/4 : ℝ) ≤
    ‖actualFreeNormalProjectionRaw
      (fderiv ℝ (F ((Ref.parameterChart i.2).symm z.1) ∘ ((piece nu i a).slices z.1).symm) z.2)
      (incrementsModeAmbientTransverseFrame
        (F ((Ref.parameterChart i.2).symm z.1)) (hF ((Ref.parameterChart i.2).symm z.1))
        ((piece nu i a).slices z.1).symm z.2)
      (Ref.freeNormal nu ((Ref.parameterChart i.2).symm z.1,((piece nu i a).slices z.1).symm z.2))‖
  inverse_jets : ∀ nu i a j z, z ∈ (piece nu i a).native.target →
    ‖iteratedFDeriv ℝ j (piece nu i a).native.symm z‖ ≤ profiles.Tinv j
  forward_jets : ∀ nu i a j z, z ∈ (piece nu i a).native.source →
    ‖iteratedFDeriv ℝ j (piece nu i a).native z‖ ≤ profiles.Tforward j

theorem round3Parameter_whole_reference_stable_family
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hK : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (hParam : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff → y.1 ∈ Ref.parameterNormDomain i.2) :
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
    Nonempty (Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) := by
  have hOpen (p : P) : p ∈ Ref.parameterOpen := hd.parameter_subset (by rw [hK]; exact mem_univ _)
  have hLocal (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (a : packet.s nu i) :=
    round3Parameter_reference_C2_pointwise Ref hd hs hn i.2 nu _ (profiles.piece nu i a) hK
      (fun y hy => profiles.source_inner nu i a y ((profiles.piece nu i a).support hy))
      (fun y hy => hParam nu i a y (by rwa [profiles.cutoff] at hy)) hF0joint
      profiles.Tinv profiles.Tinv_nonneg profiles.cF profiles.cT profiles.MH
      profiles.cF_pos profiles.cT_pos profiles.MH_nonneg
      (profiles.first nu i a)
      (by
        intro z hz v
        have hh := profiles.transverse nu i a z hz v
        have hEq : actualOriginalOpenParameterSlice Ref i z.1 =
            fun x => Ref.F ((Ref.parameterChart i.2).symm z.1,x) := by
          rw [actualOriginalOpenParameterSlice_eq Ref i z.1 (hOpen _)]
          rfl
        simpa only [hEq] using hh)
      (profiles.hessian nu i a)
      (fun j y hy => profiles.inverse_jets nu i a j _ (by
        rw [← (profiles.piece nu i a).data.1]
        exact (actualHostAdaptedChart (Ref.atlas.chart (profiles.piece nu i a).host)
          (profiles.piece nu i a).native).map_source ((profiles.piece nu i a).support hy)))
  choose eps heps hStable using hLocal
  let Index := Sigma (fun nu : Fin Ref.primaryCount => Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s nu i)))
  obtain ⟨epsilon,hepsilon,hEps⟩ := finite_positive_common_lower_bound
    (fun a : Index => eps a.1 a.2.1 a.2.2) (fun a : Index => heps a.1 a.2.1 a.2.2)
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound
  have hTarget (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (a : packet.s nu i) :=
    round3Parameter_whole_primary_stable_target Ref hd hs i.2 nu _ (profiles.piece nu i a)
      F hF hFjoint (profiles.cF/4) (profiles.cT/4) (1/2)
      (div_pos profiles.cF_pos (by norm_num)) (div_pos profiles.cT_pos (by norm_num)) (by norm_num)
      (hStable nu i a F hFjoint hF hFinite (hBound.trans (hEps ⟨nu,i,a⟩)))
  choose b e hb hbi hSlices hSource hData hSupport hASource hFirst hFrame hNormal using hTarget
  have hTargetSub (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (a : packet.s nu i) :
      (b nu i a).target ⊆ (profiles.piece nu i a).native.target := by
    intro z hz
    have hh := (profiles.piece nu i a).native.map_source (hSource nu i a ((b nu i a).map_target hz))
    rw [← hb nu i a,(b nu i a).right_inv hz] at hh
    exact hh
  let out := fun nu i (a : packet.s nu i) => ({
    host := (profiles.piece nu i a).host
    native := b nu i a
    slices := e nu i a
    cutoff := (profiles.piece nu i a).cutoff
    data := hData nu i a
    native_source := (hSource nu i a).trans (profiles.piece nu i a).native_source
    source_domain := (hASource nu i a).trans (profiles.piece nu i a).source_domain
    active := fun w hw => (profiles.piece nu i a).active w (hASource nu i a hw)
    compact := (profiles.piece nu i a).compact
    smooth := (profiles.piece nu i a).smooth
    support := hSupport nu i a
    Bnative := (profiles.piece nu i a).Bnative
    positive := (profiles.piece nu i a).positive
    native_first := by
      intro z hz
      rw [hb]
      exact (profiles.piece nu i a).native_first z (hSource nu i a hz)
  } : Round3PreparedPrimaryPiece Ref i.2 nu ((Ref.parameterChart i.2).target ×ˢ (univ : Set M)))
  refine ⟨{
    piece := out
    host := fun _ _ _ => rfl
    cutoff := fun _ _ _ => rfl
    forward := hb
    inverse := hbi
    slices := hSlices
    source_subset := hSource
    target_subset := hTargetSub
    first := ?_
    transverse := ?_
    normal := ?_
    inverse_jets := ?_
    forward_jets := ?_ }⟩
  · intro nu i a z hz v
    simpa only [div_div,show (4:ℝ)*4 = 16 by norm_num] using hFirst nu i a z hz v
  · intro nu i a z hz v
    simpa only [div_div,show (4:ℝ)*4 = 16 by norm_num] using hFrame nu i a z hz v
  · intro nu i a z hz
    simpa only [div_div,show (2:ℝ)*2 = 4 by norm_num] using hNormal nu i a z hz
  · intro nu i a j z hz
    change ‖iteratedFDeriv ℝ j (b nu i a).symm z‖ ≤ _
    rw [hbi]
    exact profiles.inverse_jets nu i a j z (hTargetSub nu i a hz)
  · intro nu i a j z hz
    change ‖iteratedFDeriv ℝ j (b nu i a) z‖ ≤ _
    rw [hb]
    exact profiles.forward_jets nu i a j z (hSource nu i a hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_whole_reference_stable_family
