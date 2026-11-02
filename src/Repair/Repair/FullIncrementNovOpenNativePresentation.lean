import Repair.FullIncrementNovOpenParameterTransverse
import Probes.Round3ParameterCrossNativeFamily

/-! The original native family can be represented in every observer without
asserting equality of its base map outside the parameter-open set.  All seven
computational fields are retained.  Refinement samples depend only on cutoff,
eta and chart fields, so their transfer does not need the former global HEq.
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem fullIncrementNov_original_open_native_presentation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Data.primaryCount → Sub → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Sub → Set (Ep × M))
    (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a))
    (observer : Fin Data.atlas.count × Fin Data.parameterCount) :
    let g := round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart observer.2)
    let host := fun nu a => (piece nu a).host
    let b := fun nu a => round3ParameterCrossNativeChart (Data.parameterChart (ip nu a))
      (Data.parameterChart observer.2) (piece nu a).native
    ∃ (e : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D)
      (hdata : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (b nu a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart observer.2).symm z.1,z.2)) (e nu a))
      (hactive : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source →
        ((Data.parameterChart observer.2).symm w.1,w.2) ∈
          Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      let actual := actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive
      (∀ nu a, (b nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,observer.2)) ∧
      (∀ nu a p x, (e nu a p).symm x =
        ((piece nu a).slices ((Data.parameterChart (ip nu a)) ((Data.parameterChart observer.2).symm p))).symm x) ∧
      actual.phase = gN.phase ∧ actual.cutoff = gN.cutoff ∧ actual.normal = gN.normal ∧
      actual.linearArgument = gN.linearArgument ∧ actual.eta = gN.eta ∧
      actual.chart = gN.chart ∧ actual.inverse = gN.inverse := by
  intro g gN host b
  have hEach (nu : Fin Data.primaryCount) (a : Sub) :=
    round3Parameter_actual_cross_native_data Data hd (ip nu a) observer.2 nu (W nu a) (piece nu a)
  choose e hdata hNative hactive hSlices using hEach
  refine ⟨e, hdata, hactive, ?_⟩
  dsimp only
  refine And.intro hNative (And.intro hSlices ?_)
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_
    (And.intro ?_ (And.intro ?_ ?_)))))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext nu a
    exact round3Parameter_cross_host_conjugation (Data.parameterChart (ip nu a))
      (Data.parameterChart observer.2) (Data.atlas.chart (piece nu a).host) (piece nu a).native
      (round3Parameter_primary_native_preserves_phase Data hd (ip nu a) nu (W nu a) (piece nu a)).1
  · funext nu a p x
    exact hSlices nu a p x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_native_presentation
