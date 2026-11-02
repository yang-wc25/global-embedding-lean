import Probes.Round3ParameterFixedProfileRebase

/-! Exact physical chart/eta function identities for the actual repaired
family, derived from the stable reference pieces. These are the hypotheses
needed to retain the fixed all-B observer profiles without recomputing any
constants after the current SF or smoothing scale has been chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem round3Parameter_chart_pullback_functions_congr
    {P Q M D : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace M] [TopologicalSpace D]
    (B : OpenPartialHomeomorph P Q)
    (a a0 : OpenPartialHomeomorph (P × M) (P × D))
    (hF : (a : P × M → P × D) = a0)
    (hI : (a.symm : P × D → P × M) = a0.symm) :
    ((round3ParameterChartPullback B a : Q × M → Q × D) = round3ParameterChartPullback B a0) ∧
      (((round3ParameterChartPullback B a).symm : Q × D → Q × M) = (round3ParameterChartPullback B a0).symm) := by
  constructor
  · funext z
    exact congrArg (fun v : P × D => (B v.1,v.2)) (congrFun hF (B.symm z.1,z.2))
  · funext z
    exact congrArg (fun v : P × M => (B v.1,v.2)) (congrFun hI (B.symm z.1,z.2))

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

theorem round3Parameter_stage_primary_family_same_functions
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Ref.primaryCount → Sub → Fin Ref.parameterCount)
    (W : Fin Ref.primaryCount → Sub → Set (Ep × M))
    (old : ∀ nu a, Round3PreparedPrimaryPiece Ref (ip nu a) nu (W nu a))
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}) :
    let Data := round3ParameterStageData Ref F H V normal domain neighborhood
    ∀ (hdNew : IncrementsOriginalDomainConditions Data) (hsNew : IncrementsOriginalSmoothInputs Data)
      (hnNew : IncrementsOriginalFreeNormalConditions Data hdNew hsNew)
      (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a)),
      (∀ nu a, (piece nu a).host = (old nu a).host) →
      (∀ nu a, (piece nu a).cutoff = (old nu a).cutoff) →
      (∀ nu a, ((piece nu a).native : X → X) = (old nu a).native) →
      (∀ nu a, ((piece nu a).native.symm : X → X) = (old nu a).native.symm) →
      let g0 := round3ParameterOriginalPrimaryFamily Ref hd hs hn ip W old
      let g := round3ParameterOriginalPrimaryFamily Data hdNew hsNew hnNew ip W piece
      g.eta = g0.eta ∧
        (∀ nu a, ((g.chart nu a) : P × M → P × D) = g0.chart nu a) ∧
        (∀ nu a, ((g.chart nu a).symm : P × D → P × M) = (g0.chart nu a).symm) := by
  intro Data hdNew hsNew hnNew piece hHost hCut hForw hInv g0 g
  have hAdapt (nu) (a) :
      ((actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native : Ep × M → X) =
        actualHostAdaptedChart (Ref.atlas.chart (old nu a).host) (old nu a).native) ∧
      (((actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native).symm : X → Ep × M) =
        (actualHostAdaptedChart (Ref.atlas.chart (old nu a).host) (old nu a).native).symm) := by
    constructor
    · funext z
      change (piece nu a).native (z.1,Ref.atlas.chart (piece nu a).host z.2) =
        (old nu a).native (z.1,Ref.atlas.chart (old nu a).host z.2)
      rw [hHost]
      exact congrFun (hForw nu a) _
    · funext z
      change (((piece nu a).native.symm z).1,
          (Ref.atlas.chart (piece nu a).host).symm ((piece nu a).native.symm z).2) =
        (((old nu a).native.symm z).1,
          (Ref.atlas.chart (old nu a).host).symm ((old nu a).native.symm z).2)
      rw [hHost]
      exact congrArg (fun v : X => (v.1,(Ref.atlas.chart (old nu a).host).symm v.2)) (congrFun (hInv nu a) z)
  have hLift (nu) (a) := round3Parameter_chart_pullback_functions_congr (Ref.parameterChart (ip nu a)).symm
    (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native)
    (actualHostAdaptedChart (Ref.atlas.chart (old nu a).host) (old nu a).native)
    (hAdapt nu a).1 (hAdapt nu a).2
  refine ⟨?_,fun nu a => (hLift nu a).1,fun nu a => (hLift nu a).2⟩
  funext nu a z
  change (if z.1 ∈ (Ref.parameterChart (ip nu a)).source then
      (piece nu a).cutoff ((Ref.parameterChart (ip nu a)) z.1,z.2) else 0) =
    (if z.1 ∈ (Ref.parameterChart (ip nu a)).source then
      (old nu a).cutoff ((Ref.parameterChart (ip nu a)) z.1,z.2) else 0)
  by_cases hz : z.1 ∈ (Ref.parameterChart (ip nu a)).source
  · simp only [hz,ite_true]
    exact congrFun (hCut nu a) _
  · simp only [hz,ite_false]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_chart_pullback_functions_congr
#print axioms GlobalEmbedding.Continuation.round3Parameter_stage_primary_family_same_functions
