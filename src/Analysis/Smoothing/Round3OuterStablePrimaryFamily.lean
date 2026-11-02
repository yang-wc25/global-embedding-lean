import Probes.Round3ParameterOriginalReferenceFactory
import Probes.Round3ParameterStageFamilyFunctions

/-! The whole-parameter stable family is one actual global family on the
same finite Sigma index as the reference family. Every original cutoff and
both physical chart functions are unchanged. Inactive labels use the same
empty chart, so no spurious support or overlap term is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
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

def round3OuterReferencePrimaryPacket
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet) :=
  packet.replacePieces Ref theta profiles.piece profiles.host profiles.cutoff

def round3OuterStablePrimaryPacket
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) :=
  packet.replacePieces Ref theta stable.piece
    (fun nu i a => (stable.host nu i a).trans (profiles.host nu i a))
    (fun nu i a => (stable.cutoff nu i a).trans (profiles.cutoff nu i a))

theorem round3_stable_primary_sigma_functions
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) :
    let old := round3ParameterWholePrimaryPiece Ref hd theta (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles)
    let out := round3ParameterWholePrimaryPiece Ref hd theta (round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable)
    (∀ nu a, (out nu a).host = (old nu a).host) ∧
    (∀ nu a, (out nu a).cutoff = (old nu a).cutoff) ∧
    (∀ nu a, ((out nu a).native : X → X) = (old nu a).native) ∧
    (∀ nu a, ((out nu a).native.symm : X → X) = (old nu a).native.symm) ∧
    (∀ nu a p, (((out nu a).slices p).symm : D → M) = ((old nu a).slices p).symm) := by
  intro old out
  have hSame (nu : Fin Ref.primaryCount) (a : Round3ParameterWholePrimaryIndex Ref theta packet) :
      (out nu a).host = (old nu a).host ∧
      (out nu a).cutoff = (old nu a).cutoff ∧
      ((out nu a).native : X → X) = (old nu a).native ∧
      ((out nu a).native.symm : X → X) = (old nu a).native.symm ∧
      ∀ p, (((out nu a).slices p).symm : D → M) = ((old nu a).slices p).symm := by
    rcases a with ⟨i,mu,a⟩
    by_cases h : mu = nu
    · subst mu
      simpa only [old,out,round3OuterReferencePrimaryPacket,round3OuterStablePrimaryPacket,
        round3ParameterWholePrimaryPiece,Round3ParameterWholePrimaryPieceSupply.replacePieces,
        round3PreparedPrimarySigmaPiece_active] using
        ⟨stable.host nu i a,stable.cutoff nu i a,stable.forward nu i a,
          stable.inverse nu i a,stable.slices nu i a⟩
    · simp only [old,out,round3OuterReferencePrimaryPacket,round3OuterStablePrimaryPacket,
        round3ParameterWholePrimaryPiece,Round3ParameterWholePrimaryPieceSupply.replacePieces,
        round3PreparedPrimarySigmaPiece,h,dite_false]
      exact ⟨trivial,trivial,trivial,trivial,fun _ => trivial⟩
  exact ⟨fun nu a => (hSame nu a).1,fun nu a => (hSame nu a).2.1,
    fun nu a => (hSame nu a).2.2.1,fun nu a => (hSame nu a).2.2.2.1,
    fun nu a => (hSame nu a).2.2.2.2⟩

theorem round3_stable_primary_global_functions
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) :
    let g0 := round3ParameterWholePrimaryFamily Ref hd hs hn theta (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles)
    let g := round3ParameterWholePrimaryFamily Ref hd hs hn theta (round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable)
    g.eta = g0.eta ∧
      (∀ nu a, ((g.chart nu a) : P × M → P × D) = g0.chart nu a) ∧
      (∀ nu a, ((g.chart nu a).symm : P × D → P × M) = (g0.chart nu a).symm) ∧
      g.inverse = g0.inverse := by
  intro g0 g
  have hSame := round3_stable_primary_sigma_functions Ref hd hs theta packet profiles F hF stable
  have hFunctions := round3Parameter_stage_primary_family_same_functions Ref hd hs hn
    (fun (_ : Fin Ref.primaryCount) (a : Round3ParameterWholePrimaryIndex Ref theta packet) => a.1.2)
    (fun _ a => (Ref.parameterChart a.1.2).target ×ˢ (univ : Set M))
    (round3ParameterWholePrimaryPiece Ref hd theta (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles))
    Ref.F Ref.H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain Ref.tensorNeighborhood hd hs hn
    (round3ParameterWholePrimaryPiece Ref hd theta (round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable))
    hSame.1 hSame.2.1 hSame.2.2.1 hSame.2.2.2.1
  refine ⟨hFunctions.1,hFunctions.2.1,hFunctions.2.2,?_⟩
  funext nu a p x
  exact congrFun (hSame.2.2.2.2 nu a ((Ref.parameterChart a.1.2) p)) x

#print axioms round3_stable_primary_sigma_functions
#print axioms round3_stable_primary_global_functions
end GlobalEmbedding.Continuation
