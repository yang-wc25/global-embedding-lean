import Repair.EntranceUniformStableFamily
import Repair.IncrementUniformSecondaryStability
import Repair.IncrementStableSignedGood
import Smoothing.Round3RepairParameterStablePhase

/-!
# The same numerical geometry tolerance retains every original phase

The selected primary and secondary reference packets supply one common
original C2 tolerance.  The actual stable target constructors and the
actual support partitions then prove all original primary and signed
Good predicates.  There is no later compactness choice of a phase radius,
and no limiting Good predicate is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal BigOperators
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
local notation "𝓙" => 𝓘(ℝ,D)

/-- Numerical low geometry of the same selected packets proves the full
original phase clauses for every original-C2-close smooth map. -/
theorem repairEntrance_uniform_original_phase_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hAll : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (primary : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta primary)
    (hPrimaryParam : ∀ nu i a y, y ∈ tsupport (primary.piece nu i a).cutoff →
      y.1 ∈ Ref.parameterNormDomain i.2)
    (secondary : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hSecondaryParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier →
      y.1 ∈ Ref.parameterNormDomain i.2)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (hFirstValue : ∀ r i a, (secondary.piece r i a).cF = cF)
    (hFrameValue : ∀ r i a, (secondary.piece r i a).cT = cT)
    (hHessianBound : ∀ r i a, (secondary.piece r i a).MH ≤ MH)
    (hInverseBound : ∀ r i a j, 1 ≤ j → j ≤ 2 → (secondary.piece r i a).Tinv j ≤ T j)
    (R : ℕ) (hPart : ∀ z, ∑ i, theta i z = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) :
    let epsilonP := repairEntranceGeometryTolerance m d N profiles.Tinv
      profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos
    let epsilonS := repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT
    ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ min epsilonP epsilonS →
    ∃ domain : Fin Ref.primaryCount → Set (P × M),
      (∀ nu, domain nu ⊆ Ref.primaryDomain nu) ∧
      (∀ nu, tsupport (Ref.cutoff nu) ⊆ domain nu) ∧
      let E : IncrementsOriginalNativeData (m+1) d N M P :=
        {Ref with F := Function.uncurry F, primaryDomain := domain}
      ∃ hdE : IncrementsOriginalDomainConditions E,
      ∃ hsE : IncrementsOriginalSmoothInputs E,
        IncrementsOriginalPhaseConditions E hdE hsE := by
  intro epsilonP epsilonS F hFjoint hF S hFinite hBound
  obtain ⟨primaryStable⟩ := repairEntrance_uniform_whole_reference_stable_family Ref hd hs hn
    hF0joint hAll theta primary profiles hPrimaryParam F hFjoint hF hFinite
    (hBound.trans (min_le_left _ _))
  obtain ⟨secondaryStable⟩ := increment_uniform_secondary_stable_family Ref hd hs hAll theta
    secondary hSecondaryParam hF0joint T hT cF cT MH hcF hcT hMH
    hFirstValue hFrameValue hHessianBound hInverseBound F hFjoint hF hFinite
    (hBound.trans (min_le_right _ _))
  exact round3_repair_parameter_stable_full_phase Ref hd hs hn hAll theta primary profiles
    R hPart hCount F hFjoint hF primaryStable
    (increment_stable_secondary_signed_good Ref hd hs theta secondary hPart hSupport F hF secondaryStable)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_uniform_original_phase_factory
