import Smoothing.ParameterRound2MeanFinalRestriction
import Probes.ActualUniformRawAnalyticCosts
import Smoothing.ParameterRound2MeanGermResidualMembership
import Smoothing.ParameterRound2UniformRawMeanResidual

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def ActualRestrictedRawFiniteIncrementConclusion
    (q Rsub Lprimary Rsecondary : ℕ) (reserve : ℝ)
    (Brest Mrest Kcut T Tinv Tobs : ℕ → ℝ)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (primary : Label → Set (Ep × M)) (epsilon0 : ℝ) (C : ℕ → ℝ)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W) : Prop :=
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    ∀ (G : Set (Ep × M)) (hG : IsOpen G), G ⊆ W →
    (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) →
    let gG := parameterRound2_restrictPrimaryFamily F g G hG
    ∀ (delta : ℝ), 0 ≤ delta → delta ≤ epsilon*ell →
    ∀ (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m),
    let U := actualOriginalIncrementMap F hF gG (K q).val (q+2) (epsilon*ell) delta choice
    ∀ (j : ℕ)
      (inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (Delta : ℝ)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF gG (K q).val inputbar
        (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary
        reserve (Brest j) (Mrest j) (Kcut j) T Tinv G primary ell delta (epsilon*ell) Delta choice)
      (Obs : Fin A.count × Fin c → Set X)
      (obs : ∀ i : Fin A.count × Fin c, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))),
    let E := incrementsOriginalMetricError (fun y => F y.1 y.2) U H.val delta
    let coordinates := incrementsOriginalMapCoordinates A B U
    E ∈ parameterRound2_originalTensorGermSpace A B S G ∧
    (paperAtlasWeighted 0 j (epsilon*ell) (incrementsOriginalTensorCoordinates A B E)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j (epsilon*ell) (incrementsOriginalTensorCoordinates A B E)
        (incrementsOriginalDifferentiation A B) S).toReal ≤
        C j*(delta*((epsilon*ell)/ell)^q+delta^3/(epsilon*ell))) ∧
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 0 (j+1) (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 (j+1) (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤
        C j*delta*(epsilon*ell)) ∧
    (paperAtlasWeighted 1 j (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 1 j (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤
        C j*delta)


end GlobalEmbedding.Continuation
