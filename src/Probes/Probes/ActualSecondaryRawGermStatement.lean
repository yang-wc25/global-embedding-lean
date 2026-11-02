import Probes.ActualSecondaryRawOriginalGermRemainder
import Probes.ActualSecondaryGermMetricAddition
import Probes.ActualOriginalIncrementRawNorms
import Smoothing.ParameterRound2MeanRawGermFiniteResidual
import Smoothing.ParameterRound2MeanGermResidualMembership

/-! Complete original metric-error estimate for the SAME finite construction.
The actual finite mean iteration is performed internally. Pure original raw
profiles and fixed actual host/refinement choices produce every primary,
quadratic forcing, secondary and mixed/self metric term. No bound for a
mean, residual, U1, U2 or metric error is an input. The chosen global map and
the mean iterate precede every later derivative order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

def actualSecondarySolveOrder (q j : ℕ) : ℕ := j+q+4
def actualSecondaryInputOrder (q j : ℕ) : ℕ := j+2*q+8

def ActualOriginalRawGermFiniteStatement
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) : Prop :=
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
      (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (primary : Label → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bmean Mmean Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    ∀ (delta : ℝ), 0 ≤ delta → delta ≤ epsilon*ell →
    ∀ (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m),
    let U := actualOriginalIncrementMap F hF g (K q).val (q+2) (epsilon*ell) delta choice
    ∀ (j : ℕ)
      (inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (Delta : ℝ)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g (K q).val inputbar
        (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary
        reserve (Brest j) (Mrest j) (Kcut j) T Tinv W primary ell delta (epsilon*ell) Delta choice)
      (Obs : Fin A.count × Fin c → Set X)
      (obs : ∀ i : Fin A.count × Fin c, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))),
    let E := incrementsOriginalMetricError (fun y => F y.1 y.2) U H.val delta
    let coordinates := incrementsOriginalMapCoordinates A B U
    E ∈ parameterRound2_originalTensorGermSpace A B S W ∧
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
