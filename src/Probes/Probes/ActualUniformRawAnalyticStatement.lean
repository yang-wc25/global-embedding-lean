import Probes.ActualSecondaryRawGermFiniteIncrement

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

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

def ActualRawAnalyticBudget
    (q Rsub Lprimary Rsecondary : ℕ) (reserve : ℝ)
    (Brest Mrest Kcut T Tinv Tobs TP CR CU : ℕ → ℝ) : Prop :=
    ∀ j : ℕ, ∀
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
      (_hA : IsSmoothBufferedAtlas A) (_hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
      (_hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (ell delta tau Delta : ℝ) (_htau : 0 < tau) (_htaul : tau ≤ ell) (_hell1 : ell ≤ 1)
      (_hdelta : 0 ≤ delta) (_hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary
        reserve (Brest j) (Mrest j) (Kcut j) T Tinv W primary ell delta tau Delta choice)
      (Omega : Fin A.count × Fin c → Set X)
      (_obs : ∀ i : Fin A.count × Fin c, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Omega i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)))
      (_hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
        parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j+1 →
        ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k),
    let U := actualOriginalIncrementMap F hF g input (q+2) tau delta choice
    let coordinates := incrementsOriginalMapCoordinates A B U
    let Rest := incrementsOriginalMetricError (fun y => F y.1 y.2) U
      (incrementsGlobalPrimaryMean F hF g input (q+2) tau) delta
    Rest ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
        (incrementsOriginalDifferentiation A B) S).toReal ≤ CR j*(delta*(tau/ell)^q+delta^3/tau)) ∧
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ CU j*delta*tau) ∧
    (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ CU j*delta)

end GlobalEmbedding.Continuation
