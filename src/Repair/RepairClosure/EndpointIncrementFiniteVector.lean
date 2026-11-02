import OriginalIncrements.CommonMeanNumerics

/-!
# Independent finite-vector description of the actual increment threshold

Only numerical definitions are used here.  The proved identity is supplied
in EndpointIncrementSolution, not imported into this independent statement.
Four raw/parent profiles and Given are read through J; the two transition
profiles are read through J+1.  No original datum, chart count, constructed
packet, observation order or high input tail occurs in the finite function.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIncrements
universe uM

def endpointIncrementEntranceOrder (q : ℕ) : ℕ := (q+1)*(q+4)+2

def endpointIncrementFiniteExtension (J : ℕ) (v : Fin (J+1) → ℝ) (j : ℕ) : ℝ :=
  if h : j ≤ J then max 0 (v ⟨j,by omega⟩) else 0

theorem endpointIncrementFiniteExtension_nonneg (J : ℕ) (v : Fin (J+1) → ℝ) (j : ℕ) :
    0 ≤ endpointIncrementFiniteExtension J v j := by
  unfold endpointIncrementFiniteExtension
  split
  · exact le_max_left _ _
  · exact le_rfl

def endpointIncrementFiniteThreshold
    {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho) (Ds Dp : ℕ)
    (BS TS BP TP : Fin (endpointIncrementEntranceOrder q+1) → ℝ)
    (Parameter Spatial : Fin (endpointIncrementEntranceOrder q+2) → ℝ)
    (Given : Fin (endpointIncrementEntranceOrder q+1) → ℝ) : ℝ :=
  commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT Mb B H hrho
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q) BS)
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q) TS)
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q) BP)
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q) TP)
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q+1) Parameter)
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q+1) Spatial)
    (endpointIncrementFiniteExtension (endpointIncrementEntranceOrder q) Given)
    Ds Dp (fun j _ => endpointIncrementFiniteExtension_nonneg _ Given j)

/-- The threshold actually used in the producer equals the independent
finite-vector function.  This says more than existence of some valid
constant threshold for one already fixed input. -/
def EndpointIncrementFiniteVectorTarget : Prop :=
  ∀ {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho)
    (BS TS BP TP Parameter Spatial allowed : ℕ → ℝ) (Ds Dp : ℕ)
    (hBS : ∀ j, j ≤ endpointIncrementEntranceOrder q → 0 ≤ BS j)
    (hTS : ∀ j, j ≤ endpointIncrementEntranceOrder q → 0 ≤ TS j)
    (hBP : ∀ j, j ≤ endpointIncrementEntranceOrder q → 0 ≤ BP j)
    (hTP : ∀ j, j ≤ endpointIncrementEntranceOrder q → 0 ≤ TP j)
    (hParameter : ∀ j, j ≤ endpointIncrementEntranceOrder q+1 → 0 ≤ Parameter j)
    (hSpatial : ∀ j, j ≤ endpointIncrementEntranceOrder q+1 → 0 ≤ Spatial j)
    (hAllowed : ∀ j, j ≤ endpointIncrementEntranceOrder q → 0 ≤ allowed j),
    commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed =
    endpointIncrementFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho Ds Dp
      (fun i => BS i) (fun i => TS i) (fun i => BP i) (fun i => TP i)
      (fun i => Parameter i) (fun i => Spatial i) (fun i => allowed i)

end GlobalEmbedding.Continuation.RepairClosure
