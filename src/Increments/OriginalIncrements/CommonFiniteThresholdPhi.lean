import OriginalIncrements.CommonThresholdPrefixes

/-!
# The generic entrance is an actual function of finite vectors

This companion packages the already used common threshold without an
original datum, atlas, packet, observation order, or high input tail.
It reads Given/raw vectors through J(q) and transition vectors through
J(q)+1. Its exact equality to the actual consumer threshold is proved.
The clipping only makes the function defined for every real vector; it
does not change any admitted nonnegative original budget.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements

def commonFiniteEntranceOrder (q : ℕ) : ℕ := (q+1)*(q+4)+2

def commonThresholdFiniteExtension (order : ℕ)
    (values : Fin (order+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j ≤ order then max 0 (values ⟨j,by omega⟩) else 0

theorem commonThresholdFiniteExtension_nonneg (order : ℕ)
    (values : Fin (order+1) → ℝ) (j : ℕ) :
    0 ≤ commonThresholdFiniteExtension order values j := by
  unfold commonThresholdFiniteExtension
  split
  · exact le_max_left _ _
  · exact le_rfl

theorem commonThresholdFiniteExtension_eq (order : ℕ) (profile : ℕ → ℝ)
    (hProfile : ∀ j, j ≤ order → 0 ≤ profile j)
    (j : ℕ) (hj : j ≤ order) :
    commonThresholdFiniteExtension order (fun i => profile i) j = profile j := by
  simp only [commonThresholdFiniteExtension,dif_pos hj]
  exact max_eq_right (hProfile j hj)

universe uM
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- A concrete numerical function of seven finite vectors. The source
manifold M is fixed, as in the original mean estimate. -/
def commonFiniteThresholdPhi
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho) (Ds Dp : ℕ)
    (BS TS BP TP : Fin (commonFiniteEntranceOrder q+1) → ℝ)
    (Parameter Spatial : Fin (commonFiniteEntranceOrder q+2) → ℝ)
    (allowed : Fin (commonFiniteEntranceOrder q+1) → ℝ) : ℝ :=
  commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT Mb B H hrho
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q) BS)
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q) TS)
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q) BP)
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q) TP)
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q+1) Parameter)
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q+1) Spatial)
    (commonThresholdFiniteExtension (commonFiniteEntranceOrder q) allowed)
    Ds Dp (fun j _ => commonThresholdFiniteExtension_nonneg _ allowed j)

/-- Exact identity for the threshold used by the generic sampled original
producer. The high profile tails disappear by the proved prefix theorem;
an unrelated constant validity function is never introduced. -/
theorem commonFiniteThreshold_eq_phi
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho)
    (BS TS BP TP Parameter Spatial allowed : ℕ → ℝ) (Ds Dp : ℕ)
    (hBS : ∀ j, j ≤ commonFiniteEntranceOrder q → 0 ≤ BS j)
    (hTS : ∀ j, j ≤ commonFiniteEntranceOrder q → 0 ≤ TS j)
    (hBP : ∀ j, j ≤ commonFiniteEntranceOrder q → 0 ≤ BP j)
    (hTP : ∀ j, j ≤ commonFiniteEntranceOrder q → 0 ≤ TP j)
    (hParameter : ∀ j, j ≤ commonFiniteEntranceOrder q+1 → 0 ≤ Parameter j)
    (hSpatial : ∀ j, j ≤ commonFiniteEntranceOrder q+1 → 0 ≤ Spatial j)
    (hAllowed : ∀ j, j ≤ commonFiniteEntranceOrder q → 0 ≤ allowed j) :
    commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed =
    commonFiniteThresholdPhi (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho Ds Dp
      (fun i => BS i) (fun i => TS i) (fun i => BP i) (fun i => TP i)
      (fun i => Parameter i) (fun i => Spatial i) (fun i => allowed i) := by
  unfold commonFiniteThresholdPhi
  apply commonFiniteThreshold_prefix_congr
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ BS hBS j hj).symm
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ TS hTS j hj).symm
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ BP hBP j hj).symm
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ TP hTP j hj).symm
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ Parameter hParameter j hj).symm
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ Spatial hSpatial j hj).symm
  · exact fun j hj => (commonThresholdFiniteExtension_eq _ allowed hAllowed j hj).symm

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.commonThresholdFiniteExtension_nonneg
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.commonThresholdFiniteExtension_eq
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.commonFiniteThresholdPhi
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.commonFiniteThreshold_eq_phi
