import Smoothing.ParameterRound2NativeTensorGermNorms

/-! Literal original weighted norms are preserved by the local observer
identities.  The proof uses the original within-line partial derivatives on
the original differentiation domains, via equality on a genuine open germ.
It does not replace that norm by the total Frechet-derivative norm.  Each
observer may have its own native presentation of the same physical field.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem fullIncrementNov_original_observer_map_weighted_eq
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep) (K V : Set P)
    (hV : IsOpen V) (hKV : K ⊆ V)
    (U : P × M → Ey) (Un : (Fin A.count × Fin c) → Ep × M → Ey)
    (hEq : ∀ i t, t ∈ (B i.2).target → (B i.2).symm t ∈ V →
      ∀ x, Un i (t,x) = U ((B i.2).symm t,x))
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (fun i => incrementsOriginalMapCoordinates A B (fun z => Un i ((B i.2) z.1,z.2)) i)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) =
    paperAtlasWeighted base j ell (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) := by
  let O := incrementsOriginalDifferentiation A B
  let G := V ×ˢ (univ : Set M)
  let W := fun i => O i ∩ (incrementsOriginalJointPoint A B i) ⁻¹' G
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have hW : ∀ i, IsOpen (W i) := fun i =>
    (parameterRound2_originalJointPoint_continuousOn A B i).isOpen_inter_preimage
      (hO i) (hV.prod isOpen_univ)
  have hSW : ∀ i, incrementsOriginalEvaluation A B Omega Q K i ⊆ W i := by
    intro i y hy
    exact ⟨hy.1,hKV hy.2.2.2,mem_univ _⟩
  apply parameterRound2_paperWeighted_eq_of_open_germ _ _ O W _ hO hW
    (fun _ => inter_subset_left) hSW _ base j ell
  intro i y hy
  unfold incrementsOriginalMapCoordinates incrementsOriginalJointPoint
  dsimp only
  rw [(B i.2).right_inv hy.1.2,hEq i _ hy.1.2 hy.2.1]

theorem fullIncrementNov_original_observer_tensor_weighted_eq
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep) (K V : Set P)
    (hV : IsOpen V) (hKV : K ⊆ V)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (Tn : (Fin A.count × Fin c) → (p : Ep) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hEq : ∀ i t, t ∈ (B i.2).target → (B i.2).symm t ∈ V →
      ∀ x, Tn i t x = T ((B i.2).symm t) x)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (fun i => incrementsOriginalTensorCoordinates A B (fun p x => Tn i ((B i.2) p) x) i)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) =
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) := by
  let O := incrementsOriginalDifferentiation A B
  let G := V ×ˢ (univ : Set M)
  let W := fun i => O i ∩ (incrementsOriginalJointPoint A B i) ⁻¹' G
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have hW : ∀ i, IsOpen (W i) := fun i =>
    (parameterRound2_originalJointPoint_continuousOn A B i).isOpen_inter_preimage
      (hO i) (hV.prod isOpen_univ)
  have hSW : ∀ i, incrementsOriginalEvaluation A B Omega Q K i ⊆ W i := by
    intro i y hy
    exact ⟨hy.1,hKV hy.2.2.2,mem_univ _⟩
  apply parameterRound2_paperWeighted_eq_of_open_germ _ _ O W _ hO hW
    (fun _ => inter_subset_left) hSW _ base j ell
  intro i y hy
  funext k
  unfold incrementsOriginalTensorCoordinates incrementsOriginalJointPoint
  dsimp only
  rw [(B i.2).right_inv hy.1.2,hEq i _ hy.1.2 hy.2.1]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_observer_map_weighted_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_observer_tensor_weighted_eq
