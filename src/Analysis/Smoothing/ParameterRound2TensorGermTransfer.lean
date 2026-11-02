import Smoothing.ParameterRound2TensorGermSpace
import Smoothing.ParameterRound2PrimaryRestrictionMean
import Smoothing.ParameterRound2SymmetricTensorSpace

/-! Exact transfer from a finite positivity neighborhood back to the SAME
native mean. Both local smoothness and the unchanged original norm pass
through the proved actual chart-restriction identities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

theorem parameterRound2_originalTensor_weighted_eq_of_sample_germ
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T U : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (G : Set (P × M)) (hG : IsOpen G)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G)
    (he : ∀ z ∈ G, T z.1 z.2 = U z.1 z.2) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) S =
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S := by
  let O := incrementsOriginalDifferentiation A B
  let V := fun i => O i ∩ (incrementsOriginalJointPoint A B i) ⁻¹' G
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (parameterRound2_originalJointPoint_continuousOn A B i).isOpen_inter_preimage (hO i) hG
  have hSV : ∀ i, S i ⊆ V i := fun i y hy => ⟨hSO i hy,hSG i hy⟩
  apply parameterRound2_paperWeighted_eq_of_open_germ _ _ O V S hO hV
    (fun _ => inter_subset_left) hSV _ base j ell
  intro i y hy
  funext k
  exact congrArg (fun t => t
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).1)
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).2))
    (he (incrementsOriginalJointPoint A B i y) hy.2)

theorem parameterRound2_tensor_coordinate_germ_transfer
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T U : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (hT : ∀ i, ∃ V : Set (Fin (n+d) → ℝ), IsOpen V ∧ S i ⊆ V ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T i) V)
    (G : Set (P × M)) (hG : IsOpen G)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G)
    (he : ∀ z ∈ G, T z.1 z.2 = U z.1 z.2) :
    ∀ i, ∃ V : Set (Fin (n+d) → ℝ), IsOpen V ∧ S i ⊆ V ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B U i) V := by
  intro i
  obtain ⟨V,hV,hSV,hreg⟩ := hT i
  let OG := incrementsOriginalDifferentiation A B i ∩ (incrementsOriginalJointPoint A B i) ⁻¹' G
  have hOG : IsOpen OG := (parameterRound2_originalJointPoint_continuousOn A B i).isOpen_inter_preimage
    (parameterRound2_originalDifferentiation_open A B i) hG
  refine ⟨V ∩ OG,hV.inter hOG,fun y hy => ⟨hSV hy,hSO i hy,hSG i hy⟩,?_⟩
  apply (hreg.mono inter_subset_left).congr
  intro y hy
  funext k
  exact (congrArg (fun t => t
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).1)
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).2))
    (he (incrementsOriginalJointPoint A B i y) hy.2.2)).symm

section Mean
variable {m N : ℕ} {M0 : Type*} [TopologicalSpace M0]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M0]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M0]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M0]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D0" => EuclideanSpace ℝ (Fin (m+1))
local notation "V0" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_restrictPrimary_meanError_germ_mem
    (A : BufferedAtlas M0 D0) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M0))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F : Ep → M0 → V0) (hF : ∀ p, ContMDiff 𝓘(ℝ,D0) 𝓘(ℝ,V0) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D0)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : parameterRound2_originalTensorGermSpace A B S W)
    (length : ℕ) (tau : ℝ) (G : Set (Ep × M0)) (hG : IsOpen G)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G)
    (hreg : ∀ i, ∃ V : Set (Fin (m+1+d) → ℝ), IsOpen V ∧ S i ⊆ V ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B
        (incrementsGlobalPrimaryMeanError F hF (parameterRound2_restrictPrimaryFamily F g G hG)
          input.val length tau) i) V) :
    incrementsGlobalPrimaryMeanError F hF g input.val length tau ∈
      parameterRound2_originalTensorGermSpace A B S W := by
  constructor
  · exact parameterRound2_tensor_coordinate_germ_transfer A B S hSO _ _ hreg G hG hSG
      (parameterRound2_restrictPrimary_meanError F hF g G hG input.val length tau)
  · intro z hz
    exact (parameterRound2_actual_native_mean_symmetric F hF g input.val length tau z.1 z.2).sub
      (input.property.2 z hz)
end Mean

#print axioms parameterRound2_originalTensor_weighted_eq_of_sample_germ
#print axioms parameterRound2_restrictPrimary_meanError_germ_mem
end GlobalEmbedding.Continuation
