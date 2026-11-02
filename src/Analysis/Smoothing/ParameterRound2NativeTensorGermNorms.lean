import Probes.ActualIncrementOriginalCoordinateJets
import Smoothing.ParameterSpatialPackets

/-! The frozen original weighted tensor norms depend only on actual joint
germs near their evaluation set. The differentiation domain stays original;
restriction to a genuine open neighborhood is proved to change no partial.
No finite-toReal or reverse norm-to-jet shortcut is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

theorem parameterRound2_paperWeighted_eq_of_open_germ
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (f g : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O U S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hU : ∀ i, IsOpen (U i))
    (hUO : ∀ i, U i ⊆ O i) (hSU : ∀ i, S i ⊆ U i)
    (he : ∀ i, EqOn (f i) (g i) (U i)) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell f O S = paperAtlasWeighted base j ell g O S := by
  rw [actual_paperAtlasWeighted_open_restrict base j ell f O U S hO hU hUO hSU,
    actual_paperAtlasWeighted_open_restrict base j ell g O U S hO hU hUO hSU]
  exact paperAtlasWeighted_congr_on base j ell U S hSU he

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

theorem parameterRound2_originalJointPoint_continuousOn
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (i : Fin A.count × Fin c) :
    ContinuousOn (incrementsOriginalJointPoint A B i)
      (incrementsOriginalDifferentiation A B i) := by
  have hp : Continuous (incrementsOriginalParameterPoint (n := n) (d := d)) :=
    (parameterTensorModelEquiv n d).symm.continuous.fst
  have hx : Continuous (incrementsOriginalSourcePoint (n := n) (d := d)) :=
    (parameterTensorModelEquiv n d).symm.continuous.snd
  exact ((B i.2).symm.continuousOn.comp hp.continuousOn (fun y hy => hy.2)).prodMk
    ((A.chart i.1).symm.continuousOn.comp hx.continuousOn (fun y hy => hy.1))

/-- Equality of genuine native tensors on one joint open neighborhood gives
equality of ALL original weighted norms over K, for every later order. Both
the actual parameter inverse and the actual source frame are retained. -/
theorem parameterRound2_originalTensor_weighted_eq_of_germ
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep) (K : Set P)
    (T U : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (G : Set (P × M)) (hG : IsOpen G) (hKG : K ×ˢ (univ : Set M) ⊆ G)
    (he : ∀ z ∈ G, T z.1 z.2 = U z.1 z.2) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) =
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B U)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) := by
  let O := incrementsOriginalDifferentiation A B
  let V := fun i => O i ∩ (incrementsOriginalJointPoint A B i) ⁻¹' G
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (parameterRound2_originalJointPoint_continuousOn A B i).isOpen_inter_preimage (hO i) hG
  have hSV : ∀ i, incrementsOriginalEvaluation A B Omega Q K i ⊆ V i := by
    intro i y hy
    exact ⟨hy.1,hKG ⟨hy.2.2.2,mem_univ _⟩⟩
  apply parameterRound2_paperWeighted_eq_of_open_germ _ _ O V _ hO hV
    (fun _ => inter_subset_left) hSV _ base j ell
  intro i y hy
  funext k
  exact congrArg (fun t => t
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).1)
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).2))
    (he (incrementsOriginalJointPoint A B i y) hy.2)

#print axioms parameterRound2_originalTensor_weighted_eq_of_germ
end GlobalEmbedding.Continuation
