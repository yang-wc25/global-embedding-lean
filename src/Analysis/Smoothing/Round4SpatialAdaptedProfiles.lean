import Smoothing.Round4SpatialAdaptedNativeJets
import Smoothing.Round4SpatialPacketProjections
import Probes.ActualSpatialJointJets

/-! The literal spatial two-jet norm gives both actual first/Hessian fields
in a parameter-dependent fixed source chart. All additional derivatives are
joint derivatives and carry exactly their original ell^k weights. The
constant uses original transition jets only through j+2. No total-base-two
input is assumed and no inverse ell loss is inserted.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem round4_original_spatial_fixed_chart_first_hessian_profiles
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hFinite : parameterSpatialWeighted (n := n) (d := d) j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : (parameterSpatialWeighted (n := n) (d := d) j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (e : Ep → OpenPartialHomeomorph M Es)
    (O Z : Set X) (hO : IsOpen O) (hZO : Z ⊆ O)
    (hTransition : ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition A i.1 e) O)
    (hSource : ∀ z ∈ O, (e z.1).symm z.2 ∈ (A.chart i.1).source)
    (hParameter : ∀ z ∈ O, z.1 ∈ (B i.2).target)
    (hSample : ∀ z ∈ Z,
      parameterTensorModelEquiv n d (round3OriginalAdaptedTransition A i.1 e z) ∈ S i)
    (hChartJets : ∀ l, 1 ≤ l → l ≤ j+2 → ∀ z ∈ Z,
      ‖iteratedFDeriv ℝ l (round3OriginalAdaptedTransition A i.1 e) z‖ ≤ T l) :
    let f := fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2)
    let C := round4OriginalSpatialAdaptedCost n d N T j*R
    (ContDiffOn ℝ ∞ (fun w : X => fderiv ℝ (fun x => f (w.1,x)) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ Z, ell^k*‖iteratedFDeriv ℝ k
        (fun w : X => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤ C) ∧
    (ContDiffOn ℝ ∞ (fun w : X => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ Z, ell^k*‖iteratedFDeriv ℝ k
        (fun w : X => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤ C) := by
  dsimp only
  apply round4_spatial_packet_first_hessian_slow_jets _ O Z hO hZO
    (round3_original_actual_adapted_contDiffOn A B F hF i e O hTransition hSource hParameter)
    j ell _ hell.le
  intro k hk z hz
  exact round4_original_spatial_weighted_actual_adapted_jets T hT A B F S hSO hF j ell hell hell1
    hFinite R hR0 hR i e O hO hTransition hSource hParameter z (hZO hz) (hSample z hz)
    (fun l hl hlj => hChartJets l hl hlj z hz) k hk

#print axioms round4_original_spatial_fixed_chart_first_hessian_profiles
end GlobalEmbedding.Continuation
