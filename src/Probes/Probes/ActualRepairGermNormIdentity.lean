import Probes.ActualRepairMetricPointwise
import Probes.ActualRepairCoordinateGerms
import Probes.ActualRepairGermNormAlgebra
import Smoothing.ParameterRound2RepairNormIdentity

/-! Equation (6.6) and its original weighted norm on the actual sample
neighborhoods of the SAME update G+U. No global regularity of U is required.
The three terms are exactly the tensor tail, actual finite metric error and
Cross(G-SG,U); the second-order smoothing defect never appears. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

 theorem actual_repair_weighted_norm_identity_germs
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (G SG U : P × M → V)
    (hMaps : ∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      V0 ⊆ incrementsOriginalDifferentiation A B i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B G i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B SG i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B U i) V0)
    (hstar h0 SH : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (delta deltaNext : ℝ) (hdelta : delta ≠ 0) (hdeltaNext : deltaNext ≠ 0)
    (j : ℕ) (tau : ℝ) (htau : 0 < tau) :
    let H := fun p x => (delta^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)) x)
    let E := incrementsOriginalMetricError SG U (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) delta
    let cross := fun p x => metricCrossTerm (I := 𝓙) (fun y => G (p,y)-SG (p,y)) (fun y => U (p,y)) x
    let Hnext := fun p x => (deltaNext^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)+U (p,y)) x)
    let f := incrementsOriginalTensorCoordinates A B (fun p x => H p x-SH p x)
    let g := incrementsOriginalTensorCoordinates A B E
    let h := incrementsOriginalTensorCoordinates A B cross
    let next := incrementsOriginalTensorCoordinates A B (fun p x => Hnext p x-h0 p x)
    let O := incrementsOriginalDifferentiation A B
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (f i) V0) →
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (g i) V0) →
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (h i) V0) →
    paperAtlasWeighted 0 j tau f O S ≠ ⊤ →
    paperAtlasWeighted 0 j tau g O S ≠ ⊤ →
    paperAtlasWeighted 0 j tau h O S ≠ ⊤ →
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      V0 ⊆ O i ∧ ContDiffOn ℝ ∞ (next i) V0) ∧
    paperAtlasWeighted 0 j tau next O S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau next O S).toReal ≤ (deltaNext^2)⁻¹ *
      (delta^2*(paperAtlasWeighted 0 j tau f O S).toReal+
        (paperAtlasWeighted 0 j tau g O S).toReal+(paperAtlasWeighted 0 j tau h O S).toReal) := by
  intro H E cross Hnext f g h next O hf hg hh hfFinite hgFinite hhFinite
  choose V0 hV0 hSV hVO hG hSG hU using hMaps
  let R := fun i x => (deltaNext^2)⁻¹ • (delta^2 • f i x-g i x-h i x)
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have heq : ∀ i, EqOn (next i) (R i) (V0 i) := by
    intro i y hy
    let p := (B i.2).symm (incrementsOriginalParameterPoint y)
    let x := (A.chart i.1).symm (incrementsOriginalSourcePoint y)
    have hDG := actual_source_slice_mdifferentiable_of_original_coordinate_germ A B hA G i y (hVO i hy)
      ((hG i).contDiffAt ((hV0 i).mem_nhds hy))
    have hDSG := actual_source_slice_mdifferentiable_of_original_coordinate_germ A B hA SG i y (hVO i hy)
      ((hSG i).contDiffAt ((hV0 i).mem_nhds hy))
    have hDU := actual_source_slice_mdifferentiable_of_original_coordinate_germ A B hA U i y (hVO i hy)
      ((hU i).contDiffAt ((hV0 i).mem_nhds hy))
    have hid := actual_repair_normalized_defect_identity_at (I := 𝓙)
      (fun z => G (p,z)) (fun z => SG (p,z)) (fun z => U (p,z)) x hDG hDSG hDU
      delta deltaNext hdelta hdeltaNext (hstar p x) (h0 p x) (SH p x)
    have hid' : deltaNext^2 • (Hnext p x-h0 p x) = delta^2 • (H p x-SH p x)-E p x-cross p x := hid
    have hnative := congrArg (fun T => (deltaNext^2)⁻¹ • T) hid'
    simp only [smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hdeltaNext),one_smul] at hnative
    funext k
    exact congrArg (fun T : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) =>
      T (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).1)
        (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).2)) hnative
  obtain ⟨hRgerm,hRf,hRb⟩ := actual_paperWeighted_normalized_three_terms_germs j htau f g h O S hO hSO
    hf hg hh hfFinite hgFinite hhFinite (delta^2) ((deltaNext^2)⁻¹) (sq_nonneg _) (by positivity)
  have hnorm := parameterRound2_paperWeighted_eq_of_open_germ next R O V0 S hO hV0 hVO hSV heq 0 j tau
  refine ⟨?_,?_,?_⟩
  · intro i
    obtain ⟨V1,hV1,hSV1,hR1⟩ := hRgerm i
    refine ⟨V1 ∩ V0 i,hV1.inter (hV0 i),fun y hy => ⟨hSV1 hy,hSV i hy⟩,
      fun y hy => hVO i hy.2,?_⟩
    exact (hR1.mono inter_subset_left).congr (fun y hy => heq i hy.2)
  · rwa [hnorm]
  · rwa [hnorm]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_weighted_norm_identity_germs
