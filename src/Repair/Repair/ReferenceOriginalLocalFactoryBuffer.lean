import Repair.ReferenceOriginalLocalFactory
import Repair.ReferencePlateau

/-! A genuine common buffer inside the same original normal carrier. The
factory source is the radius-4 ball, the primary support lies in radius 2,
and the numerical normal cap keeps the radius-3 ball in the carrier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

theorem repair_reference_ball_buffer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c x : E) (r : ℝ) (hx : x ∈ closedBall c (2*r)) :
    ball x r ⊆ closedBall c (3*r) := by
  intro y hy
  have h := (dist_triangle y x c).trans_lt
    (add_lt_add_of_lt_of_le (mem_ball.mp hy) (mem_closedBall.mp hx))
  exact mem_closedBall.mpr (by linarith)

theorem repair_reference_three_ball_normal_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : OpenPartialHomeomorph E E) (c : E) (r B rho : ℝ)
    (hr : 0 < r) (hB : 0 < B) (hSource : b.source=ball c (4*r))
    (hSmooth : ContDiffOn ℝ ∞ b b.source) (hConv : Convex ℝ b.source)
    (hBound : ∀ x ∈ b.source, ‖fderiv ℝ b x‖ ≤ B)
    (hCap : 4*B*r ≤ rho) :
    closedBall c (3*r) ⊆ round4NormalCutoffCarrier b c rho := by
  have hcenter : c ∈ b.source := by rw [hSource]; exact mem_ball_self (by positivity)
  have hSmall : 2*B*(3*r/2)<rho := by nlinarith [mul_pos hB hr]
  have hSub : closedBall c (2*(3*r/2)) ⊆ b.source := by
    rw [hSource]
    exact closedBall_subset_ball (by linarith)
  have hh := round4_actual_closedBall_in_normal_carrier b hSmooth hConv B hB.le hBound c hcenter
    (3*r/2) rho hSub hSmall
  have heq : 2*(3*r/2)=3*r := by ring
  simpa only [heq] using hh

namespace RepairReferenceFactoryBudget
variable {m d N : ℕ}

theorem forward_pos (b : RepairReferenceFactoryBudget m d N) : 0 < b.forward := by
  have := b.cover.covectorBound_pos
  dsimp [forward]
  positivity

theorem normal_cutoff_cap (b : RepairReferenceFactoryBudget m d N) :
    4*b.forward*b.cutoffRadius ≤ b.normalRadius := by
  have hfactor := actualPhaseRefinementFactor_pos
    (round4UniformTemplateCovectorLower_spec (EuclideanSpace ℝ (Fin (m+1)))
      (EuclideanSpace ℝ (Fin N)) b.templateDim b.operatorBound b.phaseMargin b.tensorLower
      b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos).1 b.cover.covectorBound_pos.le
  change 0 < actualPhaseRefinementFactor b.covectorLower b.cover.covectorBound at hfactor
  have hh := (round4UniformNormalRefinementRadius_spec (N := N) b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos b.buffer b.firstLower b.nativeMap3 b.lipschitz
    b.buffer_pos b.firstLower_pos b.nativeMap3_nonneg).2.2.2
  change b.radius ≤ actualPhaseRefinementFactor b.covectorLower b.cover.covectorBound *
    b.normalRadius/(4*b.forward) at hh
  have hforward := b.forward_pos
  have hmul := (le_div_iff₀ (show 0<4*b.forward by positivity)).mp hh
  unfold cutoffRadius
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hfactor).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hmul

end RepairReferenceFactoryBudget

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

theorem RepairReferenceOriginalLocalFactory.plateau_carrier
    {b : RepairReferenceFactoryBudget m d N}
    {seed : RepairOriginalReferenceSeed (m+1) d N M P}
    {hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x))}
    {Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    {S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ)}
    {i : Fin seed.atlas.count × Fin seed.parameterCount} {O K : Set X} {center : X}
    (localData : RepairReferenceOriginalLocalFactory b seed hF Htensor S i O K center)
    (z : localData.s) (a : Edge) :
    tsupport (repairReferencePlateau X b.cutoffRadius z.val) ⊆
      round4NormalCutoffCarrier (localData.charts z a).chart z.val b.normalRadius := by
  have hSource : (localData.charts z a).chart.source=ball z.val (4*b.cutoffRadius) := by
    rw [(localData.charts z a).source_ball, ← actualPhaseRefinementFactor_radius]
    rfl
  rw [repair_reference_plateau_support X b.cutoffRadius b.cutoffRadius_pos z.val]
  exact repair_reference_three_ball_normal_carrier (localData.charts z a).chart z.val
    b.cutoffRadius b.forward b.normalRadius b.cutoffRadius_pos b.forward_pos hSource
    (localData.charts z a).smooth (localData.charts z a).source_convex
    (localData.charts z a).forward_bound b.normal_cutoff_cap

theorem RepairReferenceOriginalLocalFactory.support_buffer
    {b : RepairReferenceFactoryBudget m d N}
    {seed : RepairOriginalReferenceSeed (m+1) d N M P}
    {hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x))}
    {Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    {S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ)}
    {i : Fin seed.atlas.count × Fin seed.parameterCount} {O K : Set X} {center : X}
    (localData : RepairReferenceOriginalLocalFactory b seed hF Htensor S i O K center)
    (z : localData.s) (a : Edge) (x : X)
    (hx : x ∈ tsupport (round4RefinementSquareCutoff X localData.s b.cutoffRadius z)) :
    ball x b.cutoffRadius ⊆
      round4NormalCutoffCarrier (localData.charts z a).chart z.val b.normalRadius := by
  have hs : x ∈ closedBall z.val (2*b.cutoffRadius) := by
    have hh := tensorLocalNormalizedCutoff_tsupport_subset
      (fun q : localData.s => actualRefinementBump X b.cutoffRadius q.val) z hx
    rwa [actualRefinementBump_tsupport X b.cutoffRadius b.cutoffRadius_pos z.val] at hh
  have hb := repair_reference_ball_buffer z.val x b.cutoffRadius hs
  apply hb.trans
  rw [← repair_reference_plateau_support X b.cutoffRadius b.cutoffRadius_pos z.val]
  exact localData.plateau_carrier z a

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.RepairReferenceOriginalLocalFactory.plateau_carrier
#print axioms GlobalEmbedding.Continuation.RepairReferenceOriginalLocalFactory.support_buffer
