import Probes.Round4OriginalUniformNormal
import Probes.ActualFirstFrameChartTransfer
import Probes.ActualIncrementSymmetricCoordinates

/-! A numerical radius chosen before the fields places the entire actual
cutoff support inside one genuine normal neighborhood. The same partial
chart is used on both sides; convexity and its real forward derivative
bound produce the needed distance estimate. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def round4NativeNormalLowBudget (I K : ℝ) : ℝ :=
  actualFirstFrameTransferCost (fun _ => I) 2*K

def round4NativeNormalRadius (m N : ℕ) (c0 B I eta K : ℝ) : ℝ :=
  round4OriginalNormalRadius m N (c0/B^2)
    ((eta/(B^2*actualIncrementSortedSymmetricConstant m))^2)
    (round4NativeNormalLowBudget I K) (round4NativeNormalLowBudget I K)

theorem round4NativeNormalRadius_pos (m N : ℕ) {c0 B I eta K : ℝ}
    (hc0 : 0 < c0) (hB : 0 < B) (hI : 0 ≤ I) (heta : 0 < eta) (hK : 0 ≤ K) :
    0 < round4NativeNormalRadius m N c0 B I eta K := by
  have hcF : 0 < c0/B^2 := div_pos hc0 (sq_pos_of_pos hB)
  have hcT : 0 < (eta/(B^2*actualIncrementSortedSymmetricConstant m))^2 :=
    sq_pos_of_pos (div_pos heta (mul_pos (sq_pos_of_pos hB) (actualIncrementSortedSymmetricConstant_pos m)))
  have hLow : 0 ≤ round4NativeNormalLowBudget I K :=
    mul_nonneg (actualFirstFrameTransferCost_nonneg _ (fun _ => hI) 2) hK
  have hFrame := actualIncrementTransverseFrameConstant_nonneg m N 1 hcF hLow hLow
  have hCost := round4FreeProjectionFirstCost_nonneg hcF hcT hLow hFrame
  exact div_pos (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num)) (by
    change 0 < round4FreeProjectionFirstCost _ _ _ _ + 1
    linarith)

def round4NormalCutoffCarrier {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : OpenPartialHomeomorph X X) (center : X) (rhoN : ℝ) : Set X :=
  b.source ∩ b ⁻¹' ball (b center) rhoN

theorem round4NormalCutoffCarrier_open
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : OpenPartialHomeomorph X X) (center : X) (rhoN : ℝ) :
    IsOpen (round4NormalCutoffCarrier b center rhoN) :=
  b.isOpen_inter_preimage isOpen_ball

theorem round4NormalCutoffCarrier_mapsTo
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : OpenPartialHomeomorph X X) (center : X) (rhoN : ℝ) :
    MapsTo b (round4NormalCutoffCarrier b center rhoN)
      (b.target ∩ ball (b center) rhoN) :=
  fun _ hz => ⟨b.map_source hz.1,hz.2⟩

theorem round4_actual_closedBall_in_normal_carrier
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : OpenPartialHomeomorph X X)
    (hb : ContDiffOn ℝ ∞ b b.source) (hConv : Convex ℝ b.source)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ B)
    (center : X) (hcenter : center ∈ b.source) (r rhoN : ℝ)
    (hSource : closedBall center (2*r) ⊆ b.source)
    (hSmall : 2*B*r < rhoN) :
    closedBall center (2*r) ⊆ round4NormalCutoffCarrier b center rhoN := by
  have hLip : LipschitzOnWith ⟨B,hB⟩ b b.source :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hb.contDiffAt (b.open_source.mem_nhds hz)).differentiableAt (by simp))
      hBound hConv
  intro z hClosed
  have hzs := hSource hClosed
  refine ⟨hzs,?_⟩
  change dist (b z) (b center) < rhoN
  have hDist := hLip.dist_le_mul z hzs center hcenter
  change dist (b z) (b center) ≤ B*dist z center at hDist
  have hRad : dist z center ≤ 2*r := hClosed
  calc
    dist (b z) (b center) ≤ B*dist z center := hDist
    _ ≤ B*(2*r) := mul_le_mul_of_nonneg_left hRad hB
    _ = 2*B*r := by ring
    _ < rhoN := hSmall

theorem round4_actual_cutoff_support_in_normal_carrier
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : OpenPartialHomeomorph X X)
    (hb : ContDiffOn ℝ ∞ b b.source) (hConv : Convex ℝ b.source)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ B)
    (center : X) (hcenter : center ∈ b.source) (r rhoN : ℝ)
    (hSource : closedBall center (2*r) ⊆ b.source)
    (hSmall : 2*B*r < rhoN)
    (chi : X → ℝ) (hSupport : tsupport chi ⊆ closedBall center (2*r)) :
    tsupport chi ⊆ round4NormalCutoffCarrier b center rhoN :=
  hSupport.trans (round4_actual_closedBall_in_normal_carrier b hb hConv B hB hBound
    center hcenter r rhoN hSource hSmall)

theorem round4_normal_refinement_cap
    {rho factor rhoN B : ℝ} (hfactor : 0 < factor) (hN : 0 < rhoN) (hB : 0 < B)
    (hcap : rho ≤ factor*rhoN/(4*B)) :
    2*B*(rho/factor) < rhoN := by
  have hb : rho*factor⁻¹ ≤ (factor*rhoN/(4*B))*factor⁻¹ :=
    mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr hfactor.le)
  have heq : 2*B*((factor*rhoN/(4*B))*factor⁻¹) = rhoN/2 := by
    field_simp [ne_of_gt hB,ne_of_gt hfactor]
    ring
  have hle := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*B by positivity)
  rw [heq] at hle
  simpa only [div_eq_mul_inv] using hle.trans_lt (by linarith : rhoN/2 < rhoN)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4NativeNormalRadius_pos
#print axioms GlobalEmbedding.Continuation.round4_actual_cutoff_support_in_normal_carrier
