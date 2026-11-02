import Repair.ReferencePlateau
import Mathlib.Analysis.Calculus.MeanValue

/-! A numerical interaction buffer from the actual global primary plateaus.
The plateaus equal one on the true support pair. Their original full joint
first derivative bound prevents either from vanishing in a common ball,
so that ball lies in both genuine primary domains. No minimum over pieces
or unknown reference map is taken. -/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def repairReferenceInteractionBuffer (parentBuffer derivativeBound : ℝ) : ℝ :=
  min (parentBuffer/2) (1/(2*(derivativeBound+1)))

theorem repair_reference_interaction_buffer_pos {parentBuffer derivativeBound : ℝ}
    (hParent : 0 < parentBuffer) (hDerivative : 0 ≤ derivativeBound) :
    0 < repairReferenceInteractionBuffer parentBuffer derivativeBound := by
  unfold repairReferenceInteractionBuffer
  apply lt_min <;> positivity

def repairReferenceBufferedInteractionDomain {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (radius : ℝ) : Set E := ⋃ x ∈ K, ball x radius

theorem repair_reference_buffered_interaction_mem
    {E : Type*} [PseudoMetricSpace E] (K : Set E) (radius : ℝ) (y : E) :
    y ∈ repairReferenceBufferedInteractionDomain K radius ↔ ∃ x ∈ K, y ∈ ball x radius := by
  simp only [repairReferenceBufferedInteractionDomain,mem_iUnion,exists_prop]

theorem repair_reference_buffered_interaction_nonempty
    {E : Type*} [PseudoMetricSpace E] (K : Set E) (radius : ℝ) (hRadius : 0 < radius) :
    (repairReferenceBufferedInteractionDomain K radius).Nonempty ↔ K.Nonempty := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨x,hx,_⟩ := (repair_reference_buffered_interaction_mem K radius y).mp hy
    exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,(repair_reference_buffered_interaction_mem K radius x).mpr ⟨x,hx,mem_ball_self hRadius⟩⟩

theorem repair_reference_plateau_remains_positive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (parentBuffer derivativeBound : ℝ) (hParent : 0 < parentBuffer)
    (hDerivative : 0 ≤ derivativeBound)
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (hBound : ∀ z ∈ U, ‖fderiv ℝ f z‖ ≤ derivativeBound)
    (x : E) (hBuffer : ball x parentBuffer ⊆ U) (hOne : f x=1) :
    ∀ y ∈ ball x (repairReferenceInteractionBuffer parentBuffer derivativeBound), 1/2 < f y := by
  let radius := repairReferenceInteractionBuffer parentBuffer derivativeBound
  have hr : 0 < radius := repair_reference_interaction_buffer_pos hParent hDerivative
  have hrParent : radius ≤ parentBuffer :=
    (min_le_left _ _).trans (by linarith : parentBuffer/2 ≤ parentBuffer)
  have hCap : radius*(2*(derivativeBound+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2*(derivativeBound+1))).mp (min_le_right _ _)
  have hSmall : derivativeBound*radius < 1/2 := by nlinarith
  have hLip : LipschitzOnWith ⟨derivativeBound,hDerivative⟩ f (ball x parentBuffer) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hf.contDiffAt (hU.mem_nhds (hBuffer hz))).differentiableAt (by simp))
      (fun z hz => hBound z (hBuffer hz)) (convex_ball _ _)
  intro y hy
  have hyU : y ∈ ball x parentBuffer := (ball_subset_ball hrParent) hy
  have hdist := hLip.dist_le_mul y hyU x (mem_ball_self hParent)
  have hLess : dist (f y) (f x) < 1/2 :=
    hdist.trans_lt ((mul_le_mul_of_nonneg_left (mem_ball.mp hy).le hDerivative).trans_lt hSmall)
  rw [hOne,Real.dist_eq] at hLess
  have hLower := (abs_lt.mp hLess).1
  linarith

/-- Both primary domains are produced on one open interaction region.
The parent sampling domain is retained literally, including its buffer. -/
theorem repair_reference_actual_buffered_interaction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (parentBuffer derivativeBound : ℝ) (hParent : 0 < parentBuffer)
    (hDerivative : 0 ≤ derivativeBound)
    (U K A B : Set E) (hU : IsOpen U)
    (left right : E → ℝ) (hLeft : ContDiffOn ℝ ∞ left U) (hRight : ContDiffOn ℝ ∞ right U)
    (hLeftBound : ∀ z ∈ U, ‖fderiv ℝ left z‖ ≤ derivativeBound)
    (hRightBound : ∀ z ∈ U, ‖fderiv ℝ right z‖ ≤ derivativeBound)
    (hLeftOne : ∀ z ∈ K, left z=1) (hRightOne : ∀ z ∈ K, right z=1)
    (hLeftDomain : ∀ z ∈ U, left z ≠ 0 → z ∈ A)
    (hRightDomain : ∀ z ∈ U, right z ≠ 0 → z ∈ B)
    (hBuffer : ∀ z ∈ K, ball z parentBuffer ⊆ U)
    (center : E) (R : ℝ) (hBounded : K ⊆ closedBall center R) :
    let radius := repairReferenceInteractionBuffer parentBuffer derivativeBound
    let O := repairReferenceBufferedInteractionDomain K radius
    0 < radius ∧ IsOpen O ∧ (∀ z ∈ K, ball z radius ⊆ O) ∧
      O ⊆ U ∩ (A ∩ B) ∧ O ⊆ ball center (R+radius) ∧
      (∀ z ∈ O, 1/2 < left z ∧ 1/2 < right z) ∧
      ∀ z ∈ O, ‖z‖ ≤ ‖center‖+R+radius := by
  intro radius O
  have hr : 0 < radius := repair_reference_interaction_buffer_pos hParent hDerivative
  have hrParent : radius ≤ parentBuffer :=
    (min_le_left _ _).trans (by linarith : parentBuffer/2 ≤ parentBuffer)
  have hSub : O ⊆ U := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := (repair_reference_buffered_interaction_mem K radius y).mp hy
    exact hBuffer x hx ((ball_subset_ball hrParent) hxy)
  have hPos : ∀ z ∈ O, 1/2 < left z ∧ 1/2 < right z := by
    intro z hz
    obtain ⟨x,hx,hxz⟩ := (repair_reference_buffered_interaction_mem K radius z).mp hz
    exact ⟨repair_reference_plateau_remains_positive parentBuffer derivativeBound hParent hDerivative
      U hU left hLeft hLeftBound x (hBuffer x hx) (hLeftOne x hx) z hxz,
      repair_reference_plateau_remains_positive parentBuffer derivativeBound hParent hDerivative
      U hU right hRight hRightBound x (hBuffer x hx) (hRightOne x hx) z hxz⟩
  have hRad : O ⊆ ball center (R+radius) := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := (repair_reference_buffered_interaction_mem K radius y).mp hy
    apply mem_ball.mpr
    calc
      dist y center ≤ dist y x+dist x center := dist_triangle _ _ _
      _ < radius+R := add_lt_add_of_lt_of_le (mem_ball.mp hxy) (mem_closedBall.mp (hBounded hx))
      _ = R+radius := add_comm _ _
  refine ⟨hr,isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball)),?_,?_,hRad,hPos,?_⟩
  · intro z hz y hy
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨hz,hy⟩⟩
  · intro z hz
    have hp := hPos z hz
    exact ⟨hSub hz,hLeftDomain z (hSub hz) (ne_of_gt (by linarith : 0<left z)),
      hRightDomain z (hSub hz) (ne_of_gt (by linarith : 0<right z))⟩
  · intro z hz
    have hh := norm_le_norm_add_const_of_dist_le (le_of_lt (hRad hz))
    linarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_actual_buffered_interaction
