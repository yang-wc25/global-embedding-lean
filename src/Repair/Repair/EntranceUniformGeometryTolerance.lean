import Smoothing.Round3OuterReferenceFrameStability

/-!
# A numerical geometry entrance before the reference map and atlas

The normal projection tolerance is selected in fixed finite-dimensional
matrix spaces from the two numerical frame reserves.  The full two-jet and
original-C2 tolerances below consequently read only these numbers, the
Hessian bound, the fixed coordinate dimensions, and the prescribed inverse
chart profile.  They do not read a reference map, atlas, chart count or
piece.  The subsequent stability proofs use the actual frames and normal.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

private local instance entranceToleranceFirstNormed (m N : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance entranceToleranceFirstSpace (m N : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance entranceToleranceHessianNormed (m N : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance entranceToleranceHessianSpace (m N : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance entranceToleranceFrameNormed (m N : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance entranceToleranceFrameSpace (m N : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance entranceToleranceColumnsNormed (m N : ℕ) :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance entranceToleranceColumnsSpace (m N : ℕ) :
    NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := ContinuousLinearMap.toNormedSpace

def repairEntranceProjectionTolerance (m N : ℕ) (cF cT : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) : ℝ :=
  Classical.choose (actual_free_normal_projection_uniform_reserve
    (E := EuclideanSpace ℝ (Fin (m+1)))
    (T := EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p})
    (N := N) cF cT hcF hcT)

theorem repairEntranceProjectionTolerance_pos (m N : ℕ) (cF cT : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) :
    0 < repairEntranceProjectionTolerance m N cF cT hcF hcT :=
  (Classical.choose_spec (actual_free_normal_projection_uniform_reserve
    (E := EuclideanSpace ℝ (Fin (m+1)))
    (T := EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p})
    (N := N) cF cT hcF hcT)).1

def repairEntranceTransverseChangeCost (m N : ℕ) (cF MH : ℝ) : ℝ :=
  ‖actualIncrementTransverseColumns m N‖*(1+(3/Real.sqrt cF)*MH)

def repairEntranceTwoJetTolerance (m N : ℕ) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) : ℝ :=
  let C := repairEntranceTransverseChangeCost m N cF MH
  let en := repairEntranceProjectionTolerance m N cF cT hcF hcT
  min (Real.sqrt cF/2) (min (Real.sqrt cT/(2*(C+1))) (min en (en/(C+1))))

theorem repairEntranceTwoJetTolerance_pos (m N : ℕ) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH) :
    0 < repairEntranceTwoJetTolerance m N cF cT MH hcF hcT := by
  have hEn := repairEntranceProjectionTolerance_pos m N cF cT hcF hcT
  have hC : 0 ≤ repairEntranceTransverseChangeCost m N cF MH := by
    unfold repairEntranceTransverseChangeCost
    positivity
  unfold repairEntranceTwoJetTolerance
  positivity

def repairEntranceGeometryTolerance (m d N : ℕ) (T : ℕ → ℝ) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) : ℝ :=
  repairEntranceTwoJetTolerance m N cF cT MH hcF hcT /
    (round3OriginalC2AdaptedCost (m+1) d N T+1)

theorem repairEntranceGeometryTolerance_pos (m d N : ℕ) (T : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH) :
    0 < repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT :=
  div_pos (repairEntranceTwoJetTolerance_pos m N cF cT MH hcF hcT hMH)
    (by have := round3OriginalC2AdaptedCost_nonneg (m+1) d N T hT; positivity)

variable {m N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- The numerical two-jet tolerance works for every actual map and chart.
The original normal and both new reserves are conclusions of the original
two-jet comparison. -/
theorem repairEntrance_uniform_two_jet_stability
    (cF cT MH : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (F0 F : M → V) (hF0 : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F0) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ e.target)
    (hFirst : ∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F0 ∘ e.symm) x v‖^2)
    (hTransverse : ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F0 hF0 e.symm x v‖^2)
    (hHessian : ‖fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤ MH)
    (hD : ‖fderiv ℝ (F0 ∘ e.symm) x-fderiv ℝ (F ∘ e.symm) x‖ ≤
      repairEntranceTwoJetTolerance m N cF cT MH hcF hcT)
    (hH : ‖fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x-fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤
      repairEntranceTwoJetTolerance m N cF cT MH hcF hcT)
    (normal : normalSpace (I := 𝓙) F0 (e.symm x)) (hUnit : ‖normal‖ = 1)
    (hBeta : incrementsTransversePairing F0 hF0 (e.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections e.symm x a.succ) normal = 0) :
    (∀ v : D, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F ∘ e.symm) x v‖^2) ∧
    (∀ v : Tdata, (cT/4)*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF e.symm x v‖^2) ∧
    (1/2 : ℝ) ≤ ‖actualFreeNormalProjectionRaw
      (fderiv ℝ (F ∘ e.symm) x) (incrementsModeAmbientTransverseFrame F hF e.symm x) (normal : V)‖ := by
  let C := repairEntranceTransverseChangeCost m N cF MH
  let en := repairEntranceProjectionTolerance m N cF cT hcF hcT
  let epsilon := repairEntranceTwoJetTolerance m N cF cT MH hcF hcT
  have hEn : 0 < en := repairEntranceProjectionTolerance_pos m N cF cT hcF hcT
  have hC : 0 ≤ C := by dsimp [C,repairEntranceTransverseChangeCost]; positivity
  have hSmallF : epsilon ≤ Real.sqrt cF/2 := min_le_left _ _
  have hSmallT : C*epsilon ≤ Real.sqrt cT/2 := by
    calc
      _ ≤ C*(Real.sqrt cT/(2*(C+1))) :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hC
      _ ≤ (C+1)*(Real.sqrt cT/(2*(C+1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Real.sqrt cT/2 := by field_simp
  have hSmallN : epsilon ≤ en :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hCost : C*epsilon ≤ en := by
    calc
      _ ≤ C*(en/(C+1)) := mul_le_mul_of_nonneg_left
        (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)) hC
      _ ≤ (C+1)*(en/(C+1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = en := by field_simp
  have hFrame := actual_original_transverse_frame_two_jet_difference F0 F hF0 hF e he x hx
    cF MH hcF hFirst hHessian (hD.trans hSmallF)
  have hFrameBound : ‖incrementsModeAmbientTransverseFrame F hF e.symm x-
      incrementsModeAmbientTransverseFrame F0 hF0 e.symm x‖ ≤ C*epsilon := by
    apply hFrame.trans
    calc
      _ ≤ ‖actualIncrementTransverseColumns m N‖*(epsilon+(3/Real.sqrt cF)*MH*epsilon) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hH (mul_le_mul_of_nonneg_left hD (by positivity))) (norm_nonneg _)
      _ = C*epsilon := by dsimp [C,repairEntranceTransverseChangeCost]; ring
  refine ⟨actual_first_frame_reserve_perturbation _ _ cF hcF hFirst
      (by simpa only [norm_sub_rev] using hD.trans hSmallF),
    actual_first_frame_reserve_perturbation _ _ cT hcT hTransverse
      (hFrameBound.trans hSmallT),?_⟩
  have hNormal := (Classical.choose_spec (actual_free_normal_projection_uniform_reserve
    (E := D) (T := Tdata) (N := N) cF cT hcF hcT)).2
  apply hNormal _ _ _ _ hFirst hTransverse (hD.trans hSmallN)
    (by rw [norm_sub_rev]; exact hFrameBound.trans hCost) (normal : V) hUnit
  · rw [← actual_increment_normalSpace_eq_chart_range F0 hF0 e he x hx]
    exact normal.property
  · exact actual_original_frame_orthogonal_of_normal_beta F0 hF0 e.symm x normal hBeta

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_uniform_two_jet_stability
