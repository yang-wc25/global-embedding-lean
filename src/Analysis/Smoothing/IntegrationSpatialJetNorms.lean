import Smoothing.IntegrationSpatialCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Dimension-only comparison of genuine source jets and their spatial words

The finite coordinate reconstruction below depends only on the source and
target dimensions. Its fixed operator norm is a legitimate uniform constant:
it has no manifold, atlas, chart count, scale, or unknown map argument.
The coordinate packet still contains only spatial derivatives at its base.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Filter Set Function
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

abbrev CoordinateSpatialNativeJet (n q : ℕ) := SpatialNativeJet (Fin n → ℝ) (Fin q → ℝ)

/-- Evaluation of the actual value/first/second source jet on an ordered
spatial word. All directions are source coordinate unit vectors. -/
def spatialJetEvaluation {n q : ℕ} (w : ParameterSpatialWord n) :
    CoordinateSpatialNativeJet n q →L[ℝ] (Fin q → ℝ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun v =>
      if h0 : w.1.val = 0 then v.1
      else if h1 : w.1.val = 1 then
        v.2.1 (Pi.single (w.2 ⟨0, by omega⟩) 1)
      else v.2.2 (Pi.single (w.2 ⟨0, by omega⟩) 1)
        (Pi.single (w.2 ⟨1, by omega⟩) 1)
    map_add' := by
      intro v v'
      split_ifs <;> simp
    map_smul' := by
      intro r v
      split_ifs <;> simp }

@[simp] theorem spatialJetEvaluation_zero {n q : ℕ} (v : CoordinateSpatialNativeJet n q) :
    spatialJetEvaluation (spatialWordZero n) v = v.1 := by
  simp [spatialJetEvaluation, spatialWordZero]

@[simp] theorem spatialJetEvaluation_one {n q : ℕ} (i : Fin n) (v : CoordinateSpatialNativeJet n q) :
    spatialJetEvaluation (spatialWordOne i) v = v.2.1 (Pi.single i 1) := by
  simp [spatialJetEvaluation, spatialWordOne]

@[simp] theorem spatialJetEvaluation_two {n q : ℕ} (i j : Fin n) (v : CoordinateSpatialNativeJet n q) :
    spatialJetEvaluation (spatialWordTwo i j) v = v.2.2 (Pi.single i 1) (Pi.single j 1) := by
  simp [spatialJetEvaluation, spatialWordTwo]

/-- All ordered spatial words as one genuine continuous linear evaluation map. -/
def spatialJetCoordinates (n q : ℕ) :
    CoordinateSpatialNativeJet n q →L[ℝ] (ParameterSpatialWord n → Fin q → ℝ) :=
  ContinuousLinearMap.pi fun w => spatialJetEvaluation w

/-- The original source coordinate basis reconstructs every continuous linear map. -/
theorem clm_apply_eq_source_basis_sum {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : (Fin n → ℝ) →L[ℝ] Y) (v : Fin n → ℝ) :
    L v = ∑ i, v i • L (Pi.single i 1) := by
  have he : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    L v = L (∑ i, v i • Pi.single i (1 : ℝ)) := congrArg L he
    _ = _ := by simp

/-- Explicit reconstruction of the native spatial two-jet from its coordinate
words, independent of the function or the number of atlas charts. -/
def spatialJetReconstruction (n q : ℕ) :
    (ParameterSpatialWord n → Fin q → ℝ) →L[ℝ] CoordinateSpatialNativeJet n q :=
  LinearMap.toContinuousLinearMap
  { toFun := fun a =>
      (a (spatialWordZero n),
        ∑ i, (ContinuousLinearMap.proj i).smulRight (a (spatialWordOne i)),
        ∑ i, (ContinuousLinearMap.proj i).smulRight
          (∑ j, (ContinuousLinearMap.proj j).smulRight (a (spatialWordTwo i j))))
    map_add' := by
      intro a b
      ext <;> simp [ContinuousLinearMap.smulRight_apply, smul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext <;> simp [ContinuousLinearMap.smulRight_apply, smul_smul,
        Finset.smul_sum, mul_comm, mul_left_comm, mul_assoc] }

/-- The coordinate packet reconstructs the original native jet exactly. -/
theorem spatialJetReconstruction_coordinates (n q : ℕ) (v : CoordinateSpatialNativeJet n q) :
    spatialJetReconstruction n q (spatialJetCoordinates n q v) = v := by
  apply Prod.ext
  · simp [spatialJetReconstruction, spatialJetCoordinates]
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro a
    simpa [spatialJetReconstruction, spatialJetCoordinates,
      ContinuousLinearMap.smulRight_apply] using
      (clm_apply_eq_source_basis_sum v.2.1 a).symm
  · apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    have he := congrArg (fun L => L b) (clm_apply_eq_source_basis_sum v.2.2 a)
    simp only [sum_apply, smul_apply] at he
    rw [he]
    simp [spatialJetReconstruction, spatialJetCoordinates,
      ContinuousLinearMap.smulRight_apply,
      clm_apply_eq_source_basis_sum (v.2.2 (Pi.single _ 1)) b]

/-- Dimension-only inverse-coordinate cost for a native source two-jet. -/
def spatialJetReconstructionConstant (n q : ℕ) : ℝ := ‖spatialJetReconstruction n q‖

theorem spatialJetReconstructionConstant_nonneg (n q : ℕ) :
    0 ≤ spatialJetReconstructionConstant n q := norm_nonneg _

/-- Coordinate word bounds control the true native spatial jet. -/
theorem norm_spatialNativeJet_of_coordinate_bound {n q : ℕ}
    (v : CoordinateSpatialNativeJet n q) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ w, ‖spatialJetEvaluation w v‖ ≤ R) :
    ‖v‖ ≤ spatialJetReconstructionConstant n q * R := by
  have hb : ‖spatialJetCoordinates n q v‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR).mpr h
  calc
    ‖v‖ = ‖spatialJetReconstruction n q (spatialJetCoordinates n q v)‖ :=
      congrArg norm (spatialJetReconstruction_coordinates n q v).symm
    _ ≤ ‖spatialJetReconstruction n q‖ * ‖spatialJetCoordinates n q v‖ :=
      (spatialJetReconstruction n q).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- Dimension-only forward coordinate cost. -/
def spatialJetEvaluationConstant (n q : ℕ) : ℝ := ‖spatialJetCoordinates n q‖

theorem spatialJetEvaluationConstant_nonneg (n q : ℕ) :
    0 ≤ spatialJetEvaluationConstant n q := norm_nonneg _

theorem spatialJetEvaluation_norm_le {n q : ℕ} (w : ParameterSpatialWord n) :
    ‖spatialJetEvaluation (q := q) w‖ ≤ spatialJetEvaluationConstant n q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_le_pi_norm (spatialJetCoordinates n q v) w).trans
    ((spatialJetCoordinates n q).le_opNorm v)

section HigherDerivatives
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {n q j : ℕ} {f : Z → CoordinateSpatialNativeJet n q} {x : Z}

/-- All joint derivatives of literal coordinate evaluations are controlled
by the same native jet field. -/
theorem norm_iteratedFDeriv_spatialJetEvaluation_le
    (hf : ContDiffAt ℝ ∞ f x) (w : ParameterSpatialWord n) :
    ‖iteratedFDeriv ℝ j (spatialJetEvaluation w ∘ f) x‖ ≤
      spatialJetEvaluationConstant n q * ‖iteratedFDeriv ℝ j f x‖ := by
  exact ((spatialJetEvaluation w).norm_iteratedFDeriv_comp_left hf (by simp)).trans
    (mul_le_mul_of_nonneg_right (spatialJetEvaluation_norm_le w) (norm_nonneg _))

/-- Conversely, bounds for all coordinate words at a joint derivative order
control that order of the genuine native spatial jet, with one fixed inverse
constant. This is an operator-norm statement, not just directional bounds. -/
theorem norm_iteratedFDeriv_nativeJet_of_word_bounds
    (hf : ContDiffAt ℝ ∞ f x) (R : ℝ) (hR : 0 ≤ R)
    (hwords : ∀ w, ‖iteratedFDeriv ℝ j (spatialJetEvaluation w ∘ f) x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ spatialJetReconstructionConstant n q * R := by
  apply (ContinuousMultilinearMap.opNorm_le_iff
    (mul_nonneg (spatialJetReconstructionConstant_nonneg n q) hR)).mpr
  intro v
  have hword (w : ParameterSpatialWord n) :
      ‖spatialJetEvaluation w (iteratedFDeriv ℝ j f x v)‖ ≤ R * ∏ i, ‖v i‖ := by
    have he := (spatialJetEvaluation w).iteratedFDeriv_comp_left hf (i := j) (by simp)
    have he' := congrArg (fun L => L v) he
    change iteratedFDeriv ℝ j (spatialJetEvaluation w ∘ f) x v =
      spatialJetEvaluation w (iteratedFDeriv ℝ j f x v) at he'
    rw [← he']
    exact (iteratedFDeriv ℝ j (spatialJetEvaluation w ∘ f) x).le_of_opNorm_le (hwords w) v
  have h := norm_spatialNativeJet_of_coordinate_bound
    (iteratedFDeriv ℝ j f x v) (R * ∏ i, ‖v i‖) (by positivity) hword
  simpa only [mul_assoc] using h

end HigherDerivatives

/-- Exact identification for every ordered spatial word, including lengths
zero and one. There is no equality of unrelated derivative carriers. -/
theorem parameterSpatialJet_eq_native_evaluation {n d q : ℕ}
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    {z : (Fin d → ℝ) × (Fin n → ℝ)} (hz : sourceFirstCoordinates n d z ∈ O)
    (w : ParameterSpatialWord n) :
    parameterSpatialJet u w (sourceFirstCoordinates n d z) =
      spatialJetEvaluation w (spatialNativeJet (u ∘ sourceFirstCoordinates n d) z) := by
  rcases w with ⟨k, s⟩
  fin_cases k
  · have he : s = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst s
    exact parameterSpatialJet_zero_native u z
  · have he : s = fun _ => s 0 := by funext i; congr; exact Fin.eq_zero i
    rw [he]
    simpa [spatialWordOne, spatialJetEvaluation] using
      parameterSpatialJet_one_native
        ((hu.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) (s 0)
  · have he : s = fun a => if a.val = 0 then s 0 else s 1 := by
      funext a
      fin_cases a <;> simp
    rw [he]
    simpa [spatialWordTwo, spatialJetEvaluation] using
      parameterSpatialJet_two_native hO hu hz (s 0) (s 1)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.spatialJetReconstruction_coordinates
#print axioms GlobalEmbedding.Continuation.norm_spatialNativeJet_of_coordinate_bound
#print axioms GlobalEmbedding.Continuation.norm_iteratedFDeriv_nativeJet_of_word_bounds
#print axioms GlobalEmbedding.Continuation.parameterSpatialJet_eq_native_evaluation
