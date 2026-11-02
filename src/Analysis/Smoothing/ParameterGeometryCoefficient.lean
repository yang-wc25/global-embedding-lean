import Smoothing.ParameterGeometryInput

/-!
# Uniform transfer coefficients are produced from the original B and T

The coefficient below is defined before any atlas or field. Its radius uses
B through two and T through two, and its order-k bound uses B,T through k+2.
Only the fixed universal model ball is compact; no atlas compactness or
chart-count-dependent supremum is used.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable (Es Y : Type*)
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace
attribute [local instance] spatialTransferInputNormedAddCommGroup spatialTransferInputNormedSpace

/-- A predeclared geometric constant for the true transfer operator's k-th jet. -/
def parameterSpatialTransferCoefficient (B T : ℕ → ℝ) (k : ℕ) : ℝ :=
  let G := parameterGeometryInputBound (bufferedCutoffSquareConstant B) T
  (k.factorial : ℝ) * spatialTransferModelBound (Es := Es) Y (G 0) k *
    bufferedTransitionPrefix G k ^ k

theorem parameterSpatialTransferCoefficient_nonneg {B T : ℕ → ℝ}
    (hB : ∀ k, 0 ≤ B k) (hT : ∀ k, 0 ≤ T k) (k : ℕ) :
    0 ≤ parameterSpatialTransferCoefficient Es Y B T k := by
  unfold parameterSpatialTransferCoefficient
  exact mul_nonneg (mul_nonneg (by positivity) (spatialTransferModelBound_nonneg Y _ _))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix
      (parameterGeometryInputBound_nonneg (bufferedCutoffSquareConstant_nonneg hB) hT) _)) _)

variable {Es Y}
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- Native Leibniz supplies each genuine squared-cutoff derivative from only
the corresponding finite prefix of the original cutoff provider. -/
theorem parameter_square_jet_le {w : Ep × Es → ℝ} {O : Set (Ep × Es)}
    (hO : IsOpen O) (hw : ContDiffOn ℝ ∞ w O) (B : ℕ → ℝ) (hB : ∀ a, 0 ≤ B a)
    {z : Ep × Es} (hz : z ∈ O) (k : ℕ)
    (hbound : ∀ a ≤ k, ‖iteratedFDeriv ℝ a w z‖ ≤ B a) :
    ‖iteratedFDeriv ℝ k (fun y => w y^2) z‖ ≤ bufferedCutoffSquareConstant B k := by
  have hm := norm_iteratedFDerivWithin_mul_le hw hw hO.uniqueDiffOn hz (n := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hz, ← pow_two] at hm
  apply hm.trans
  apply Finset.sum_le_sum
  intro a ha
  have hak : a ≤ k := by simpa using ha
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound a hak) (by positivity))
    (hbound (k-a) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (by positivity) (hB a))

/-- The coefficient-model composition bound using real geometric input jets. -/
theorem spatialTransferModel_composed_jet_le {w : Ep × Es → ℝ} {v : Ep × Es → Es}
    {O : Set (Ep × Es)} (hO : IsOpen O)
    (hw : ContDiffOn ℝ ∞ w O) (hv : ContDiffOn ℝ ∞ v O)
    (W T : ℕ → ℝ) (hW : ∀ a, 0 ≤ W a) (hT : ∀ a, 0 ≤ T a)
    {z : Ep × Es} (hz : z ∈ O) (k : ℕ)
    (hwBound : ∀ a ≤ k+2, ‖iteratedFDeriv ℝ a w z‖ ≤ W a)
    (hvBound : ∀ a, 1 ≤ a → a ≤ k+2 → ‖iteratedFDeriv ℝ a v z‖ ≤ T a) :
    ‖iteratedFDeriv ℝ k (spatialTransferModel (Es := Es) Y ∘ spatialTransferInputField w v) z‖ ≤
      (k.factorial : ℝ) * spatialTransferModelBound (Es := Es) Y (parameterGeometryInputBound W T 0) k *
        bufferedTransitionPrefix (parameterGeometryInputBound W T) k ^ k := by
  have hinput := spatialTransferInputField_contDiffOn hO hw hv
  have hinputBound (a : ℕ) (ha : a ≤ k) :
      ‖iteratedFDeriv ℝ a (spatialTransferInputField w v) z‖ ≤ parameterGeometryInputBound W T a :=
    spatialTransferInputField_jet_le hO hw hv W T hW hT hz a
      (fun b hb => hwBound b (by omega)) (fun b hb hb' => hvBound b hb (by omega))
  have hvalue : ‖spatialTransferInputField w v z‖ ≤ parameterGeometryInputBound W T 0 := by
    simpa only [norm_iteratedFDeriv_zero] using hinputBound 0 (Nat.zero_le k)
  exact parameter_general_composition_jet_le (parameterGeometryInputBound W T)
    (parameterGeometryInputBound_nonneg hW hT) hO isOpen_univ hinput
    (spatialTransferModel_contDiff (Es := Es) Y).contDiffOn (fun _ _ => trivial) hz k
    (spatialTransferModelBound (Es := Es) Y (parameterGeometryInputBound W T 0) k)
    (fun a ha => spatialTransferModel_jet_le Y _ k a ha hvalue)
    (fun a _ ha => hinputBound a ha)

/-- The genuine transfer coefficient is controlled by the original cutoff and
full product transition providers; there is no independent coefficient hypothesis. -/
theorem spatialTransferField_jet_le_of_geometry
    {w : Ep × Es → ℝ} (a : Ep → Ep) (b : Es → Es) {O : Set (Ep × Es)}
    (hO : IsOpen O) (hw : ContDiffOn ℝ ∞ w O)
    (ht : ContDiffOn ℝ ∞ (fun y : Ep × Es => (a y.1,b y.2)) O)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    {z : Ep × Es} (hz : z ∈ O) (k : ℕ)
    (hweight : ∀ j ≤ k+2, ‖iteratedFDeriv ℝ j w z‖ ≤ B j)
    (htransition : ∀ j, 1 ≤ j → j ≤ k+2 →
      ‖iteratedFDeriv ℝ j (fun y : Ep × Es => (a y.1,b y.2)) z‖ ≤ T j) :
    ‖iteratedFDeriv ℝ k (spatialTransferField (Y := Y) (fun y => w y^2) b) z‖ ≤
      parameterSpatialTransferCoefficient Es Y B T k := by
  have hv : ContDiffOn ℝ ∞ (fun y : Ep × Es => b y.2) O := ht.snd
  have hbound : ∀ j, 1 ≤ j → j ≤ k+2 →
      ‖iteratedFDeriv ℝ j (fun y : Ep × Es => b y.2) z‖ ≤ T j := by
    intro j hj hjk
    exact (parameter_source_component_jet_le hO ht hz j).trans (htransition j hj hjk)
  exact spatialTransferModel_composed_jet_le (Y := Y) hO (hw.pow 2) hv
    (bufferedCutoffSquareConstant B) T (bufferedCutoffSquareConstant_nonneg hB) hT hz k
    (fun j hj => parameter_square_jet_le hO hw B hB hz j (fun l hl => hweight l (hl.trans hj))) hbound

/-- The squared-cutoff profile depends only on the stated finite prefix. -/
theorem parameterCutoffSquareConstant_congr_prefix {B₁ B₂ : ℕ → ℝ} (j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) :
    bufferedCutoffSquareConstant B₁ j = bufferedCutoffSquareConstant B₂ j := by
  unfold bufferedCutoffSquareConstant
  apply Finset.sum_congr rfl
  intro a ha
  rw [hB a (by simpa using ha), hB (j-a) (Nat.sub_le _ _)]

/-- Formal finite-prefix audit of the uniform coefficient: no derivative
beyond k+2 of B or T can influence it, and T(0) is never used. -/
theorem parameterSpatialTransferCoefficient_congr_prefix
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (k : ℕ)
    (hB : ∀ a ≤ k+2, B₁ a = B₂ a)
    (hT : ∀ a, 1 ≤ a → a ≤ k+2 → T₁ a = T₂ a) :
    parameterSpatialTransferCoefficient Es Y B₁ T₁ k =
      parameterSpatialTransferCoefficient Es Y B₂ T₂ k := by
  let G₁ := parameterGeometryInputBound (bufferedCutoffSquareConstant B₁) T₁
  let G₂ := parameterGeometryInputBound (bufferedCutoffSquareConstant B₂) T₂
  have hW (a : ℕ) (ha : a ≤ k+2) : bufferedCutoffSquareConstant B₁ a = bufferedCutoffSquareConstant B₂ a :=
    parameterCutoffSquareConstant_congr_prefix a (fun b hb => hB b (hb.trans ha))
  have hG (a : ℕ) (ha : a ≤ k) : G₁ a = G₂ a := by
    dsimp [G₁, G₂, parameterGeometryInputBound]
    rw [hW a (by omega), hW (a+1) (by omega), hW (a+2) (by omega),
      hT (a+1) (by omega) (by omega), hT (a+2) (by omega) (by omega)]
  have hp : bufferedTransitionPrefix G₁ k = bufferedTransitionPrefix G₂ k := by
    unfold bufferedTransitionPrefix
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    exact hG a (by simpa using ha)
  change (k.factorial : ℝ) * spatialTransferModelBound (Es := Es) Y (G₁ 0) k *
      bufferedTransitionPrefix G₁ k ^ k =
    (k.factorial : ℝ) * spatialTransferModelBound (Es := Es) Y (G₂ 0) k *
      bufferedTransitionPrefix G₂ k ^ k
  rw [hG 0 (Nat.zero_le k), hp]

#print axioms parameterSpatialTransferCoefficient_congr_prefix
#print axioms parameterSpatialTransferCoefficient_nonneg
#print axioms spatialTransferModel_composed_jet_le
#print axioms spatialTransferField_jet_le_of_geometry
end
end GlobalEmbedding.Continuation
