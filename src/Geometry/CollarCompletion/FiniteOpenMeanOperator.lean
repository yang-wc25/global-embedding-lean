import SourceCollarsBridge.FiniteTensorGermSpace
import Repair.FullIncrementNovPrimaryAtParameter
import Smoothing.ParameterRound2MeanResidualScaling

/-!
# The actual physical mean operator on finite original tensor norms

Only a proof carrier changes. For every allowed scale the returned native
tensor is literally the original physical mean error; all coordinate maps,
differentiation domains and original weighted norms are unchanged. The
membership argument is produced from actual raw estimates by the following
module, not requested as a new entrance condition of the paper theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation.CollarCompletion
open SourceCollarsBridge

variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

variable (A : BufferedAtlas M (EuclideanSpace ℝ (Fin (m+1))))
  (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
  (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
  (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
  (ell : ℝ) (H : finiteTensorGermSpace A B S W hSO) (rho : ℝ)
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m := m) (Λ := Λ) (Β := Β) F)
  (hActive : ∀ nu beta (z : P × M), z ∈ (g.chart nu beta).source →
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F z.1))
  (q : ℕ)
local notation "𝓔" => finiteTensorGermSpace A B S W hSO
local notation "p" => finiteTensorGermSeminorm A B S W hSO ell

/-- Smoothness and original norm finiteness of the actual mean tensor.
This proposition has no numerical output estimate. -/
def actualFiniteMeanMembership : Prop :=
  ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
    ∀ K : {K : 𝓔 // p 0 (K-H) < rho},
    let U := fullIncrementNovPrimaryMeanError F g K.val.val.val hActive (q+2) (epsilon*ell)
    U ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    ∀ j, paperAtlasCj j (incrementsOriginalTensorCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤

/-- For valid scales only membership proofs are attached to the literal
finite differential mean formula. Outside those scales the function is totalized. -/
def actualFiniteMeanOperator
    (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q)
    (epsilon : ℝ) (K : {K : 𝓔 // p 0 (K-H) < rho}) : 𝓔 :=
  if he : 0 < epsilon ∧ epsilon ≤ 1 then
    ⟨⟨fullIncrementNovPrimaryMeanError F g K.val.val.val hActive (q+2) (epsilon*ell),
      (hsm epsilon he.1 he.2 K).1⟩,(hsm epsilon he.1 he.2 K).2⟩
  else 0

theorem actualFiniteMeanOperator_value
    (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q)
    (epsilon : ℝ) (K : {K : 𝓔 // p 0 (K-H) < rho}) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm epsilon K).val.val =
      fullIncrementNovPrimaryMeanError F g K.val.val.val hActive (q+2) (epsilon*ell) := by
  simp only [actualFiniteMeanOperator,dite_eq_left (show 0 < epsilon ∧ epsilon ≤ 1 from ⟨he,he1⟩)]

theorem actualFiniteMeanOperator_size
    (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (hell : 0 < ell)
    (K : {K : 𝓔 // p 0 (K-H) < rho}) (j : ℕ) (C : ℝ)
    (hb : (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B
      (fullIncrementNovPrimaryMeanError F g K.val.val.val hActive (q+2) (epsilon*ell)))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ C*((epsilon*ell)/ell)) :
    p j (actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm epsilon K) ≤ epsilon*C := by
  rw [finiteTensorGermSeminorm_apply,
    actualFiniteMeanOperator_value A B S W hSO ell H rho F g hActive q hsm epsilon K he he1]
  simpa only [mul_div_cancel_right₀ epsilon hell.ne',mul_comm C epsilon] using hb

/-- Subtraction in the finite carrier retains literal native subtraction. -/
theorem finite_original_seminorm_sub_value (T U : 𝓔) (j : ℕ) :
    p j (T-U) = (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates A B (fun t x => T.val.val t x-U.val.val t x))
      (incrementsOriginalDifferentiation A B) S).toReal := rfl

theorem actualFiniteMeanOperator_difference
    (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (hell : 0 < ell)
    (K L : {K : 𝓔 // p 0 (K-H) < rho}) (j loss : ℕ) (C Dcoef : ℝ)
    (hb : (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B
      (fun t x => fullIncrementNovPrimaryMeanError F g K.val.val.val hActive (q+2) (epsilon*ell) t x-
        fullIncrementNovPrimaryMeanError F g L.val.val.val hActive (q+2) (epsilon*ell) t x))
      (incrementsOriginalDifferentiation A B) S).toReal ≤
        C*((epsilon*ell)/ell)*(Dcoef*p (j+loss) (K.val-L.val))) :
    p j (actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm epsilon K-
      actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm epsilon L) ≤
        epsilon*(C*Dcoef)*p (j+loss) (K.val-L.val) := by
  let TK := actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm epsilon K
  let TL := actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm epsilon L
  have hTK : TK.val.val = fullIncrementNovPrimaryMeanError F g K.val.val.val hActive (q+2) (epsilon*ell) :=
    actualFiniteMeanOperator_value A B S W hSO ell H rho F g hActive q hsm epsilon K he he1
  have hTL : TL.val.val = fullIncrementNovPrimaryMeanError F g L.val.val.val hActive (q+2) (epsilon*ell) :=
    actualFiniteMeanOperator_value A B S W hSO ell H rho F g hActive q hsm epsilon L he he1
  have heq := finite_original_seminorm_sub_value A B S W hSO ell TK TL j
  let normDiff := fun (T U : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) =>
    (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates A B (fun t x => T t x-U t x))
      (incrementsOriginalDifferentiation A B) S).toReal
  have hv := congrArg₂ normDiff hTK hTL
  have harith (r : ℝ) : C*((epsilon*ell)/ell)*(Dcoef*r) = epsilon*(C*Dcoef)*r := by
    rw [mul_div_cancel_right₀ epsilon hell.ne']
    ring
  exact (heq.trans hv).le.trans (hb.trans_eq (harith (p (j+loss) (K.val-L.val))))

/-- Scaling the unchanged actual finite tensor uses the same original fast
norm, without compactness of any observation set. -/
theorem finite_original_mean_residual_fast_scale
    (E : 𝓔) (j : ℕ) (tau delta R : ℝ) (hle : tau ≤ ell) (hR : p j E ≤ R) :
    let scaled := fun t x => delta^2 • E.val.val t x
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B scaled)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B scaled)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ delta^2*R := by
  intro scaled
  let SE : 𝓔 := delta^2 • E
  have hse : p j SE ≤ delta^2*R := by
    change p j (delta^2 • E) ≤ _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg delta)]
    exact mul_le_mul_of_nonneg_left hR (sq_nonneg delta)
  have hfinite := finiteTensorGerm_weighted_finite A B S W hSO SE 0 j ell
  have hmono := parameterRound2_paperAtlasWeighted_mono_scale 0 j tau ell hle
    (incrementsOriginalTensorCoordinates A B scaled) (incrementsOriginalDifferentiation A B) S
  exact ⟨ne_top_of_le_ne_top hfinite hmono,(ENNReal.toReal_mono hfinite hmono).trans hse⟩

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.actualFiniteMeanOperator_value
#print axioms GlobalEmbedding.Continuation.CollarCompletion.actualFiniteMeanOperator_difference
#print axioms GlobalEmbedding.Continuation.CollarCompletion.finite_original_mean_residual_fast_scale
