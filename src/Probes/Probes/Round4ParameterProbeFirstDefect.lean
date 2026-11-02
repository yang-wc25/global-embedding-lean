import GlobalEmbedding.Offline.RepairMetricIdentity
import Probes.Round3ParameterMetricAddition
import Probes.Round4ParameterProbeCombinedSecondary

/-! Normalization of the actual first map G₁=G₀+U₀. The contracted G₀,
reserved target, and complete physical metric error are retained literally.
The original tensor-germ seminorm is changed only by the exact scalar. This
module does not assume or claim a producer of the combined error estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N count : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

/-- Exact first-step normalization on the original native tensors. The
metric of G₀ is derived from the actual square-root contraction. -/
theorem round4ParameterProbe_first_normalized_defect
    (F0 : P × M → V) (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (U : P × M → V) (delta delta1 : ℝ) (hdelta : delta ≠ 0)
    (hdelta1 : delta1 ≠ 0) (hsmall : delta^2 ≤ 1) :
    let G0 := fun z => Real.sqrt (1-delta^2) • F0 z
    let h0 := fun p x => inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x
    let Hfirst := fun p x => (1-(delta1/delta)^2) • h0 p x
    let G1 := fun z => G0 z+U z
    (fun p x => (delta1^2)⁻¹ • (h0 p x-inducedMetric (I := 𝓙) (fun y => G1 (p,y)) x)-h0 p x) =
      -(delta1^2)⁻¹ • incrementsOriginalMetricError G0 U Hfirst delta := by
  intro G0 h0 Hfirst G1
  have hG0 (p : P) (x : M) : inducedMetric (I := 𝓙) (fun y => G0 (p,y)) x =
      (1-delta^2) • h0 p x :=
    repair_initial_metric (fun y => F0 (p,y)) (hF0 p) delta hsmall x
  funext p x
  change (delta1^2)⁻¹ • (h0 p x-inducedMetric (I := 𝓙) (fun y => G0 (p,y)+U (p,y)) x)-h0 p x =
    -(delta1^2)⁻¹ •
      (inducedMetric (I := 𝓙) (fun y => G0 (p,y)+U (p,y)) x-
        inducedMetric (I := 𝓙) (fun y => G0 (p,y)) x-delta^2 • Hfirst p x)
  rw [hG0]
  ext v w
  simp only [Hfirst,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
  field_simp [hdelta,hdelta1]
  ring

/-- A genuine physical error germ produces the same normalized first-defect
error germ. Its seminorm is exactly δ₁⁻² times the original error seminorm;
all original coordinate charts, slots, samples and the weight are unchanged. -/
theorem round4ParameterProbe_first_defect_germ
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F0 : P × M → V) (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (U : P × M → V) (delta delta1 : ℝ) (hdelta : delta ≠ 0)
    (hdelta1 : delta1 ≠ 0) (hsmall : delta^2 ≤ 1) :
    let G0 := fun z => Real.sqrt (1-delta^2) • F0 z
    let h0 := fun p x => inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x
    let Hfirst := fun p x => (1-(delta1/delta)^2) • h0 p x
    let G1 := fun z => G0 z+U z
    ∀ hError : incrementsOriginalMetricError G0 U Hfirst delta ∈
      parameterRound2_originalTensorGermSpace A B S W,
    ∃ normalized : parameterRound2_originalTensorGermSpace A B S W,
      normalized.val = (fun p x => (delta1^2)⁻¹ •
        (h0 p x-inducedMetric (I := 𝓙) (fun y => G1 (p,y)) x)-h0 p x) ∧
      ∀ (weight : ℝ) (j : ℕ),
        parameterRound2_originalTensorGermSeminorm A B S W hS hSO weight j normalized =
          (delta1^2)⁻¹ * parameterRound2_originalTensorGermSeminorm A B S W hS hSO weight j
            ⟨incrementsOriginalMetricError G0 U Hfirst delta,hError⟩ := by
  intro G0 h0 Hfirst G1 hError
  let error : parameterRound2_originalTensorGermSpace A B S W := ⟨_,hError⟩
  let normalized := -(delta1^2)⁻¹ • error
  refine ⟨normalized,?_,?_⟩
  · exact (round4ParameterProbe_first_normalized_defect F0 hF0 U delta delta1 hdelta hdelta1 hsmall).symm
  · intro weight j
    change (parameterRound2_originalTensorGermSeminorm A B S W hS hSO weight j)
      (-(delta1^2)⁻¹ • error) = _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg delta1))]

/-- The two literal normalized error powers for accuracy 440. The input
scale is τ=t^(6/5), and the repair starts at δ₁=τ^10. -/
theorem round4ParameterProbe_first_error_scale_identity
    {t : ℝ} (ht : 0 < t) :
    (((t^(6/5 : ℝ))^10)^2)⁻¹ *
      (t^10*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^440+(t^10)^3/t^(6/5 : ℝ)) =
      t^(30 : ℝ)+t^(24/5 : ℝ) := by
  have hratio : t^(6/5 : ℝ)/t^(11/10 : ℝ) = t^(1/10 : ℝ) := by
    rw [← Real.rpow_sub ht]
    norm_num
  have hden : ((t^(6/5 : ℝ))^10)^2 = t^(24 : ℝ) := by
    rw [← pow_mul,← Real.rpow_mul_natCast ht.le]
    norm_num
  have hlarge : (t^(1/10 : ℝ))^440 = t^(44 : ℝ) := by
    rw [← Real.rpow_mul_natCast ht.le]
    norm_num
  have hten : t^(10 : ℕ) = t^(10 : ℝ) := by norm_num
  have hthirty : (t^10)^3 = t^(30 : ℝ) := by norm_num [← pow_mul]
  rw [hratio,hden,hlarge,hthirty,hten]
  rw [← Real.rpow_add ht,← Real.rpow_sub ht]
  rw [mul_add,← div_eq_inv_mul,← div_eq_inv_mul,← Real.rpow_sub ht,← Real.rpow_sub ht]
  norm_num

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_first_normalized_defect
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_first_defect_germ
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_first_error_scale_identity
