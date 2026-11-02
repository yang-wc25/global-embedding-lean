import Probes.ActualIncrementPrimitiveNormalizedMean
import Smoothing.ParameterRound2CrossCoordinates

/-!
# Real tensor assembly of the SAME actual mean coefficients

Every ordered Euclidean basis coefficient is retained. The fixed real-linear
assembly is defined by genuine coordinate covectors; on each basis pair it
is exactly the real part of the supplied original complex coefficient. Its
operator norm depends only on the fixed source dimension, never an atlas
or subordinate chart count. Full joint jets pass through this fixed map.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

private local instance meanTensorSemi (n : ℕ) : SeminormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance meanTensorNormed (n : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanTensorSpace (n : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The genuine ordered coordinate covector product. -/
def parameterRound2_coordinateTensor (n : ℕ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).smulRight
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j)

theorem parameterRound2_coordinateTensor_apply (n : ℕ) (i j : Fin n)
    (u v : EuclideanSpace ℝ (Fin n)) :
    parameterRound2_coordinateTensor n i j u v = u i * v j := rfl

/-- Fixed assembly of all original real mean coefficient slots. -/
def parameterRound2_meanTensorAssembly (n : ℕ) :
    ((Fin n × Fin n) → ℂ) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ∑ i, (Complex.reCLM.comp (ContinuousLinearMap.proj i)).smulRight
    (parameterRound2_coordinateTensor n i.1 i.2)

theorem parameterRound2_meanTensorAssembly_apply (n : ℕ)
    (coeff : (Fin n × Fin n) → ℂ) (u v : EuclideanSpace ℝ (Fin n)) :
    parameterRound2_meanTensorAssembly n coeff u v =
      ∑ i, (coeff i).re * (u i.1 * v i.2) := by
  simp [parameterRound2_meanTensorAssembly, parameterRound2_coordinateTensor_apply]

/-- The assembled tensor has exactly the original real coefficient in every
ordered source direction; no metric or symmetric-part replacement is made. -/
theorem parameterRound2_meanTensorAssembly_basis (n : ℕ)
    (coeff : (Fin n × Fin n) → ℂ) (i j : Fin n) :
    parameterRound2_meanTensorAssembly n coeff
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = (coeff (i,j)).re := by
  rw [parameterRound2_meanTensorAssembly_apply]
  simp [EuclideanSpace.single, PiLp.single_apply]
  have hcond (x : Fin n × Fin n) : x.2 = j ∧ x.1 = i ↔ x = (i,j) := by
    simp [Prod.ext_iff, and_comm]
  simp_rw [← ite_and, hcond]
  simp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Pointwise finite Pi assembly of actual joint jets. No index-cardinality
factor is lost in the coefficient supremum norm. -/
theorem parameterRound2_joint_pi_weighted_jet {ι Y : Type*} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → ι → Y) (x : X) (hf : ContDiffAt ℝ ∞ f x) (k : ℕ)
    (ell C : ℝ) (hell : 0 < ell) (hC : 0 ≤ C)
    (hb : ∀ a, ell^k * ‖iteratedFDeriv ℝ k (fun y => f y a) x‖ ≤ C) :
    ell^k * ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have he : iteratedFDeriv ℝ k f x = ContinuousMultilinearMap.pi
      (fun a => iteratedFDeriv ℝ k (fun y => f y a) x) := by
    ext w a
    have hp := (ContinuousLinearMap.proj a).iteratedFDeriv_comp_left hf
      (by simp : (k : WithTop ℕ∞) ≤ ∞)
    exact (congrArg (fun t => t w) hp).symm
  rw [he, ContinuousMultilinearMap.opNorm_pi, mul_comm (ell^k)]
  apply (le_div_iff₀ (pow_pos hell k)).mp
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hC (pow_nonneg hell.le k))).2
  intro a
  exact (le_div_iff₀ (pow_pos hell k)).2 (by simpa [mul_comm] using hb a)

/-- Full joint derivative bound for the exact tensor assembled above. -/
theorem parameterRound2_meanTensorAssembly_weighted_jets
    (n j : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (coeff : X → (Fin n × Fin n) → ℂ)
    (hcoeff : ∀ a, ContDiffOn ℝ ∞ (fun x => coeff x a) O)
    (ell C : ℝ) (hell : 0 < ell) (hC : 0 ≤ C)
    (hb : ∀ a, ∀ k ≤ j, ∀ x ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k (fun y => coeff y a) x‖ ≤ C) :
    ContDiffOn ℝ ∞ (fun x => parameterRound2_meanTensorAssembly n (coeff x)) O ∧
    ∀ k ≤ j, ∀ x ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k (fun y => parameterRound2_meanTensorAssembly n (coeff y)) x‖ ≤
        ‖parameterRound2_meanTensorAssembly n‖*C := by
  have hc : ContDiffOn ℝ ∞ coeff O := contDiffOn_pi.2 hcoeff
  refine ⟨(parameterRound2_meanTensorAssembly n).contDiff.comp_contDiffOn hc,?_⟩
  intro k hk x hx
  have hcx : ContDiffAt ℝ ∞ coeff x := hc.contDiffAt (hO.mem_nhds (hSO hx))
  have hjet := parameterRound2_joint_pi_weighted_jet coeff x hcx k ell C hell hC
    (fun a => hb a k hk x hx)
  rw [show (fun y => parameterRound2_meanTensorAssembly n (coeff y)) =
      parameterRound2_meanTensorAssembly n ∘ coeff from rfl,
    (parameterRound2_meanTensorAssembly n).iteratedFDeriv_comp_left hcx (by simp)]
  calc
    _ ≤ ell^k * (‖parameterRound2_meanTensorAssembly n‖ * ‖iteratedFDeriv ℝ k coeff x‖) :=
      mul_le_mul_of_nonneg_left
        ((parameterRound2_meanTensorAssembly n).norm_compContinuousMultilinearMap_le _)
        (pow_nonneg hell.le k)
    _ = ‖parameterRound2_meanTensorAssembly n‖ * (ell^k * ‖iteratedFDeriv ℝ k coeff x‖) := by ring
    _ ≤ ‖parameterRound2_meanTensorAssembly n‖ * C :=
      mul_le_mul_of_nonneg_left hjet (norm_nonneg _)

#print axioms parameterRound2_meanTensorAssembly_basis
#print axioms parameterRound2_meanTensorAssembly_weighted_jets
end
end GlobalEmbedding.Continuation
