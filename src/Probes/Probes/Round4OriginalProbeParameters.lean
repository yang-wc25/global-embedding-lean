import Probes.Round4PrescribedGlobalWave
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
The original paired-probe parameter space is (Fin r × Bool) → ℝ with its
Pi norm. A genuine coordinate reindexing identifies it isometrically with
the Fin p parameter space of the constructed modes, including r = 0.
No Euclidean norm substitution, extra coordinates, or dimension loss occurs.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def round4PairedParameterIndex (r : ℕ) :
    (Fin r × Bool) ≃ Fin (Fintype.card (Fin r × Bool)) := Fintype.equivFin _

def round4PairedParameterReindex (r : ℕ) :
    ((Fin r × Bool) → ℝ) ≃ₗᵢ[ℝ] (Fin (Fintype.card (Fin r × Bool)) → ℝ) where
  toLinearEquiv := LinearEquiv.piCongrLeft' ℝ (fun _ : Fin r × Bool => ℝ)
    (round4PairedParameterIndex r)
  norm_map' u := by
    change ‖fun j => u ((round4PairedParameterIndex r).symm j)‖ = ‖u‖
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
        (fun j => norm_le_pi_norm u _)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro q
      simpa only [Equiv.symm_apply_apply] using
        norm_le_pi_norm (fun j => u ((round4PairedParameterIndex r).symm j))
          (round4PairedParameterIndex r q)

@[simp] theorem round4PairedParameterReindex_apply_label {r : ℕ}
    (u : (Fin r × Bool) → ℝ) (q : Fin r × Bool) :
    round4PairedParameterReindex r u (round4PairedParameterIndex r q) = u q := by
  change u ((round4PairedParameterIndex r).symm (round4PairedParameterIndex r q)) = u q
  rw [Equiv.symm_apply_apply]

@[simp] theorem round4PairedParameterReindex_single {r : ℕ} (q : Fin r × Bool) (x : ℝ) :
    round4PairedParameterReindex r (Pi.single q x) =
      Pi.single (round4PairedParameterIndex r q) x := by
  classical
  ext j
  change (Pi.single q x : (Fin r × Bool) → ℝ) ((round4PairedParameterIndex r).symm j) =
    (Pi.single (round4PairedParameterIndex r q) x : Fin (Fintype.card (Fin r × Bool)) → ℝ) j
  by_cases h : j = round4PairedParameterIndex r q
  · subst j
    simp
  · have hh : (round4PairedParameterIndex r).symm j ≠ q := by
      intro heq
      apply h
      exact ((round4PairedParameterIndex r).apply_symm_apply j).symm.trans
        (congrArg (round4PairedParameterIndex r) heq)
    simp [h,hh]

theorem round4PairedParameterReindex_ball {r : ℕ} (radius : ℝ) :
    (round4PairedParameterReindex r) ⁻¹' Metric.ball 0 radius = Metric.ball 0 radius := by
  ext u
  simp only [mem_preimage,Metric.mem_ball,dist_zero_right,
    LinearIsometryEquiv.norm_map]

theorem round4_paired_parameter_derivative {r : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : (Fin (Fintype.card (Fin r × Bool)) → ℝ) → Y)
    (u d : (Fin r × Bool) → ℝ)
    (hf : DifferentiableAt ℝ f (round4PairedParameterReindex r u)) :
    fderiv ℝ (fun v => f (round4PairedParameterReindex r v)) u d =
      fderiv ℝ f (round4PairedParameterReindex r u) (round4PairedParameterReindex r d) := by
  have h := hf.hasFDerivAt.comp u (round4PairedParameterReindex r).toContinuousLinearEquiv.hasFDerivAt
  convert congrArg (fun A : ((Fin r × Bool) → ℝ) →L[ℝ] Y => A d) h.fderiv using 1 <;> rfl

theorem round4_paired_parameter_response_column {r : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : (Fin (Fintype.card (Fin r × Bool)) → ℝ) → Y)
    (u : (Fin r × Bool) → ℝ) (q : Fin r × Bool)
    (hf : DifferentiableAt ℝ f (round4PairedParameterReindex r u)) :
    fderiv ℝ (fun v => f (round4PairedParameterReindex r v)) u (Pi.single q 1) =
      fderiv ℝ f (round4PairedParameterReindex r u)
        (Pi.single (round4PairedParameterIndex r q) 1) := by
  rw [round4_paired_parameter_derivative f u (Pi.single q 1) hf,
    round4PairedParameterReindex_single]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4PairedParameterReindex
#print axioms GlobalEmbedding.Continuation.round4_paired_parameter_response_column
