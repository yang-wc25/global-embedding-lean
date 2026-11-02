import GlobalEmbedding.Paper.IncrementsActualFiniteResidual
import GlobalEmbedding.Paper.IncrementsModeComplexLinearity

/-!
# The original geometric finite mode residual

Source: `main.tex`, lem:increments630–650. These actual consumer identities reuse
normal canonical finite residual and SAME geometric coefficients. Their proofs are
extracted verbatim from W4 frozen118b9e0a; no finite telescoping or estimate is repeated.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

open Manifold

section OriginalMode

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The ORIGINAL geometric reduced operator has the actual finite residual, with
complex commutation discharged by its constructed coefficients. Geometry/source
smoothness remain genuine internal caller outputs on the original open chart. -/
theorem incrementsModeActualFiniteResidual_eq
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (α : ℂ) (hα : α ≠ 0) (p : ℕ) (k : D → Cdata) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ContDiffOn ℝ ∞ k O) (x : D) (hx : x ∈ O) :
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let U := incrementsActualModeSum A B α p k
    α⁻¹ • U x + incrementsModeComplexReducedOperator F hF c U x - k x =
      -((incrementsActualModeStep A B α)^[p] k) x := by
  let A := incrementsModeComplexFirstOrderA F hF c
  let B := incrementsModeComplexFirstOrderB F hF c
  let U := incrementsActualModeSum A B α p k
  change α⁻¹ • U x + incrementsModeComplexReducedOperator F hF c U x - k x = _
  have hd : DifferentiableAt ℝ U x :=
    ((increments_actual_mode_sum_contDiffOn A B α p k O hO hA hB hk x hx).contDiffAt
      (hO.mem_nhds hx)).differentiableAt (by simp)
  rw [incrementsModeComplexReducedOperator_first_order F hF c U x hd]
  exact increments_actual_mode_residual_eq A B α hα p k O hO hA hB hk
    (fun y _ jet ↦ incrementsModeComplexFirstOrderA_smul F hF c y α jet)
    (fun y _ z ↦ incrementsModeComplexFirstOrderB_smul F hF c y α z) x hx

/-- The SAME original geometric residual has the genuine (tau/ell)^p weighted bound.
Only accepted coefficient identities and germ locality are added. Geometry/source
jet bounds remain explicit internal caller outputs; no desired residual bound is assumed. -/
theorem incrementsModeActualFiniteResidual_scaled_jet_tau
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (n p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (τ : ℝ) (hτ : 0 < τ) (k : D → Cdata)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ContDiffOn ℝ ∞ k O)
    (ell Mb Kb : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mb)
    (hBb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mb)
    (hkb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ Kb)
    (j : ℕ) (hjp : j + p ≤ n) (x : D) (hx : x ∈ S) :
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let α := (τ : ℂ) / Complex.I
    let U := incrementsActualModeSum A B α p k
    ell ^ j * ‖iteratedFDeriv ℝ j
        (fun y ↦ α⁻¹ • U y + incrementsModeComplexReducedOperator F hF c U y - k y) x‖ ≤
      (2 * 2 ^ n * Mb) ^ p * (τ / ell) ^ p * Kb := by
  let A := incrementsModeComplexFirstOrderA F hF c
  let B := incrementsModeComplexFirstOrderB F hF c
  let α := (τ : ℂ) / Complex.I
  let U := incrementsActualModeSum A B α p k
  change ell ^ j * ‖iteratedFDeriv ℝ j
    (fun y ↦ α⁻¹ • U y + incrementsModeComplexReducedOperator F hF c U y - k y) x‖ ≤ _
  have he : (fun y ↦ α⁻¹ • U y + incrementsModeComplexReducedOperator F hF c U y - k y)
      =ᶠ[𝓝 x] incrementsActualModeResidual A B α p k := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    have hd : DifferentiableAt ℝ U y :=
      ((increments_actual_mode_sum_contDiffOn A B α p k O hO hA hB hk y hy).contDiffAt
        (hO.mem_nhds hy)).differentiableAt (by simp)
    rw [incrementsModeComplexReducedOperator_first_order F hF c U y hd]
    rfl
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
  exact increments_actual_mode_residual_scaled_jet_tau n p O S hO hSO A B τ hτ k
    hA hB hk
    (fun y _ jet ↦ incrementsModeComplexFirstOrderA_smul F hF c y α jet)
    (fun y _ z ↦ incrementsModeComplexFirstOrderB_smul F hF c y α z)
    ell Mb Kb hell hell1 hM hK hAb hBb hkb j hjp x hx

end OriginalMode
end GlobalEmbedding.Paper
