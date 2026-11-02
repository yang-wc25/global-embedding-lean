import Probes.ActualFixedMetricSecondForm
import Probes.ActualProbeConnectionResponse

/-!
# Native parameter derivative of the original true second form

The family is assumed to have the actual fixed induced metric, exactly as the
output of repair in prop:probes. Its connection equality is derived from that
metric equality. The conclusion uses native derivatives of the actual first
and second spatial jets, not an assumed formula for the response. This is the
bridge through which the actual free and reconstructed columns enter true B.
-/
noncomputable section
open Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Offline

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Actual differentiation of the original trueSecondForm at every binary
Sym2 product for a genuine fixed-metric family. Connection differentiation
vanishes because fixed-metric germs give an actual constant connection. -/
theorem fderiv_trueSecondForm_fixed_metric
    (F : P → E → V) (F₀ : E → V) (x v w : E)
    (hF : ∀ u, ContDiff ℝ ∞ (F u)) (hF₀ : ContDiffAt ℝ 2 F₀ x)
    (hinjF : ∀ u, Function.Injective (fderiv ℝ (F u) x))
    (hinjF₀ : Function.Injective (fderiv ℝ F₀ x))
    (hmetric : ∀ u, ∀ᶠ y in 𝓝 x, ∀ a b : E,
      inner ℝ (fderiv ℝ (F u) y a) (fderiv ℝ (F u) y b) =
        inner ℝ (fderiv ℝ F₀ y a) (fderiv ℝ F₀ y b))
    (u a : P)
    (hH : DifferentiableAt ℝ (fun z ↦ fderiv ℝ (fderiv ℝ (F z)) x) u)
    (hD : DifferentiableAt ℝ (fun z ↦ fderiv ℝ (F z) x) u) :
    fderiv ℝ (fun z ↦ (trueSecondForm (I := 𝓘(ℝ, E)) (F z) (hF z).contMDiff x
      (symmetricSquareProduct (TangentSpace 𝓘(ℝ, E) x)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm w)) : V)) u a =
      fderiv ℝ (fun z ↦ fderiv ℝ (fderiv ℝ (F z)) x) u a v w -
        fderiv ℝ (fun z ↦ fderiv ℝ (F z) x) u a (probeInducedConnection F₀ x v w) := by
  have heq : (fun z ↦ (trueSecondForm (I := 𝓘(ℝ, E)) (F z) (hF z).contMDiff x
      (symmetricSquareProduct (TangentSpace 𝓘(ℝ, E) x)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm w)) : V)) =
      fun z ↦ fderiv ℝ (fderiv ℝ (F z)) x v w -
        fderiv ℝ (F z) x (probeInducedConnection F₀ x v w) := by
    funext z
    exact trueSecondForm_eq_hessian_sub_fixedConnection (F z) F₀ x v w
      (hF z) hF₀ (hinjF z) hinjF₀ (hmetric z)
  have hHv := hH.clm_apply (differentiableAt_const v)
  have hHvw := hHv.clm_apply (differentiableAt_const w)
  have hDΓ := hD.clm_apply (differentiableAt_const (probeInducedConnection F₀ x v w))
  rw [heq, fderiv_fun_sub hHvw hDΓ, sub_apply]
  simp only [fderiv_clm_apply hHv (differentiableAt_const w),
    fderiv_clm_apply hH (differentiableAt_const v),
    fderiv_clm_apply hD (differentiableAt_const (probeInducedConnection F₀ x v w)),
    fderiv_fun_const, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Pi.zero_apply, zero_apply, map_zero, zero_add, add_zero]

#print axioms fderiv_trueSecondForm_fixed_metric
end GlobalEmbedding.Offline
