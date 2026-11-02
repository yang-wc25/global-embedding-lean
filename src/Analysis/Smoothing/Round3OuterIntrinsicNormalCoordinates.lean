import Smoothing.ParameterRound2IntrinsicNormalField

/-! A parameter chart and an adapted source chart evaluate one physical
intrinsic normal. The parameter type is arbitrary: no identity-chart or
vector-space structure on the physical parameter manifold is used.
This equality binds the actual new-stage projection to one field before
the original coordinate norms are assembled.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep P M : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_actual_normal_parameter_pullback_eq_intrinsic
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : P → M → ℝ) (vref : P × M → V) (sigma : Ep → P)
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hpsi : ∀ z ∈ O, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (psi (sigma z.1)) ((e z.1).symm z.2))
    (hadapt : ∀ z ∈ O, psi (sigma z.1) ((e z.1).symm z.2) = z.2 0) :
    EqOn (actualOriginalUnitFreeNormalField (fun p => F (sigma p)) (fun p => hF (sigma p)) e
      (fun z : X => vref (sigma z.1,(e z.1).symm z.2)))
      (fun z : X => parameterRound2_intrinsicUnitFreeNormalField F hF psi vref
        (sigma z.1,(e z.1).symm z.2)) O := by
  have h := (parameterRound2_actual_normal_field_eq_intrinsic_on
    (fun p => F (sigma p)) (fun p => hF (sigma p)) (fun p => psi (sigma p))
    e he O hO hcoord hpsi hadapt (fun z : Ep × M => vref (sigma z.1,z.2))).2
  exact h

/-- Smoothness and every joint jet of the constructed normal belong to the
same physical field, even when different parameter charts are used. -/
theorem round3_actual_normal_parameter_pullback_germs
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : P → M → ℝ) (vref : P × M → V) (sigma : Ep → P)
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hpsi : ∀ z ∈ O, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (psi (sigma z.1)) ((e z.1).symm z.2))
    (hadapt : ∀ z ∈ O, psi (sigma z.1) ((e z.1).symm z.2) = z.2 0) :
    let native := actualOriginalUnitFreeNormalField (fun p => F (sigma p)) (fun p => hF (sigma p)) e
      (fun z : X => vref (sigma z.1,(e z.1).symm z.2))
    let physical := fun z : X => parameterRound2_intrinsicUnitFreeNormalField F hF psi vref
      (sigma z.1,(e z.1).symm z.2)
    (ContDiffOn ℝ ∞ native O ↔ ContDiffOn ℝ ∞ physical O) ∧
    ∀ j z, z ∈ O → iteratedFDeriv ℝ j native z = iteratedFDeriv ℝ j physical z := by
  intro native physical
  have heq : EqOn native physical O :=
    round3_actual_normal_parameter_pullback_eq_intrinsic F hF psi vref sigma e he O hO hcoord hpsi hadapt
  refine ⟨⟨fun h => h.congr (fun z hz => (heq hz).symm),
    fun h => h.congr (fun z hz => heq hz)⟩,?_⟩
  intro j z hz
  exact ((Filter.eventuallyEq_of_mem (hO.mem_nhds hz) (fun y hy => heq hy)).iteratedFDeriv ℝ j).eq_of_nhds

omit [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
/-- Projection and normalization retain the intrinsic normal and exact
phase-kernel condition pointwise. Nonvanishing is needed only for unit length. -/
theorem round3_intrinsic_unit_normal_mem_phase_free
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : P → M → ℝ) (vref : P × M → V) (z : P × M) :
    parameterRound2_intrinsicUnitFreeNormalField F hF psi vref z ∈
      parameterRound2_intrinsicPhaseFreeSpace (F z.1) (hF z.1) (psi z.1) z.2 := by
  let L := parameterRound2_intrinsicPhaseFreeSpace (F z.1) (hF z.1) (psi z.1) z.2
  exact L.smul_mem _ (L.starProjection_apply_mem (vref z))

#print axioms round3_intrinsic_unit_normal_mem_phase_free
#print axioms round3_actual_normal_parameter_pullback_eq_intrinsic
#print axioms round3_actual_normal_parameter_pullback_germs
end GlobalEmbedding.Continuation
