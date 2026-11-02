import Smoothing.ParameterRound2IntrinsicNormalProjection

/-! One actual physical normal field, independent of every adapted chart.
Every coordinate formula is a pullback of this same intrinsic projection of
the same reference field. No compatibility of separately chosen normals is
assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def parameterRound2_intrinsicFreeNormalFieldRaw
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep → M → ℝ) (vref : Ep × M → V) (z : Ep × M) : V :=
  (parameterRound2_intrinsicPhaseFreeSpace (F z.1) (hF z.1) (psi z.1) z.2).starProjection (vref z)

def parameterRound2_intrinsicUnitFreeNormalField
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep → M → ℝ) (vref : Ep × M → V) : Ep × M → V :=
  NormedSpace.normalize ∘ parameterRound2_intrinsicFreeNormalFieldRaw F hF psi vref

theorem parameterRound2_actual_normal_field_eq_intrinsic_on
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep → M → ℝ) (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hpsi : ∀ z ∈ O, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
    (hadapt : ∀ z ∈ O, psi z.1 ((e z.1).symm z.2) = z.2 0)
    (vref : Ep × M → V) :
    let kappa := fun z : X => (z.1,(e z.1).symm z.2)
    EqOn (actualOriginalFreeNormalFieldRaw F hF e (vref ∘ kappa))
      (parameterRound2_intrinsicFreeNormalFieldRaw F hF psi vref ∘ kappa) O ∧
    EqOn (actualOriginalUnitFreeNormalField F hF e (vref ∘ kappa))
      (parameterRound2_intrinsicUnitFreeNormalField F hF psi vref ∘ kappa) O := by
  intro kappa
  have hraw : EqOn (actualOriginalFreeNormalFieldRaw F hF e (vref ∘ kappa))
      (parameterRound2_intrinsicFreeNormalFieldRaw F hF psi vref ∘ kappa) O := by
    intro z hz
    exact parameterRound2_actual_normal_raw_eq_intrinsic (F z.1) (hF z.1) (psi z.1)
      (e z.1) (he z.1) {y | (z.1,y) ∈ O}
      (hO.preimage (continuous_const.prodMk continuous_id)) (fun y hy => hcoord (z.1,y) hy)
      z.2 hz (hpsi z hz) (fun y hy => hadapt (z.1,y) hy) (vref (kappa z))
  refine ⟨hraw,?_⟩
  intro z hz
  exact congrArg NormedSpace.normalize (hraw hz)

theorem parameterRound2_actual_unit_normal_charts_agree
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep → M → ℝ) (vref : Ep × M → V)
    (e₁ e₂ : Ep → OpenPartialHomeomorph M D)
    (he₁ : ∀ p, e₁ p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (he₂ : ∀ p, e₂ p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O₁ O₂ : Set X) (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hcoord₁ : ∀ z ∈ O₁, z.2 ∈ (e₁ z.1).target)
    (hcoord₂ : ∀ z ∈ O₂, z.2 ∈ (e₂ z.1).target)
    (hpsi₁ : ∀ z ∈ O₁, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e₁ z.1).symm z.2))
    (hpsi₂ : ∀ z ∈ O₂, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e₂ z.1).symm z.2))
    (hadapt₁ : ∀ z ∈ O₁, psi z.1 ((e₁ z.1).symm z.2) = z.2 0)
    (hadapt₂ : ∀ z ∈ O₂, psi z.1 ((e₂ z.1).symm z.2) = z.2 0)
    (p : Ep) (x : M) (hx₁ : x ∈ (e₁ p).source) (hx₂ : x ∈ (e₂ p).source)
    (hz₁ : (p,e₁ p x) ∈ O₁) (hz₂ : (p,e₂ p x) ∈ O₂) :
    actualOriginalUnitFreeNormalField F hF e₁ (fun z : X => vref (z.1,(e₁ z.1).symm z.2)) (p,e₁ p x) =
      actualOriginalUnitFreeNormalField F hF e₂ (fun z : X => vref (z.1,(e₂ z.1).symm z.2)) (p,e₂ p x) := by
  have h₁ := (parameterRound2_actual_normal_field_eq_intrinsic_on F hF psi e₁ he₁ O₁ hO₁
    hcoord₁ hpsi₁ hadapt₁ vref).2 hz₁
  have h₂ := (parameterRound2_actual_normal_field_eq_intrinsic_on F hF psi e₂ he₂ O₂ hO₂
    hcoord₂ hpsi₂ hadapt₂ vref).2 hz₂
  dsimp only [Function.comp_apply] at h₁ h₂
  rw [(e₁ p).left_inv hx₁] at h₁
  rw [(e₂ p).left_inv hx₂] at h₂
  exact h₁.trans h₂.symm

#print axioms parameterRound2_actual_normal_field_eq_intrinsic_on
#print axioms parameterRound2_actual_unit_normal_charts_agree
end GlobalEmbedding.Continuation
