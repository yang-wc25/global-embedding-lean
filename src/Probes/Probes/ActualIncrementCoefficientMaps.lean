import Probes.ActualIncrementTrueBJets
import Probes.ActualConnectionSlowBounds
import GlobalEmbedding.Paper.IncrementsSecondaryMode

/-!
# Fixed native coefficient maps for the actual increment operator

The same original Gamma, true-B rows, J, and transverse symmetrization are
used. The identities below preserve the 11/mixed row weights and the original
factor one half in T. Fixed coordinate-map norms can therefore remain in the
uniform constants without assuming the desired A/B/T0 coefficient estimates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

private local instance coefficientDDNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance coefficientDDSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance coefficientHessianNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance coefficientHessianSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance coefficientT0Normed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) := inferInstance
private local instance coefficientT0Space (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) := inferInstance

def actualIncrementFullRowPairing (m N : ℕ) :
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) →L[ℝ]
      (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) :=
  (2 : ℝ) • incrementsModeForcingSourcePairing

theorem actualIncrementFullRowPairing_apply (m N : ℕ)
    (b : Fin (m+1) → EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin (m+1)) :
    actualIncrementFullRowPairing m N b v i = incrementsModeRowWeight i * inner ℝ (b i) v := by
  change 2 * incrementsModeForcingSourcePairing b v i = _
  rw [incrementsModeForcingSourcePairing_apply]
  ring

def actualIncrementTransverseValueFromGamma (m : ℕ) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
        (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
          EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) :=
  - ∑ q : {p : Fin m × Fin m // p.1 ≤ p.2},
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (m+1))) ℝ
      (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}))
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single q 1))).comp
        ((innerSL ℝ : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ).comp
            (actualIncrementHessianEntry m (m+1) q.val.1.succ q.val.2.succ))

theorem actualIncrementTransverseValueFromGamma_apply (m : ℕ)
    (G : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (u : EuclideanSpace ℝ (Fin (m+1))) (q : {p : Fin m × Fin m // p.1 ≤ p.2}) :
    actualIncrementTransverseValueFromGamma m G u q =
      -inner ℝ (G (EuclideanSpace.single q.val.1.succ 1)
        (EuclideanSpace.single q.val.2.succ 1)) u := by
  simp [actualIncrementTransverseValueFromGamma, actualIncrementHessianEntry,
    Pi.single_apply, ite_mul, mul_comm]

def actualIncrementGammaRowOperator (m : ℕ) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
        (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) :=
  (actualIncrementFullRowPairing m (m+1)).comp (actualIncrementFirstRows m (m+1))

def actualIncrementPrincipalFirstOrderA (m : ℕ) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) :=
  (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Fin.cases (incrementsModeJetComponent 0 0)
      (fun a => incrementsModeJetComponent 0 a.succ + incrementsModeJetComponent a.succ 0) i)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P

/-- Exact original T0 as a fixed linear observation of the actual induced
connection of this same coordinate map. -/
theorem actual_increment_transverse_value_from_connection
    (F : M → V) (c : D → M) (x : D) :
    incrementsModeTransverseValue F c x = actualIncrementTransverseValueFromGamma m
      (actualConnectionFromJets (fun y => fderiv ℝ (F ∘ c) y)
        (fun y => fderiv ℝ (fderiv ℝ (F ∘ c)) y) x) := by
  ext u q
  rw [actualIncrementTransverseValueFromGamma_apply]
  rfl

/-- The original row Gamma contribution is a fixed linear observation of
the same actual connection, with all original row weights. -/
theorem actual_increment_gamma_row_from_connection
    (F : M → V) (c : D → M) (x : D) :
    actualIncrementFullRowPairing m (m+1) (fun i => incrementsModeGamma F c x 0 i) =
      actualIncrementGammaRowOperator m
        (actualConnectionFromJets (fun y => fderiv ℝ (F ∘ c) y)
          (fun y => fderiv ℝ (fderiv ℝ (F ∘ c)) y) x) := rfl

/-- Exact original A uses the same true-B row and included J; it is a fixed
principal coefficient minus their composition with the original half T-jet. -/
theorem actual_increment_first_order_A_eq
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) :
    incrementsModeFirstOrderA F hF c x = actualIncrementPrincipalFirstOrderA m -
      ((actualIncrementFullRowPairing m N
        (fun i => (incrementsModeSecondForm F hF c x 0 i : V))).comp
          ((normalSpace (I := I) F (c x)).subtypeL.comp
            (incrementsModeCoordinateJ F hF c x))).comp incrementsModeTransverseJet := by
  ext u i
  change incrementsModeFirstOrderA F hF c x u i =
    actualIncrementPrincipalFirstOrderA m u i -
      actualIncrementFullRowPairing m N
        (fun a => (incrementsModeSecondForm F hF c x 0 a : V))
          (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseJet u) : V) i
  rw [actualIncrementFullRowPairing_apply]
  simp [incrementsModeFirstOrderA, actualIncrementPrincipalFirstOrderA, Submodule.coe_inner]

/-- Exact original B has the same Gamma contribution and the same true-B/J/T0
composition. The submodule inner product is converted by its isometric inclusion. -/
theorem actual_increment_first_order_B_eq
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) :
    incrementsModeFirstOrderB F hF c x =
      -(actualIncrementFullRowPairing m (m+1) (fun i => incrementsModeGamma F c x 0 i)) -
        ((actualIncrementFullRowPairing m N
          (fun i => (incrementsModeSecondForm F hF c x 0 i : V))).comp
            ((normalSpace (I := I) F (c x)).subtypeL.comp
              (incrementsModeCoordinateJ F hF c x))).comp (incrementsModeTransverseValue F c x) := by
  ext u i
  change incrementsModeFirstOrderB F hF c x u i =
    -(actualIncrementFullRowPairing m (m+1) (fun a => incrementsModeGamma F c x 0 a) u i) -
      actualIncrementFullRowPairing m N
        (fun a => (incrementsModeSecondForm F hF c x 0 a : V))
          (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseValue F c x u) : V) i
  rw [actualIncrementFullRowPairing_apply, actualIncrementFullRowPairing_apply]
  simp [incrementsModeFirstOrderB, Submodule.coe_inner]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_value_from_connection
#print axioms GlobalEmbedding.Continuation.actual_increment_first_order_A_eq
#print axioms GlobalEmbedding.Continuation.actual_increment_first_order_B_eq
