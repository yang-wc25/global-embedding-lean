import GlobalEmbedding.Paper.PlanarHopfSphere
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Algebra.Ring.Int.Units

/-!
# The actual antipodal quotient and its double covering

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–259.
DAG node: `planar-antipodal-quotient`.
This file establishes the actual quotient topology and pulled charted-space atlas.
Smoothness of that atlas is a separate obligation.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The actual deck map of either integer unit. -/
def planarAntipodalDeck {C : ℕ} (u : ℤˣ) (z : PlanarHopfSphere C) : PlanarHopfSphere C :=
  if u = 1 then z else -z

/-- The two integer units act by the identity and the genuine antipodal map. -/
instance planarAntipodalMulAction (C : ℕ) : MulAction ℤˣ (PlanarHopfSphere C) where
  smul := planarAntipodalDeck
  one_smul z := by
    change planarAntipodalDeck 1 z = z
    simp [planarAntipodalDeck]
  mul_smul u v z := by
    change planarAntipodalDeck (u * v) z = planarAntipodalDeck u (planarAntipodalDeck v z)
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;> simp [planarAntipodalDeck]

/-- The nontrivial deck transformation is the actual sphere antipode. -/
@[simp] theorem planarAntipodal_neg_one_smul {C : ℕ} (z : PlanarHopfSphere C) :
    (-1 : ℤˣ) • z = -z := by
  change (if (-1 : ℤˣ) = 1 then z else -z) = -z
  simp

/-- Every deck map is continuous in the native sphere topology. -/
instance planarAntipodalContinuous (C : ℕ) : ContinuousConstSMul ℤˣ (PlanarHopfSphere C) where
  continuous_const_smul u := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · change Continuous (fun z : PlanarHopfSphere C ↦ z)
      exact continuous_id
    · simpa only [planarAntipodal_neg_one_smul] using
        (continuous_neg : Continuous (fun z : PlanarHopfSphere C ↦ -z))

/-- Unit norm excludes a fixed point of the antipodal deck map. -/
theorem planarAntipodal_ne_neg {C : ℕ} (z : PlanarHopfSphere C) : z ≠ -z :=
  ne_neg_of_mem_unit_sphere ℝ z

/-- The two-element action is genuinely free. -/
instance planarAntipodalFree (C : ℕ) : IsCancelSMul ℤˣ (PlanarHopfSphere C) where
  left_cancel' u z w h := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa using h
    · simpa using h
  right_cancel' u v z h := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · rfl
    · exact False.elim (planarAntipodal_ne_neg z (by simpa using h))
    · exact False.elim (planarAntipodal_ne_neg z (by simpa using h.symm))
    · rfl

/-- Real projective space here is literally the quotient of the actual complex unit
sphere by its antipodal action, with the actual quotient topology. -/
abbrev PlanarRealProjective (C : ℕ) := MulAction.orbitRel.Quotient ℤˣ (PlanarHopfSphere C)

/-- The actual quotient projection. -/
def planarAntipodalProjection {C : ℕ} : PlanarHopfSphere C → PlanarRealProjective C :=
  Quotient.mk (MulAction.orbitRel ℤˣ (PlanarHopfSphere C))

/-- The native quotient projection is surjective. -/
theorem planarAntipodalProjection_surjective (C : ℕ) :
    Function.Surjective (@planarAntipodalProjection C) := Quotient.mk_surjective

/-- The quotient is the genuine free finite-action covering, not an assumed cover. -/
theorem planarAntipodalProjection_quotientCovering (C : ℕ) :
    IsQuotientCoveringMap (@planarAntipodalProjection C) ℤˣ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- In particular the actual quotient projection is a covering map. -/
theorem planarAntipodalProjection_covering (C : ℕ) :
    IsCoveringMap (@planarAntipodalProjection C) :=
  (planarAntipodalProjection_quotientCovering C).isCoveringMap

/-- Equal projected points are exactly equal or antipodal sphere points. -/
theorem planarAntipodalProjection_eq_iff {C : ℕ} (z w : PlanarHopfSphere C) :
    planarAntipodalProjection z = planarAntipodalProjection w ↔ z = w ∨ z = -w := by
  rw [(planarAntipodalProjection_quotientCovering C).apply_eq_iff_mem_orbit,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, hu⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact Or.inl (by simpa using hu.symm)
    · exact Or.inr (by simpa using hu.symm)
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨-1, planarAntipodal_neg_one_smul w⟩

/-- The genuine antipodal points have the same projective image. -/
@[simp] theorem planarAntipodalProjection_neg {C : ℕ} (z : PlanarHopfSphere C) :
    planarAntipodalProjection (-z) = planarAntipodalProjection z :=
  (planarAntipodalProjection_eq_iff _ _).mpr (Or.inr rfl)

/-- Each actual deck transformation is native smooth on the sphere. -/
theorem planarAntipodalDeck_contMDiff (C : ℕ) [Fact (0 < C)] (u : ℤˣ) :
    ContMDiff (planarHopfModel C) (planarHopfModel C) ∞
      (fun z : PlanarHopfSphere C ↦ u • z) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · change ContMDiff (planarHopfModel C) (planarHopfModel C) ∞
        (fun z : PlanarHopfSphere C ↦ z)
    exact contMDiff_id
  · simpa only [planarAntipodal_neg_one_smul] using
      (contMDiff_neg_sphere : ContMDiff (planarHopfModel C) (planarHopfModel C) ∞
        (fun z : PlanarHopfSphere C ↦ -z))

/-- Every fiber has precisely the two deck-group elements as its points. -/
def planarAntipodalFiberEquiv {C : ℕ} (z : PlanarHopfSphere C) :
    {w : PlanarHopfSphere C // planarAntipodalProjection w = planarAntipodalProjection z} ≃ ℤˣ :=
  (planarAntipodalProjection_quotientCovering C).fiberEquivGroup ⟨z, rfl⟩

/-- Every actual fiber has cardinality two; the unit sphere action has no branching. -/
theorem planarAntipodalFiber_card {C : ℕ} (z : PlanarHopfSphere C) :
    Nat.card {w : PlanarHopfSphere C //
      planarAntipodalProjection w = planarAntipodalProjection z} = 2 := by
  rw [Nat.card_congr (planarAntipodalFiberEquiv z)]
  rw [Nat.card_eq_fintype_card]
  decide

/-- Compactness is inherited from the actual compact sphere through its continuous
surjective quotient projection. -/
instance planarRealProjectiveCompact (C : ℕ) : CompactSpace (PlanarRealProjective C) :=
  inferInstance

/-- Proper discontinuity of the actual finite action makes the quotient Hausdorff. -/
theorem planarRealProjective_t2 (C : ℕ) : T2Space (PlanarRealProjective C) := inferInstance

/-- The open finite-action quotient preserves second countability. -/
instance planarRealProjectiveSecondCountable (C : ℕ) :
    SecondCountableTopology (PlanarRealProjective C) :=
  ContinuousConstSMul.secondCountableTopology

/-- The pulled native sphere atlas exists on the actual quotient. This statement
asserts a charted space only; its smooth transition proof is supplied separately. -/
abbrev planarRealProjective_charted (C : ℕ) [Fact (0 < C)] :
    ChartedSpace (EuclideanSpace ℝ (Fin (2 * C - 1))) (PlanarRealProjective C) := inferInstance

end GlobalEmbedding.Paper
