import GlobalEmbedding.Offline.PairedValueCoincidenceRank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Combining incidence-normal, value-normal, and source-tangent columns

The normal space is the orthogonal complement of the actual tangent image.
The injection proved here adds actual tangent directions to the independent
normal/incidence principal columns. The existing finite-column stability
theorem then yields the required lower bound for a perturbed joint derivative.
No rank of that derivative is a hypothesis.
-/

noncomputable section
open Function GlobalEmbedding.Offline

namespace GlobalEmbedding.Upgrade

variable {E R V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Add an actual normal vector to an actual source tangent vector, preserving
the independent incidence-equation component. -/
def normalTangentAssembly (T : E →L[ℝ] V) :
    ((R × T.rangeᗮ) × E) →ₗ[ℝ] R × V where
  toFun z := (z.1.1, (z.1.2 : V) + T z.2)
  map_add' x y := by ext <;> simp; abel
  map_smul' a z := by ext <;> simp [smul_add]

/-- Immersion and actual orthogonality force the assembly to be injective.
This requires neither surjectivity of the tangent map nor a chosen normal
orientation or global normal frame. -/
theorem normalTangentAssembly_injective (T : E →L[ℝ] V) (hT : Injective T) :
    Injective (normalTangentAssembly (R := R) T) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨⟨r, w⟩, e⟩ h
  have hr : r = 0 := congrArg Prod.fst h
  have he : (w : V) + T e = 0 := congrArg Prod.snd h
  have hwR : (w : V) ∈ T.range := by
    refine ⟨-e, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left he).symm
  have hw0 : (w : V) = 0 :=
    (Submodule.disjoint_def.mp T.range.orthogonal_disjoint) _ hwR w.property
  have hw : w = 0 := Subtype.ext hw0
  have hTe : T e = 0 := by simpa only [hw0, zero_add] using he
  have he0 : e = 0 := hT (by simpa using hTe)
  simp [hr, hw, he0]

/-- The actual principal joint columns: selected incidence/normal parameter
columns followed by the first-source tangent columns. -/
def normalTangentColumns {k n : ℕ} (T : E →L[ℝ] V)
    (v : Fin k → R × T.rangeᗮ) (e : Fin n → E) : Fin (k + n) → R × V :=
  fun i ↦ normalTangentAssembly T
    (Sum.elim (fun j ↦ (v j, 0)) (fun j ↦ (0, e j)) (finSumFinEquiv.symm i))

theorem normalTangentColumns_independent {k n : ℕ}
    (T : E →L[ℝ] V) (hT : Injective T)
    (v : Fin k → R × T.rangeᗮ) (e : Fin n → E)
    (hv : LinearIndependent ℝ v) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (normalTangentColumns T v e) := by
  have hp := linearIndependent_inl_union_inr' hv he
  have hm := hp.map' (normalTangentAssembly (R := R) T)
    (LinearMap.ker_eq_bot.mpr (normalTangentAssembly_injective T hT))
  exact hm.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective

/-- A positive margin for the actual full principal columns is selected before
all perturbed maps and all fast angles. The old finite-column theorem is used
directly after that geometric independence proof. -/
theorem exists_normalTangent_joint_rank_tolerance {k n : ℕ}
    [FiniteDimensional ℝ R] [FiniteDimensional ℝ V]
    (T : E →L[ℝ] V) (hT : Injective T)
    (v : Fin k → R × T.rangeᗮ) (e : Fin n → E)
    (hv : LinearIndependent ℝ v) (he : LinearIndependent ℝ e) :
    ∃ eps > 0, ∀ {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      (J : P →L[ℝ] R × V) (d : Fin (k + n) → P),
      (∀ i, ‖J (d i) - normalTangentColumns T v e i‖ ≤ eps) →
        k + n ≤ Module.finrank ℝ J.range := by
  obtain ⟨m, hm, hframe⟩ := exists_positive_finite_frame_margin
    (normalTangentColumns T v e) (normalTangentColumns_independent T hT v e hv he)
  let eps := m / (2 * ((k + n : ℕ) + 1 : ℝ))
  have heps : 0 < eps := div_pos hm (by positivity)
  have hsmall : ((k + n : ℕ) : ℝ) * eps < m := by
    dsimp [eps]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (((k + n : ℕ) : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (k + n)]
  refine ⟨eps, heps, ?_⟩
  intro P _ _ J d herr
  exact finrank_range_ge_of_close_finite_columns J (ContinuousLinearMap.id ℝ (R × V))
    d (normalTangentColumns T v e) heps.le hframe herr hsmall

end GlobalEmbedding.Upgrade
