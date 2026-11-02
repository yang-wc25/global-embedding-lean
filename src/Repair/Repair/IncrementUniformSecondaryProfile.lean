import Repair.IncrementUniformSecondaryRaw
import Probes.Round4ParameterSecondaryGeometryProfile

/-!
# One numerical secondary geometry profile and its exact finite prefix

When the actual raw factory installs the same numerical transverse reserve
in every signed piece, its existing finite-maximum geometry profile is
bounded by one fixed scalar profile.  The bound is independent of the
number of pieces, even for an empty family.  The original profile order and
the two extra inverse-coordinate derivatives are retained verbatim.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped Classical
namespace GlobalEmbedding.Continuation

theorem increment_finite_maximum_le {I : Type*} [Fintype I]
    (f : I → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ i, f i ≤ B) :
    round3PreparedFiniteMaximum f ≤ B := by
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact hB
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact hf i

/-- The original geometry cost evaluated once, rather than selected from
the geometry of a particular reference family. -/
def incrementUniformSecondaryGeometryProfile
    (m d N q : ℕ) (reserve : ℝ) (InputBudget Tinv Tobs : ℕ → ℝ)
    (c : ℝ) (j : ℕ) : ℝ :=
  round4ParameterSecondaryGeometryProfile m d N q (fun _ : Unit => reserve)
    InputBudget Tinv Tobs c j

theorem incrementUniformSecondaryGeometryProfile_nonneg
    (m d N q : ℕ) (reserve : ℝ) (InputBudget Tinv Tobs : ℕ → ℝ)
    (c : ℝ) (j : ℕ) :
    0 ≤ incrementUniformSecondaryGeometryProfile m d N q reserve InputBudget Tinv Tobs c j :=
  round4ParameterSecondaryGeometryProfile_nonneg m d N q (fun _ : Unit => reserve)
    InputBudget Tinv Tobs c j

/-- This applies to the literal `cT` equality exported by
`increment_uniform_secondary_raw_piece_from_host`, and to the same reserve
divided by sixteen in the existing stable-reference factory. -/
theorem increment_uniform_secondary_geometry_profile_bound
    {I : Type*} [Fintype I]
    (m d N q : ℕ) (reserves : I → ℝ) (reserve : ℝ)
    (hReserve : ∀ i, reserves i = reserve)
    (InputBudget Tinv Tobs : ℕ → ℝ) (c : ℝ) (j : ℕ) :
    round4ParameterSecondaryGeometryProfile m d N q reserves InputBudget Tinv Tobs c j ≤
      incrementUniformSecondaryGeometryProfile m d N q reserve InputBudget Tinv Tobs c j := by
  apply increment_finite_maximum_le
  · exact incrementUniformSecondaryGeometryProfile_nonneg m d N q reserve InputBudget Tinv Tobs c j
  · intro i
    rw [hReserve i]
    exact round3PreparedFiniteMaximum_bound (fun _ : Unit =>
      round3PreparedGeometryCost m d N Tinv reserve (1+Tobs 1)
        (actualSecondarySolveOrder q j) (j+1)
        (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c) ()

/-- All numerical secondary geometry through order `J` reads the original
input profile only through `J+q+4`, inverse jets through `J+q+6`, and the
observer first derivative. No maximum over a new actual family is read. -/
theorem increment_uniform_secondary_geometry_prefix
    (m d N q : ℕ) (reserve : ℝ)
    (InputBudget Tinv Tobs InputBudget' Tinv' Tobs' : ℕ → ℝ)
    (c : ℝ) (J : ℕ)
    (hInput : ∀ k, k ≤ J+q+4 → InputBudget k = InputBudget' k)
    (hInv : ∀ k, k ≤ J+q+6 → Tinv k = Tinv' k)
    (hObs : Tobs 1 = Tobs' 1) :
    ∀ j, j ≤ J →
      incrementUniformSecondaryGeometryProfile m d N q reserve InputBudget Tinv Tobs c j =
        incrementUniformSecondaryGeometryProfile m d N q reserve InputBudget' Tinv' Tobs' c j := by
  intro j hj
  exact round4ParameterSecondaryGeometryProfile_prefix m d N q (fun _ : Unit => reserve)
    InputBudget Tinv Tobs InputBudget' Tinv' Tobs' c j
    (hInput _ (by omega)) (fun k hk => hInv k (by omega)) hObs

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_uniform_secondary_geometry_profile_bound
#print axioms GlobalEmbedding.Continuation.increment_uniform_secondary_geometry_prefix
