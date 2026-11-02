import Smoothing.Round3RepairUniformMeanData

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairProfileFactoryChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairProfileFactoryIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
/-- Primitive mean constants, fixed independently of all secondary
geometry and final increment constants. -/
structure Round3RepairMeanPrimitiveProfiles where
  rho : ℝ
  rho_pos : 0 < rho
  reserve : ℝ
  reserve_pos : 0 < reserve
  Rsub : ℕ
  Lprimary : ℕ
  Bnd : ℕ → ℝ → ℝ
  Mg : ℕ → ℝ
  Dinput : ℕ → ℝ
  T : ℕ → ℝ
  Bnd_nonneg : ∀ j R, 0 ≤ Bnd j R
  Mg_nonneg : ∀ j, 0 ≤ Mg j
  Dinput_nonneg : ∀ j, 0 ≤ Dinput j
  T_nonneg : ∀ j, 0 ≤ T j

/-- Complete the primitive profile by explicit maxima. Only the original
finite Kq input profile is consumed; no current SF/Kq norm is selected. -/
def Round3RepairMeanPrimitiveProfiles.complete
    (mean : Round3RepairMeanPrimitiveProfiles) (q : ℕ) (Input : ℕ → ℝ)
    (Rsecondary : ℕ) (Mrest Kcut Tinv Tobs : ℕ → ℝ) : Round3RepairPrimitiveProfiles where
  rho := mean.rho
  rho_pos := mean.rho_pos
  reserve := mean.reserve
  reserve_pos := mean.reserve_pos
  Rsub := mean.Rsub
  Lprimary := mean.Lprimary
  Rsecondary := Rsecondary
  Bnd := mean.Bnd
  Mg := mean.Mg
  Dinput := mean.Dinput
  T := mean.T
  Bsec := fun j => max 0 (mean.Bnd (j+q+4) (Input (j+q+4+(q+4))))
  Msec := fun j => max (mean.Mg (j+q+4)) (Mrest j)
  Ccut := fun j => max 0 (Kcut j)
  Tsec := fun _ => mean.T
  Tinv := fun _ a => max 0 (Tinv a)
  Tobs := fun _ a => max 0 (Tobs a)
  Bnd_nonneg := mean.Bnd_nonneg
  Mg_nonneg := mean.Mg_nonneg
  Dinput_nonneg := mean.Dinput_nonneg
  T_nonneg := mean.T_nonneg
  Bsec_nonneg := fun _ => le_max_left _ _
  Msec_nonneg := fun j => (mean.Mg_nonneg _).trans (le_max_left _ _)
  Ccut_nonneg := fun _ => le_max_left _ _
  Tsec_nonneg := fun _ => mean.T_nonneg
  Tinv_nonneg := fun _ _ => le_max_left _ _
  Tobs_nonneg := fun _ _ => le_max_left _ _

/-- The explicit profile simultaneously pays for the canonical primary
raw atlas and dominates the original secondary family. -/
theorem round3_repair_completed_profile_bounds
    (mean : Round3RepairMeanPrimitiveProfiles) (q : ℕ) (Input : ℕ → ℝ)
    (Rsecondary : ℕ) (Mrest Kcut Tinv Tobs : ℕ → ℝ) :
    let profile := mean.complete q Input Rsecondary Mrest Kcut Tinv Tobs
    (∀ j, profile.Bnd (j+q+4) (Input (j+q+4+(q+4))) ≤ profile.Bsec j) ∧
    (∀ j, profile.Mg (j+q+4) ≤ profile.Msec j) ∧
    (∀ j, Mrest j ≤ profile.Msec j) ∧ (∀ j, Kcut j ≤ profile.Ccut j) ∧
    (∀ j a, Tinv a ≤ profile.Tinv j a) ∧ (∀ j a, Tobs a ≤ profile.Tobs j a) ∧
    (∀ j, profile.Tsec j=mean.T) ∧
    (∀ j, profile.Tinv j=fun a => max 0 (Tinv a)) ∧
    (∀ j, profile.Tobs j=fun a => max 0 (Tobs a)) := by
  exact ⟨fun _ => le_max_right _ _,fun _ => le_max_left _ _,
    fun _ => le_max_right _ _,fun _ => le_max_right _ _,fun _ _ => le_max_right _ _,
    fun _ _ => le_max_right _ _,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_completed_profile_bounds
