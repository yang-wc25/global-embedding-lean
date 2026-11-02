import Probes.Round3PreparedFiniteAssembly
import Probes.ActualSecondaryRawGermStatement
import Smoothing.ParameterRound2IdentityCostPrefix

/-!
# The numerical geometry profile of the actual secondary family

The finite maximum is the existing physical factory's exact choice. Its
jth value reads the original core budget at j+q+4, inverse-coordinate jets
through j+q+6, and the observer first jet. No derivative profile is selected
by a new compactness argument. The per-piece transverse reserves remain
actual reference geometry inputs.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped Classical
namespace GlobalEmbedding.Continuation

def round4ParameterSecondaryGeometryProfile {I : Type*} [Fintype I]
    (m d N q : ℕ) (reserve : I → ℝ) (InputBudget Tinv Tobs : ℕ → ℝ)
    (c : ℝ) (j : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun a =>
    round3PreparedGeometryCost m d N Tinv (reserve a) (1+Tobs 1)
      (actualSecondarySolveOrder q j) (j+1)
      (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c)

theorem round4ParameterSecondaryGeometryProfile_nonneg {I : Type*} [Fintype I]
    (m d N q : ℕ) (reserve : I → ℝ) (InputBudget Tinv Tobs : ℕ → ℝ)
    (c : ℝ) (j : ℕ) :
    0 ≤ round4ParameterSecondaryGeometryProfile m d N q reserve InputBudget Tinv Tobs c j :=
  round3PreparedFiniteMaximum_nonneg _

theorem round4ParameterSecondaryGeometryProfile_prefix {I : Type*} [Fintype I]
    (m d N q : ℕ) (reserve : I → ℝ)
    (InputBudget Tinv Tobs InputBudget' Tinv' Tobs' : ℕ → ℝ)
    (c : ℝ) (j : ℕ)
    (hInput : InputBudget (j+q+4) = InputBudget' (j+q+4))
    (hInv : ∀ k, k ≤ j+q+6 → Tinv k = Tinv' k)
    (hObs : Tobs 1 = Tobs' 1) :
    round4ParameterSecondaryGeometryProfile m d N q reserve InputBudget Tinv Tobs c j =
    round4ParameterSecondaryGeometryProfile m d N q reserve InputBudget' Tinv' Tobs' c j := by
  unfold round4ParameterSecondaryGeometryProfile
  congr 1
  funext a
  have hmax : max (actualSecondarySolveOrder q j) (j+1) = j+q+4 := by
    unfold actualSecondarySolveOrder
    omega
  simp only [round3PreparedGeometryCost,hmax,hInput,hObs]
  exact actualAdaptedUniformGeometryCost_prefix_congr m N (j+q+4) Tinv Tinv' c
    (reserve a) (1+Tobs' 1) _ _ (fun k hk => hInv k (by omega))

#print axioms round4ParameterSecondaryGeometryProfile_prefix
end GlobalEmbedding.Continuation
