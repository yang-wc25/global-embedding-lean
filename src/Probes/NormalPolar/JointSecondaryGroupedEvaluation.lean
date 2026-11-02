import NormalPolar.JointMixedGroupedPrimary
import NormalPolar.JointSecondaryGroupedParameter
import NormalPolar.JointSecondaryGroupedVariableWave
import NormalPolar.ActualProbeInitialSupplyPrimary

/-! The complete grouped primary keeps exactly the original common labels.
Every subordinate reconstructed amplitude is summed inside its original label
before the physical wave, mean or quadratic forcing is formed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)] {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Pspace" => Fin p → ℝ

variable
    (F : Ep → M → EuclideanSpace ℝ (Fin N)) (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Sub l → Ep → EuclideanSpace ℝ (Fin (m+1)) → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : EuclideanSpace ℝ (Fin (m+1))) → normalSpace (I := I) (F b) (c l s b x))
    (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) (Ep × EuclideanSpace ℝ (Fin (m+1))))

theorem jointGroupedCombinedPrimary_diagonal
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Ep → Fin p → ℝ) (z : Ep × M) :
    jointGroupedCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input (u z.1) z =
      ∑ l, (Real.cos (Sum.elim g.phase phase l z/tau) •
        jointGroupedCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false l z -
        Real.sin (Sum.elim g.phase phase l z/tau) •
        jointGroupedCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true l z) := by
  unfold jointGroupedCombinedPrimary
  apply Finset.sum_congr rfl
  intro l _
  cases l <;> simp only [jointGroupedCombinedAmplitude, Sum.elim_inl, Sum.elim_inr]

end GlobalEmbedding.Continuation

namespace GlobalEmbedding.Continuation
variable {E H M P U Label : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

theorem jointGrouped_native_coefficient_diagonal
    (imag : Bool) (phase : P × M → ℝ) (tau : ℝ)
    (R Q : U → P × M → EuclideanSpace ℝ (Fin N)) (u : P → U) (b : P) (x : M) :
    round4PrescribedNativeCoefficient (I := I) imag phase tau
      (fun z => R (u z.1) z) (fun z => Q (u z.1) z) (b,x) =
    round4PrescribedNativeCoefficient (I := I) imag phase tau (R (u b)) (Q (u b)) (b,x) := by
  cases imag <;> rfl


theorem jointGrouped_native_mean_diagonal {r : ℕ}
    (phase : Fin r → P × M → ℝ) (tau : ℝ)
    (R Q : U → Fin r → P × M → EuclideanSpace ℝ (Fin N))
    (u : P → U) (b : P) (x : M) :
    round4NativeOppositeMean (I := I) phase tau
      (fun l z => R (u z.1) l z) (fun l z => Q (u z.1) l z) b x =
    round4NativeOppositeMean (I := I) phase tau (R (u b)) (Q (u b)) b x := by
  unfold round4NativeOppositeMean
  congr 1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointGroupedCombinedPrimary_diagonal
#print axioms GlobalEmbedding.Continuation.jointGrouped_native_coefficient_diagonal

#print axioms GlobalEmbedding.Continuation.jointGrouped_native_mean_diagonal
