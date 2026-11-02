import NormalPolar.JointSecondaryGroupedCommon
import NormalPolar.JointSecondaryGroupedVariableWave
import NormalPolar.ActualProbeInitialSupplyPrimary

/-! The complete grouped primary keeps exactly the original common labels.
Every subordinate reconstructed amplitude is summed inside its original label
before the physical wave, mean or quadratic forcing is formed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

/-- The literal common phase-array wave, before any quadratic cancellation. -/
def jointGroupedCombinedPrimary
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (z : Ep × M) : V :=
  let phi := Sum.elim g.phase phase
  let R := jointGroupedCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input (fun _ => u) false
  let Q := jointGroupedCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input (fun _ => u) true
  ∑ l, (Real.cos (phi l z/tau) • R l z - Real.sin (phi l z/tau) • Q l z)

omit [NormedSpace ℝ Ep] in
/-- The common array is exactly physical background plus the complete actual
probe, rather than just the leading trigonometric approximation. -/
theorem jointGroupedCombinedPrimary_eq
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (z : Ep × M) :
    jointGroupedCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u z =
      delta • incrementsGlobalPrimaryWave F hF g input backgroundLength tau z +
        jointGroupedPrescribedWave label F hF c vf phase tau probeLength a u z := by
  simp only [jointGroupedCombinedPrimary,Fintype.sum_sum_type,
    jointGroupedCombinedAmplitude,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    incrementsGlobalPrimaryWave,jointGroupedPrescribedWave,Finset.smul_sum,smul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro nu _
  rw [smul_comm (Real.cos _),smul_comm (Real.sin _)]


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGroupedCombinedPrimary_eq
