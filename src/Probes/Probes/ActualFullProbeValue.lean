import Probes.ActualFullProbeFirstStep

/-! Exact value parameter response of the same actual free-plus-original
homogeneous family. Both original reconstruction channels remain present. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

theorem actualFullProbe_value_response_sub_principal
    (label : (Fin r × Bool) ↪ Fin p) (delta tau : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) (i : Fin r) (sine : Bool) :
    fderiv ℝ (fun w ↦ actualFiniteProbeWithReconstruction label delta tau weight phase amplitude
      F hF c order k w x) u (Pi.single (label (i, sine)) 1) -
      (if sine then actualProbeSinColumn delta tau (weight i) (phase i) (amplitude i) x
        else actualProbeCosColumn delta tau (weight i) (phase i) (amplitude i) x) =
      ∑ l, actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c tau order
        (k l (label (i, sine))) x := by
  have hf := hasFDerivAt_actualFiniteProbeDisplacement label delta tau weight phase amplitude u x
  have hr := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ ↦
    hasFDerivAt_actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
      F hF c tau order (k l) O hO hA hB (hk l) x hx u
  have ht := hf.add hr
  change HasFDerivAt (fun w ↦ actualFiniteProbeWithReconstruction label delta tau weight phase amplitude
    F hF c order k w x) _ u at ht
  rw [ht.fderiv]
  simp only [add_apply, sum_apply, probeColumnMap_column]
  cases sine with
  | false =>
    have hc := actualFiniteProbeDisplacement_cos_response label delta tau weight phase amplitude u x i
    rw [hf.fderiv] at hc
    rw [hc]
    simp
  | true =>
    have hs := actualFiniteProbeDisplacement_sin_response label delta tau weight phase amplitude u x i
    rw [hf.fderiv] at hs
    rw [hs]
    simp

#print axioms actualFullProbe_value_response_sub_principal
end GlobalEmbedding.Offline
