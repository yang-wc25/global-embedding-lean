import Probes.ActualSecondaryFiniteTensorIdentity
import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-! Exact binding of the original global U1 to the actual primary expansion
used by the physical quadratic forcing and finite metric identity. The original
subordinate cutoff remains inside the free datum; the expansion cutoff is one.
The amplitudes are the same original supported fullZ extensions, scaled by delta.
No replacement wave or coefficient is supplied. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actual_original_primary_wave_physical_binding
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau delta : ℝ) (kappa : X → Ep × M) :
    actualPrimaryJointWave
      (fun ν b x => g.phase ν (kappa (b,x))) tau (fun _ _ _ _ => 1)
      (fun ν b β x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true ν β (kappa (b,x)))
      (fun ν b β x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false ν β (kappa (b,x))) =
      fun z => delta • incrementsGlobalPrimaryWave F hF g input length tau (kappa z) := by
  funext z
  unfold actualPrimaryJointWave incrementsPrimaryWave
  simp only [one_smul]
  have hm (ν : Λ) (β : Β) := congrFun (increments_primary_real_mode_eq
    (fun x => g.phase ν (kappa (z.1,x))) tau
    (fun x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true ν β (kappa (z.1,x)))
    (fun x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false ν β (kappa (z.1,x)))) z.2
  simp_rw [hm]
  simp only [incrementsGlobalPrimaryWave,incrementsGlobalPrimaryAmplitude,
    Finset.smul_sum,Finset.sum_sub_distrib,smul_sub,smul_smul,mul_comm]

/-- The same literal binding also permits a nontrivial observation parameter chart. -/
theorem actual_original_primary_wave_parameter_binding
    {Eq : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau delta : ℝ) (kappa : Eq × D → Ep × M) :
    actualPrimaryJointWave
      (fun ν b x => g.phase ν (kappa (b,x))) tau (fun _ _ _ _ => 1)
      (fun ν b β x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true ν β (kappa (b,x)))
      (fun ν b β x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false ν β (kappa (b,x))) =
      fun z => delta • incrementsGlobalPrimaryWave F hF g input length tau (kappa z) := by
  funext z
  unfold actualPrimaryJointWave incrementsPrimaryWave
  simp only [one_smul]
  have hm (ν : Λ) (β : Β) := congrFun (increments_primary_real_mode_eq
    (fun x => g.phase ν (kappa (z.1,x))) tau
    (fun x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true ν β (kappa (z.1,x)))
    (fun x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false ν β (kappa (z.1,x)))) z.2
  simp_rw [hm]
  simp only [incrementsGlobalPrimaryWave,incrementsGlobalPrimaryAmplitude,
    Finset.smul_sum,Finset.sum_sub_distrib,smul_sub,smul_smul,mul_comm]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_primary_wave_physical_binding

#print axioms GlobalEmbedding.Continuation.actual_original_primary_wave_parameter_binding
