import Smoothing.ParameterRound2MeanGermPhysicalConclusion

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M Tr : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- The physical mean residual is the SAME native tensor and belongs to the
actual local-germ submodule. This is exact submodule algebra, with no extra
smoothness or residual budget premise. -/
theorem parameterRound2_actual_germ_physical_mean_mem
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (q : ℕ)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W)
    (epsilon delta : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}) :
    (fun t x => delta^2 •
      (incrementsGlobalPrimaryMean F hF g K.val.val (q+2) (epsilon*ell) t x-H.val t x)) ∈
      parameterRound2_originalTensorGermSpace A B S W := by
  let T : parameterRound2_originalTensorGermSpace A B S W :=
    ⟨incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell),hsm epsilon he he1 K⟩
  let E : parameterRound2_originalTensorGermSpace A B S W := delta^2 • (K.val+T-H)
  have hE : E.val = (fun t x => delta^2 •
      (incrementsGlobalPrimaryMean F hF g K.val.val (q+2) (epsilon*ell) t x-H.val t x)) := by
    funext t x
    change delta^2 • (K.val.val t x+
      (incrementsGlobalPrimaryMean F hF g K.val.val (q+2) (epsilon*ell) t x-K.val.val t x)-H.val t x) = _
    congr 1
    abel
  rw [← hE]
  exact E.property

#print axioms parameterRound2_actual_germ_physical_mean_mem
end GlobalEmbedding.Continuation
