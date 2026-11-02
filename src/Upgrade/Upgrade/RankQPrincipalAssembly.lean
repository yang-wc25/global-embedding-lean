import GlobalEmbedding.Offline.CoincidenceDifferentialRank
import GlobalEmbedding.Offline.PairedValueCoincidenceRank

/-!
Internal finite-dimensional assembly used only to avoid repeatedly unfolding
the native symmetric-square quotient instances in the actual geometric proof.
The rank inequality and perturbation margin are the accepted consumers, not
new versions of them.
-/

noncomputable section
open Module
open scoped BigOperators
namespace GlobalEmbedding.Upgrade

/-- A purely algebraic packaging of the accepted rank inequality. This keeps
all native quotient norms out of the rank-only calculation. -/
theorem rankQPrincipalColumns_finrank
    {ι A C D : Type*} [Fintype ι]
    [AddCommGroup A] [Module ℝ A] [AddCommGroup C] [Module ℝ C]
    [AddCommGroup D] [Module ℝ D] [FiniteDimensional ℝ C]
    (c : ι → C) (T : A →ₗ[ℝ] C) (Q : C →ₗ[ℝ] D)
    (hT : Function.Injective T) (hQT : Q.comp T = 0) (a r : ℕ)
    (ha : finrank ℝ A = a)
    (hpacket : finrank ℝ (Submodule.span ℝ (Set.range (Q ∘ c))) = r) :
    a + r ≤ finrank ℝ ((Fintype.linearCombination ℝ c).coprod T).range := by
  let P := Fintype.linearCombination ℝ c
  have hQP : finrank ℝ (Q.comp P).range = r := by
    rw [LinearMap.range_comp, Fintype.range_linearCombination, Submodule.map_span,
      ← Set.range_comp]
    exact hpacket
  have hTJ : T.range ≤ (P.coprod T).range := by
    rintro _ ⟨w, rfl⟩
    exact ⟨(0,w), by simp⟩
  have hPJ : P.range ≤ (P.coprod T).range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨(p,0), by simp⟩
  have h := Offline.finrank_joint_range_ge_tangent_add_projected_parameter
    (P.coprod T) T P Q hT hTJ hPJ hQT
  rwa [ha, hQP] at h

end GlobalEmbedding.Upgrade
