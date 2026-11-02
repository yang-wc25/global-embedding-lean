import Initialization.Assembly.FullCore

/-!
# Frequencies meet the actual entrance and an arbitrary extra scale bound

The entrance epsilon and error constant are fixed first. We then choose
K large enough and T/K large enough to make the literal initialization
error C (K⁻¹ + K/T) strictly smaller than epsilon, while retaining any
additional lower bound on T required by the final small-image scaling.
-/

noncomputable section
namespace GlobalEmbedding.Continuation.RepairClosure

theorem canonical_frequencies_enter
    (K0 R0 C epsilon lowerT : ℝ) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∃ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
      K0 ≤ K ∧ R0*K ≤ T ∧ lowerT < T ∧
      C * (K⁻¹ + K/T) < epsilon := by
  obtain ⟨K,hKlarge⟩ := exists_gt (max 1 (max K0 (4*C/epsilon)))
  have hK : 1 ≤ K := (le_max_left _ _).trans hKlarge.le
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : K0 ≤ K :=
    ((le_max_left K0 (4*C/epsilon)).trans (le_max_right _ _)).trans hKlarge.le
  have hKerror : 4*C/epsilon < K :=
    ((le_max_right K0 (4*C/epsilon)).trans (le_max_right _ _)).trans_lt hKlarge
  obtain ⟨T,hTlarge⟩ := exists_gt (max K (max (R0*K) (max lowerT (4*C*K/epsilon))))
  have hKT : K ≤ T := (le_max_left _ _).trans hTlarge.le
  have hTpos : 0 < T := hKpos.trans_le hKT
  have hR0 : R0*K ≤ T :=
    ((le_max_left (R0*K) (max lowerT (4*C*K/epsilon))).trans
      (le_max_right _ _)).trans hTlarge.le
  have hLower : lowerT < T :=
    (((le_max_left lowerT (4*C*K/epsilon)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans_lt hTlarge
  have hTerror : 4*C*K/epsilon < T :=
    (((le_max_right lowerT (4*C*K/epsilon)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans_lt hTlarge
  have hFirst : C/K < epsilon/4 := (div_lt_iff₀ hKpos).2 (by
    have h := (div_lt_iff₀ hepsilon).1 hKerror
    nlinarith)
  have hSecond : C*K/T < epsilon/4 := (div_lt_iff₀ hTpos).2 (by
    have h := (div_lt_iff₀ hepsilon).1 hTerror
    nlinarith)
  refine ⟨K,T,hK,hKT,hK0,hR0,hLower,?_⟩
  calc
    C * (K⁻¹ + K/T) = C/K + C*K/T := by ring
    _ < epsilon/4 + epsilon/4 := add_lt_add hFirst hSecond
    _ < epsilon := by linarith

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.canonical_frequencies_enter
