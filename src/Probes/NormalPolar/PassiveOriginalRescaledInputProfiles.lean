import NormalPolar.PassiveOriginalGivenProfile
import NormalPolar.PassiveRescaledGiven

/-! One nonnegative complete input budget for the actual original compact
parameter extension and every reference contraction. The seed contribution
and the actual new parameter-transition cost are fixed before both c and
ell; no output estimate is supplied as input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem passiveOriginal_reference_rescaled_given_profiles
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hAll : seed.parameterSet = univ)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (SeedPacket : ℕ → ℝ)
    (hSeed : ∀ n ell, 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile seed n ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile seed n ell).toReal ≤ SeedPacket n) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
    ∃ Packet : ℕ → ℝ, (∀ n, 0 ≤ Packet n) ∧
      ∀ c : ℝ, |c| ≤ 1 → ∀ ell, 0 < ell → ell ≤ 1 → ∀ n,
        actualOriginalGivenInputProfile (passiveRescaledData Data c) n ell ≠ ⊤ ∧
        (actualOriginalGivenInputProfile (passiveRescaledData Data c) n ell).toReal ≤ Packet n := by
  intro Data hd hs
  have hzero : (0 : E₀) ∈ seed.parameterSet := by rw [hAll]; trivial
  obtain ⟨ib,hib,hQb⟩ := hd₀.parameter_cover 0 hzero
  have hbzero : seed.parameterChart ib 0 = (0 : E₀) := Subsingleton.elim _ _
  have hbT : (0 : E₀) ∈ (seed.parameterChart ib).target :=
    hbzero ▸ (seed.parameterChart ib).map_source hib
  have hbQ : (0 : E₀) ∈ seed.parameterNormDomain ib := hbzero ▸ hQb
  obtain ⟨C,hC,hCost⟩ := passiveOriginal_given_profile_uniform_cost (0 : E₀) seed B Q hd hd₀ hs₀
    ib hbT hbQ hzero hib hB hforward hQ hQT
  let Packet : ℕ → ℝ := fun n => SeedPacket n+C n
  have hPacket (n) : 0 ≤ Packet n :=
    add_nonneg (ENNReal.toReal_nonneg.trans (hSeed n 1 (by norm_num) le_rfl).2) (hC n)
  refine ⟨Packet,hPacket,?_⟩
  intro c hc ell hell hell1 n
  have hBaseGiven := (hCost n ell hell1 (hSeed n ell hell hell1).1).1
  have hBaseBound : (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n :=
    ((hCost n ell hell1 (hSeed n ell hell hell1).1).2).trans
      (add_le_add (hSeed n ell hell hell1).2 le_rfl)
  have hScaled := passiveRescaledData_given_bound Data hd hs rfl c hc n ell hell hBaseGiven
  exact ⟨hScaled.1,hScaled.2.trans hBaseBound⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_rescaled_given_profiles
