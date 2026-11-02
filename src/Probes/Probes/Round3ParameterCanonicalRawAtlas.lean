import Probes.Round3ParameterCanonicalFinalRaw
import Probes.Round3ParameterSecondaryCommonRawAtlas

/-! One whole-parameter primary supply and one coherent physical secondary
choice produce all orders of the actual final raw atlas at the SAME tensor.
The final input is arbitrary within the original reserve, so the independent
canonical finite mean iteration can be substituted without a circular bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_canonical_all_order_raw_atlas
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q Rsub Lprimary Rsecondary : ℕ) (ell rho reserve : ℝ)
    (S : (Fin Data.atlas.count × Fin Data.parameterCount) → Set (Fin (m+1+d) → ℝ))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S univ))
    (H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S univ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput T : ℕ → ℝ)
    (primary : Fin Data.primaryCount → Set (P × M))
    (supply : Round3ParameterCanonicalMeanRawReserveSupply (Tr := ℝ) Data.atlas Data.parameterChart
      S univ p H rho q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell)
    (Input Bsec Msec Ccut Tinv Tobs : ℕ → ℝ)
    (hBsec : ∀ j, Bnd (actualSecondarySolveOrder q j)
      (Input (actualSecondarySolveOrder q j+(q+4))) ≤ Bsec j)
    (hMsec : ∀ j, Mg (actualSecondarySolveOrder q j) ≤ Msec j)
    (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
      Round3ParameterSecondaryChoice P M m)
    (family : ∀ ip : Fin Data.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F
          (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) (Data.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Data.parameterChart ip) (univ : Set (P × M)))
        (round3ParameterNativeDomain (Data.parameterChart ip) (univ : Set (P × M)))
        Msec Ccut Tinv Tobs Rsecondary
        (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip)))
    (hChoice : ∀ ip, (family ip).choice = round3ParameterNativeChoices choice (Data.parameterChart ip))
    (K : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S univ)
    (hK : p 0 (K-H) < rho) (hInput : ∀ j, p j K ≤ Input j)
    (epsilon delta : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    ∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart F hF
      (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) K.val K.val
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary reserve (Bsec j) (Msec j) (Ccut j)
      T Tinv Tobs univ primary S ell delta (epsilon*ell) 0 choice) := by
  intro j
  obtain ⟨raw⟩ := round3Parameter_canonical_final_raw Data.atlas Data.parameterChart S univ p H rho
    q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell supply epsilon he he1
    (actualSecondarySolveOrder q j) (Input (actualSecondarySolveOrder q j+(q+4)))
    (Bsec j) (Msec j) (hBsec j) (hMsec j) K hK (hInput _)
  have hAtlas := round3Parameter_secondary_common_raw_atlas Data hd F hF
    (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) q ell univ
    Msec Ccut Tinv Tobs Rsecondary S choice family hChoice K.val K.val
    (actualSecondarySolveOrder q j+(q+4)) j Rsub Lprimary reserve (Bsec j) T primary delta
    (epsilon*ell) 0 raw
  have hn : actualSecondarySolveOrder q j+(q+4) = j+2*q+8 := by
    unfold actualSecondarySolveOrder
    omega
  rw [hn] at hAtlas
  simpa only [actualSecondarySolveOrder] using hAtlas

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_canonical_all_order_raw_atlas
