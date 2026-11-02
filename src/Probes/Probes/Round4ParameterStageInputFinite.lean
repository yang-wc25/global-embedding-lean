import Probes.Round4ParameterCarrierMeanCosts
import Probes.Round4ParameterRepairFinitePrefix
import Smoothing.Round4SpatialReferenceNormalProfile
import Smoothing.Round4ClosedPairFiniteGeometry

/-!
# Finite dependence of the actual smoothed-stage input budget

The displayed maximum is the actual Packet used by the canonical mean:
the same smoothed map, smoothed target, fixed given data and newly
constructed normal. Its dependence is through finite raw reference jets.
Composing this with the carrier mean gives the explicit order
j+(q+2)*(q+4)+4 for the selected entrance and residual numbers. The
construction of uniform reference chart/template budgets is not assumed
to follow merely from these numerical equalities.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def round4ParameterStageInputProfile (m d N : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (BS TS BP TP Inverse Forward Given reference : ℕ → ℝ) (Ds Dp q : ℕ)
    (budget normalF normalT : ℝ) (j : ℕ) : ℝ :=
  let C := round4PreparedPairConstant (m+1) d radius hradius BS TS BP TP Ds Dp j q
  max (C*budget) (max (C*budget+(j+1)*reference j)
    (max (Given j) (round4SpatialReferenceNormalProfile m d N radius hradius BS TS BP TP
      Inverse Forward Given Ds Dp q budget normalF normalT j)))

theorem round4ParameterStageInputProfile_prefix_congr
    (m d N : ℕ) (radius : ℝ) (hradius : 0 < radius) (Ds Dp q j : ℕ)
    (budget normalF normalT : ℝ)
    {BS TS BP TP Inverse Forward Given reference BS' TS' BP' TP' Inverse' Forward' Given' reference' : ℕ → ℝ}
    (hBS : ∀ k, k ≤ j+2 → BS k = BS' k) (hTS : ∀ k, k ≤ j+2 → TS k = TS' k)
    (hBP : ∀ k, k ≤ j+2 → BP k = BP' k) (hTP : ∀ k, k ≤ j+2 → TP k = TP' k)
    (hI : ∀ k, k ≤ j+2 → Inverse k = Inverse' k)
    (hF : ∀ k, k ≤ j+1 → Forward k = Forward' k)
    (hG : ∀ k, k ≤ j → Given k = Given' k) (hRef : reference j = reference' j) :
    round4ParameterStageInputProfile m d N radius hradius BS TS BP TP Inverse Forward Given reference
      Ds Dp q budget normalF normalT j =
    round4ParameterStageInputProfile m d N radius hradius BS' TS' BP' TP' Inverse' Forward' Given' reference'
      Ds Dp q budget normalF normalT j := by
  have hPair := round4PreparedPairConstant_congr_prefix (m+1) d radius hradius Ds Dp j q hBS hTS hBP hTP
  have hNormal := round4SpatialReferenceNormalProfile_congr_prefix m d N radius hradius Ds Dp q j
    budget normalF normalT hBS hTS hBP hTP hI hF hG
  unfold round4ParameterStageInputProfile
  rw [hPair,hNormal,hG j le_rfl,hRef]

universe uM uP uΛ uΒ
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round4Parameter_smoothed_carrier_mean_prefix_congr
    (radius : ℝ) (hradius : 0 < radius) (Ds Dp : ℕ)
    (BS TS BP TP Inverse Forward Given reference metricReference Meta : ℕ → ℝ)
    (BS' TS' BP' TP' Inverse' Forward' Given' reference' metricReference' Meta' : ℕ → ℝ)
    (budget normalF normalT rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ) (j : ℕ)
    (hBS : ∀ k, k ≤ j+(q+2)*(q+4)+4 → BS k = BS' k)
    (hTS : ∀ k, k ≤ j+(q+2)*(q+4)+4 → TS k = TS' k)
    (hBP : ∀ k, k ≤ j+(q+2)*(q+4)+4 → BP k = BP' k)
    (hTP : ∀ k, k ≤ j+(q+2)*(q+4)+4 → TP k = TP' k)
    (hI : ∀ k, k ≤ j+(q+2)*(q+4)+4 → Inverse k = Inverse' k)
    (hF : ∀ k, k ≤ j+(q+2)*(q+4)+4 → Forward k = Forward' k)
    (hG : ∀ k, k ≤ j+(q+2)*(q+4)+4 → Given k = Given' k)
    (hRef : ∀ k, k ≤ j+(q+2)*(q+4)+4 → reference k = reference' k)
    (hMetricRef : ∀ k, k ≤ j+(q+2)*(q+4)+4 → metricReference k = metricReference' k)
    (hMeta : ∀ k, k ≤ j+(q+2)*(q+4)+4 → Meta k = Meta' k) :
    let Packet := round4ParameterStageInputProfile m d N radius hradius BS TS BP TP
      Inverse Forward Given reference Ds Dp q budget normalF normalT
    let Packet' := round4ParameterStageInputProfile m d N radius hradius BS' TS' BP' TP'
      Inverse' Forward' Given' reference' Ds Dp q budget normalF normalT
    ∀ (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k),
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius BS TS BP TP Ds Dp q metricReference budget
    let B0' := round4ParameterRepairReferenceProfile (m+1) d N radius hradius BS' TS' BP' TP' Ds Dp q metricReference' budget
    let C := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket
    let C' := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) ∧
    round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0 q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket j =
    round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0' q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket' j := by
  intro Packet Packet' hPacket hPacket' B0 B0' C C'
  have hL : j+(q+1)*(q+4) ≤ j+(q+2)*(q+4)+2 := by
    simp only [Nat.add_mul,Nat.one_mul,Nat.two_mul]
    omega
  have hB0 (k) (hk : k ≤ j+(q+1)*(q+4)) : B0 k = B0' k := by
    have hPair := round4SpatialPairConstant_congr_prefix (m+1) d N radius hradius Ds Dp k q
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
    change _*budget+(k+1)*metricReference k = _*budget+(k+1)*metricReference' k
    rw [hPair,hMetricRef k (by omega)]
  have hPacketEq (k) (hk : k ≤ j+(q+2)*(q+4)+2) : Packet k = Packet' k :=
    round4ParameterStageInputProfile_prefix_congr m d N radius hradius Ds Dp q k
      budget normalF normalT
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
      (fun a ha => hI a (by omega)) (fun a ha => hF a (by omega))
      (fun a ha => hG a (by omega)) (hRef k (by omega))
  exact round4ParameterCarrierMeanCosts_prefix_congr B0 B0' rho q Rsub Lprimary hq reserve hc c cT
    Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket' j hB0 hPacketEq
    (fun k hk => hF k (by omega)) (fun k hk => hI k (by omega)) (fun k hk => hMeta k (by omega))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterStageInputProfile_prefix_congr
#print axioms GlobalEmbedding.Continuation.round4Parameter_smoothed_carrier_mean_prefix_congr
