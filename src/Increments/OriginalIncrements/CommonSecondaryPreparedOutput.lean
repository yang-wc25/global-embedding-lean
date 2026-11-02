import FaithfulIncrements.PreparedFiniteBudgetOutput
import OriginalIncrements.SecondaryNumericalProfiles

/-!
# Actual mean output with common secondary numerical inputs

The secondary reserve and all three secondary profiles are fixed numerical
inputs before the datum. The actual signed packet proves these bounds.
The mean and final same-U output consume exactly those numbers; this
endpoint performs no compact maximum or post-data reserve selection.
The geometric factory discharges these internal numerical fields.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion FaithfulIncrements

universe uM uP uB
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

/-- Full original norms, supports, scales, and one U for every order.
The displayed threshold contains only finite primitive-prefix reads. -/
theorem prepared_current_common_secondary_finite_budget_output
    (secondaryReserve : ℝ) (hSecondaryReserve : 0 < secondaryReserve)
    (SecondaryInverse SecondaryCutoff SecondaryObserver : ℕ → ℝ)
    (hSecondaryInverse : ∀ j, 0 ≤ SecondaryInverse j)
    (hSecondaryCutoff : ∀ j, 0 ≤ SecondaryCutoff j)
    (hSecondaryObserver : ∀ j, 0 ≤ SecondaryObserver j)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (Lactive : ℕ)
    (hPrimaryCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu =>
        z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (Β : Type uB) [Fintype Β] (primaryHost : Β → Fin Data.atlas.count)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m)
      (Λ := Fin Data.primaryCount) (Β := Β) (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (hPhase : ∀ nu, g.phase nu = Data.phase nu)
    (hCutoff : ∀ nu, g.cutoff nu = Data.cutoff nu)
    (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hMargin : ∀ r i (a : secondary.s r i), secondaryReserve ≤ (secondary.piece r i a).cT)
    (secondaryProfiles : ∀ ell, 0 ≤ ell → ell ≤ 1 →
      IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta secondary ell
        SecondaryInverse SecondaryCutoff SecondaryObserver)
    (hSupport : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (L : ℕ) (hCount : ∀ z,
      (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k)
    (hMeta : ∀ k, 0 ≤ Meta k) (Rsub : ℕ)
    (q : ℕ) (hq : 1 ≤ q) (allowed : ℕ → ℝ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤)
    (prep : ∀ ell, 0 < ell → ell ≤ 1 →
      (∀ n, n ≤ (q+1)*(q+4)+2 →
        (actualOriginalGivenInputProfile Data n ell).toReal ≤ allowed n) →
      ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
        (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i) :
    let J := (q+1)*(q+4)+2
    let P0 := finitePrefixProfile J allowed
    let F0 := finitePrefixProfile J Forward
    let M0 := finitePrefixProfile J Meta
    let I0 := finitePrefixProfile J Tinv
    let hP0 := finitePrefixProfile_nonneg J allowed hAllowed
    let hF0 := finitePrefixProfile_nonneg J Forward (fun k _ => hForward k)
    let Theta := finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos P0 F0 M0 I0 hP0 hF0
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ ell, 0 < ell → ell ≤ 1 →
    (∀ n, n ≤ J → (actualOriginalGivenInputProfile Data n ell).toReal ≤ allowed n) →
    ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion Data ∧
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ U G ∧
      FullIncrementNovOriginalSupportConclusion Data.cutoff G U ∧
      ∀ j, paperAtlasWeighted 0 j tau
        (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) ≠ ⊤ ∧
        (paperAtlasWeighted 0 j tau
          (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet)).toReal ≤ C j*delta*tau ∧
        paperAtlasWeighted 0 j tau
          (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
            (incrementsOriginalMetricError Data.F U Data.H delta))
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet) ≠ ⊤ ∧
        (paperAtlasWeighted 0 j tau
          (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
            (incrementsOriginalMetricError Data.F U Data.H delta))
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet)).toReal ≤
          C j*(delta*(tau/ell)^q+delta^3/tau) := by
  intro J P0 F0 M0 I0 hP0 hF0 Theta
  let Packet := actualGivenEnvelope Data J allowed
  have hPacket : ∀ k, 0 ≤ Packet k := actualGivenEnvelope_nonneg Data J allowed hAllowed
  have hThreshold :
      finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
        q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket hForward =
      Theta := by
    apply finiteOriginalMeanThreshold_prefix_congr
    · intro k hk
      exact (actualGivenEnvelope_prefix Data J allowed k hk).trans
        (finitePrefixProfile_eq J allowed k hk).symm
    · intro k hk
      exact (finitePrefixProfile_eq J Forward k hk).symm
    · intro k hk
      exact (finitePrefixProfile_eq J Meta k hk).symm
    · intro k hk
      exact (finitePrefixProfile_eq J Tinv k hk).symm
  obtain ⟨hTheta,hTheta1,C,hC,hActual⟩ :=
    incrementsCompletion_sample_data_uniform_original_output.{uM,uP,uB}
      (m := m) (d := d) (N := N) (M := M)
      rho hReserve.reserve_pos c L secondaryReserve hSecondaryReserve
      SecondaryInverse SecondaryCutoff SecondaryObserver
      hSecondaryInverse hSecondaryCutoff hSecondaryObserver
      cT hcT Tinv Forward Meta hTinv hForward hMeta Rsub Lactive q hq Packet hPacket
  rw [hThreshold] at hTheta hTheta1 hActual
  refine ⟨hTheta,hTheta1,C,hC,?_⟩
  intro ell hell hell1 hPrefix tau delta hdelta hdt htaul hRatio
  have hGiven := actualGivenEnvelope_current_scale Data J allowed hFinite ell hell1 hPrefix
  exact hActual P Data hd hs hn hp hImm hLinear hDecomp hReserve hEll hPrimaryCount
    ell hell hell1 (fun j => (hGiven j).1) (fun j => (hGiven j).2)
    V0 hV0 hKV0 theta secondary hSupport hPart hCount hMargin
    (secondaryProfiles ell hell.le hell1)
    Β primaryHost g hPreserves hTarget hPhase hCutoff
    (prep ell hell hell1 hPrefix)
    tau delta hdelta hdt htaul hRatio

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.prepared_current_common_secondary_finite_budget_output
