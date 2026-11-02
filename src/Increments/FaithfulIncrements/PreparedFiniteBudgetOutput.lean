import FaithfulIncrements.GivenFiniteEnvelope
import IncrementsCompletion.SampleDataUniformOriginalOutput

/-!
# Actual same-object increment from only the current finite Given prefix

This is the final numerical readout of the existing actual construction.
The original datum is fixed.  Its high-order actual norms manufacture the
estimate profile; they are never entrance upper-budget assumptions.  The
ratio threshold is visibly truncated in all four primitive numerical
profiles at the finite order (q+1)*(q+4)+2.  Each current scale only pays
the original weighted Given prefix at that scale.

The preparation, actual finite-norm proof, and geometric budgets are
internal producer outputs, to be discharged by the original geometric
entrance.  The explicit local active-primary bound permits the repair
factory's count-independent bound; the fixed-data corollary may use the
finite given list and makes no claim across arbitrary decompositions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements
open CollarCompletion

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

private local instance faithfulPreparedSignedFinite (n : ℕ) :
    Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- A numerical entrance profile with no reads beyond its finite prefix. -/
def finitePrefixProfile (J : ℕ) (f : ℕ → ℝ) : ℕ → ℝ :=
  repairEntranceFiniteProfile J f (fun _ => 0)

theorem finitePrefixProfile_eq (J : ℕ) (f : ℕ → ℝ) (k : ℕ) (hk : k ≤ J) :
    finitePrefixProfile J f k = f k :=
  repairEntranceFiniteProfile_prefix J f _ k hk

theorem finitePrefixProfile_nonneg (J : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k, k ≤ J → 0 ≤ f k) :
    ∀ k, 0 ≤ finitePrefixProfile J f k :=
  repairEntranceFiniteProfile_nonneg J f _ hf (fun _ => le_rfl)

/-- The genuine finite signed packet has a positive lower transverse
reserve.  This is produced from its actual positive pieces, not assumed. -/
theorem actual_secondary_reserve
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta) :
    ∃ cT : ℝ, 0 < cT ∧
      ∀ r i (a : secondary.s r i), cT ≤ (secondary.piece r i a).cT := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(secondary.s r i)))
  let B := round3PreparedFiniteMaximum
    (fun a : A => ((secondary.piece a.1 a.2.1 a.2.2).cT)⁻¹)
  have hB : 0 ≤ B := round3PreparedFiniteMaximum_nonneg _
  refine ⟨(1+B)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro r i a
  have hp := (secondary.piece r i a).cT_pos
  have hle : ((secondary.piece r i a).cT)⁻¹ ≤ 1+B :=
    (round3PreparedFiniteMaximum_bound
      (fun b : A => ((secondary.piece b.1 b.2.1 b.2.2).cT)⁻¹)
      (⟨r,⟨i,a⟩⟩ : A)).trans (by linarith)
  simpa only [one_div, inv_inv] using
    (one_div_le_one_div_of_le (inv_pos.mpr hp) hle)

/-- Literal restriction of the already manufactured all-scale secondary
profiles to the current scale. -/
def actual_secondary_profiles_at_scale
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (profiles : IncrementsCompletionSecondaryPacketProfiles Data hd hs theta secondary)
    (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) :
    IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta secondary ell
      profiles.Tinv profiles.Kcut profiles.Tobs where
  positive := profiles.positive ell hell hell1
  cutoff := profiles.cutoff ell hell hell1

/-- Full original norms, supports, scales, and one U for every order.
The displayed threshold contains only finite primitive-prefix reads. -/
theorem prepared_finite_budget_output
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
    (secondaryProfiles : IncrementsCompletionSecondaryPacketProfiles Data hd hs theta secondary)
    (hSupport : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (L : ℕ) (hCount : ∀ z,
      (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k)
    (hMeta : ∀ k, 0 ≤ Meta k) (Rsub : ℕ)
    (prep : ∀ i, FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i)
    (q : ℕ) (hq : 1 ≤ q) (allowed : ℕ → ℝ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤) :
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
  obtain ⟨secondaryReserve,hSecondaryReserve,hMargin⟩ :=
    actual_secondary_reserve Data hd hs theta secondary
  obtain ⟨hTheta,hTheta1,C,hC,hActual⟩ :=
    incrementsCompletion_sample_data_uniform_original_output.{uM,uP,uB}
      (m := m) (d := d) (N := N) (M := M)
      rho hReserve.reserve_pos c L secondaryReserve hSecondaryReserve
      secondaryProfiles.Tinv secondaryProfiles.Kcut secondaryProfiles.Tobs
      secondaryProfiles.inverse_nonneg secondaryProfiles.cutoff_nonneg secondaryProfiles.observer_nonneg
      cT hcT Tinv Forward Meta hTinv hForward hMeta Rsub Lactive q hq Packet hPacket
  rw [hThreshold] at hTheta hTheta1 hActual
  refine ⟨hTheta,hTheta1,C,hC,?_⟩
  intro ell hell hell1 hPrefix tau delta hdelta hdt htaul hRatio
  have hGiven := actualGivenEnvelope_current_scale Data J allowed hFinite ell hell1 hPrefix
  exact hActual P Data hd hs hn hp hImm hLinear hDecomp hReserve hEll hPrimaryCount
    ell hell hell1 (fun j => (hGiven j).1) (fun j => (hGiven j).2)
    V0 hV0 hKV0 theta secondary hSupport hPart hCount hMargin
    (actual_secondary_profiles_at_scale Data hd hs theta secondary secondaryProfiles ell hell.le hell1)
    Β primaryHost g hPreserves hTarget hPhase hCutoff
    (fun i => incrementsCompletion_original_preparation_at_scale Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell hell.le hell1 i (prep i))
    tau delta hdelta hdt htaul hRatio

end GlobalEmbedding.Continuation.FaithfulIncrements
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.actual_secondary_reserve
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.prepared_finite_budget_output

