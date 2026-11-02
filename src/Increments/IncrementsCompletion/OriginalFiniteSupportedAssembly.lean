import IncrementsCompletion.RawFiniteMeanAllOrders
import IncrementsCompletion.FiniteMeanFinalDomain
import Repair.AuxBridgeNovOpenGermTransport
import Repair.FullIncrementNovSupportConclusion

/-!
# Same-U original-data assembly from the actual finite mean tensor

The finite iteration supplies one actual native tensor K and its exact finite
residual E = physicalMean(K) - Data.H.  The raw geometric construction supplies
the actual primary/secondary profiles for K.  This module combines those
already constructed objects, derives the final mean estimate, and returns the
joint conclusion for Data.F and Data.H with the original labelled supports.

Every order uses the same K, the same secondary choice, and the same literal
finite displacement.  The original sampling domains need not be compact.
This is an internal assembly theorem: it does not assert that the unresolved
original finite-budget geometric suppliers have been manufactured.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge
universe uM uTr uP uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem incrementsCompletion_original_finite_supported_assembly
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Cmean : ℕ → ℝ) (hCM : ∀ j, 0 ≤ Cmean j)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k)
    (hTobs : ∀ j k, 0 ≤ Tobs j k) :
    ∃ Cmap Cmetric : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧ ∀
      (P : Type uP) [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      (Β : Type uΒ) (SubSecondary : Type uSubSecondary) [Fintype Β] [Fintype SubSecondary]
      (Data : IncrementsOriginalNativeData (m+1) d N M P)
      (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
        (fun p x => Data.F (p,x)))
      (hg : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
      (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
      (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
        ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
      (hCutoff : g.cutoff = Data.cutoff)
      (ell delta tau : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (G : Set (P × M)) (hG : IsOpen G)
      (hGR : G ⊆ incrementsOriginalParameterRegion Data)
      (hKG : Data.parameterSet ×ˢ (univ : Set M) ⊆ G)
      (coverG : ∀ z ∈ G, ∃ b, z.1 ∈ (Data.parameterChart b).source),
      let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
      let W := incrementsOriginalParameterRegion Data
      let F := fullIncrementNovOriginalSourceSlice Data
      let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
      let gG := round3Parameter_restrictPrimaryFamily F
        (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG
      ∀ (E : finiteTensorGermSpace Data.atlas Data.parameterChart S W (fun _ _ hy => hy.1)),
      (∀ z ∈ W, E.val.val z.1 z.2 =
        fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g input hActive (q+2) tau z.1 z.2-
          Data.H z.1 z.2) →
      (∀ j, finiteTensorGermSeminorm Data.atlas Data.parameterChart S W (fun _ _ hy => hy.1) ell j E ≤
        Cmean j*(tau/ell)^(q+1)) →
      ∀ (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
        Round3ParameterSecondaryChoice P M m),
      (∀ r a, Round3ParameterChartPreserves (choice r a).chart) →
      (∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := Tr) Data.atlas Data.parameterChart F hF gG input input
        (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary reserve (Bsec j) (Msec j) (Ccut j)
        (Tsec j) (Tinv j) (Tobs j) G Data.primaryDomain S ell delta tau 0 choice)) →
      let U := round3ParameterIncrementMap F hF gG input (q+2) tau delta choice
      Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart S G
        Data.F U Data.H q delta tau ell Cmap Cmetric ∧
      FullIncrementNovOriginalSupportConclusion Data.cutoff G U := by
  obtain ⟨Cmap,Cmetric,hCmap,hCmetric,hFinish⟩ :=
    incrementsCompletion_actual_all_orders_from_finite_mean.{uM,uTr,uP,0,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Cmean hCM Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs
  refine ⟨Cmap,Cmetric,hCmap,hCmetric,?_⟩
  intro P _ _ _ Β SubSecondary _ _ Data hd hs g hg hTarget hActive hCutoff
    ell delta tau htau htaul hell1 hdelt hdt input G hG hGR hKG coverG
    S W F hF gG E hE hMean choice hchoice hraw U
  have hgG : ∀ nu beta, Round3ParameterChartPreserves (gG.chart nu beta) :=
    fun nu beta z hz => hg nu beta z hz.1
  have hMeanG := incrementsCompletion_finite_physical_mean_final_domain Data hd hs g hg hTarget hActive
    input (q+2) ell delta tau htaul E hE G hG hGR hKG
  have hMeanFinal (j : ℕ) :
      paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (fun t x => delta^2 • (round3ParameterPrimaryMean F hF gG input (q+2) tau t x-Data.H t x)))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (fun t x => delta^2 • (round3ParameterPrimaryMean F hF gG input (q+2) tau t x-Data.H t x)))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤
        Cmean j*delta^2*(tau/ell)^(q+1) := by
    refine ⟨(hMeanG.2 j).1,?_⟩
    exact ((hMeanG.2 j).2.trans
      (mul_le_mul_of_nonneg_left (hMean j) (sq_nonneg delta))).trans_eq (by ring)
  have hInternal := hFinish P (Fin Data.primaryCount) Β SubSecondary Data.parameterCount
    Data.atlas Data.parameterChart hd.atlas_smooth hd.parameter_charts_smooth S (fun _ _ hy => hy.1)
    G hG coverG ell delta tau htau htaul hell1 hdelt hdt F hF gG hgG Data.primaryDomain input Data.H
    choice hchoice hraw hMeanG.1 hMeanFinal
  have hSupports := auxBridgeNov_original_supports_of_raw
    (Tr := Tr) (0+2*q+8) (0+q+4) 0 q Rsub Lprimary Rsecondary hq (by omega)
    reserve (Bsec 0) (Msec 0) (Ccut 0) hc (hBsec 0) (hMsec 0) (hCcut 0)
    (Tsec 0) (Tinv 0) (Tobs 0) (hTsec 0) (hTinv 0) Data.atlas Data.parameterChart
    F hF gG hgG input input G hG coverG Data.primaryDomain S ell delta tau 0 choice hchoice
    (Classical.choice (hraw 0))
  have hSupportConclusion := fullIncrementNov_original_support_decomposition F hF gG input
    (q+2) tau delta choice G hSupports
  have hCutoffG : gG.cutoff = Data.cutoff := hCutoff
  rw [hCutoffG] at hSupportConclusion
  refine ⟨?_,hSupportConclusion⟩
  exact auxBridgeNov_open_joint_increment_conclusion Data hd U G hGR q delta tau ell Cmap Cmetric hInternal

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_finite_supported_assembly
