import CollarCompletion.FiniteOpenMeanEstimates
import CollarCompletion.FiniteMeanNumerics

/-!
# Actual mean estimates from original primitive inputs on finite norm domains

The original target is inserted by `originalFiniteTarget`. For every pair
of finite iterates, the existing original positivity construction and raw
profile producer are run internally. Their analytic estimate proves smooth
membership and all-order finiteness of the same physical mean error. No
compact norm-domain assumption, raw supply, mean estimate, or mean closure
is requested at this entrance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation.CollarCompletion
open SourceCollarsBridge
universe uM uP uB
variable {m d N : ℕ} {M : Type uM} {P : Type uP} {Β : Type uB}
  [TopologicalSpace M] [TopologicalSpace P] [Fintype Β]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_finite_actual_mean_tensor
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (q Rsub : ℕ) (hq : 1 ≤ q) (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hPacket : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (prep : ∀ i, FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W := incrementsOriginalParameterRegion Data
    let hSO := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) (y) (hy : y ∈ S i) => hy.1
    let H := originalFiniteTarget Data hd hs hDecomp ell hell hGiven
    let p := finiteTensorGermSeminorm Data.atlas Data.parameterChart S W hSO ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
    let hPacket0 := fun j => ENNReal.toReal_nonneg.trans (hPacket j)
    let C := finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Data.primaryCount rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let Cdiff := finiteOriginalMeanDifferenceCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Data.primaryCount rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let epsilon0 := finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Data.primaryCount rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let hActive := active_slices_from_original_data Data hd hs g hPreserves hTarget
    0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
    ∃ hsm : actualFiniteMeanMembership Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q,
    let Top := actualFiniteMeanOperator Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q hsm
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let K := fun i : ℕ => (meanReserveStep (p 0) H radius (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ radius/2) ∧
    (∀ i ≤ q, ∀ s, p s (K i) ≤ parameterRound2_uniformMeanProfile Packet C (q+4) i s) ∧
    ∃ E : finiteTensorGermSpace Data.atlas Data.parameterChart S W hSO,
      E.val.val = (fun t x => fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g
        (K q).val.val hActive (q+2) (epsilon*ell) t x-Data.H t x) ∧
      ∀ j, p j E ≤ epsilon^(q+1)*finitePhysicalMeanCost Packet C Cdiff q j := by
  intro S W hSO H p radius hPacket0 C Cdiff epsilon0 hActive
  have hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_linear_le Data 0 ell)
  have hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ Packet 0 :=
    (ENNReal.toReal_mono (hGiven 0) (actualOriginalGivenInputProfile_linear_le Data 0 ell)).trans (hPacket 0)
  have estimates := original_finite_mean_estimates Data hd hs hn hp g hPreserves hTarget V0 hV0 hKV0
    hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve (Packet 0) hProfile hML
    q Rsub hq Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep
  have hradius : 0 < radius := estimates.1
  have he0 := parameterRound2_uniformMeanThreshold_pos Packet C radius hradius q (q+4)
  have hest := estimates.2.2
  obtain ⟨hsm,hsize,hdiff⟩ := hest
  refine ⟨he0.1,he0.2,hsm,?_⟩
  intro Top epsilon he he0lt K
  have hH : ∀ s, p s H ≤ Packet s :=
    originalFiniteTarget_budget Data hd hs hDecomp ell hell hGiven Packet hPacket
  exact finite_actual_mean_iterate_tensor Packet C Cdiff radius hradius q
    Data.atlas Data.parameterChart S W hSO ell hell H (fun p x => Data.F (p,x))
    g hActive hsm hH hsize hdiff epsilon he he0lt

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_finite_actual_mean_tensor
