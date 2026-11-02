import OriginalIntegration.OriginalCommonFiniteIncrement

/-!
# Unconditional fixed-data original increments

The original qualitative fixed decomposition and buffered geometry are the
only inputs. The finite weighted input prefix is manufactured on internal
neighborhoods containing the original active carriers; callers need not
bound arbitrary inactive extensions on an unnecessarily large phase domain.
The public output retains every original Omega/Q, F/H, support and pairwise
intersection, with one actual U for all orders. The quantitative companion
continues to expose exactly which finite prefix the same solver consumes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars FaithfulIncrements FaithfulIntegration FaithfulRepair CollarCompletion

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The original fixed-data existence assertion, with no pre-made analytic
supplier and no finite or infinite Given-norm hypothesis. The finite
numerical prefix is proved admissible internally; the original output is
not weakened to the smaller internal work domains. -/
theorem original_buffered_fixed_data_increment
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (RSrc bSrc RPar bPar : ℝ)
    (gS : OriginalSourceNormBuffer Data.atlas Data.sourceNormDomain RSrc bSrc)
    (WParam : Fin Data.parameterCount → Set P)
    (gP : OriginalParameterNormBuffer Data.parameterChart Data.parameterNormDomain
      WParam Data.parameterSet RPar bPar)
    (TS TP Parameter Spatial : ℕ → ℝ)
    (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Ds Dp : ℕ) (hDs : Data.atlas.supportDegree ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree WParam i ≤ Dp)
    (hSTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.atlas.chart p).target,
      (Data.atlas.chart p).symm y ∈ Data.atlas.support i →
      ‖iteratedFDeriv ℝ j (Data.atlas.chart i ∘ (Data.atlas.chart p).symm) y‖ ≤ TS j)
    (hPTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.parameterChart p).target,
      (Data.parameterChart p).symm y ∈ WParam i →
      (Data.parameterChart p).symm y ∈ (Data.parameterChart i).source →
      ‖iteratedFDeriv ℝ j (Data.parameterChart i ∘ (Data.parameterChart p).symm) y‖ ≤ TP j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    : ∀ q : ℕ, 1 ≤ q → ∃ Theta : ℝ, 0 < Theta ∧ Theta ≤ 1 ∧
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ ell, 0 < ell → ell ≤ 1 →
      ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
        OriginalIncrementOutput Data q C ell tau delta := by
  letI : CompactSpace M := original_data_source_compact_of_source_radius Data hd RSrc gS.norm_radius
  obtain ⟨V,domain,hV,hKV,hVU,hVC,hOpen,hCompact,hClosure,hSupport,hFinite⟩ :=
    original_local_given_finite_neighborhoods Data hd hs hLinear Parameter Spatial
      hParameter hSpatial transition
  have hVold : V ⊆ Data.parameterOpen := subset_closure.trans hVU
  have hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu :=
    fun nu => subset_closure.trans ((hClosure nu).trans inter_subset_left)
  let L := localPrimaryData Data V domain
  let hdL := localPrimaryData_domain_conditions Data hd V domain hV hKV hOpen hSupport
  let hsL := localPrimaryData_smooth_inputs Data hs V domain hVold hDomain
  let hpL := localPrimaryData_phase_conditions Data hd hs hp V domain hVold hDomain hdL hsL
  let hnL := localPrimaryData_free_normal_conditions Data hd hs hn V domain hVold hDomain hdL hsL
  let hImmL := localPrimaryData_slice_immersion Data hImm V domain hVold
  let hLinearL := localPrimaryData_linear_smooth Data hLinear V domain hVold hDomain
  let hDecompL := localPrimaryData_decomposition Data hDecomp V domain hVold
  let hReserveL := localPrimaryData_reserve Data rho hReserve V domain hVold
  let hEllL := localPrimaryData_ellipticity Data c hEll V domain
  have hTransitionL : RepairOriginalTransitionBudgets L Parameter Spatial :=
    ⟨transition.parameter,transition.spatial⟩
  obtain ⟨BS,BP,cT,Mb,BInv,HGrid,hBS,hBP,hcT,hMb,hBInv,hHGrid,hAll⟩ :=
    original_buffered_common_numeric_increment L hdL hsL hpL hnL hImmL hLinearL hDecompL
      rho hReserveL c hEllL RSrc bSrc RPar bPar gS WParam gP TS TP Parameter Spatial
      hTS hTP hParameter hSpatial Ds Dp hDs hDp hSTrans hPTrans hTransitionL
  let allowed : ℕ → ℝ := fun j => (actualOriginalGivenInputProfile L j 1).toReal
  intro q hq
  obtain ⟨hTheta,hThetaOne,C,hC,hOutput⟩ := hAll q hq allowed
    (fun _ _ => ENNReal.toReal_nonneg)
  refine ⟨_,hTheta,hThetaOne,C,hC,?_⟩
  intro ell hell hellOne tau delta hdelta hdeltaTau htauEll hRatio
  have hGiven : OriginalFinitePrefixBudget L ((q+1)*(q+4)+2) allowed ell := by
    intro j hj
    have hle := given_profile_mono_scale L j ell 1 hellOne
    exact ⟨ne_top_of_le_ne_top (hFinite j 1) hle,
      ENNReal.toReal_mono (hFinite j 1) hle⟩
  exact localPrimaryData_original_output Data V domain hVold q C ell tau delta
    (hOutput ell hell hellOne hGiven tau delta hdelta hdeltaTau htauEll hRatio)

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_buffered_fixed_data_increment
