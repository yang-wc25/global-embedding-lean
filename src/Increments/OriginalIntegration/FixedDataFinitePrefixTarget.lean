import OriginalIntegration.FinitePositiveFiniteEntranceStatement
import OriginalIntegration.FixedDataIncrementTarget
import OriginalIntegration.OriginalCommonFiniteIncrement
import OriginalIncrements.CommonThresholdPrefixes

/-!
# Exact finite-prefix companion of the fixed-decomposition source target

The original input profile in the independent statement is definitionally
the complete actual Given profile. The constructed low constants remain
after the fixed original Data and before q and allowed. The exact common
threshold formula is displayed, together with its true finite-prefix
invariance; no existential constant function can hide further dependence.

This proves the fixed-phase finite-entrance companion. It does not move
chosen inverse margins before arbitrary varying qualitative phases, nor
change a canonical challenge, locked target or acceptance count.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Paper
open GlobalEmbedding.Continuation GlobalEmbedding.Continuation.OriginalIntegration
open GlobalEmbedding.Continuation.OriginalIncrements GlobalEmbedding.Continuation.FaithfulCollars

section Profile
variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- All original coordinate terms, including total phase and transition
differentials, agree exactly with the implementation's actual profile. -/
theorem finite_positive_given_profile_eq_actual
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) :
    finitePositiveGivenInputProfile Data j ell = actualOriginalGivenInputProfile Data j ell := rfl

/-- Genuine finiteness is proved before any conversion to a real norm. -/
theorem finite_positive_given_prefix_iff
    (Data : IncrementsOriginalNativeData n d N M P)
    (J : ℕ) (allowed : ℕ → ℝ) (hAllowed : ∀ j, j ≤ J → 0 ≤ allowed j) (ell : ℝ) :
    FinitePositiveGivenPrefix Data J allowed ell ↔ OriginalFinitePrefixBudget Data J allowed ell := by
  constructor
  · intro h j hj
    have hb := h j hj
    rw [finite_positive_given_profile_eq_actual] at hb
    refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb,?_⟩
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (hAllowed j hj))
  · intro h j hj
    rw [finite_positive_given_profile_eq_actual]
    exact (ENNReal.ofReal_toReal (h j hj).1).symm.le.trans
      (ENNReal.ofReal_le_ofReal (h j hj).2)

end Profile

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- Fixed actual decomposition, then constructed low geometry, then q and
the finite input budget, then all scales and one U at every order. The
right-hand threshold formula and its prefix certificate are both literal. -/
theorem finite_positive_increments_fixed_data_finite_prefix
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
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    ∃ (BS BP : ℕ → ℝ) (cT Mb BInv HGrid : ℝ),
      (∀ j, 0 ≤ BS j) ∧ (∀ j, 0 ≤ BP j) ∧
      0 < cT ∧ 0 < Mb ∧ 0 < BInv ∧ 0 < HGrid ∧
      ∀ (q : ℕ), 1 ≤ q → ∀ (allowed : ℕ → ℝ)
        (hAllowed : ∀ j, j ≤ (q+1)*(q+4)+2 → 0 ≤ allowed j),
      let J := (q+1)*(q+4)+2
      let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)
      let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
        q Rsub (originalPrimaryInteractionDegree Data+1) rho c cT Mb BInv HGrid hReserve.reserve_pos
        BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
      FinitePositiveIncrementFiniteEntrance Data q J allowed Theta ∧
        ∀ (allowed' : ℕ → ℝ) (hAllowed' : ∀ j, j ≤ J → 0 ≤ allowed' j),
          (∀ j, j ≤ J → allowed j = allowed' j) →
          Theta = commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
            q Rsub (originalPrimaryInteractionDegree Data+1) rho c cT Mb BInv HGrid hReserve.reserve_pos
            BS TS BP TP Parameter Spatial allowed' Ds Dp hAllowed' := by
  obtain ⟨BS,BP,cT,Mb,BInv,HGrid,hBS,hBP,hcT,hMb,hBInv,hHGrid,hRun⟩ :=
    original_buffered_common_numeric_increment Data hd hs hp hn hImm hLinear hDecomp
      rho hReserve c hEll RSrc bSrc RPar bPar gS WParam gP TS TP Parameter Spatial
      hTS hTP hParameter hSpatial Ds Dp hDs hDp hSTrans hPTrans transition
  refine ⟨BS,BP,cT,Mb,BInv,HGrid,hBS,hBP,hcT,hMb,hBInv,hHGrid,?_⟩
  intro q hq allowed hAllowed
  constructor
  · obtain ⟨hTheta,hThetaOne,C,hC,hOutput⟩ := hRun q hq allowed hAllowed
    refine ⟨hTheta,hThetaOne,C,hC,?_⟩
    intro ell hell hellOne hGiven tau delta hdelta hdeltaTau htauEll hRatio
    exact original_increment_output_to_paper Data q C ell tau delta
      (hOutput ell hell hellOne
        ((finite_positive_given_prefix_iff Data _ allowed hAllowed ell).mp hGiven)
        tau delta hdelta hdeltaTau htauEll hRatio)
  · intro allowed' hAllowed' hPrefix
    exact commonFiniteThreshold_prefix_congr
      q (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D))
      (originalPrimaryInteractionDegree Data+1) rho c cT Mb BInv HGrid hReserve.reserve_pos
      BS BS TS TS BP BP TP TP Parameter Parameter Spatial Spatial allowed allowed' Ds Dp
      hAllowed hAllowed' (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hPrefix

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.finite_positive_given_profile_eq_actual
#print axioms GlobalEmbedding.Paper.finite_positive_given_prefix_iff
#print axioms GlobalEmbedding.Paper.finite_positive_increments_fixed_data_finite_prefix
