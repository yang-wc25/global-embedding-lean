import Probes.Round3PreparedParameterOriginalSignedGood
import Probes.Round3PreparedPrimaryPhaseLegality
import Probes.Round3PreparedHostGood

/-! The actual perturbed transverse reserve on a fixed signed carrier gives
the ORIGINAL physical signed covector, for an arbitrary parameter manifold.
There is no new-map phase-legality premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_parameter_phase_conditions_of_actual_good
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (hPrimary : ∀ nu z (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      GoodCovector (fun x => Data.F (z.1,x))
        (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) z.2
        (incrementsOriginalPhaseCovector Data nu z.1 z.2))
    (hSigned : ∀ (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) z,
      z ∈ incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 →
      GoodCovector (fun x => Data.F (z.1,x)) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Data r z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Data r (z.1,x)) z.2))) :
    IncrementsOriginalPhaseConditions Data hd hs := by
  refine ⟨hPrimary,?_,?_⟩
  · intro nu z hz
    exact (good_covector_smul_iff _ _ _ _ 2 (by norm_num)).mpr (hPrimary nu z hz)
  · intro nu mu hne sign z hz
    have hnu : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local nu hz.1,incrementsOriginalRelativeCutoffSupport_subset Data nu hz.1⟩
    have hmu : z ∈ Data.primaryDomain mu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local mu hz.2,incrementsOriginalRelativeCutoffSupport_subset Data mu hz.2⟩
    cases sign with
    | false =>
      let r : ActualSecondarySignedRecord (Fin Data.primaryCount) := ⟨((nu,mu),1),Or.inl hne⟩
      have hGood := hSigned r z hz
      have hPhase : round3PreparedPhysicalSignedPhase Data r =
          fun y => Data.phase nu y-Data.phase mu y := by
        funext y
        simp [r,round3PreparedPhysicalSignedPhase]
      rw [hPhase,actual_original_phase_sub_covector Data hd hs nu mu z.1 z.2 hnu hmu] at hGood
      have hNeg : (-1 : ℝ) • incrementsOriginalPhaseCovector Data mu z.1 z.2 =
          -incrementsOriginalPhaseCovector Data mu z.1 z.2 := by
        ext v
        simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
      simpa only [Bool.false_eq_true,ite_false,hNeg,sub_eq_add_neg] using hGood
    | true =>
      let r : ActualSecondarySignedRecord (Fin Data.primaryCount) := ⟨((nu,mu),0),Or.inl hne⟩
      have hGood := hSigned r z hz
      have hPhase : round3PreparedPhysicalSignedPhase Data r =
          fun y => Data.phase nu y+Data.phase mu y := by
        funext y
        simp [r,round3PreparedPhysicalSignedPhase]
      rw [hPhase,actual_original_phase_sum_covector Data hd hs nu mu z.1 z.2 hnu hmu] at hGood
      simpa only [ite_true,one_smul] using hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_phase_conditions_of_actual_good
