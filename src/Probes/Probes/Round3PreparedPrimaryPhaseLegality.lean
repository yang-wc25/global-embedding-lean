import Probes.Round3PreparedHostGood
import Probes.ActualIncrementOriginalPrimitiveBinding
import Probes.ActualOriginalSignedPhaseGood
import Probes.ActualIncrementOriginalSignedPhaseJets

/-! Actual stable primary charts supply the original primary Good condition.
The doubled condition follows by its exact original nonzero rescaling. The
signed interaction consumer retains the literal original phase derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round3_prepared_primary_good_from_stable_cover
    {Β : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (ip : Fin Data.parameterCount) (hId : Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (b nu a)
      (fun z => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2)) (e nu a))
    (hCover : ∀ nu z, z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data →
      ∃ a, z ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source)
    (cT : Fin Data.primaryCount → Β → ℝ) (hcT : ∀ nu a, 0 < cT nu a)
    (hFrame : ∀ nu a z, z ∈ (b nu a).target → ∀ v : Tdata,
      cT nu a*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (fun x => Data.F (z.1,x))
        (hF z.1) (e nu a z.1).symm z.2 v‖^2) :
    ∀ nu z (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      GoodCovector (fun x => Data.F (z.1,x))
        (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) z.2
        (incrementsOriginalPhaseCovector Data nu z.1 z.2) := by
  intro nu z hz
  obtain ⟨a,ha⟩ := hCover nu z hz
  have hpsi := actual_original_phase_mdifferentiableAt Data hd hs nu z.1 z.2 hz
  have hGood := round3_prepared_host_good_of_reserve (Data.atlas.chart (host nu a)) (b nu a)
    (fun y => Data.phase nu ((Data.parameterChart ip).symm y.1,y.2)) (e nu a) (hdata nu a)
    (fun p x => Data.F (p,x)) hF (cT nu a) (hcT nu a) (hFrame nu a) z ha
    (by simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hpsi)
  dsimp only at hGood
  have hpId : (Data.parameterChart ip).symm z.1 = z.1 := by rw [hId]; rfl
  rw [hpId] at hGood
  exact hGood

theorem round3_prepared_original_phase_conditions_of_actual_good
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart i.2 = OpenPartialHomeomorph.refl Ep)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (hPrimary : ∀ nu z (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      GoodCovector (fun x => Data.F (z.1,x))
        (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) z.2
        (incrementsOriginalPhaseCovector Data nu z.1 z.2))
    (hSigned : ∀ (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) z,
      z ∈ incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 →
      GoodCovector (fun x => Data.F (z.1,x)) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (actualOriginalParameterSignedPhase Data i r.val z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => actualOriginalParameterSignedPhase Data i r.val (z.1,x)) z.2))) :
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
      have hPhase : actualOriginalParameterSignedPhase Data i r.val =
          fun y => Data.phase nu y-Data.phase mu y := by
        funext y
        simp [r,actualOriginalParameterSignedPhase,hId]
      rw [hPhase,actual_original_phase_sub_covector Data hd hs nu mu z.1 z.2 hnu hmu] at hGood
      have hNeg : (-1 : ℝ) • incrementsOriginalPhaseCovector Data mu z.1 z.2 =
          -incrementsOriginalPhaseCovector Data mu z.1 z.2 := by
        ext v
        simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
      simpa only [Bool.false_eq_true,ite_false,hNeg,sub_eq_add_neg] using hGood
    | true =>
      let r : ActualSecondarySignedRecord (Fin Data.primaryCount) := ⟨((nu,mu),0),Or.inl hne⟩
      have hGood := hSigned r z hz
      have hPhase : actualOriginalParameterSignedPhase Data i r.val =
          fun y => Data.phase nu y+Data.phase mu y := by
        funext y
        simp [r,actualOriginalParameterSignedPhase,hId]
      rw [hPhase,actual_original_phase_sum_covector Data hd hs nu mu z.1 z.2 hnu hmu] at hGood
      simpa only [ite_true,one_smul] using hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_good_from_stable_cover
#print axioms GlobalEmbedding.Continuation.round3_prepared_original_phase_conditions_of_actual_good
