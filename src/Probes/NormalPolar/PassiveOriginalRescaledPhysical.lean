import NormalPolar.PassiveOriginalRescaledMean
import NormalPolar.PassiveOriginalGeometry
import NormalPolar.ActualProbeInitialSupplyPrimaryOriginal
import Probes.Round3ParameterPreparedPhysicalGeometry

/-! Actual physical geometry of the same reference family for every
contraction c >= 1/2. One fixed conditioned packet supplies the real native
preparation. Its unchanged primitive fields define the physical family;
no completed geometry record and no c-dependent primary choice is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P Sub : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IM" => 𝓘(ℝ,D)

theorem passiveOriginal_reference_rescaled_physical_geometry
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hi₀ : IncrementsOriginalSliceImmersionInputs seed)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀)
    (R : ℕ) (reference : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub R)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B) (Q : Fin B.count → Set Ep)
    (hSamples : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart
      seed.sourceNormDomain Q univ i)) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    let g := passiveOriginalReferencePrimary seed hd₀ hs₀ hn₀ base R reference
    let gp := passiveParameterPrimary (P := P) (0 : E₀) (fun p x => seed.F (p,x)) g
    let hF₀ := passiveOriginal_reference_base_smooth seed hd₀ hs₀ hAll base
    let hF := fun _ : P => hF₀
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
      ∀ (c : ℝ) (hc : 1/2 ≤ c),
        let hcz : c ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc)
        let DataC := passiveRescaledData Data c
        let gC := passiveRescaledPrimary (fun p x => Data.F (p,x)) hF gp c hcz
        let hFC := fun p : P => contMDiff_const_rescale (fun x => Data.F (p,x)) (hF p) c
        ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
          Nonempty (ActualOriginalPrimaryPhysicalGeometry
            (fun p x => DataC.F ((Data.parameterChart i.2).symm p,x))
            (fun p => hFC ((Data.parameterChart i.2).symm p))
            (round3ParameterNativePrimary (fun p x => DataC.F (p,x)) gC
              (Data.parameterChart i.2))) := by
  intro Data g gp hF₀ hF hd hs
  have hzero : (0 : E₀) ∈ seed.parameterSet := by rw [hAll]; trivial
  have hopen := hd₀.parameter_subset hzero
  let hn := passiveOriginalData_freeNormalConditions (0 : E₀) seed hd₀ hs₀ hn₀ hopen B Q hd hs
  have hi := passiveOriginalData_immersion (0 : E₀) seed B Q hi₀ hopen
  obtain ⟨Forward,Inverse,Meta,hFwd,hInv,hMeta,hProfiles,hPrep⟩ :=
    passiveOriginal_reference_rescaled_mean_preparation seed hd₀ hs₀ hn₀ hAll base hId R reference
      B hB Q hSamples hd hs hn
  intro c hc hcz DataC gC hFC i
  let hdC := passiveRescaledData_domains Data hd c
  let hsC := passiveRescaledData_smooth Data hs c
  let hnC := passiveRescaledData_free_normals Data hd hs hn c hcz
  have hphys := round3Parameter_prepared_native_physical_geometry DataC hdC hsC hnC rfl hFC gC
    (passiveRescaledData_immersion Data hd hs hi c hcz) 1 (reference.cT/4)
    (div_pos reference.cT_pos (by norm_num)) Inverse
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i
    (Classical.choice (hPrep c hc 1 (by norm_num) le_rfl i))
  simpa only [actualProbeInitialSupply_restrict_univ,DataC,passiveRescaledData] using hphys

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_rescaled_physical_geometry
