import NormalPolar.PassiveOriginalRescaledSupply
import NormalPolar.PassiveOriginalRescaledInputProfiles
import NormalPolar.PassiveRawCounts
import Smoothing.Round3RepairOriginalMeanNumbers

/-! The actual same-reference raw supplier with its numerical profile
explicitly fixed before c and ell. The existing original mean numbers give
the radius, reserve and every sign proof. Only the bookkeeping count is
enlarged to the full original background-plus-probe label count. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N r : ℕ} {M P Sub : Type*}
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

theorem passiveOriginal_reference_rescaled_raw_numbers
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hp₀ : IncrementsOriginalPhaseConditions seed hd₀ hs₀)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hi₀ : IncrementsOriginalSliceImmersionInputs seed)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀)
    (R : ℕ) (reference : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub R)
    (cF rho : ℝ) (he₀ : IncrementsOriginalCoordinateEllipticityInputs seed cF)
    (hl₀ : IncrementsOriginalLinearSmoothInputs seed)
    (hc₀ : IncrementsOriginalQualitativeDecompositionInputs seed)
    (hr₀ : IncrementsOriginalDecompositionReserveInputs seed rho)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSamples : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart
      seed.sourceNormDomain Q univ i))
    (SeedPacket : ℕ → ℝ)
    (hSeed : ∀ n ell, 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile seed n ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile seed n ell).toReal ≤ SeedPacket n)
    (q : ℕ) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    let g := passiveOriginalReferencePrimary seed hd₀ hs₀ hn₀ base R reference
    let gp := passiveParameterPrimary (P := P) (0 : E₀) (fun p x => seed.F (p,x)) g
    let hF₀ := passiveOriginal_reference_base_smooth seed hd₀ hs₀ hAll base
    let hF := fun _ : P => hF₀
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
    ∃ Packet Forward Inverse Meta : ℕ → ℝ, ∃ hPacket : ∀ k, 0 ≤ Packet k,
      let numbers := round3RepairOriginalMeanNumbers m d N q R
        (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) (cF/4) (reference.cT/4)
        rho hr₀.reserve_pos Packet Forward Inverse Meta hPacket
      ∀ (c : ℝ) (hc : 1/2 ≤ c), c ≤ 1 →
        let hcz : c ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc)
        let DataC := passiveRescaledData Data c
        let gC := passiveRescaledPrimary (fun p x => Data.F (p,x)) hF gp c hcz
        let hFC := fun p : P => contMDiff_const_rescale (fun x => Data.F (p,x)) (hF p) c
        ∀ ell, 0 < ell → ell ≤ 1 →
        ∀ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S univ,
          H.val = Data.H →
          Round3ParameterCanonicalMeanRawReserveSupply (Tr := ℝ) Data.atlas Data.parameterChart
            S univ (parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart
              S univ hSamples (fun _ _ hy => hy.1) ell)
            H numbers.rho q numbers.Rsub numbers.Lprimary numbers.reserve
            numbers.Bnd numbers.Mg numbers.Dinput numbers.T
            (fun p x => DataC.F (p,x)) hFC gC Data.primaryDomain ell := by
  intro Data g gp hF₀ hF S hd hs
  have hzero : (0 : E₀) ∈ seed.parameterSet := by rw [hAll]; trivial
  have hopen := hd₀.parameter_subset hzero
  obtain ⟨ib,hib,hQb⟩ := hd₀.parameter_cover 0 hzero
  have hbzero : seed.parameterChart ib 0 = (0 : E₀) := Subsingleton.elim _ _
  have hbT : (0 : E₀) ∈ (seed.parameterChart ib).target :=
    hbzero ▸ (seed.parameterChart ib).map_source hib
  let hn := passiveOriginalData_freeNormalConditions (0 : E₀) seed hd₀ hs₀ hn₀ hopen B Q hd hs
  let hp := passiveOriginalData_phaseConditions (0 : E₀) seed hd₀ hs₀ hp₀ hopen B Q hd hs
  have hi := passiveOriginalData_immersion (0 : E₀) seed B Q hi₀ hopen
  have he := passiveOriginalData_ellipticity (0 : E₀) seed B Q cF he₀ hzero
  have hl := passiveOriginalData_linearSmooth (0 : E₀) seed B Q ib hl₀ hopen hbT
  have hdec := passiveOriginalData_decomposition (0 : E₀) seed B Q hc₀ hopen
  have hres := passiveOriginalData_reserve (0 : E₀) seed B Q rho hr₀ hopen hzero
  obtain ⟨Forward,Inverse,Meta,hFwd,hInv,hMeta,hProfiles,hPrep⟩ :=
    passiveOriginal_reference_rescaled_mean_preparation seed hd₀ hs₀ hn₀ hAll base hId R reference
      B hB Q hSamples hd hs hn
  obtain ⟨Packet,hPacket,hGiven⟩ := passiveOriginal_reference_rescaled_given_profiles seed hd₀ hs₀ hAll
    B hB hforward Q hQ hQT SeedPacket hSeed hd hs
  refine ⟨Packet,Forward,Inverse,Meta,hPacket,?_⟩
  intro numbers c hc hc1 hcz DataC gC hFC ell hell hell1 H hH
  let hdC := passiveRescaledData_domains Data hd c
  let hsC := passiveRescaledData_smooth Data hs c
  let hnC := passiveRescaledData_free_normals Data hd hs hn c hcz
  have hpC := passiveRescaledData_phase_conditions Data hd hs hp c hcz
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ c)]; exact hc1
  have hLin := actualOriginalGivenInputProfile_linear_le DataC 0 ell
  have hFin : incrementsOriginalInputProfileWithLinear DataC 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven c hcabs ell hell hell1 0).1 hLin
  have hML : (incrementsOriginalInputProfileWithLinear DataC 0 ell).toReal ≤ Packet 0 :=
    (ENNReal.toReal_mono (hGiven c hcabs ell hell hell1 0).1 hLin).trans
      (hGiven c hcabs ell hell hell1 0).2
  have hRaw := round3Parameter_actual_original_canonical_raw_reserve_supply DataC hdC hsC hnC hpC rfl hFC gC
    (passiveRescaledData_immersion Data hd hs hi c hcz) ell (cF/4) (reference.cT/4) hell hell1
    (passiveRescaledData_ellipticity Data cF he c hc) (div_pos reference.cT_pos (by norm_num))
    (passiveRescaledData_linear Data hl c) (passiveRescaledData_decomposition Data hdec c)
    rho (passiveRescaledData_reserve Data rho hres c) hSamples (Packet 0) hFin hML q R Data.primaryCount
    Packet Inverse
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
    hInv (fun _ => round3PreparedFiniteMaximum_nonneg _) (fun _ => round3PreparedFiniteMaximum_nonneg _)
    (fun n => (hGiven c hcabs ell hell hell1 n).1)
    (fun n => (hGiven c hcabs ell hell hell1 n).2)
    (fun i => Classical.choice (hPrep c hc ell hell.le hell1 i))
  have hRegion : incrementsOriginalParameterRegion DataC = (univ : Set (P × M)) := by
    change (univ : Set P) ×ˢ (univ : Set M) = univ
    exact univ_prod_univ
  dsimp only at hRaw
  rw [hRegion] at hRaw
  have supply := hRaw.2 H hH
  exact round3Parameter_canonical_supply_enlarge_counts Data.atlas Data.parameterChart S univ
    (parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart
      S univ hSamples (fun _ _ hy => hy.1) ell) H numbers.rho q R Data.primaryCount numbers.reserve
    numbers.Bnd numbers.Mg numbers.Dinput numbers.T (fun p x => DataC.F (p,x)) hFC gC
    Data.primaryDomain ell supply R (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) le_rfl
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_rescaled_raw_numbers
