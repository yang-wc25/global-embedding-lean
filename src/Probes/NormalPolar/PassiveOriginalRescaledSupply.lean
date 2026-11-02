import NormalPolar.PassiveOriginalRescaledMean
import NormalPolar.PassiveOriginalReferenceSupply
import NormalPolar.PassiveRescaledGiven
import NormalPolar.PassiveRescaledReserve

/-! One actual canonical mean/raw reserve supplier uniformly for every
reference contraction in [1/2,1]. The seed packet is selected once. Its
same whole-P primary fields and original samples are retained, with the
original geometry constants divided by four. All raw budget sequences
are selected before both c and ell. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
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

theorem passiveOriginal_reference_rescaled_canonical_supply
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
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
    ∃ Packet Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      ∀ (c : ℝ) (hc : 1/2 ≤ c), c ≤ 1 →
        let hcz : c ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc)
        let DataC := passiveRescaledData Data c
        let gC := passiveRescaledPrimary (fun p x => Data.F (p,x)) hF gp c hcz
        let hFC := fun p : P => contMDiff_const_rescale (fun x => Data.F (p,x)) (hF p) c
        ∀ ell, 0 < ell → ell ≤ 1 →
          Round3ParameterOriginalCanonicalRawOutput DataC hFC gC hSamples ell (cF/4) (reference.cT/4)
            rho (Packet 0) q R Data.primaryCount Packet Inverse
            (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
            (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) := by
  intro Data g gp hF₀ hF hd hs
  have hzero : (0 : E₀) ∈ seed.parameterSet := by rw [hAll]; trivial
  have hopen := hd₀.parameter_subset hzero
  obtain ⟨ib,hib,hQb⟩ := hd₀.parameter_cover 0 hzero
  have hbzero : seed.parameterChart ib 0 = (0 : E₀) := Subsingleton.elim _ _
  have hbT : (0 : E₀) ∈ (seed.parameterChart ib).target :=
    hbzero ▸ (seed.parameterChart ib).map_source hib
  have hbQ : (0 : E₀) ∈ seed.parameterNormDomain ib := hbzero ▸ hQb
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
  obtain ⟨C,hC,hCost⟩ := passiveOriginal_given_profile_uniform_cost (0 : E₀) seed B Q hd hd₀ hs₀
    ib hbT hbQ hzero hib hB hforward hQ hQT
  let Packet : ℕ → ℝ := fun n => SeedPacket n+C n
  refine ⟨Packet,Forward,Inverse,Meta,hFwd,hInv,hMeta,?_⟩
  intro c hc hc1 hcz DataC gC hFC ell hell hell1
  let hdC := passiveRescaledData_domains Data hd c
  let hsC := passiveRescaledData_smooth Data hs c
  let hnC := passiveRescaledData_free_normals Data hd hs hn c hcz
  have hpC := passiveRescaledData_phase_conditions Data hd hs hp c hcz
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ c)]; exact hc1
  have hBaseGiven (n) : actualOriginalGivenInputProfile Data n ell ≠ ⊤ :=
    (hCost n ell hell1 (hSeed n ell hell hell1).1).1
  have hBaseBound (n) : (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n :=
    ((hCost n ell hell1 (hSeed n ell hell hell1).1).2).trans
      (add_le_add (hSeed n ell hell hell1).2 le_rfl)
  have hGiven (n) : actualOriginalGivenInputProfile DataC n ell ≠ ⊤ :=
    (passiveRescaledData_given_bound Data hd hs rfl c hcabs n ell hell (hBaseGiven n)).1
  have hPacket (n) : (actualOriginalGivenInputProfile DataC n ell).toReal ≤ Packet n :=
    ((passiveRescaledData_given_bound Data hd hs rfl c hcabs n ell hell (hBaseGiven n)).2).trans
      (hBaseBound n)
  have hLin := actualOriginalGivenInputProfile_linear_le DataC 0 ell
  have hFin : incrementsOriginalInputProfileWithLinear DataC 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) hLin
  have hML : (incrementsOriginalInputProfileWithLinear DataC 0 ell).toReal ≤ Packet 0 :=
    (ENNReal.toReal_mono (hGiven 0) hLin).trans (hPacket 0)
  exact round3Parameter_actual_original_canonical_raw_reserve_supply DataC hdC hsC hnC hpC rfl hFC gC
    (passiveRescaledData_immersion Data hd hs hi c hcz) ell (cF/4) (reference.cT/4) hell hell1
    (passiveRescaledData_ellipticity Data cF he c hc) (div_pos reference.cT_pos (by norm_num))
    (passiveRescaledData_linear Data hl c) (passiveRescaledData_decomposition Data hdec c)
    rho (passiveRescaledData_reserve Data rho hres c) hSamples (Packet 0) hFin hML q R Data.primaryCount
    Packet Inverse
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
    hInv (fun _ => round3PreparedFiniteMaximum_nonneg _) (fun _ => round3PreparedFiniteMaximum_nonneg _)
    hGiven hPacket (fun i => Classical.choice (hPrep c hc ell hell.le hell1 i))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_rescaled_canonical_supply
