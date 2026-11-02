import NormalPolar.PassiveOriginalReferenceMean
import NormalPolar.PassiveOriginalGivenProfile
import NormalPolar.PassiveOriginalGeometry
import NormalPolar.PassiveOriginalSmooth
import Smoothing.Round3ParameterOriginalCanonicalRawSupply

/-! A genuine canonical mean/raw reserve supply on the full original
parameter manifold. The conditioned reference packet supplies its actual
native preparation. The original seed Given budget plus the actual parameter
transition cost supplies all raw input budgets. All costs are selected
before ell; no mean, increment, remainder or repaired-map bound is assumed. -/

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

theorem passiveOriginal_reference_canonical_supply
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hp₀ : IncrementsOriginalPhaseConditions seed hd₀ hs₀)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hi₀ : IncrementsOriginalSliceImmersionInputs seed)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀)
    (R : ℕ) (reference : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub R)
    (c rho : ℝ) (he₀ : IncrementsOriginalCoordinateEllipticityInputs seed c)
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
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
    ∃ (hF : ∀ p, ContMDiff IM 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => Data.F (p,x)))
      (Packet Forward Inverse Meta : ℕ → ℝ),
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data gp Forward Inverse Meta ∧
      ∀ ell, 0 < ell → ell ≤ 1 →
        Round3ParameterOriginalCanonicalRawOutput Data hF gp hSamples ell c reference.cT rho
          (Packet 0) q R Data.primaryCount Packet Inverse
          (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
          (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) := by
  intro Data g gp hd hs
  have hzero : (0 : E₀) ∈ seed.parameterSet := by rw [hAll]; trivial
  have hopen := hd₀.parameter_subset hzero
  obtain ⟨ib,hib,hQb⟩ := hd₀.parameter_cover 0 hzero
  have hbzero : seed.parameterChart ib 0 = (0 : E₀) := Subsingleton.elim _ _
  have hbT : (0 : E₀) ∈ (seed.parameterChart ib).target :=
    hbzero ▸ (seed.parameterChart ib).map_source hib
  have hbQ : (0 : E₀) ∈ seed.parameterNormDomain ib := hbzero ▸ hQb
  let hn := passiveOriginalData_freeNormalConditions (0 : E₀) seed hd₀ hs₀ hn₀ hopen B Q hd hs
  let hp := passiveOriginalData_phaseConditions (0 : E₀) seed hd₀ hs₀ hp₀ hopen B Q hd hs
  have hF : ∀ p, ContMDiff IM 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => Data.F (p,x)) :=
    fun _ => incrementsOriginal_slice_contMDiff seed hd₀ hs₀ 0 hopen
  obtain ⟨Forward,Inverse,Meta,hFwd,hInv,hMeta,hProfiles,hPrep⟩ :=
    passiveOriginal_reference_mean_preparation seed hd₀ hs₀ hn₀ hAll base hId R reference
      B hB Q hSamples hd hs hn
  obtain ⟨C,hC,hCost⟩ := passiveOriginal_given_profile_uniform_cost (0 : E₀) seed B Q hd hd₀ hs₀
    ib hbT hbQ hzero hib hB hforward hQ hQT
  let Packet : ℕ → ℝ := fun n => SeedPacket n+C n
  refine ⟨hF,Packet,Forward,Inverse,Meta,hFwd,hInv,hMeta,hProfiles,?_⟩
  intro ell hell hell1
  have hGiven (n) : actualOriginalGivenInputProfile Data n ell ≠ ⊤ :=
    (hCost n ell hell1 (hSeed n ell hell hell1).1).1
  have hPacket (n) : (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n :=
    ((hCost n ell hell1 (hSeed n ell hell hell1).1).2).trans
      (add_le_add (hSeed n ell hell hell1).2 le_rfl)
  have hLin := actualOriginalGivenInputProfile_linear_le Data 0 ell
  have hFin : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) hLin
  have hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ Packet 0 :=
    (ENNReal.toReal_mono (hGiven 0) hLin).trans (hPacket 0)
  exact round3Parameter_actual_original_canonical_raw_reserve_supply Data hd hs hn hp rfl hF gp
    (passiveOriginalData_immersion (0 : E₀) seed B Q hi₀ hopen)
    ell c reference.cT hell hell1
    (passiveOriginalData_ellipticity (0 : E₀) seed B Q c he₀ hzero) reference.cT_pos
    (passiveOriginalData_linearSmooth (0 : E₀) seed B Q ib hl₀ hopen hbT)
    (passiveOriginalData_decomposition (0 : E₀) seed B Q hc₀ hopen)
    rho (passiveOriginalData_reserve (0 : E₀) seed B Q rho hr₀ hopen hzero)
    hSamples (Packet 0) hFin hML q R Data.primaryCount Packet Inverse
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
    hInv (fun _ => round3PreparedFiniteMaximum_nonneg _) (fun _ => round3PreparedFiniteMaximum_nonneg _)
    hGiven hPacket (fun i => Classical.choice (hPrep ell hell.le hell1 i))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_canonical_supply
