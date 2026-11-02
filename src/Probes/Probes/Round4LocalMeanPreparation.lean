import Probes.Round4PrimaryLocalMultiplicity
import Smoothing.Round3ParameterClosedMeanReserveSupply

/-!
The original mean reserve supplier with a genuine local primary count.
An existing native preparation is reused literally: all charts, inverses,
cutoffs, samples and derivative estimates remain the same. Only its numerical
primary-count field is improved from an actual support calculation. The final
theorem feeds that preparation into the actual closed-parameter mean supplier.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {Sub : Type*} [Fintype Sub]

def round4NativeMeanPreparationLocal
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m)
      (Λ := Fin Data.primaryCount) (Β := Sub) (fun p x => Data.F (p,x)))
    (ell cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (R Lold L : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hcount : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Data.cutoff nu))).card ≤ L)
    (prep : Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT
      Tinv Forward Meta R Lold i) :
    Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT
      Tinv Forward Meta R L i := by
  refine { prep with refinement := { prep.refinement with primary_count := ?_ } }
  intro w hw
  let W : Set (Ep × M) := (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW : IsOpen W := (Data.parameterChart i.2).open_target.prod isOpen_univ
  change (Finset.univ.filter (fun nu => w ∈ incrementsGlobalRelativeSupport W
    (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)))).card ≤ L
  apply (Finset.card_le_card ?_).trans (hcount ((Data.parameterChart i.2).symm w.1,w.2))
  intro nu hnu
  have hnw := (Finset.mem_filter.mp hnu).2
  rw [parameterRound2_global_relativeSupport_eq W hW] at hnw
  have hphys := round3Parameter_plain_pullback_tsupport
    (round3ParameterProductChart (M := M) (Data.parameterChart i.2))
    (Data.cutoff nu) w hw hnw.2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hphys⟩

/-- The actual mean reserve construction depends on `(degree+1)*basisCount`,
not on `Data.primaryCount`. The host/basis injection and support relation are
the raw geometric input; the local count and its observer versions are proved. -/
theorem round4_closed_mean_reserve_of_normalized_hosts
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hAll : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m)
      (Λ := Fin Data.primaryCount) (Β := Sub) (fun p x => Data.F (p,x)))
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ML : ℝ) (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (q Rsub Lold degree basisCount : ℕ)
    (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n)
    (prep : ∀ i, Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT
      Tinv Forward Meta Rsub Lold i)
    {Host : Type*} [Fintype Host]
    (raw : Host → P × M → ℝ) (supports : Host → Set (P × M))
    (hraw : ∀ a, tsupport (raw a) ⊆ supports a)
    (hdegree : ∀ a, tensorEnlargedSupportDegree supports a ≤ degree)
    (host : Fin Data.primaryCount → Host) (slot : Fin Data.primaryCount → Fin basisCount)
    (hlabel : Function.Injective (fun nu => (host nu,slot nu)))
    (hsub : ∀ nu, tsupport (Data.cutoff nu) ⊆ tsupport (squareNormalizedCutoff raw (host nu))) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := (univ : Set (P × M))
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    0 < radius ∧ ∀ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
      H.val = Data.H → Round3ParameterMeanRawReserveSupply (Tr := ℝ) Data.atlas Data.parameterChart
        S W0 p H radius q Rsub ((degree+1)*basisCount) (rho/4) Bnd Mg Dinput Tfixed
        (fun p x => Data.F (p,x)) hF g Data.primaryDomain ell := by
  have hcount := round4_primary_count_of_normalized_hosts raw supports hraw degree basisCount
    hdegree Data.cutoff host slot hlabel hsub
  exact round3Parameter_actual_closed_original_mean_raw_reserve_supply Data hd hs hn hp hAll hF g
    hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML
    q Rsub ((degree+1)*basisCount) Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket
    (fun i => round4NativeMeanPreparationLocal Data hd hs hn g ell cT Tinv Forward Meta
      Rsub Lold ((degree+1)*basisCount) i hcount (prep i))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4NativeMeanPreparationLocal
#print axioms GlobalEmbedding.Continuation.round4_closed_mean_reserve_of_normalized_hosts
