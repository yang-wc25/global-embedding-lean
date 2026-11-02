import IncrementsCompletion.SamplePrimaryMeanRaw
import IncrementsCompletion.ActivePrimaryMeanNorms
import CollarCompletion.FiniteOpenMeanEstimates

/-! The true physical mean is internally proved to belong to the finite
original tensor carrier, with size and difference estimates, from refinement
at the actual ell only. All numeric costs, domains and tensor values are
unchanged. No actual mean or raw-output estimate is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge CollarCompletion
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

/-- Mean membership, size and difference are all outputs of the original
primitive construction. The physical tensor formula is the same for every
observation order. -/
theorem incrementsCompletion_sample_finite_mean_estimates
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
    (ML : ℝ) (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (Lactive : ℕ)
    (hCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (q Rsub : ℕ) (hq : 1 ≤ q) (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hPacket : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W := incrementsOriginalParameterRegion Data
    let hSO := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) (y) (hy : y ∈ S i) => hy.1
    let H := originalFiniteTarget Data hd hs hDecomp ell hell hGiven
    let p := finiteTensorGermSeminorm Data.atlas Data.parameterChart S W hSO ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    let hPacket0 := fun j => ENNReal.toReal_nonneg.trans (hPacket j)
    let hBnd := fun s R => parameterRound2_identityRawBnd_nonneg m d N (s+(q+4))
      (Packet (s+(q+4))) c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R (hPacket0 _) Tinv
    let hMg := fun s => parameterRound2_identityRawMg_nonneg m d N (s+(q+4))
      (Packet (s+(q+4))) c cT (1+Forward (s+(q+4))) Tinv
    let hT := parameterRound2_identityRawTransition_nonneg m d Packet Forward hPacket0 hForward
    let hreserve := div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)
    let C := fun s R => fullIncrementNovMeanNormCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      (s+(q+4)) q s Rsub Lactive (by omega) (rho/4) (Bnd s R) (Mg s)
      hreserve (hBnd s R) (hMg s) Tfixed hT
    let hActive := active_slices_from_original_data Data hd hs g hPreserves hTarget
    0 < radius ∧ (∀ s R, 0 ≤ C s R) ∧
    ∃ hsm : actualFiniteMeanMembership Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q,
    let Top := actualFiniteMeanOperator Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q hsm
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : finiteTensorGermSpace Data.atlas Data.parameterChart S W hSO // p 0 (K-H) < radius}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) ∧
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : finiteTensorGermSpace Data.atlas Data.parameterChart S W hSO // p 0 (K-H) < radius}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*(C s R*Dinput s)*p (s+(q+4)) (K.val-L.val)) := by
  intro S W hSO H p radius Bnd Mg Dinput Tfixed hPacket0 hBnd hMg hT hreserve C hActive
  have hBase := incrementsCompletion_sample_finite_germ_common_raw Data hd hs hn hp g V0 hV0 hKV0 hImm
    ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve ML hProfile hML
    Lactive hCount q Rsub Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep
  have hDinput (s) : 0 ≤ Dinput s := parameterRound2_identityRawDinput_nonneg _ _ _ _ (hPacket0 _) _
  have hNorm (s R) := incrementsCompletion_active_raw_mean_original_norms Data hd hs hn g hActive hPreserves
    V0 cT Tinv Forward Meta Rsub Lactive ell prep (s+(q+4)) q s hq (by omega)
    (rho/4) (Bnd s R) (Mg s) hreserve (hBnd s R) (hMg s) Tfixed hT
  let Nrm := fun s (Q0 : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) =>
    paperAtlasWeighted 0 s ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Q0)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S
  have hRaw (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (s : ℕ) (R : ℝ)
      (K L : {K : finiteTensorGermSpace Data.atlas Data.parameterChart S W hSO // p 0 (K-H) < radius})
      (hK : p (s+(q+4)) K.val ≤ R) (hL : p (s+(q+4)) L.val ≤ R) :
      let TA := fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g K.val.val.val hActive (q+2) (epsilon*ell)
      let TB := fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g L.val.val.val hActive (q+2) (epsilon*ell)
      (TA ∈ parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W ∧
        TB ∈ parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W) ∧
      (Nrm s TA ≠ ⊤ ∧ (Nrm s TA).toReal ≤ C s R*((epsilon*ell)/ell)) ∧
      (Nrm s TB ≠ ⊤ ∧ (Nrm s TB).toReal ≤ C s R*((epsilon*ell)/ell)) ∧
      (Nrm s (fun t x => TA t x-TB t x) ≠ ⊤ ∧
        (Nrm s (fun t x => TA t x-TB t x)).toReal ≤
          C s R*((epsilon*ell)/ell)*(Dinput s*p (s+(q+4)) (K.val-L.val))) := by
    have hH : H.val.val = Data.H := originalFiniteTarget_value Data hd hs hDecomp ell hell hGiven
    have hcommon := hBase.2 H hH K L
    obtain ⟨G,hG,hGW,hKG,hGV,hCover,raw⟩ := hcommon
    have htaul : epsilon*ell ≤ ell := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le
    have hnorm := (hNorm s R).2 K.val.val L.val.val G hG hGW (epsilon*ell) ell
      (Dinput s*p (s+(q+4)) (K.val-L.val)) (mul_pos he hell) htaul hell1
      (mul_nonneg (hDinput s) (apply_nonneg _ _))
      (raw (epsilon*ell) (mul_pos he hell) htaul s R hK hL)
    exact hnorm
  have hsm : actualFiniteMeanMembership Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q := by
    intro epsilon he he1 K U
    refine ⟨(hRaw epsilon he he1 0 (p (0+(q+4)) K.val) K K le_rfl le_rfl).1.1,?_⟩
    intro j
    have hf := (hRaw epsilon he he1 j (p (j+(q+4)) K.val) K K le_rfl le_rfl).2.1.1
    simpa only [Nat.add_zero] using parameterRound2_topOrder_finite_of_weighted 0 j hell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart U)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S hf
  refine ⟨hBase.1,(fun s R => (hNorm s R).1),hsm,?_⟩
  intro Top
  constructor
  · intro epsilon he he1 s R K hK
    exact actualFiniteMeanOperator_size Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q hsm epsilon he he1 hell K s (C s R)
      (hRaw epsilon he he1 s R K K hK hK).2.1.2
  · intro epsilon he he1 s R K L hK hL
    exact actualFiniteMeanOperator_difference Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q hsm epsilon he he1 hell K L s (q+4) (C s R) (Dinput s)
      (hRaw epsilon he he1 s R K L hK hL).2.2.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_sample_finite_mean_estimates
