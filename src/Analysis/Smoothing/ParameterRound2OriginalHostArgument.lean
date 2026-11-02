import Probes.ActualIncrementOriginalHostFields
import Smoothing.ParameterRound2OriginalArgumentGermProfiles
import Smoothing.ParameterRound2OriginalArgumentGermDifference
import Smoothing.ParameterRound2ScalarRawInput

/-! The same constructed host inverse pulls the literal original cutoff and
normal Core entries to the actual family. All estimates retain original
samples; actual open domains supply only qualitative differentiation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem parameterRound2_original_host_inverse_point
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M Es)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) e)
    (z : X) (hz : z ∈ b.target) :
    incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterTensorModelEquiv (m+1) d (b.symm z)) =
      ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2) := by
  rw [actual_original_jointPoint_native]
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hp := hpair z hz
  change ((b.symm z).1,(Data.atlas.chart i.1).symm (b.symm z).2) =
    (z.1,(e z.1).symm z.2) at hp
  exact congrArg (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) hp

/-- Original norms produce the actual original L(input) in the SAME adapted
host. The inverse and parameter response are the actual hdata fields. Only
coordinate germs of input are needed. -/
theorem parameterRound2_original_host_argument_germ_profiles
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (hInput : ∀ a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input a) UI)
    (hSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (input p x).IsSymm)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M Es)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) e)
    (S : Set X) (hS : S ⊆ b.target)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hsample : MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hprimary : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu)
    (ell ML MA : ℝ) (hell : 0 < ell)
    (hProfile : incrementsOriginalInputProfileWithLinear Data j ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data j ell).toReal ≤ ML)
    (hInputFinite : paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hMA : (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ MA)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    let a := parameterTensorModelEquiv (m+1) d
    let C := actualFastChartTransferPrefix (fun k => ‖a.toContinuousLinearMap‖*T k) j *
      coordinateDimensionFactor (m+1+d) j
    let arg := fun z : X => Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
      ((e z.1).symm z.2) (input ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2))
    ∃ V0 : Set X, IsOpen V0 ∧ S ⊆ V0 ∧ V0 ⊆ b.target ∧ ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k arg z‖ ≤
        2^j*(‖actualOriginalCoefficientFunctional (m+1)‖*C*ML)*(C*MA) := by
  intro a C arg
  have hg := actual_host_slice_geometry_inputs _ (hd.atlas_smooth.chart_mem i.1) _ _ _ hdata
  have hsource' := actual_original_host_source_primary_open Data hd i nu b e hdata hsource hprimary
  have hsample' : MapsTo b.symm S (a ⁻¹' incrementsOriginalPrimaryEvaluation Data nu i) := by
    intro z hz
    exact ⟨hsample hz,(hsource' (b.map_target (hS hz))).1.2⟩
  let phi := a ∘ b.symm
  let Tphi := fun k => ‖a.toContinuousLinearMap‖*T k
  have hTphi : ∀ k, 0 ≤ Tphi k := fun k => mul_nonneg a.toContinuousLinearMap.opNorm_nonneg (hT k)
  have hphi : ContDiffOn ℝ ∞ phi b.target := a.contDiff.comp_contDiffOn hg.2.2.1
  have hphijet : ∀ z ∈ S, ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k phi z‖ ≤ Tphi k := by
    intro z hz k hk hkj
    have hb := a.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
      ((hg.2.2.1).contDiffAt (b.open_target.mem_nhds (hS hz))) (n := k) (by simp)
    calc
      _ ≤ ell^(k-1)*(‖a.toContinuousLinearMap‖*‖iteratedFDeriv ℝ k b.symm z‖) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hell.le _)
      _ = ‖a.toContinuousLinearMap‖*(ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖) := by ring
      _ ≤ Tphi k := mul_le_mul_of_nonneg_left (hinvjet k hk hkj z hz) a.toContinuousLinearMap.opNorm_nonneg
  obtain ⟨V0,hV0,hSV0,hV0T,hreg,hbound⟩ := parameterRound2_original_argument_germ_profiles
    Data hd hLinear input hInput hSymm j Tphi hTphi ell hell ML MA hProfile hML hInputFinite hMA
    nu i phi b.target S b.open_target hS hphi (fun z hz => hsource' (b.map_target hz)) hsample' hphijet
  let origArg := fun z => Data.linearArgument nu
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).1
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).2
    (input (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).1
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).2)
  have heq : EqOn arg origArg b.target := by
    intro z hz
    dsimp only [origArg,phi,Function.comp_apply]
    rw [parameterRound2_original_host_inverse_point Data i nu b e hdata z hz]
  refine ⟨V0,hV0,hSV0,hV0T,hreg.congr (fun z hz => heq (hV0T hz)),?_⟩
  intro k hk z hz
  have he : arg =ᶠ[𝓝 z] origArg := by
    filter_upwards [b.open_target.mem_nhds (hS hz)] with w hw
    exact heq hw
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hbound k hk z hz

#print axioms parameterRound2_original_host_inverse_point
#print axioms parameterRound2_original_host_argument_germ_profiles
end GlobalEmbedding.Continuation
