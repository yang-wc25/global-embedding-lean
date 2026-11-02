import Smoothing.Round4PrimaryPieceProfiles
import Smoothing.Round4NativeParentProfiles
import Smoothing.Round4FixedPacketPhaseJets
import Probes.Round3ParameterCrossNativeData

/-! The SAME chosen phase charts and refinement cutoffs consume the original
fixed packet and original raw parent profiles. All high-order costs are
explicit scalar expressions with finite input prefixes; no compact maximum
of the produced high derivatives is used. Zeroth-order chart values are
intentionally separate from these positive-order coordinate estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators ENNReal
namespace GlobalEmbedding.Continuation

def round4RefinementPhaseProfile (n d : ℕ) (Given : ℕ → ℝ) (j : ℕ) : ℝ :=
  actualOriginalTotalPhaseJetCost n d j * Given j

def round4RefinementInverseProfile (n d : ℕ) (mu Mb : ℝ) (Given : ℕ → ℝ) (j : ℕ) : ℝ :=
  actualEuclideanPhaseSampleInverseJetCost mu Mb (round4RefinementPhaseProfile n d Given j) j

def round4RefinementMetaProfile (n d : ℕ) (mu Mb : ℝ)
    (BS TS BP TP Given : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  actualHostRefinementSampleCutoffCost
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) mu Mb
    (round4RefinementPhaseProfile n d Given j)
    (∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k) j

theorem round4RefinementPhaseProfile_nonneg (n d j : ℕ) {Given : ℕ → ℝ}
    (hGiven : 0 ≤ Given j) : 0 ≤ round4RefinementPhaseProfile n d Given j := by
  unfold round4RefinementPhaseProfile actualOriginalTotalPhaseJetCost
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (linearModelFactor_nonneg _ _) (actualScalarCovectorAssembly (n+d)).opNorm_nonneg)
    (coordinateDimensionFactor_nonneg _ _)) hGiven

theorem round4RefinementInverseProfile_congr (n d : ℕ) (mu Mb : ℝ) (j : ℕ)
    {G₁ G₂ : ℕ → ℝ} (hG : G₁ j = G₂ j) :
    round4RefinementInverseProfile n d mu Mb G₁ j =
      round4RefinementInverseProfile n d mu Mb G₂ j := by
  simp only [round4RefinementInverseProfile,round4RefinementPhaseProfile,hG]

theorem round4RefinementMetaProfile_congr_prefix (n d : ℕ) (mu Mb : ℝ) (Ds Dp j : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ G₁ G₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j, TP₁ a = TP₂ a)
    (hG : G₁ j = G₂ j) :
    round4RefinementMetaProfile n d mu Mb BS₁ TS₁ BP₁ TP₁ G₁ Ds Dp j =
      round4RefinementMetaProfile n d mu Mb BS₂ TS₂ BP₂ TP₂ G₂ Ds Dp j := by
  have hsum : (∑ k ∈ Finset.range (j+1), round4ParentProfile BS₁ TS₁ BP₁ TP₁ Ds Dp k) =
      ∑ k ∈ Finset.range (j+1), round4ParentProfile BS₂ TS₂ BP₂ TP₂ Ds Dp k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := by simpa using hk
    exact round4ParentProfile_congr_prefix Ds Dp k
      (fun a ha => hBS a (ha.trans hkj)) (fun a ha => hTS a (ha.trans hkj))
      (fun a ha => hBP a (ha.trans hkj)) (fun a ha => hTP a (ha.trans hkj))
  simp only [round4RefinementMetaProfile,round4RefinementPhaseProfile,hG,hsum]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es

theorem Round4PrimaryJetSupply.actual_original_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP Given : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (s : Finset X)
    (piece : s → Round3PreparedPrimaryPiece Data i.2 nu W)
    (jet : Round4PrimaryJetSupply Data i nu W
      (round3ParameterNativeParent (Data.parameterChart i.2)
        (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
          (tensorLocalNormalizedCutoff RP.raw) i)) s piece)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hbuffer : ell ≤ jet.buffer)
    (hGiven : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hGivenBound : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j)
    (S : Set X) (hS : S ⊆ (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalPrimaryEvaluation Data nu i) :
    (∀ (a : s) k, 1 ≤ k → k ≤ j → ∀ x ∈ (piece a).native.source ∩ S,
      ell^k*‖iteratedFDeriv ℝ (k+1) (piece a).native x‖ ≤
        2^(j+2)*round4RefinementPhaseProfile (m+1) d Given j) ∧
    (∀ (a : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (piece a).native.target,
      (piece a).native.symm y ∈ S → ell^(k-1)*‖iteratedFDeriv ℝ k (piece a).native.symm y‖ ≤
        round4RefinementInverseProfile (m+1) d jet.mu jet.Mb Given j) ∧
    ∀ (a : s) y, y ∈ (piece a).native.target → (piece a).native.symm y ∈ S →
      ell^j*‖iteratedFDeriv ℝ j
        ((piece a).cutoff ∘ (actualHostAdaptedChart (Data.atlas.chart (piece a).host) (piece a).native).symm) y‖ ≤
          round4RefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp j := by
  let Mj := round4RefinementPhaseProfile (m+1) d Given j
  let Mt := ∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k
  have hMj : 0 ≤ Mj := round4RefinementPhaseProfile_nonneg (m+1) d j
    (ENNReal.toReal_nonneg.trans hGivenBound)
  have hMt : 0 ≤ Mt := Finset.sum_nonneg (fun k _ =>
    round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp k)
  have hFixedLe := parameterRound2_originalFixedPacketProfile_mono_scale Data j ell 1 hell1
  have hFixed := ne_top_of_le_ne_top hGiven hFixedLe
  have hFixedBound := (ENNReal.toReal_mono hGiven hFixedLe).trans hGivenBound
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  have hPsiEq : ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘ q.symm) =
      actualOriginalJointPhase Data nu i ∘ parameterTensorModelEquiv (m+1) d := by
    funext z
    change Data.phase nu ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) =
      Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (parameterTensorModelEquiv (m+1) d z))
    rw [actual_original_jointPoint_native]
  have hPhase : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ jet.O ∩ S,
      ell^k*‖iteratedFDeriv ℝ (k+1)
        ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘ q.symm) x‖ ≤ Mj := by
    intro k hk hkj x hx
    rw [hPsiEq]
    exact round4_actual_fixed_packet_phase_positive_jets Data hd hs j ell (Given j)
      hell hFixed hFixedBound nu i k hkj x (hS hx.2)
  have hAll := jet.jets S j ell Mj hell hMj hPhase
  refine ⟨hAll.1,hAll.2.1,?_⟩
  apply hAll.2.2 Mt hMt hbuffer
  intro k hk x hx
  have hxNative : x ∈ actualOriginalNativeOpen Data i :=
    ⟨(jet.domain hx.1).1.1,(jet.domain hx.1).2⟩
  have hxTargets := (round3Parameter_originalNativeOpen_iff Data i x).mp hxNative
  have hTarget : x ∈ ((parameterLocalProductFamily Data.atlas B).chart i).target := by
    change x.1 ∈ (B.chart i.2).target ∧ x.2 ∈ (Data.atlas.chart i.1).target
    rw [hChart]
    exact ⟨hxTargets.2.1,hxTargets.1⟩
  have hB : ∀ ip, B.chart ip ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hp := round4_actual_native_parent_jets BS TS BP TP hBS hTS hBP hTP Ds Dp
    Data.atlas B hd.atlas_smooth hB Data.parameterSet RS RP i i k ell hell.le hell1 x hTarget
  rw [hChart] at hp
  exact hp.trans (Finset.single_le_sum
    (fun a _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp a) (by simpa using hk))

#print axioms Round4PrimaryJetSupply.actual_original_profiles
#print axioms round4RefinementMetaProfile_congr_prefix
end GlobalEmbedding.Continuation
