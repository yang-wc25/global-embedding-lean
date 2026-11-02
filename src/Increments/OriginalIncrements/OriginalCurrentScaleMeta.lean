import OriginalIncrements.OriginalFinitePrimarySupply
import Smoothing.Round4ParentFiniteProfiles
import Smoothing.Round4NativeParentProfiles
import Probes.ActualHostRefinementSampleJets
import Probes.ActualIncrementHostGeometryInputs
import CollarCompletion.OriginalParentSampling

/-!
# The literal primary cutoff has a finite original current-scale profile

The exact grid factor is used for every scale `0 < ell ≤ 1`; no new bound
`ell ≤ buffer` is imposed. The parameter localizer is one on the original
sample neighborhood, so it contributes no derivative budget. The parent
jets come from the literal raw source/parameter preparation, and the inverse
jets come from the original Given norm at the CURRENT scale and finite
order. All cutoffs, charts and observation samples are the same objects as
the actual manufactured primary packet.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

def originalGridCutoffBudget (mu Mb buffer : ℝ) (j : ℕ) : ℝ :=
  ((actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j)/buffer^j

def originalGridCutoffPrefix (mu Mb buffer : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), originalGridCutoffBudget X mu Mb buffer k

theorem originalGridCutoffBudget_nonneg
    (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer) (j : ℕ) :
    0 ≤ originalGridCutoffBudget X mu Mb buffer j := by
  exact div_nonneg (mul_nonneg (pow_nonneg (actualPhaseRefinementFactor_pos hmu hMb).le _)
    (actualRefinementCutoffJetCost_nonneg X j)) (pow_nonneg hbuffer.le _)

theorem originalGridCutoffPrefix_nonneg
    (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer) (j : ℕ) :
    0 ≤ originalGridCutoffPrefix X mu Mb buffer j :=
  Finset.sum_nonneg (fun k _ => originalGridCutoffBudget_nonneg X mu Mb buffer hmu hMb hbuffer k)

variable {X}

def originalCurrentScaleMetaProfile (m d : ℕ) (mu Mb buffer : ℝ)
    (BS TS BP TP Given : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  actualFastChartTransferCost
    (fun _ => actualEuclideanPhaseSampleInverseJetCost mu Mb
      (actualOriginalTotalPhaseJetCost (m+1) d j*max 0 (Given j)) j) j *
    (2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*
      (∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k))*
      originalGridCutoffPrefix (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
        mu Mb buffer j)

theorem originalCurrentScaleMetaProfile_nonneg
    (m d : ℕ) (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (BS TS BP TP Given : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp j : ℕ) :
    0 ≤ originalCurrentScaleMetaProfile m d mu Mb buffer BS TS BP TP Given Ds Dp j := by
  have hMj : 0 ≤ actualOriginalTotalPhaseJetCost (m+1) d j*max 0 (Given j) :=
    mul_nonneg (incrementsCompletion_original_phase_jet_cost_nonneg m d j) (le_max_left _ _)
  have hInv := actualEuclideanPhaseSampleInverseJetCost_nonneg hmu hMb hMj j
  have hParent : 0 ≤ ∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k :=
    Finset.sum_nonneg (fun k _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp k)
  have hGrid := originalGridCutoffPrefix_nonneg
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))) mu Mb buffer hmu hMb hbuffer j
  unfold originalCurrentScaleMetaProfile
  exact mul_nonneg (actualFastChartTransferCost_nonneg _ (fun _ => hInv) j)
    (mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg hParent)) hGrid)

theorem originalCurrentScaleMetaProfile_prefix_congr
    (m d Ds Dp j : ℕ) (mu Mb buffer : ℝ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ Given₁ Given₂ : ℕ → ℝ}
    (hBS : ∀ k ≤ j, BS₁ k = BS₂ k) (hTS : ∀ k ≤ j, TS₁ k = TS₂ k)
    (hBP : ∀ k ≤ j, BP₁ k = BP₂ k) (hTP : ∀ k ≤ j, TP₁ k = TP₂ k)
    (hGiven : Given₁ j = Given₂ j) :
    originalCurrentScaleMetaProfile m d mu Mb buffer BS₁ TS₁ BP₁ TP₁ Given₁ Ds Dp j =
      originalCurrentScaleMetaProfile m d mu Mb buffer BS₂ TS₂ BP₂ TP₂ Given₂ Ds Dp j := by
  have hParent : (∑ k ∈ Finset.range (j+1), round4ParentProfile BS₁ TS₁ BP₁ TP₁ Ds Dp k) =
      ∑ k ∈ Finset.range (j+1), round4ParentProfile BS₂ TS₂ BP₂ TP₂ Ds Dp k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := by simpa using hk
    exact round4ParentProfile_congr_prefix Ds Dp k
      (fun a ha => hBS a (ha.trans hkj)) (fun a ha => hTS a (ha.trans hkj))
      (fun a ha => hBP a (ha.trans hkj)) (fun a ha => hTP a (ha.trans hkj))
  simp only [originalCurrentScaleMetaProfile,hGiven,hParent]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Xn" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- Explicit cutoff cost of the same constructed piece, using only the
current original Given slot and raw parent prefix through the observation
order. The localizer's actual equality near the original compact parameter
set is used, so no derivative bound for that auxiliary scalar is assumed. -/
theorem original_primary_cutoff_current_scale_profile
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP Given : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
    (hOne : EqOn psi 1 V) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (supply : OriginalBudgetedPrimarySupply Data theta)
      (_hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (_hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
      (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (a : supply.packet.s nu i) (j : ℕ) (ell : ℝ), 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile Data j ell ≠ ⊤ →
      (actualOriginalGivenInputProfile Data j ell).toReal ≤ Given j →
      ∀ y ∈ (supply.packet.piece nu i a).native.target,
        parameterTensorModelEquiv (m+1) d ((supply.packet.piece nu i a).native.symm y) ∈
          incrementsOriginalPrimaryEvaluation Data nu i →
        ell^j*‖iteratedFDeriv ℝ j
          ((supply.packet.piece nu i a).cutoff ∘
            (actualHostAdaptedChart (Data.atlas.chart (supply.packet.piece nu i a).host)
              (supply.packet.piece nu i a).native).symm) y‖ ≤
          originalCurrentScaleMetaProfile m d (supply.mu nu i) (supply.Mb nu i)
            (supply.buffer nu i) BS TS BP TP Given Ds Dp j := by
  intro theta supply hCompact hSmooth nu i a j ell hell hell1 hGiven hGivenBound y hy hSample
  let piece := supply.packet.piece nu i a
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let thetaN := round3ParameterNativeParent (Data.parameterChart i.2) (theta i)
  let rawParent := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw) i
  let native := piece.native
  let x := native.symm y
  let Mj := actualOriginalTotalPhaseJetCost (m+1) d j*max 0 (Given j)
  let Mt := ∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k
  let Me := originalGridCutoffPrefix Xn (supply.mu nu i) (supply.Mb nu i) (supply.buffer nu i) j
  let T := fun _ : ℕ => actualEuclideanPhaseSampleInverseJetCost (supply.mu nu i) (supply.Mb nu i) Mj j
  have hMj : 0 ≤ Mj := mul_nonneg (incrementsCompletion_original_phase_jet_cost_nonneg m d j)
    (le_max_left _ _)
  have hMt : 0 ≤ Mt := Finset.sum_nonneg (fun k _ =>
    round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp k)
  have hMe : 0 ≤ Me := originalGridCutoffPrefix_nonneg Xn _ _ _
    (supply.mu_pos nu i) (supply.Mb_nonneg nu i) (supply.buffer_pos nu i) j
  have hT : ∀ k, 0 ≤ T k := fun _ => actualEuclideanPhaseSampleInverseJetCost_nonneg
    (supply.mu_pos nu i) (supply.Mb_nonneg nu i) hMj j
  have hHost : piece.host = i.1 := supply.packet.host nu i a
  have hGeo := actual_host_slice_geometry_inputs (Data.atlas.chart piece.host)
    (hd.atlas_smooth.chart_mem piece.host) native _ piece.slices piece.data
  have hSource : native.source ⊆ q.target := by simpa only [q,hHost] using hGeo.1
  have hThetaSupport : tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) := by
    intro z hz
    have hh := CollarCompletion.original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi i hz
    have hp := B.inner_subset i.2 hh.1
    rw [hChart] at hp
    exact ⟨hp,mem_univ _⟩
  have hThetaNative := (round3Parameter_native_compact_parent (Data.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) hThetaSupport).1
  have hqi : ContMDiffOn 𝓘(ℝ,Xn) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm q.target := by
    have hcs : ContMDiffOn 𝓘(ℝ,Xn) 𝓙 ∞
        (fun z : Xn => (Data.atlas.chart i.1).symm z.2) q.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  have hThetaCoord : ContDiffOn ℝ ∞ (thetaN ∘ q.symm) q.target :=
    (hThetaNative.comp_contMDiffOn hqi).contDiffOn
  have hEval := (actual_original_native_evaluation_iff Data hd i x).mp hSample.1
  have hxP := hd.parameter_norm_subset i.2 hEval.2.1
  have hxD := hd.source_norm_subset i.1 hEval.1
  have hB : ∀ ip, B.chart ip ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hParent (k : ℕ) (hkj : k ≤ j) :
      ell^k*‖iteratedFDeriv ℝ k (thetaN ∘ q.symm) x‖ ≤ Mt := by
    have hGerm := sourceCollarNov_parameter_native_parent_host_germ psi V Data.parameterSet hV hKV hOne
      (Data.parameterChart i.2) (Data.atlas.chart i.1) rawParent x hxP hxD hEval.2.2
    have hEq := (hGerm.iteratedFDeriv ℝ k).eq_of_nhds
    change iteratedFDeriv ℝ k (thetaN ∘ q.symm) x = _ at hEq
    rw [hEq]
    have hTarget : x ∈ ((parameterLocalProductFamily Data.atlas B).chart i).target := by
      change x.1 ∈ (B.chart i.2).target ∧ x.2 ∈ (Data.atlas.chart i.1).target
      rw [hChart]
      exact ⟨hxP,hxD⟩
    have hh := round4_actual_native_parent_jets BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet RS RP i i k ell hell.le hell1 x hTarget
    rw [hChart] at hh
    exact hh.trans (Finset.single_le_sum
      (fun l _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp l) (by simpa using hkj))
  have hPsiEq : ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘ q.symm) =
      actualOriginalJointPhase Data nu i ∘ parameterTensorModelEquiv (m+1) d := by
    funext z
    simp only [Function.comp_apply,actualOriginalJointPhase,actual_original_jointPoint_native]
    rfl
  have hInv := supply.native_inverse nu i a {y}
    (singleton_subset_iff.mpr hy) j ell Mj hell hMj (by
      intro k hk hkj w hw
      obtain ⟨z,hz,rfl⟩ := hw
      have hzEq : z = y := mem_singleton_iff.mp hz
      rw [hzEq]
      change ell^k*‖iteratedFDeriv ℝ (k+1)
        ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘ q.symm) x‖ ≤ Mj
      rw [hPsiEq]
      exact actual_original_given_phase_positive_jets Data hd hs j ell (max 0 (Given j)) hell hGiven
        (hGivenBound.trans (le_max_right _ _)) nu i k hkj x hSample)
  have hGrid (k : ℕ) (hkj : k ≤ j) (w : Xn) :
      ell^k*‖iteratedFDeriv ℝ k
        (actualRefinementCutoff Xn (supply.packet.s nu i)
          (supply.buffer nu i/actualPhaseRefinementFactor (supply.mu nu i) (supply.Mb nu i)) a.val) w‖ ≤ Me := by
    have hh := supply.cutoff_jets nu i k (supply.buffer nu i)
      (supply.buffer_pos nu i).le le_rfl a w
    have hb := pow_pos (supply.buffer_pos nu i) k
    have hUnweighted : ‖iteratedFDeriv ℝ k
        (actualRefinementCutoff Xn (supply.packet.s nu i)
          (supply.buffer nu i/actualPhaseRefinementFactor (supply.mu nu i) (supply.Mb nu i)) a.val) w‖ ≤
        originalGridCutoffBudget Xn (supply.mu nu i) (supply.Mb nu i) (supply.buffer nu i) k := by
      apply (le_div_iff₀ hb).mpr
      simpa only [mul_comm] using hh
    exact ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell.le hell1)).trans hUnweighted).trans
      (Finset.single_le_sum (fun l _ => originalGridCutoffBudget_nonneg Xn _ _ _
        (supply.mu_pos nu i) (supply.Mb_nonneg nu i) (supply.buffer_pos nu i) l) (by simpa using hkj))
  have hCut := actual_host_refinement_cutoff_adapted_jets_at q thetaN
    (actualRefinementCutoff Xn (supply.packet.s nu i)
      (supply.buffer nu i/actualPhaseRefinementFactor (supply.mu nu i) (supply.Mb nu i)) a.val)
    native q.target q.open_target (Subset.refl _) hSource hThetaCoord
    (actualRefinementCutoff_contDiff Xn _ _ _) hGeo.2.2.1 j ell Mt Me hell hMt hMe T hT y hy
    hParent hGrid (fun k hk hkj => hInv k hk (by omega) y (mem_singleton _))
  rw [← supply.cutoff_eq nu i a] at hCut
  change ell^j*‖iteratedFDeriv ℝ j
    (piece.cutoff ∘ (actualHostAdaptedChart (Data.atlas.chart piece.host) native).symm) y‖ ≤ _
  rw [hHost]
  exact hCut

/-- The explicit current-scale Meta profile is an output certificate of one
actual budgeted primary packet, universally over the later Given bound. -/
def OriginalCurrentScaleMetaCertificate
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (supply : OriginalBudgetedPrimarySupply Data theta) : Prop :=
  ∀ (Given : ℕ → ℝ) (nu : Fin Data.primaryCount)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : supply.packet.s nu i)
    (j : ℕ) (ell : ℝ), 0 < ell → ell ≤ 1 →
    actualOriginalGivenInputProfile Data j ell ≠ ⊤ →
    (actualOriginalGivenInputProfile Data j ell).toReal ≤ Given j →
    ∀ y ∈ (supply.packet.piece nu i a).native.target,
      parameterTensorModelEquiv (m+1) d ((supply.packet.piece nu i a).native.symm y) ∈
        incrementsOriginalPrimaryEvaluation Data nu i →
      ell^j*‖iteratedFDeriv ℝ j
        ((supply.packet.piece nu i a).cutoff ∘
          (actualHostAdaptedChart (Data.atlas.chart (supply.packet.piece nu i a).host)
            (supply.packet.piece nu i a).native).symm) y‖ ≤
        originalCurrentScaleMetaProfile m d (supply.mu nu i) (supply.Mb nu i)
          (supply.buffer nu i) BS TS BP TP Given Ds Dp j

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.originalCurrentScaleMetaProfile_prefix_congr
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_cutoff_current_scale_profile
