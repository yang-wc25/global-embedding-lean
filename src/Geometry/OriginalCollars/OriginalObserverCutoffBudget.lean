import OriginalCollars.PointwiseCutoffTransfer
import OriginalIncrements.OriginalCurrentScaleMeta
import CompletionIntegration.PreparedPrimaryObserverCutoffs
import Probes.Round3ParameterWholePieceReplacement

/-!
# The same raw-parent/grid cutoffs have explicit original observer budgets

The host bound is the literal raw-parent prefix times the manufactured grid
prefix.  Original transition bounds transport it to every original observer.
The localizing scalar is one near the original parameter set and contributes
no derivative budget.  Outside actual support the same scalar has zero jets.
No maximum of constructed derivatives, native inverse profile or auxiliary
compact-domain supremum enters the formula.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalCollars
open OriginalIncrements

def originalParentGridHostCutoffProfile (m d : ℕ) (mu Mb buffer : ℝ)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  2^j * (‖ContinuousLinearMap.mul ℝ ℝ‖ *
    (∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k)) *
    originalGridCutoffPrefix (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
      mu Mb buffer j

theorem originalParentGridHostCutoffProfile_nonneg
    (m d : ℕ) (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (BS TS BP TP : ℕ → ℝ) (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k) (Ds Dp j : ℕ) :
    0 ≤ originalParentGridHostCutoffProfile m d mu Mb buffer BS TS BP TP Ds Dp j := by
  exact mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg
      (Finset.sum_nonneg (fun k _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp k))))
    (originalGridCutoffPrefix_nonneg _ mu Mb buffer hmu hMb hbuffer j)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def originalObserverCutoffProfile
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (BS TS BP TP Parameter Spatial : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  round3PreparedFiniteMaximum
    (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
      actualFastChartTransferCost (fun k => max (Parameter k) (Spatial k)) j *
        originalParentGridHostCutoffProfile m d (supply.mu a.1 a.2) (supply.Mb a.1 a.2)
          (supply.buffer a.1 a.2) BS TS BP TP Ds Dp j)

theorem originalObserverCutoffProfile_nonneg
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (BS TS BP TP Parameter Spatial : ℕ → ℝ) (Ds Dp j : ℕ) :
    0 ≤ originalObserverCutoffProfile Data theta supply BS TS BP TP Parameter Spatial Ds Dp j :=
  round3PreparedFiniteMaximum_nonneg _

/-- The exact local primary cutoff has its explicit host-prefix bound at
every original parameter sample.  The chart and grid are the supplied
packet's own objects; the profile reads no constructed derivative. -/
theorem original_primary_cutoff_host_prefix
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k) (Ds Dp : ℕ)
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
      (a : supply.packet.s nu i) (j k : ℕ), k ≤ j → ∀ x : X,
      x.1 ∈ (Data.parameterChart i.2).target → x.2 ∈ (Data.atlas.chart i.1).target →
      (Data.parameterChart i.2).symm x.1 ∈ Data.parameterSet →
      ‖iteratedFDeriv ℝ k
        ((supply.packet.piece nu i a).cutoff ∘
          (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖ ≤
        originalParentGridHostCutoffProfile m d (supply.mu nu i) (supply.Mb nu i)
          (supply.buffer nu i) BS TS BP TP Ds Dp j := by
  intro theta supply hCompact hSmooth nu i a j k hkj x hxP hxD hxK
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let thetaN := round3ParameterNativeParent (Data.parameterChart i.2) (theta i)
  let rawParent := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw) i
  let eta := actualRefinementCutoff X (supply.packet.s nu i)
    (supply.buffer nu i/actualPhaseRefinementFactor (supply.mu nu i) (supply.Mb nu i)) a.val
  let Mt := ∑ l ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp l
  let Me := originalGridCutoffPrefix X (supply.mu nu i) (supply.Mb nu i) (supply.buffer nu i) j
  have hMt : 0 ≤ Mt := Finset.sum_nonneg (fun l _ =>
    round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp l)
  have hMe : 0 ≤ Me := originalGridCutoffPrefix_nonneg X _ _ _
    (supply.mu_pos nu i) (supply.Mb_nonneg nu i) (supply.buffer_pos nu i) j
  have hThetaSupport : tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) := by
    intro z hz
    have hh := CollarCompletion.original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi i hz
    have hp := B.inner_subset i.2 hh.1
    rw [hChart] at hp
    exact ⟨hp,mem_univ _⟩
  have hThetaNative := (round3Parameter_native_compact_parent (Data.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) hThetaSupport).1
  have hqi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm q.target := by
    have hcs : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞
        (fun z : X => (Data.atlas.chart i.1).symm z.2) q.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  have hThetaCoord : ContDiffOn ℝ ∞ (thetaN ∘ q.symm) q.target :=
    (hThetaNative.comp_contMDiffOn hqi).contDiffOn
  have hB : ∀ ip, B.chart ip ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hParent (l : ℕ) (hlj : l ≤ j) : ‖iteratedFDeriv ℝ l (thetaN ∘ q.symm) x‖ ≤ Mt := by
    have hGerm := sourceCollarNov_parameter_native_parent_host_germ psi V Data.parameterSet hV hKV hOne
      (Data.parameterChart i.2) (Data.atlas.chart i.1) rawParent x hxP hxD hxK
    have hEq := (hGerm.iteratedFDeriv ℝ l).eq_of_nhds
    change iteratedFDeriv ℝ l (thetaN ∘ q.symm) x = _ at hEq
    rw [hEq]
    have hTarget : x ∈ ((parameterLocalProductFamily Data.atlas B).chart i).target := by
      change x.1 ∈ (B.chart i.2).target ∧ x.2 ∈ (Data.atlas.chart i.1).target
      rw [hChart]
      exact ⟨hxP,hxD⟩
    have hh := round4_actual_native_parent_jets BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet RS RP i i l 1 zero_le_one le_rfl x hTarget
    rw [hChart] at hh
    simp only [one_pow,one_mul] at hh
    exact hh.trans (Finset.single_le_sum
      (fun r _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp r) (by simpa using hlj))
  have hGrid (l : ℕ) (hlj : l ≤ j) : ‖iteratedFDeriv ℝ l eta x‖ ≤ Me := by
    have hh := supply.cutoff_jets nu i l (supply.buffer nu i)
      (supply.buffer_pos nu i).le le_rfl a x
    have hb := pow_pos (supply.buffer_pos nu i) l
    have hUnweighted : ‖iteratedFDeriv ℝ l eta x‖ ≤
        originalGridCutoffBudget X (supply.mu nu i) (supply.Mb nu i) (supply.buffer nu i) l := by
      apply (le_div_iff₀ hb).mpr
      simpa only [mul_comm] using hh
    exact hUnweighted.trans (Finset.single_le_sum (fun r _ => originalGridCutoffBudget_nonneg X _ _ _
      (supply.mu_pos nu i) (supply.Mb_nonneg nu i) (supply.buffer_pos nu i) r) (by simpa using hlj))
  have hx : x ∈ q.target := ⟨mem_univ _,hxD⟩
  rw [supply.cutoff_eq nu i a,actual_host_cutoff_original_coordinates q thetaN eta k x hx]
  have hh := slow_bilinear_jet_bound_norm (ContinuousLinearMap.mul ℝ ℝ)
    q.target q.open_target (thetaN ∘ q.symm) eta hThetaCoord
    (actualRefinementCutoff_contDiff X _ _ _).contDiffOn k 1 Mt Me zero_le_one x hx
    (fun l hl => by simpa only [one_pow,one_mul] using hParent l (hl.trans hkj))
    (fun l hl => by simpa only [one_pow,one_mul] using hGrid l (hl.trans hkj))
  simp only [one_pow,one_mul] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkj)
      (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg hMt)) hMe

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.original_primary_cutoff_host_prefix
