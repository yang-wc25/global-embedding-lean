import NormalPolar.ActualProbeInitialSupplyPaddedRehost
import NormalPolar.PassiveRawBudget

/-! One numerical background budget for all original observers and every
actual signed host.  The finite costs are fixed before contraction, input,
orders and reconstruction scales.  The primary scalar representation also
fits this same budget. Every output record is the genuine rehosted original
background on the same padded source and sample. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P Tr Β Rec : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Β] [Fintype Rec] [DecidableEq Rec]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem actualProbeInitialSupply_signed_atlas_background_uniform
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i))
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (phase : Rec → M → ℝ) (K O : Rec → Set M)
    (seeds : (rec : Rec) → JointSecondarySignedSeed («Ep» := Ep) F0 hF0 (phase rec) (K rec) (O rec)) :
    ∃ C : ℕ → ℕ → ℝ → ℝ, ∃ Tcost : ℕ → ℝ,
      (∀ k, 0 ≤ Tcost k) ∧
      (∀ n j B, 0 ≤ B → 0 ≤ C n j B ∧ actualProbeRawScalarCost n j B ≤ C n j B) ∧
      ∀ (i : Fin Data.atlas.count × Fin Data.parameterCount),
      let B := Data.parameterChart i.2
      let Q := Data.parameterNormDomain i.2
      let hQT := hd.parameter_norm_subset i.2
      let Spatial := passiveOriginalSpatialNormSample Data i.1
      let W := round3ParameterNativeDomain B (univ : Set (P × M))
      let Sold := (parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet i
      ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
        (nG jG n length j Rsub Lprimary : ℕ)
        (reserve Bnd Mg : ℝ) (hBnd : 0 ≤ Bnd)
        (Tbackground : ℕ → ℝ) (hTbackground : ∀ k, 0 ≤ Tbackground k)
        (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N)
          (Λ := Fin Data.primaryCount) (Β := Β) (fun _ : Ep => scale • F0)),
        (∀ nu, g.cutoff nu = fun z => Data.cutoff nu (B.symm z.1,z.2)) →
        (∀ nu, g.phase nu = fun z => Data.phase nu (B.symm z.1,z.2)) →
        ∀ (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
        (primary : Fin Data.primaryCount → Set (Ep × M))
        (Oold : Set X) (tau ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1),
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
          reserve Bnd Mg Tbackground (fun _ : Ep => scale • F0)
          (fun _ => contMDiff_const_rescale F0 hF0 scale) g input input W primary
          (Data.atlas.chart i.1) Oold Sold tau ell 0 →
        ∀ rec s, Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
          reserve (C n j Bnd) Mg
          (fun k => Tbackground k+Tcost k*bufferedTransitionPrefix Tbackground k)
          (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
          g input input W primary (jointSecondarySeedPaddedChoice (P := P) seeds rec s).host
          (jointSecondarySignedNativeHostTransition seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).source
          ((jointSecondarySignedNativeHostTransition seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).symm ''
            (jointSecondarySignedNativeRaw seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).sample)
          tau ell 0) := by
  let Idx := (Fin Data.atlas.count × Fin Data.parameterCount) ×
    (Σ rec, Fin (seeds rec).refinement.count)
  choose Cs Ts hTs hCs hProduce using fun idx : Idx =>
    actualProbeInitialSupply_padded_rehost_uniform (Tr := Tr) (Β := Β)
      Data hd hs hAll idx.1 (hQ idx.1.2) (hOmega idx.1.1) F0 hF0 phase K O seeds idx.2
  let C := fun n j B => actualProbeRawScalarCost n j B+∑ idx : Idx, Cs idx n j B
  let Tcost := fun k => ∑ idx : Idx, actualFastChartTransferPrefix (Ts idx) k
  have hTc k : 0 ≤ Tcost k := Finset.sum_nonneg (fun idx _ =>
    actualFastChartTransferPrefix_nonneg (Ts idx) (hTs idx) k)
  have hCsSum n j B (hB : 0 ≤ B) : 0 ≤ ∑ idx : Idx, Cs idx n j B :=
    Finset.sum_nonneg (fun idx _ => hCs idx n j B hB)
  refine ⟨C,Tcost,hTc,?_,?_⟩
  · intro n j B hB
    exact ⟨add_nonneg (actualProbeRawScalarCost_nonneg n j B hB) (hCsSum n j B hB),
      le_add_of_nonneg_right (hCsSum n j B hB)⟩
  intro i B Q hQT Spatial W Sold scale hscale nG jG n length j Rsub Lprimary reserve Bnd Mg hBnd
    Tbackground hTbackground g hCutoff hPhase input primary Oold tau ell hell hell1 raw rec s
  let idx : Idx := (i,s)
  obtain ⟨single⟩ := hProduce idx scale hscale nG jG n length j Rsub Lprimary reserve Bnd Mg hBnd
    Tbackground hTbackground g hCutoff hPhase input primary Oold tau ell hell hell1 raw rec
  have hBudget : Cs idx n j Bnd ≤ C n j Bnd := by
    have hsum : Cs idx n j Bnd ≤ ∑ idx' : Idx, Cs idx' n j Bnd := Finset.single_le_sum
      (fun idx' _ => hCs idx' n j Bnd hBnd) (Finset.mem_univ idx)
    exact hsum.trans (le_add_of_nonneg_left (actualProbeRawScalarCost_nonneg n j Bnd hBnd))
  have hTransition k : actualFastChartTransferPrefix (Ts idx) k*bufferedTransitionPrefix Tbackground k ≤
      Tbackground k+Tcost k*bufferedTransitionPrefix Tbackground k := by
    have hsum : actualFastChartTransferPrefix (Ts idx) k ≤ Tcost k := Finset.single_le_sum
      (fun idx' _ => actualFastChartTransferPrefix_nonneg (Ts idx') (hTs idx') k) (Finset.mem_univ idx)
    exact (mul_le_mul_of_nonneg_right hsum
      (zero_le_one.trans (one_le_bufferedTransitionPrefix hTbackground k))).trans
      (le_add_of_nonneg_left (hTbackground k))
  exact ⟨single.enlargeBudgets (C n j Bnd) Mg
    (fun k => Tbackground k+Tcost k*bufferedTransitionPrefix Tbackground k)
    hBudget le_rfl hTransition⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_signed_atlas_background_uniform
