import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility
import NormalPolar.PassiveParameterSupport

/-!
# Original primitive data on the actual compact parameter manifold

The source atlas, its enlarged norm domains, the supplied phase labels,
cutoffs, free normals and tensor functionals are retained literally from a
one-point seed.  Only the auxiliary parameter manifold is enlarged, using
the given smooth finite parameter atlas and its actual norm samples.
The parameter set and parameter open are both the whole new manifold.
This construction supplies original data, never a finished increment or an
estimate for a solver output.  Source supports and overlap counts are exact.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d₀ d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [TopologicalSpace P]

/-- Actual passive extension of the original native fields. -/
def passiveOriginalData (s₀ : S) (seed : IncrementsOriginalNativeData n d₀ N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d))) :
    IncrementsOriginalNativeData n d N M P where
  atlas := seed.atlas
  sourceNormDomain := seed.sourceNormDomain
  parameterCount := B.count
  parameterChart := B.chart
  parameterNormDomain := Q
  parameterSet := univ
  parameterOpen := univ
  F := fun z => seed.F (s₀,z.2)
  H := fun _ => seed.H s₀
  reference := fun _ => seed.reference s₀
  primaryCount := seed.primaryCount
  phase := fun l z => seed.phase l (s₀,z.2)
  cutoff := fun l z => seed.cutoff l (s₀,z.2)
  freeNormal := fun l z => seed.freeNormal l (s₀,z.2)
  primaryDomain := fun l => (fun z : P × M => (s₀,z.2)) ⁻¹' seed.primaryDomain l
  linearArgument := fun l _ => seed.linearArgument l s₀
  tensorNeighborhood := fun _ => seed.tensorNeighborhood s₀

theorem passiveOriginalData_parameterRegion (s₀ : S)
    (seed : IncrementsOriginalNativeData n d₀ N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hs₀ : s₀ ∈ seed.parameterOpen) :
    (fun z : P × M => (s₀,z.2)) ⁻¹' incrementsOriginalParameterRegion seed =
      incrementsOriginalParameterRegion (passiveOriginalData s₀ seed B Q) := by
  ext z
  simp only [incrementsOriginalParameterRegion,passiveOriginalData,mem_preimage,
    mem_prod,mem_univ,and_true,true_and,hs₀]

theorem passiveOriginalData_support_iff [Subsingleton S]
    (s₀ : S) (seed : IncrementsOriginalNativeData n d₀ N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hs₀ : s₀ ∈ seed.parameterOpen) (l : Fin seed.primaryCount) (b : P) (x : M) :
    (b,x) ∈ incrementsOriginalRelativeCutoffSupport (passiveOriginalData s₀ seed B Q) l ↔
      (s₀,x) ∈ incrementsOriginalRelativeCutoffSupport seed l := by
  have h := passiveParameter_relativeSupport_iff (P := P) s₀
    (incrementsOriginalParameterRegion seed) (seed.cutoff l) b x
  rw [passiveOriginalData_parameterRegion s₀ seed B Q hs₀] at h
  exact h

theorem passiveOriginalData_overlap [Subsingleton S]
    (s₀ : S) (seed : IncrementsOriginalNativeData n d₀ N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hs₀ : s₀ ∈ seed.parameterOpen) (b : P) (x : M) :
    (Finset.univ.filter (fun l =>
      (b,x) ∈ incrementsOriginalRelativeCutoffSupport (passiveOriginalData s₀ seed B Q) l)).card =
    (Finset.univ.filter (fun l =>
      (s₀,x) ∈ incrementsOriginalRelativeCutoffSupport seed l)).card := by
  exact congrArg (fun pred : Fin seed.primaryCount → Prop => (Finset.univ.filter pred).card)
    (funext fun l => propext (passiveOriginalData_support_iff s₀ seed B Q hs₀ l b x))

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d₀)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d₀)) ∞ S]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The actual full parameter domain is valid for every compact P.  All
source atlas fields and source norm sets are literally unchanged. -/
theorem passiveOriginalData_domain [Subsingleton S] [CompactSpace P]
    (s₀ : S) (seed : IncrementsOriginalNativeData n d₀ N M S)
    (hd : IncrementsOriginalDomainConditions seed) (hs₀ : s₀ ∈ seed.parameterOpen)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ b, Q b ⊆ (B.chart b).target)
    (hInner : ∀ b p, p ∈ B.inner b → B.chart b p ∈ Q b) :
    IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q) where
  source_dim := hd.source_dim
  target_dim := hd.target_dim
  parameter_open := isOpen_univ
  parameter_compact := isCompact_univ
  parameter_subset := Subset.rfl
  atlas_smooth := hd.atlas_smooth
  parameter_charts_smooth := hB.chart_mem
  source_norm_subset := hd.source_norm_subset
  source_inner_norm := hd.source_inner_norm
  parameter_norm_subset := hQ
  parameter_cover := by
    intro p _
    obtain ⟨b,hb⟩ := B.cover p
    exact ⟨b,B.inner_subset b hb,hInner b p hb⟩
  primary_open := fun l => (hd.primary_open l).preimage (continuous_const.prodMk continuous_snd)
  cutoff_support_local := by
    intro l z hz
    exact hd.cutoff_support_local l
      ((passiveOriginalData_support_iff s₀ seed B Q hs₀ l z.1 z.2).mp hz)

/-- Actual source phase covectors are unchanged. This includes their real
native tangent spaces and the original source-only differentiation. -/
theorem passiveOriginalData_phaseCovector (s₀ : S)
    (seed : IncrementsOriginalNativeData n d₀ N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (l : Fin seed.primaryCount) (b : P) (x : M) :
    incrementsOriginalPhaseCovector (passiveOriginalData s₀ seed B Q) l b x =
      incrementsOriginalPhaseCovector seed l s₀ x := rfl

/-- Canonical GoodCovector conditions retain the supplied primary, doubled
and signed interacting phases, with the original label identities. -/
theorem passiveOriginalData_phaseConditions [Subsingleton S]
    (s₀ : S) (seed : IncrementsOriginalNativeData n d₀ N M S)
    (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
    (hg : IncrementsOriginalPhaseConditions seed hd hs) (hs₀ : s₀ ∈ seed.parameterOpen)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))
    (hsP : IncrementsOriginalSmoothInputs (passiveOriginalData s₀ seed B Q)) :
    IncrementsOriginalPhaseConditions (passiveOriginalData s₀ seed B Q) hdP hsP where
  primary_good := fun l z hz => hg.primary_good l (s₀,z.2) ⟨hz.1,hs₀,mem_univ _⟩
  doubled_good := fun l z hz => hg.doubled_good l (s₀,z.2) ⟨hz.1,hs₀,mem_univ _⟩
  interaction_good := by
    intro l k hlk sign z hz
    exact hg.interaction_good l k hlk sign (s₀,z.2)
      ⟨(passiveOriginalData_support_iff s₀ seed B Q hs₀ l z.1 z.2).mp hz.1,
        (passiveOriginalData_support_iff s₀ seed B Q hs₀ k z.1 z.2).mp hz.2⟩

/-- The supplied Euclidean unit free normals are retained; no new choice of
a normal or change of its norm is made. -/
theorem passiveOriginalData_freeNormalConditions (s₀ : S)
    (seed : IncrementsOriginalNativeData n d₀ N M S)
    (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
    (hn : IncrementsOriginalFreeNormalConditions seed hd hs) (hs₀ : s₀ ∈ seed.parameterOpen)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))
    (hsP : IncrementsOriginalSmoothInputs (passiveOriginalData s₀ seed B Q)) :
    IncrementsOriginalFreeNormalConditions (passiveOriginalData s₀ seed B Q) hdP hsP where
  unit := fun l z hz => hn.unit l (s₀,z.2) ⟨hz.1,hs₀,mem_univ _⟩
  normal := fun l z hz => hn.normal l (s₀,z.2) ⟨hz.1,hs₀,mem_univ _⟩
  free := fun l z hz u v => hn.free l (s₀,z.2) ⟨hz.1,hs₀,mem_univ _⟩ u v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalData
#print axioms GlobalEmbedding.Continuation.passiveOriginalData_domain
#print axioms GlobalEmbedding.Continuation.passiveOriginalData_phaseConditions
#print axioms GlobalEmbedding.Continuation.passiveOriginalData_freeNormalConditions
