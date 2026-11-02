import IncrementsCompletion.PositiveWeightedObserverPointJets

/-!
# One observed order reads only its finite native jet prefix

The older all-order point tool is applied with internally completed
numerical tails.  An unobserved tail entry is the norm of the actual native
jet at the actual single point, never an assumed bound.  Exact positive
prefix congruence then removes every such tail from the final cost.
Thus the statement requires only orders 1 through j of the primitive
native jets and has the same explicit original numerical profiles.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem incrementsCompletion_original_native_observer_finite_weighted_jets_at
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip : Fin Ref.parameterCount) (host : Fin Ref.atlas.count)
    (native : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (slices : Ep → OpenPartialHomeomorph M D)
    (data : ActualOriginalHostSliceData (Ref.atlas.chart host) native psi slices)
    (hNativePreserves : Round3ParameterChartPreserves native)
    (NF NI Parameter Spatial : ℕ → ℝ)
    (hNF : ∀ k, 1 ≤ k → 0 ≤ NF k) (hNI : ∀ k, 1 ≤ k → 0 ≤ NI k)
    (hParameter : ∀ k, 1 ≤ k → 0 ≤ Parameter k) (hSpatial : ∀ k, 1 ≤ k → 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (z : X)
    (hp : z.1 ∈ Ref.parameterNormDomain i.2) (hx : z.2 ∈ Ref.sourceNormDomain i.1)
    (hOwnP : Ref.parameterChart ip ((Ref.parameterChart i.2).symm z.1) ∈ Ref.parameterNormDomain ip)
    (hOwnX : Ref.atlas.chart host ((Ref.atlas.chart i.1).symm z.2) ∈ Ref.sourceNormDomain host)
    (j : ℕ) (hj : 1 ≤ j)
    (hForward : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k native (incrementsCompletionOriginalHostPoint Ref ip host i z)‖ ≤ NF k)
    (hInverse : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k native.symm
        (native (incrementsCompletionOriginalHostPoint Ref ip host i z))‖ ≤ NI k) :
    let b := round3ParameterCrossNativeChart (Ref.parameterChart ip) (Ref.parameterChart i.2) native
    let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans
      (actualHostAdaptedChart (Ref.atlas.chart host) b)
    z ∈ t.source →
      ell^(j-1)*‖iteratedFDeriv ℝ j t z‖ ≤ incrementsCompletionPositiveObserverForwardProfile NF Parameter Spatial j ∧
      ell^(j-1)*‖iteratedFDeriv ℝ j t.symm (t z)‖ ≤ incrementsCompletionPositiveObserverInverseProfile NI Parameter Spatial j := by
  intro b t hz
  let point := incrementsCompletionOriginalHostPoint Ref ip host i z
  let NFx := fun k => if k ≤ j then NF k else ell^(k-1)*‖iteratedFDeriv ℝ k native point‖
  let NIx := fun k => if k ≤ j then NI k else ell^(k-1)*‖iteratedFDeriv ℝ k native.symm (native point)‖
  have hNFx (k : ℕ) (hk : 1 ≤ k) : 0 ≤ NFx k := by
    dsimp only [NFx]
    split_ifs
    · exact hNF k hk
    · exact mul_nonneg (pow_nonneg hell.le _) (norm_nonneg _)
  have hNIx (k : ℕ) (hk : 1 ≤ k) : 0 ≤ NIx k := by
    dsimp only [NIx]
    split_ifs
    · exact hNI k hk
    · exact mul_nonneg (pow_nonneg hell.le _) (norm_nonneg _)
  have hForwardAll (k : ℕ) (hk : 1 ≤ k) :
      ell^(k-1)*‖iteratedFDeriv ℝ k native point‖ ≤ NFx k := by
    dsimp only [NFx]
    split_ifs with hkj
    · exact hForward k hk hkj
    · exact le_rfl
  have hInverseAll (k : ℕ) (hk : 1 ≤ k) :
      ell^(k-1)*‖iteratedFDeriv ℝ k native.symm (native point)‖ ≤ NIx k := by
    dsimp only [NIx]
    split_ifs with hkj
    · exact hInverse k hk hkj
    · exact le_rfl
  have hActual := incrementsCompletion_original_native_observer_weighted_point_jets_at
    Ref hd ip host native psi slices data hNativePreserves NFx NIx Parameter Spatial
    hNFx hNIx hParameter hSpatial transition ell hell hell1 i z hp hx hOwnP hOwnX
    hForwardAll hInverseAll hz j hj
  have hCost := incrementsCompletionPositiveObserverProfiles_prefix_congr
    NFx NIx Parameter Spatial NF NI Parameter Spatial j
    (fun k _ hkj => if_pos hkj) (fun k _ hkj => if_pos hkj)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hCost.1,hCost.2] at hActual
  exact hActual

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_native_observer_finite_weighted_jets_at
