import OriginalCollars.OriginalObserverCutoffBudget

/-!
# Literal primary packets realize the explicit original-observer cutoff profile

The finite maximum contains only the raw-parent/grid formula and original
transition budgets.  Each physical scalar is the one in the actual packet;
conditioning preserves it pointwise.  Original evaluation domains are not
replaced by host compact sets, and no observed derivative is an input field.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalCollars
open OriginalIncrements

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

theorem lifted_primary_cutoff_host_jet_identity
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (piece : Round3PreparedPrimaryPiece Data i.2 nu W)
    (k : ℕ) (x : X)
    (hxP : x.1 ∈ (Data.parameterChart i.2).target) (hxD : x.2 ∈ (Data.atlas.chart i.1).target) :
    iteratedFDeriv ℝ k
      (round3ParameterLiftedPrimaryCutoff Data i.2 nu W piece ∘
        ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm) x =
      iteratedFDeriv ℝ k
        (piece.cutoff ∘ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x := by
  let q := (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  have hx : x ∈ q.target := ⟨hxP,hxD⟩
  have hEq : (round3ParameterLiftedPrimaryCutoff Data i.2 nu W piece ∘ q.symm) =ᶠ[𝓝 x]
      (piece.cutoff ∘ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) := by
    filter_upwards [q.open_target.mem_nhds hx] with w hw
    change round3ParameterLiftedPrimaryCutoff Data i.2 nu W piece
      ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2) =
        piece.cutoff (w.1,(Data.atlas.chart i.1).symm w.2)
    rw [round3ParameterLiftedPrimaryCutoff_eq]
    rw [ite_eq_left ((Data.parameterChart i.2).map_target hw.1),
      (Data.parameterChart i.2).right_inv hw.1]
  exact (hEq.iteratedFDeriv ℝ k).eq_of_nhds

private local instance originalCutoffProductChart : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P D M
private local instance originalCutoffProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem original_primary_family_cutoff_host_prefix
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
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
      (_hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)),
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta supply.packet
    ∀ (nu : Fin Data.primaryCount) (beta : Round3ParameterWholePrimaryIndex Data theta supply.packet)
      (j k : ℕ), k ≤ j → ∀ x : X,
      x.1 ∈ (Data.parameterChart beta.1.2).target →
      x.2 ∈ (Data.atlas.chart beta.1.1).target →
      (Data.parameterChart beta.1.2).symm x.1 ∈ Data.parameterSet →
      ‖iteratedFDeriv ℝ k (g.eta nu beta ∘
        ((Data.parameterChart beta.1.2).prod (Data.atlas.chart beta.1.1)).symm) x‖ ≤
        originalParentGridHostCutoffProfile m d (supply.mu nu beta.1) (supply.Mb nu beta.1)
          (supply.buffer nu beta.1) BS TS BP TP Ds Dp j := by
  intro theta supply hCompact hSmooth g nu beta j k hkj x hxP hxD hxK
  rcases beta with ⟨i,mu,a⟩
  rw [round3ParameterWholePrimaryFamily_eta]
  by_cases h : mu = nu
  · subst mu
    simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active]
    rw [lifted_primary_cutoff_host_jet_identity Data i nu _ (supply.packet.piece nu i a) k x hxP hxD]
    exact original_primary_cutoff_host_prefix Data hd BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart
      RS RP psi V hV hKV hOne supply hCompact hSmooth nu i a j k hkj x hxP hxD hxK
  · simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,h,dite_false,
      round3ParameterLiftedPrimaryCutoff_empty,Function.comp_def,Pi.zero_apply,
      iteratedFDeriv_fun_zero,norm_zero]
    exact originalParentGridHostCutoffProfile_nonneg m d _ _ _ (supply.mu_pos nu i)
      (supply.Mb_nonneg nu i) (supply.buffer_pos nu i) BS TS BP TP hBS hTS hBP hTP Ds Dp j

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.original_primary_family_cutoff_host_prefix
