import NormalPolar.ActualRepairModelChart

/-!
# Pure spatial norms of the same actual joint-coordinate repair

Parameter order zero is retained in the original mixed norm. Consequently
fixing an actual parameter coordinate bounds every original spatial Cj
norm with constant one, including the C3 norm needed by the probe theorem.
-/

noncomputable section
open Set Filter Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n d N : ℕ}

theorem actualRepairModel_spatial_Cj_le_mixed
    (j : ℕ) (f : (Fin (n+d) → ℝ) → Fin N → ℝ)
    (O S : Set (Fin (n+d) → ℝ)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O)
    (u : Fin d → ℝ) (Ox Sx : Set (Fin n → ℝ)) (hOx : IsOpen Ox)
    (hsource : Ox ⊆ actualRepairModelSlice u O) (hSx : Sx ⊆ Ox)
    (hsample : ∀ x ∈ Sx, sourceFirstCoordinates n d (u,x) ∈ S) :
    paperCoordinateCj j (fun x => f (sourceFirstCoordinates n d (u,x))) Ox Sx ≤
      paperMixedCoordinateCj (nx := n) (np := d) j 0 f O S := by
  refine iSup_le fun l => iSup_le fun x => iSup_le fun c => ?_
  rw [actualRepairModel_partial_open_domain l.val _ hOx (actualRepairModelSlice_open u hO)
    x (hSx x.property) (hsource (hSx x.property))]
  rw [actualRepairModel_source_partial (fun y => f y c) O hO
    ((contDiffOn_pi.mp hf) c) u l.val x (hsource (hSx x.property))]
  simpa only [List.map_nil,List.append_nil] using
    paper_mixed_partial_le f O S l.val [] l.property.2 (by simp)
      ⟨sourceFirstCoordinates n d (u,x),hsample x x.property⟩ c

variable {c : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local instance actualRepairModelSliceNormProduct : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelSliceNormManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- The whole-source spatial norm is controlled in the original sampling
atlas. This includes order zero and does not discard lower-order terms. -/
theorem actualRepairModelChartFamily_spatial_le_mixed
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : Fin c → OpenPartialHomeomorph P Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQ : ∀ b, Q b ⊆ (B b).target)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (b : Fin c) (u : Fin d → ℝ)
    (hu : u ∈ (EuclideanSpace.equiv (Fin d) ℝ) '' Q b) (j : ℕ) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) j (actualRepairModelChartFamily (B b) F u) ≤
      ⨆ i, paperMixedCoordinateCj (nx := n) (np := d) j 0
        (incrementsOriginalMapCoordinates A B F i)
        (incrementsOriginalDifferentiation A B i)
        (incrementsOriginalEvaluation A B Omega Q univ i) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let ex := EuclideanSpace.equiv (Fin n) ℝ
  have huQ : e.symm u ∈ Q b := by
    rcases hu with ⟨p,hp,rfl⟩
    simpa only [e,ContinuousLinearEquiv.symm_apply_apply] using hp
  rw [actualRepairSamplingAtlas_probeAtlasCj A Omega hOmega j]
  apply iSup_le
  intro i
  have hsource : ex '' (A.chart i).target ⊆
      actualRepairModelSlice u (incrementsOriginalDifferentiation A B (i,b)) := by
    rintro _ ⟨x,hx,rfl⟩
    change incrementsOriginalSourcePoint (sourceFirstCoordinates n d (u,ex x)) ∈ (A.chart i).target ∧
      incrementsOriginalParameterPoint (sourceFirstCoordinates n d (u,ex x)) ∈ (B b).target
    simpa only [actualRepairModel_sourcePoint,actualRepairModel_parameterPoint,
      ex,ContinuousLinearEquiv.symm_apply_apply] using And.intro hx (hQ b huQ)
  have hsample : ∀ x ∈ ex '' Omega i,
      sourceFirstCoordinates n d (u,x) ∈ incrementsOriginalEvaluation A B Omega Q univ (i,b) := by
    rintro _ ⟨x,hx,rfl⟩
    simp only [incrementsOriginalEvaluation,incrementsOriginalDifferentiation,
      actualRepairModel_sourcePoint,actualRepairModel_parameterPoint,ex,
      ContinuousLinearEquiv.symm_apply_apply,mem_ofPred_eq,mem_univ,and_true]
    exact ⟨⟨hOmega i hx,hQ b huQ⟩,hx,huQ⟩
  have h := actualRepairModel_spatial_Cj_le_mixed j
    (incrementsOriginalMapCoordinates A B F (i,b))
    (incrementsOriginalDifferentiation A B (i,b))
    (incrementsOriginalEvaluation A B Omega Q univ (i,b))
    (parameterRound2_originalDifferentiation_open A B (i,b))
    (parameterRound2_originalMapCoordinates_contDiffOn A B hA hB F hF (i,b))
    u (ex '' (A.chart i).target) (ex '' Omega i)
    (ex.toHomeomorph.isOpenMap _ (A.chart i).open_target) hsource
    (image_mono (hOmega i)) hsample
  simp only [actualRepairModelChartFamily_coordinates] at h
  exact h.trans (le_iSup (fun k => paperMixedCoordinateCj (nx := n) (np := d) j 0
    (incrementsOriginalMapCoordinates A B F k) (incrementsOriginalDifferentiation A B k)
    (incrementsOriginalEvaluation A B Omega Q univ k)) (i,b))

/-- The same comparison to the original TOTAL-order norm uses order j,
not j+1. In particular the repair's order-three entrance controls spatial C3. -/
theorem actualRepairModelChartFamily_spatial_le_total
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : Fin c → OpenPartialHomeomorph P Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQ : ∀ b, Q b ⊆ (B b).target)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (b : Fin c) (u : Fin d → ℝ)
    (hu : u ∈ (EuclideanSpace.equiv (Fin d) ℝ) '' Q b) (j : ℕ) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) j (actualRepairModelChartFamily (B b) F u) ≤
      paperAtlasCj j (incrementsOriginalMapCoordinates A B F)
        (incrementsOriginalDifferentiation A B)
        (incrementsOriginalEvaluation A B Omega Q univ) := by
  apply (actualRepairModelChartFamily_spatial_le_mixed A hA B hB Omega Q hOmega hQ F hF b u hu j).trans
  apply iSup_le
  intro i
  have h := paperMixedCoordinateCj_le_total j 0 (incrementsOriginalMapCoordinates A B F i)
    (incrementsOriginalDifferentiation A B i)
    (incrementsOriginalEvaluation A B Omega Q univ i)
    (parameterRound2_originalDifferentiation_open A B i) (fun _ hx => hx.1)
    (parameterRound2_originalMapCoordinates_contDiffOn A B hA hB F hF i)
  exact h.trans (le_iSup (fun k => paperCoordinateCj j
    (incrementsOriginalMapCoordinates A B F k) (incrementsOriginalDifferentiation A B k)
    (incrementsOriginalEvaluation A B Omega Q univ k)) i)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModelChartFamily_spatial_le_total
