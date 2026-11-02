import NormalPolar.ParameterDisplacementFirstIncrementRawJets
import NormalPolar.ActualRepairModelFirstDefectMapCharts

/-! Actual primitive observations for the SAME complete first increment.
The samples are the true inverse-parameter-chart images of the original
compact samples. No completed wave, increment, or norm estimate is a field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M Tr Λ Β SubSecondary : Type*}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

structure ActualRepairModelFirstDefectIncrementProfiles
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (n backgroundLength j Rbackground L Rsecondary : ℕ)
    (reserve Bnd Mg CH Bchi Bnu Mphase tau ell delta Delta : ℝ)
    (Tbackground Tprobe Tsecondary : ℕ → ℝ)
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+2) ell Mg CH delta W)
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ)) where
  domains : Fin A.count × Fin count → Set X
  background : ∀ i : Fin A.count × Fin count,
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n backgroundLength (j+1) Rbackground L
      reserve Bnd Mg Tbackground F hF g input inputbar W (fun l => K (Sum.inl l)) (A.chart i.1)
      (domains i) (parameterRound2_meanParameterMap (m := m) (B i.2) ''
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) tau ell Delta
  adaptation : ∀ l q z, z ∈ (g.chart l q).source → g.phase l z = (g.chart l q z).2 0
  observer_smooth : ∀ i : Fin A.count × Fin count,
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞
      (fun z : X => (z.1,(A.chart i.1).symm z.2)) (domains i)
  prescribed : ∀ i : Fin A.count × Fin count,
    ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
      n (j+2) ell Mg Bchi Bnu (fun z : X => (z.1,(A.chart i.1).symm z.2))
      (domains i) (parameterRound2_meanParameterMap (m := m) (B i.2) ''
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) Tprobe phase Mphase
  secondary : ∀ i : Fin A.count × Fin count,
    ActualSecondaryRawObservationProfiles F hF n (j+2) ell Mg CH delta W data
      (fun z : X => (z.1,(A.chart i.1).symm z.2)) (domains i)
      (parameterRound2_meanParameterMap (m := m) (B i.2) ''
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) K Tsecondary L Rsecondary

end GlobalEmbedding.Continuation
#check GlobalEmbedding.Continuation.ActualRepairModelFirstDefectIncrementProfiles
