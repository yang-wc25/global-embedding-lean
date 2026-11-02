import NormalPolar.ActualRepairModelFirstDefectOriginal

/-! A finite bundle of the actual common-array observation choices and
primitive primary profiles. It has no remainder, full-error, normalized
error or repaired-map estimate field. It only avoids repeated elaboration
of the same charts, source samples and signed physical pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M Label SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance obsFirstTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance obsFirstTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance obsFirstTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace
structure ActualRepairModelFirstDefectObservationData (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
  (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ))
  (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
  (phases : Label → Ep × M → ℝ) (R0 Q0 : Label → Ep × M → V) (primary : Ep × M → V)
  (n j length : ℕ) (ell Mg CH delta tau : ℝ) (W : Set (Ep × M))
  (data : ActualSecondarySignedRecord Label → SubSecondary →
    ActualSecondaryPhysicalPieceData (m := m) F hF n (j+1) ell Mg CH delta W)
  (L R : ℕ) (M1 CP : ℝ) (T : ℕ → ℝ) where
  K : Label → Set (Ep × M)
  hprimary : ∀ (rec : ActualSecondarySignedRecord Label) (a : SubSecondary), (data rec a).base.support ⊆ K rec.val.1.1 ∩ K rec.val.1.2
  Omega : Fin atlas.count × Fin count → Set X
  hOmega : ∀ (i : Fin atlas.count × Fin count), IsOpen (Omega i)
  hSample : ∀ (i : Fin atlas.count × Fin count), (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) ⊆ Omega i
  hTarget : ∀ (i : Fin atlas.count × Fin count) z, z ∈ Omega i → z.2 ∈ (atlas.chart i.1).target
  hmap : ∀ (i : Fin atlas.count × Fin count), MapsTo (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) (Omega i) W
  binding : ∀ (i : Fin atlas.count × Fin count), ∀ rec : ActualSecondarySignedRecord Label,
        let H := incrementsSecondaryQuadraticForcing (fun l t x => phases l (t,(atlas.chart i.1).symm x)) tau (fun (_ : Label) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ)) (fun l t (_ : Unit) x => R0 l (t,(atlas.chart i.1).symm x)) (fun l t (_ : Unit) x => Q0 l (t,(atlas.chart i.1).symm x))
          (fun k _ => EuclideanSpace.single k 1) rec.1.1.1 rec.1.1.2 rec.1.2
        ActualSecondaryForcingBinding F hF (fun a => (data rec a).base) ((OpenPartialHomeomorph.refl Ep).prod (atlas.chart i.1))
          (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
          (incrementsSecondaryQuadraticPhase (fun l t x => phases l (t,(atlas.chart i.1).symm x)) rec.1.1.1 rec.1.1.2 rec.1.2)
  O : (Fin atlas.count × Fin count) → ActualSecondarySignedRecord Label → SubSecondary → Set X
  hO : ∀ (i : Fin atlas.count × Fin count) rec a, IsOpen (O i rec a)
  hOOmega : ∀ (i : Fin atlas.count × Fin count) rec a, O i rec a ⊆ Omega i
  hActive : ∀ (i : Fin atlas.count × Fin count) rec a, (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) ∩ (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) ⁻¹' (data rec a).base.support ⊆ O i rec a
  hSource : ∀ (i : Fin atlas.count × Fin count) rec a, MapsTo (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) (O i rec a) (data rec a).base.chart.source
  hTransition : ∀ (i : Fin atlas.count × Fin count) rec a, ContDiffOn ℝ ∞ ((data rec a).base.chart ∘ (fun z : X => (z.1,(atlas.chart i.1).symm z.2))) (O i rec a)
  hT : ∀ k, 0 ≤ T k
  hSecondarySample : ∀ (i : Fin atlas.count × Fin count) rec a z, z ∈ (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) ∩ (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) ⁻¹' (data rec a).base.support →
        (data rec a).base.chart ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z) ∈ (data rec a).base.sample
  hTransitionBound : ∀ (i : Fin atlas.count × Fin count) rec a z, z ∈ (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) ∩ (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) ⁻¹' (data rec a).base.support →
        ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k ((data rec a).base.chart ∘ (fun z : X => (z.1,(atlas.chart i.1).symm z.2))) z‖ ≤ T k
  hL : ∀ (i : Fin atlas.count × Fin count) z, z ∈ (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) → (Finset.univ.filter (fun nu => (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z ∈ K nu)).card ≤ L
  hR : ∀ (i : Fin atlas.count × Fin count) rec z, z ∈ (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) → (Finset.univ.filter (fun a => (fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z ∈ (data rec a).base.support)).card ≤ R
  hM1 : 0 ≤ M1
  hCP : 0 ≤ CP
  hFobs : ∀ (i : Fin atlas.count × Fin count), ContDiffOn ℝ ∞ (fun z : X => F ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z).1 ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z).2) (Omega i)
  hU1 : ∀ (i : Fin atlas.count × Fin count), ContDiffOn ℝ ∞ (primary ∘ (fun z : X => (z.1,(atlas.chart i.1).symm z.2))) (Omega i)
  hLin : ∀ (i : Fin atlas.count × Fin count), ContDiffOn ℝ ∞ (actualJointMetricLinearization
        (fun z : X => F ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z).1 ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z).2) (primary ∘ (fun z : X => (z.1,(atlas.chart i.1).symm z.2)))) (Omega i)
  hMean : ∀ (i : Fin atlas.count × Fin count), ContDiffOn ℝ ∞ (actualPrimaryOppositeMeanTensor (fun l t x => phases l (t,(atlas.chart i.1).symm x)) tau (fun (_ : Label) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ)) (fun l t (_ : Unit) x => R0 l (t,(atlas.chart i.1).symm x)) (fun l t (_ : Unit) x => Q0 l (t,(atlas.chart i.1).symm x))) (Omega i)
  hGrouped : ∀ (i : Fin atlas.count × Fin count) z, z ∈ Omega i → ∀ k,
        fderiv ℝ (fun x => primary ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) (z.1,x))) z.2 (EuclideanSpace.single k 1) =
        incrementsGroupedRealDerivative (fun nu => phases nu (z.1,(atlas.chart i.1).symm z.2)/tau)
          (incrementsSecondaryPhysicalCoefficient (fun l t x => phases l (t,(atlas.chart i.1).symm x)) tau (fun (_ : Label) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ)) (fun l t (_ : Unit) x => R0 l (t,(atlas.chart i.1).symm x)) (fun l t (_ : Unit) x => Q0 l (t,(atlas.chart i.1).symm x))
            (fun k _ => EuclideanSpace.single k 1) z) k
  hU1jet : ∀ (i : Fin atlas.count × Fin count) k, k ≤ j+1 → ∀ z ∈ (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)),
        tau^k*‖iteratedFDeriv ℝ k (primary ∘ (fun z : X => (z.1,(atlas.chart i.1).symm z.2))) z‖ ≤ M1*delta*tau
  hLinJet : ∀ (i : Fin atlas.count × Fin count) k, k ≤ j → ∀ z ∈ (parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)),
        tau^k*‖iteratedFDeriv ℝ k (actualJointMetricLinearization
          (fun z : X => F ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z).1 ((fun z : X => (z.1,(atlas.chart i.1).symm z.2)) z).2) (primary ∘ (fun z : X => (z.1,(atlas.chart i.1).symm z.2)))) z‖ ≤
          CP*delta*tau*(tau/ell)^length


end GlobalEmbedding.Continuation
#check GlobalEmbedding.Continuation.ActualRepairModelFirstDefectObservationData
