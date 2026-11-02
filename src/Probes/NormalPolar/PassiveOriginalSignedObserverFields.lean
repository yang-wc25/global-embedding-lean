import NormalPolar.PassiveRawObserverPhase

/-! All new-host elementary fields on the actual signed compact samples.
The original parameter and spatial norm domains are retained. The only
input bounds here are compactness and original primitive smoothness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

variable {phase : M → ℝ} {K O : Set M}
  {ref : JointSecondarySignedRefinement (m := m) phase K O} {ib : Fin ref.count}

theorem passiveOriginal_signed_observer_field_domain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hAll : Data.parameterSet = univ)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (b b' : JointSecondarySignedBuffer ref ib)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget)
    (Q : Set Ep) (hQ : IsCompact Q) (hQQ : Q ⊆ Data.parameterNormDomain i.2)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ (Data.atlas.chart i.1).source)
    (hSS : (Data.atlas.chart i.1) '' S ⊆ Data.sourceNormDomain i.1) :
    passiveOriginalSignedObserverSample Data nu i b b' Q S ⊆
      passiveOriginalObserverFieldDomain Data nu i.2 b'.chart := by
  have hs := passiveOriginal_signed_observer_samples Data hd hAll nu i b b' hbb
    Q hQ hQQ S hS hSe hSS
  intro z hz
  have hzO := hs.2.1 hz
  have hprim := (hs.2.2 hz).2
  change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
    (passiveOriginalObserverCoordinates (Data.atlas.chart i.1) b'.chart z) ∈
      Data.primaryDomain nu at hprim
  rw [passiveOriginalObserverCoordinates_point Data.atlas Data.parameterChart i b'.chart z hzO] at hprim
  exact ⟨⟨hzO.1,hzO.2.1⟩,hprim,
    hd.parameter_subset (by rw [hAll]; exact mem_univ _),mem_univ _⟩

theorem passiveOriginal_signed_observer_fields
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (b b' : JointSecondarySignedBuffer ref ib)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget)
    (Q : Set Ep) (hQ : IsCompact Q) (hQQ : Q ⊆ Data.parameterNormDomain i.2)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ (Data.atlas.chart i.1).source)
    (hSS : (Data.atlas.chart i.1) '' S ⊆ Data.sourceNormDomain i.1) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ nu n k, k ≤ n →
        ∀ z ∈ passiveOriginalSignedObserverSample Data nu i b b' Q S,
          ell^k*‖iteratedFDeriv ℝ k (fun w : X => Data.cutoff nu
            ((Data.parameterChart i.2).symm w.1,b'.chart.symm w.2)) z‖ ≤ C n ∧
          ell^k*‖iteratedFDeriv ℝ k (fun w : X => Data.freeNormal nu
            ((Data.parameterChart i.2).symm w.1,b'.chart.symm w.2)) z‖ ≤ C n ∧
          ∀ r : Fin (m+1), ell^k*‖iteratedFDeriv ℝ k
            (fun w : X => fderiv ℝ (fun y => Data.phase nu
              ((Data.parameterChart i.2).symm w.1,b'.chart.symm y)) w.2
                (EuclideanSpace.single r 1)) z‖ ≤ C n := by
  let R := fun nu => passiveOriginalSignedObserverSample Data nu i b b' Q S
  have hRc nu : IsCompact (R nu) := (passiveOriginal_signed_observer_samples
    Data hd hAll nu i b b' hbb Q hQ hQQ S hS hSe hSS).1
  have hRO nu : R nu ⊆ passiveOriginalObserverFieldDomain Data nu i.2 b'.chart :=
    passiveOriginal_signed_observer_field_domain Data hd hAll nu i b b' hbb
      Q hQ hQQ S hS hSe hSS
  have hf nu := passiveOriginal_observer_fields Data hd hs nu i.2 b'.chart
    b'.maximal (R nu) (hRc nu) (hRO nu)
  choose C hC hCb using fun nu => (hf nu).2.2.2.2.2
  refine ⟨fun n => ∑ nu, C nu n,fun n => Finset.sum_nonneg (fun nu _ => (hC nu n).le),?_⟩
  intro ell hell hell1 nu n k hk z hz
  have hsum : C nu n ≤ ∑ mu, C mu n := Finset.single_le_sum
    (fun mu _ => (hC mu n).le) (Finset.mem_univ nu)
  have hb := hCb nu ell hell hell1 n k hk z hz
  refine ⟨hb.1.trans hsum,hb.2.1.trans hsum,?_⟩
  intro r
  have heval := norm_iteratedFDeriv_clm_apply_const
    ((hf nu).2.2.2.2.1.contDiffAt ((hf nu).1.mem_nhds (hRO nu hz)))
    (n := k) (c := EuclideanSpace.single r (1:ℝ)) (by simp)
  have hnorm : ‖EuclideanSpace.single r (1:ℝ)‖ = 1 := by simp
  rw [hnorm,one_mul] at heval
  exact ((mul_le_mul_of_nonneg_left heval (pow_nonneg hell k)).trans hb.2.2).trans hsum

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_signed_observer_field_domain
#print axioms GlobalEmbedding.Continuation.passiveOriginal_signed_observer_fields
