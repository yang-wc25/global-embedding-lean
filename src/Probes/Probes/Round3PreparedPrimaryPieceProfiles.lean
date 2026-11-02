import Probes.Round3PreparedPrimaryPiece
import Probes.Round3PreparedCompactProfiles

/-! All-order primary inverse, forward and cutoff profiles are produced on
the actual compact support of one fixed piece. They precede every scale and
order. No original evaluation domain is assumed equal to an open inner chart. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_primary_piece_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) :
    ∃ Tinv Forward Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Tinv k) ∧ (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Meta k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ k y, y ∈ tsupport piece.cutoff →
        (ell^(k-1)*‖iteratedFDeriv ℝ k piece.native.symm
          (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native y)‖ ≤ Tinv k) ∧
        (ell^(k-1)*‖iteratedFDeriv ℝ k piece.native
          (actualOriginalHostJointChart (Data.atlas.chart piece.host) y)‖ ≤ Forward k) ∧
        ell^k*‖iteratedFDeriv ℝ k
          (piece.cutoff ∘ (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native).symm)
          (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native y)‖ ≤ Meta k := by
  let c := Data.atlas.chart piece.host
  let b := piece.native
  let a := actualHostAdaptedChart c b
  let q := actualOriginalHostJointChart («Ep» := Ep) c
  have hg := actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem piece.host) b
    (fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2)) piece.slices piece.data
  let Ka := a '' tsupport piece.cutoff
  let Kq := q '' tsupport piece.cutoff
  have hKa : IsCompact Ka := piece.compact.image_of_continuousOn (a.continuousOn.mono piece.support)
  have hKq : IsCompact Kq := piece.compact.image_of_continuousOn
    (q.continuousOn.mono (fun _ hz => (piece.support hz).1))
  have hKaTarget : Ka ⊆ b.target := by
    rintro _ ⟨y,hy,rfl⟩
    rw [← piece.data.1]
    exact a.map_source (piece.support hy)
  have hKqSource : Kq ⊆ b.source := by
    rintro _ ⟨y,hy,rfl⟩
    exact (piece.support hy).2
  have hEta : ContDiffOn ℝ ∞ (piece.cutoff ∘ a.symm) b.target :=
    (piece.smooth.comp_contMDiffOn (piece.data.2.2.1.mono (by rw [piece.data.1]))).contDiffOn
  obtain ⟨Ti,hTi,hInv⟩ := round3_prepared_compact_profiles b.symm b.target Ka
    b.open_target hKa hKaTarget hg.2.2.1
  obtain ⟨Tf,hTf,hForw⟩ := round3_prepared_compact_profiles b b.source Kq
    b.open_source hKq hKqSource hg.2.1
  obtain ⟨Te,hTe,hEtaJet⟩ := round3_prepared_compact_profiles (piece.cutoff ∘ a.symm) b.target Ka
    b.open_target hKa hKaTarget hEta
  refine ⟨Ti,Tf,Te,hTi,hTf,hTe,?_⟩
  intro ell hell hell1 k y hy
  exact ⟨(hInv ell hell hell1 k (a y) ⟨y,hy,rfl⟩).2,
    (hForw ell hell hell1 k (q y) ⟨y,hy,rfl⟩).2,
    (hEtaJet ell hell hell1 k (a y) ⟨y,hy,rfl⟩).1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_piece_profiles
