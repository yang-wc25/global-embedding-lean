import Probes.ActualOriginalSignedPhaseGood

/-! The effective secondary carrier is the compact ordinary-cutoff carrier
intersected with two relative primary supports. Ordinary cutoffs themselves
need not be supported inside that closed intersection. Relative closedness,
compactness and transport to the original support are proved for the actual
subtype supports. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped Topology
namespace GlobalEmbedding.Continuation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem actual_relative_support_preimage_closed (W : Set X) (f : X → ℝ) :
    IsClosed (Subtype.val ⁻¹' (Subtype.val '' tsupport (fun w : W => f w.val)) : Set W) := by
  have he : (Subtype.val ⁻¹' (Subtype.val '' tsupport (fun w : W => f w.val)) : Set W) =
      tsupport (fun w : W => f w.val) := by
    ext w
    constructor
    · rintro ⟨v,hv,heq⟩
      have hvw : v = w := Subtype.ext heq
      simpa only [hvw] using hv
    · intro hw
      exact ⟨w,hw,rfl⟩
  rw [he]
  exact isClosed_tsupport _

theorem actual_compact_interaction_carrier
    (K W : Set X) (hK : IsCompact K) (hKW : K ⊆ W) (f g : X → ℝ) :
    IsCompact (K ∩ ((Subtype.val '' tsupport (fun w : W => f w.val)) ∩
      (Subtype.val '' tsupport (fun w : W => g w.val)))) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : K → W := fun x => ⟨x.val,hKW x.property⟩
  have hIncl : Continuous incl := continuous_subtype_val.subtype_mk _
  let S : Set W := Subtype.val ⁻¹' ((Subtype.val '' tsupport (fun w : W => f w.val)) ∩
    (Subtype.val '' tsupport (fun w : W => g w.val)))
  have hS : IsClosed S := (actual_relative_support_preimage_closed W f).inter
    (actual_relative_support_preimage_closed W g)
  have hCompact : IsCompact (Subtype.val '' (incl ⁻¹' S)) :=
    ((hS.preimage hIncl).isCompact).image continuous_subtype_val
  convert hCompact using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,hy⟩

theorem actual_relative_support_pullback_subset
    (W : Set X) (Omega : Set Y) (f : X → Y)
    (hf : ContinuousOn f W) (hmap : MapsTo f W Omega) (g : Y → ℝ) :
    Subtype.val '' tsupport (fun w : W => g (f w.val)) ⊆
      f ⁻¹' (Subtype.val '' tsupport (fun y : Omega => g y.val)) := by
  let Phi : W → Omega := fun w => ⟨f w.val,hmap w.property⟩
  have hRestrict : Continuous (fun w : W => f w.val) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  have hPhi : Continuous Phi := hRestrict.subtype_mk _
  have hSupport : tsupport (fun w : W => g (f w.val)) ⊆
      Phi ⁻¹' tsupport (fun y : Omega => g y.val) := by
    apply closure_minimal _ ((isClosed_tsupport _).preimage hPhi)
    intro w hw
    exact subset_tsupport _ hw
  rintro x ⟨w,hw,rfl⟩
  exact ⟨Phi w,hSupport hw,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_relative_support_preimage_closed
#print axioms GlobalEmbedding.Continuation.actual_compact_interaction_carrier
#print axioms GlobalEmbedding.Continuation.actual_relative_support_pullback_subset
