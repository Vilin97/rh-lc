module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafChart
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafExc
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafThom
public import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfAll
public import Development.EtaleCohomology.CohomologicalPurity.LeafDescOGluePfP
public import Development.EtaleCohomology.CohomologicalPurity.LeafDescOSepPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDescPfGlue
public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPfDbl
public import Development.EtaleCohomology.CohomologicalPurity.LeafDiscNrmPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafEvPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafGenKerPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafGenRingPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafMatPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafNbPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafPairPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafStepPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafVanFPf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.EtaleCohomology.CohomologicalPurity.LeafVanRingPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafZlocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafZornPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafBZPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem LeafBZ_of : LeafBZ := by
  intro R _ K X U n W a ⟨b, hb0, hba⟩
  subst hba
  refine ⟨?_, ?_⟩
  · show ((K.X n).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    have e := congrArg (fun φ => φ.hom b) ((K.d (n - 1) n).hom.naturality (W.ι ⁻¹ᵁ U).ι.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [← e]
    have hb0' : ((K.X (n - 1)).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom b = 0 := hb0
    rw [hb0', map_zero]
  · show ((K.d n (n + 1)).hom.app (op W.toScheme)).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    change ((K.d (n - 1) n ≫ K.d n (n + 1)).hom.app (op W.toScheme)).hom b = 0
    rw [K.d_comp_d]
    rfl

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafBdAddPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_section_boundary_of_mem_addSubgroup_closure {R : Type} [CommRing R] (K : Cx R) {Y : Scheme.{0}} (U' : Y.Opens) (n : ℤ)
    (a : Sec (K.X n) Y) (ha : a ∈ AddSubgroup.closure {a | Bd K U' n a}) : Bd K U' n a := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb0, hb⟩ := hx
    obtain ⟨c, hc0, hc⟩ := hy
    refine ⟨b + c, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0
      rw [map_add (f := _), show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y
      rw [map_add (f := _)]; rw [← hb, ← hc]
  | neg x _ hx =>
    obtain ⟨b, hb0, hb⟩ := hx
    refine ⟨-b, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0
      rw [map_neg]; rw [show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x
      rw [map_neg]; rw [← hb]

theorem LeafBdAdd_of : LeafBdAdd := by
  intro R _ K X U n W a ha
  exact etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafOffPf

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafOff_of : LeafOff := by
  intro d P F
  apply le_antisymm F.h
  intro y hy
  change y ∉ PrimeSpectrum.zeroLocus (F.I : Set F.B)
  intro hz
  have hk : RingHom.ker (Ideal.Quotient.mk F.I) = F.I := Ideal.mk_ker
  have hr : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk F.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hk]; exact hz
  obtain ⟨y0, rfl⟩ := hr
  have hw := congrArg (fun g => g.base y0) F.cart.w
  simp only [Scheme.Hom.comp_base] at hw
  have hU : F.w.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))).base y0) ∈ (P.U : Set P.X) := hy
  rw [P.hU] at hU
  exact hU ⟨F.z.base y0, hw.symm⟩

end LateralTheory.CohomologicalPurity.Cl
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafTopPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_sheaf_sections_restrict_restrict_eq_restrict_comp {R : Type} [CommRing R] {F : Shv R} {Y Z W : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ W) (a : Sec F W) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

theorem etale_sheaf_sections_restriction_of_zero_eq_zero {R : Type} [CommRing R] {F : Shv R} {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    Sec.res f (0 : Sec F Z) = 0 := by
  show (F.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem etale_sheaf_sections_map_restrict_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {Y Z : Scheme.{0}} (f : Y ⟶ Z) (a : Sec F Z) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun ψ => ψ.hom a) h

theorem LeafTop_of : LeafTop := by
  intro R _ K X U n c' hc'
  obtain ⟨h1, h2⟩ := (mem_Zc c').1 hc'
  refine ⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩
  · have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι := by
      rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · rw [etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · intro V
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp]
    congr 1
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom,
      Scheme.homOfLE_ι]

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafVanPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem van_preimage {d : ℕ} (P : SP d) (V : P.X.affineOpens) :
    off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
  have := P.cl
  have hsupp : (P.ι.ker.support : Set P.X) = Set.range P.ι := by
    rw [Scheme.Hom.support_ker, P.ι.isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  have hmem : V.2.fromSpec y ∈ V.1 := by
    rw [← SetLike.mem_coe, ← V.2.range_fromSpec]; exact Set.mem_range_self y
  have h1 := Set.ext_iff.mp (V.2.fromSpec_preimage_zeroLocus ((P.ι.ker.ideal V : Ideal Γ(P.X, V.1)) : Set Γ(P.X, V.1))) y
  have h2 := Scheme.IdealSheafData.mem_support_iff_of_mem (I := P.ι.ker) hmem
  have h3 : V.2.fromSpec y ∈ (P.U : Set P.X) ↔ V.2.fromSpec y ∉ Set.range P.ι := by rw [P.hU]; rfl
  have h4 : V.2.fromSpec y ∈ P.ι.ker.support ↔ V.2.fromSpec y ∈ Set.range P.ι := by
    rw [← SetLike.mem_coe, hsupp]
  exact (not_congr (h1.symm.trans (h2.symm.trans h4))).trans h3.symm

theorem LeafVan_of (hC : LeafChart) (hR : LeafVanRing) : LeafVan := by
  intro hH d q _ P hq i x W hxW
  obtain ⟨V, hxV, hVW, -, hch⟩ := hC d P x W hxW
  have hqV : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op).hom
    simpa using this
  refine ⟨⟨Spec (CommRingCat.of Γ(P.X, V.1)), V.2.fromSpec, V.2.isOpenImmersion_fromSpec, off Γ(P.X, V.1) (P.ι.ker.ideal V),
    van_preimage P V⟩, ?_, ?_, ?_⟩
  · rw [V.2.range_fromSpec]; exact hxV
  · rw [V.2.range_fromSpec]; exact hVW
  · intro n hn
    exact hR hH d q Γ(P.X, V.1) _ hch hqV n i hn

end LateralTheory.CohomologicalPurity.Cl
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafZeroPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (hG : IsZero G) (a : Sec G X) :
    a = 0 := by
  have h1 : Sec.map (𝟙 G) a = a := rfl
  have h2 : Sec.map (0 : G ⟶ G) a = 0 := rfl
  rw [← h1, hG.eq_of_src (𝟙 G) 0, h2]

theorem LeafZero_of : LeafZero := by
  intro R _ K X U n hz
  refine ⟨?_, ?_, ?_⟩
  · intro V W h a _
    rw [sec_eq_zero_of_isZero hz (rs h a)]
    exact zero_mem _
  · intro W a _
    rw [sec_eq_zero_of_isZero hz a]
    exact zero_mem _
  · intro V W h a _
    exact ⟨0, zero_mem _, (sec_eq_zero_of_isZero hz _).trans (sec_eq_zero_of_isZero hz a).symm⟩

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.FixLeafCl

section

@[expose] public section

theorem LateralTheory.Fix.LeafCl.intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafCl := by
  have h54 : LateralTheory.CohomologicalPurity.LeafThom := LateralTheory.Fin.LeafThom.intersectionNumber_baseChange
  have h80 : LateralTheory.CohomologicalPurity.LeafChart := LateralTheory.Fin.LeafChart.intersectionNumber_baseChange
  have h89 : LateralTheory.CohomologicalPurity.LeafExc := LateralTheory.Fin.LeafExc.intersectionNumber_baseChange
  have h55 : LateralTheory.CohomologicalPurity.Cl.LeafDisc := LateralTheory.CohomologicalPurity.Cl.LeafDisc_of'
  have h56 : LateralTheory.CohomologicalPurity.DictPf.LeafEv := LateralTheory.CohomologicalPurity.DictPf.LeafEv_of
  have h57 : LateralTheory.CohomologicalPurity.DictPf.LeafPair := LateralTheory.CohomologicalPurity.LeafPairPf.LeafPair_of
  have h58 : LateralTheory.CohomologicalPurity.Cl.LeafDict := LateralTheory.CohomologicalPurity.DictPf.LeafDict_of' h55 h56 h57
  have h59 : LateralTheory.CohomologicalPurity.Cl.LeafZorn := LateralTheory.CohomologicalPurity.ZornPf.LeafZorn_of
  have h60 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafBdAdd := LateralTheory.CohomologicalPurity.Cl.Flq.LeafBdAdd_of
  have h61 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafBZ := LateralTheory.CohomologicalPurity.Cl.Flq.LeafBZ_of
  have h62 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZloc := LateralTheory.CohomologicalPurity.ZlocPf.LeafZloc_of
  have h63 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZero := LateralTheory.CohomologicalPurity.Cl.Flq.LeafZero_of
  have h64 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafStep := LateralTheory.CohomologicalPurity.Cl.Flq.StepPf.LeafStep_of
  have h65 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafTop := LateralTheory.CohomologicalPurity.Cl.Flq.LeafTop_of
  have h66 : LateralTheory.CohomologicalPurity.Cl.LeafFlq := LateralTheory.CohomologicalPurity.Cl.Flq.LeafFlq_of h59 h60 h61 h62 h63 h64 h65
  have h67 : LateralTheory.CohomologicalPurity.Cl.LeafDescOSep := LateralTheory.CohomologicalPurity.Cl.LeafDescOSep_of
  have h68 : LateralTheory.CohomologicalPurity.Cl.LeafDescOGlue := LateralTheory.CohomologicalPurity.Cl.LeafDescOGlue_of
  have h69 : LateralTheory.CohomologicalPurity.Cl.LeafDesc := LateralTheory.CohomologicalPurity.Cl.LeafDesc_of' h58 h66 h67 h68
  have h90 : LateralTheory.CohomologicalPurity.Cl.LeafNb := LateralTheory.CohomologicalPurity.NbPf.nb h89
  have h91 : LateralTheory.CohomologicalPurity.Cl.LeafVanRing := LateralTheory.CohomologicalPurity.Cl.LeafVanRing_of h90 h54
  have h92 : LateralTheory.CohomologicalPurity.Cl.LeafVan := LateralTheory.CohomologicalPurity.Cl.LeafVan_of h80 h91
  have h93 : LateralTheory.CohomologicalPurity.Cl.LeafVanF := LateralTheory.CohomologicalPurity.Cl.LeafVanF_of h92
  have h94 : LateralTheory.CohomologicalPurity.Cl.LeafOff := LateralTheory.CohomologicalPurity.Cl.LeafOff_of
  have h95 : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of
  have h96 : LateralTheory.CohomologicalPurity.Cl.LeafGenKer := LateralTheory.CohomologicalPurity.Cl.LeafGenKer_of
  have h97 : LateralTheory.CohomologicalPurity.Cl.LeafGen := LateralTheory.CohomologicalPurity.Cl.LeafGen_of h80 h95 h96
  have h98 : LateralTheory.CohomologicalPurity.Cl.LeafMat := LateralTheory.CohomologicalPurity.Cl.LeafMat_of
  have h99 : LateralTheory.CohomologicalPurity.Cl.LeafCmp := LateralTheory.CohomologicalPurity.Cl.LeafCmp_of_Mat h98
  exact LateralTheory.CohomologicalPurity.Cl.goal_of h54 h69 h92 h93 h94 h97 h99
end
end
