module

public import Formalism.WachLatticeTwists.RealClassMaps.Statement
public import Formalism.WachLatticeTwists.CupProductVanishing.H2MapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.BkInRow
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatClause5Row
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.H2MapInjectiveStatement

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem h2Map_injective_statement : H2MapInjective := by
  intro O _ _ _ _ Γ _ _ ε hNat Y R _ _ _ _ _ _ _ _ _ _ hY hR i hic hii z hz hzc hfz
  obtain ⟨f, hf, hfz⟩ := hfz
  obtain ⟨θ⟩ := hNat
  have htw : ∀ (M : Type) [AddCommGroup M] [Module O M] (g : Γ) (m : M),
      Formalism.RepresentationBoundsCohomology.LOC.twist ε M g m = ((ε g : Oˣ) : O) • m := fun M _ _ g m => rfl

  let zz : ReciprocityTheory.Gal.Z2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) := ⟨fun p => z p.1 p.2, hzc, fun g h k => hz g h k⟩
  have hzero : ReciprocityTheory.Gal.mapH2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) (Formalism.RepresentationBoundsCohomology.LOC.twist ε R) i hic
      (ReciprocityTheory.ChartRestriction.T2.twist_map ε i) (Submodule.Quotient.mk zz) = 0 := by
    rw [ReciprocityTheory.Gal.mapH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]
    refine ⟨f, hf, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [ReciprocityTheory.Gal.d1_apply, htw]
    exact (hfz g h).symm
  have hθ := θ.nat Y R hY hR i hic (Submodule.Quotient.mk zz)
  rw [hzero, map_zero] at hθ
  have h0 : θ.θ Y hY (Submodule.Quotient.mk zz) = 0 := hii (hθ.symm.trans (map_zero i).symm)
  have hmk : (Submodule.Quotient.mk zz : ReciprocityTheory.Gal.H2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)) = 0 :=
    (θ.θ Y hY).injective (by rw [h0, map_zero])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem] at hmk
  obtain ⟨c, hc, hcz⟩ := hmk
  refine ⟨c, hc, fun g h => ?_⟩
  have e := congrFun hcz (g, h)
  rw [ReciprocityTheory.Gal.d1_apply, htw] at e
  exact e.symm

theorem clause4 : CupClause := by
  intro O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hA hNat z hz hzc hfz
  haveI : IsNoetherian O A := by
    haveI := hA.fg
    infer_instance
  haveI := hA.t2
  haveI := hA.csmul
  haveI : ContinuousConstSMul O (Ymod r χ E) :=
    ⟨fun a => continuous_induced_rng.2 ((continuous_const_smul a).comp continuous_subtype_val)⟩
  let i : Ymod r χ E →ₗ[O] A := (Ymod r χ E).subtype.restrictScalars O
  have hYfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop O (Ymod r χ E) :=
    ⟨Module.Finite.of_injective i Subtype.val_injective, inferInstance,
      ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩⟩
  exact h2Map_injective_statement O Dw (ε.comp Dw.subtype) hNat (Ymod r χ E) A hYfg hA i continuous_subtype_val
    Subtype.val_injective z hz hzc hfz

end Formalism.RepresentationBoundsCohomology.T2
end
end
end

-- Source module: Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.Clause4GK

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem clause4GK : CupClauseGK := by
  intro p _ K O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hK hO e hε hA
  obtain ⟨F⟩ := ReciprocityTheory.ChartRestriction.T2.natInv_all_iso hK hO e (ε := ε.comp Dw.subtype) hε
  exact clause4 O A T' G r χ E Dw ε hA ⟨F⟩

end Formalism.RepresentationBoundsCohomology.T2
end
end
end

-- Source module: Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.Clause5Row

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology


theorem kRow_rel {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (x : Z1 D.ρA) (b : coZ1s ρM)
    (hy : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b) :
    ∃ m' : VT ⧸ D.T, ∀ g, u ((b : Γ → M) g) = x.1 g - (D.ρA g m' - m') := by
  have hsym : ∀ g y, u.symm (D.ρA g y) = ρM g (u.symm y) := fun g y => by
    rw [LinearEquiv.symm_apply_eq, hu, LinearEquiv.apply_symm_apply]
  let b' : coZ1s ρM := ⟨fun g => u.symm (x.1 g), fun g h => by
    show u.symm (x.1 (g * h)) = u.symm (x.1 g) + ρM g (u.symm (x.1 h))
    rw [((mem_Z1_iff_cocycle _ _).1 x.2).2 g h, map_add (f := _), hsym]⟩
  have hk0 : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b' := rfl
  have hy' : Submodule.mkQ _ b' = Submodule.mkQ _ b := hk0.symm.trans hy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    coB1, LinearMap.mem_range] at hy'
  obtain ⟨m, hm⟩ := hy'
  refine ⟨u m, fun g => ?_⟩
  have h1 := congrFun hm g
  rw [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at h1
  have h2 : ρM g m - m = u.symm (x.1 g) - (b : Γ → M) g := h1
  have h3 : (b : Γ → M) g = u.symm (x.1 g) - (ρM g m - m) := by rw [h2]; abel
  rw [h3, map_sub, map_sub, LinearEquiv.apply_symm_apply, hu]


theorem clause5Gen {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (hA : ContAction D.ρA)
    (hk : Function.Injective (kRow D ρM u hu)) (b : coZ1s ρM)
    (hb : Submodule.mkQ _ b ∈ LinearMap.range (kRow D ρM u hu)) (t : Γ → D.T') (ht : t ∈ Z1 D.ρTl')
    (c : Γ → KO O) (hc : Continuous c)
    (h : ∀ g k, pairKO D.bT D.T (D.ρA g (u ((b : Γ → M) k))) (t g) =
      ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    prK D _ hk ⟨Submodule.mkQ _ b, hb⟩ (Submodule.Quotient.mk ⟨t, ht⟩) = 0 := by
  have hb0 := hb
  obtain ⟨y, hy⟩ := hb0
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m', hbg⟩ := kRow_rel D _ u hu x b hy
  have hx' : (fun g => u ((b : Γ → M) g)) ∈ Z1 D.ρA := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => ?_⟩
    · have hxc : Continuous x.1 := ((mem_Z1_iff_cocycle _ _).1 x.2).1
      have hc2 : Continuous fun g : Γ => D.ρA g m' := hA.comp (continuous_id.prodMk continuous_const)
      have : (fun g => u ((b : Γ → M) g)) = fun g => x.1 g - (D.ρA g m' - m') := funext hbg
      rw [this]
      exact hxc.sub (hc2.sub continuous_const)
    · rw [b.2 g h, map_add (f := _), hu]
  have hxx : (Submodule.Quotient.mk x : ReciprocityTheory.Gal.H1 D.ρA) = Submodule.Quotient.mk ⟨_, hx'⟩ := by
    refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m', fun g => ?_⟩)
    change x.1 g - u ((b : Γ → M) g) = _
    rw [hbg]; abel
  have e1 : (⟨Submodule.mkQ _ b, hb⟩ : LinearMap.range (kRow D _ u hu)) =
      LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x) := Subtype.ext hy.symm
  rw [e1]
  change D.pr ((LinearEquiv.ofInjective _ hk).symm (LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x))) _ = 0
  rw [LinearEquiv.symm_apply_apply, hxx]
  exact ReciprocityTheory.ChartRestriction.T2.pr_eq_zero_of_swap_cob D ⟨_, hx'⟩ ⟨_, ht⟩ c hc h

theorem clause5Row : StatClause5Row := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ π γ
    D u hu v hε hT hπ hv hγ hk C₁ hC a b hb ha hCa ⟨c, hc, hcob⟩
  have ht : (fun g => v (π (a g))) ∈ Z1 D.ρTl' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hC a hCa, fun g h => ?_⟩
    have e1 : a (g * h) = a g + ρ₁ (g : G) (a h) := ha g h
    rw [e1, map_add (f := _), map_add (f := _), hπ, hv]
  have e2 : clsRow D v (fun g => π (a g)) = Submodule.Quotient.mk ⟨_, ht⟩ := by
    unfold clsRow
    exact dif_pos ht
  rw [e2]
  refine clause5Gen D _ u hu (ReciprocityTheory.ChartRestriction.T2.contAction_quotient hT D.T D.stT) hk b hb _ ht c hc fun g k => ?_
  have h4 := hcob g k
  rw [hγ] at h4
  have h5 : u (uElt r χ (g : G) • (b : Dw → M) k) = D.ρA g (u ((b : Dw → M) k)) := hu g _
  rw [h5] at h4
  rw [hε g]
  exact h4

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
end
end
end

-- Source module: Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN


theorem rowRhoReal : StatRowRhoReal := by
  intro p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _
    M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ
    hv hγ hBK hFs hRow hk
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcyc)
  obtain ⟨inv, invF, hc⟩ := ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD
  have hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap) :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  let j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := familyMassRatio
  have j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := iS1
  let j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := familyMassSecondLine
  have j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := iS2
  have hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV',
      fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0 := by
    intro a
    rw [hBK a]
    refine forall₂_congr fun b _ => ?_
    show _ ↔ invF (cupFG D a b) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  obtain ⟨_, hbk⟩ := bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek)
    (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'
  obtain ⟨C₁, c1, c2, c3, c3', c6, c7⟩ := hRow
  let pairD := fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))
  refine ⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩
  · rw [hFs]; exact hbk
  · refine ⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f,
      fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩
    · exact clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA
    · exact clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ
        (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'


end Formalism.RepresentationBoundsCohomology.FIN
end
end
end
