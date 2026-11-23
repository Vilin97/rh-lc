module

public import Formalism.AdmissibleDesigns.RealDisplayAllK
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.LocalToDisplayFree
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
public import Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.CoboundaryTrivialActionZero
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.ClsRowVOfMem
public import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal
public import Formalism.WachLatticeTwists.RealClassMaps.Statement
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealAllLiftThird
import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.BkInRow
public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.InRowRealOf

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem ko_tors (O : Type) [CommRing O] [IsDomain O] (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hq.symm

theorem psiCont (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A : Type) [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A] (Y : Submodule A A) (hO : PadicCoeff p O) (hA : IsFGTop O A)
    (ψ : Y →ₗ[O] KO O) : Continuous ψ := by
  have hfg : IsFGTop O Y := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective (Y.subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × Y => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Y, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Y => ko_tors O (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  refine continuous_of_continuousAt_zero ψ.toAddMonoidHom ?_
  intro U hU
  have hU0 : (0 : KO O) ∈ U := by
    have := mem_of_mem_nhds hU
    simpa using this
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hopen.mem_nhds (zero_mem _)) ?_
  rintro _ ⟨z, rfl⟩
  show ψ (a • z) ∈ U
  rw [map_smul, hka]
  exact hU0

theorem inRowReal_of (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw]
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (D : LatData O Dw VT VT') (v : T₂ ≃ₗ[O] D.T') (hc : Continuous fun t => v (π t))
    (he : ∀ g t, v (π (resRep ρ₁ Dw g t)) = D.ρTl' g (v (π t)))
    (Fs : Submodule O (H1 D.ρTl')) (Hf₁ : Submodule O (H1 (resRep ρ₁ Dw)))
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hinc : Continuous inc)
    (hur : Continuous fun g : Dw => uElt r χ (g : G)) (hIm : Hf₁.map (gRow D _ π v hc he) ≤ Fs) :
    InRowReal r χ E Dw ρ₁ inc π D v Fs (Hf₁.map (gRow D _ π v hc he)) := by
  refine ⟨fun a => Continuous a, fun a ha => ?_, fun a ha => ?_, fun ψ f hf => ?_, fun a ha => hc.comp ha, ?_, hIm⟩
  · refine Continuous.subtype_mk (f := fun q : Dw × Dw =>
      inc (a q.1) * (uElt r χ (q.1 : G) * ((uElt r χ (q.2 : G) - 1) * E))) ?_ _
    exact (hinc.comp (ha.comp continuous_fst)).mul ((hur.comp continuous_fst).mul
      (((hur.comp continuous_snd).sub continuous_const).mul continuous_const))
  · exact ((hinc.comp ha).mul (hur.mul continuous_const)).neg
  · exact (psiCont p O A (Ymod r χ E) hO hA ψ).comp hf
  · rintro _ ⟨y, _, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (π (c.1 g))) ∈ Z1 D.ρTl' :=
        (cocycles1MapOfEquivariant (resRep ρ₁ Dw) D.ρTl' (v.toLinearMap ∘ₗ π) hc he c).2
      refine ⟨c.1, c.2.2, c.2.1, ?_⟩
      rw [clsRow_of_mem D v _ h]
      rfl

end Formalism.RepresentationBoundsCohomology.FIN
end
end
end

-- Source module: Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveReal

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG

theorem blk_ko {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α)
    (h : Fintype.card {a // bl a = k} = 1) : Nonempty (blockRestrictedRepresentationType bl ρk k ≃ₗ[O] KO O) := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 h
  exact ⟨(LinearEquiv.funUnique {a // bl a = k} O (KO O) : ({a // bl a = k} → KO O) ≃ₗ[O] KO O)⟩


end Formalism.RepresentationBoundsCohomology.FIN
end
end
end

-- Source module: Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem liftCoc : StatLiftCoc := by
  intro O D M₁ M₂ _ _ _ _ _ _ ρ₁ ρ₂ p hp hs Hf₁ Hf₂ ℓ e hL κ hκ
  obtain ⟨x, hx, hxe⟩ := hL _ hκ
  obtain ⟨K₀, rfl⟩ := Submodule.mkQ_surjective _ x
  have h1 : (Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp K₀ - ((ℓ : O) ^ e) • κ) : H1z ρ₂) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hxe
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, rfl⟩ := hs v
  let cb : coZ1s ρ₁ := ⟨fun g => ρ₁ g w - w, fun g h => by
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  refine ⟨K₀ - cb, ?_, fun g => ?_⟩
  · have hcb : Submodule.mkQ _ cb = (0 : H1z ρ₁) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact ⟨w, by funext g; rfl⟩
    rw [map_sub, hcb, sub_zero]
    exact hx
  · have h2 : ρ₂ g (p w) - p w = p ((K₀ : D → M₁) g) - ((ℓ : O) ^ e) • (κ : D → M₂) g :=
      congrFun hv g
    show p ((K₀ : D → M₁) g - (ρ₁ g w - w)) = _
    rw [map_sub, map_sub, hp, h2]
    abel

theorem colK : StatColK := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ L _ _ _ _ r χ Dl inc v₁ ev hev hs Hf₁ Hf₂ ℓ e' j κ κz hκ hκf hL
  have key := fun a => liftCoc O Dl P L _ _ ev (ev_equiv r χ Dl inc v₁ ev hev) hs Hf₁ Hf₂ ℓ e' hL
    (κz a) (hκf a)
  choose Kz hKz1 hKz2 using key
  refine ⟨fun a g => if h : g ∈ Dl then inc ((Kz a : Dl → P) ⟨g, h⟩) else 0, Kz, ?_, hKz1, ?_⟩
  · intro a g
    dsimp only
    rw [dite_eq_left g.2]
  · intro a g hg
    dsimp only
    rw [dite_eq_left hg, ← hev, hKz2 a ⟨g, hg⟩, hκ a ⟨g, hg⟩]

theorem colk : StatColk := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hs Hf₁ Hf₂ ℓ e' u uz huz hmem hL
  obtain ⟨kz, hk1, hk2⟩ := liftCoc O Dl P _ _ _ ev (ev_equiv_triv r χ Dl ev hev) hs Hf₁ Hf₂ ℓ e' hL
    uz hmem
  refine ⟨fun g => if h : g ∈ Dl then inc ((kz : Dl → P) ⟨g, h⟩) else 0, kz, ?_, hk1, ?_, ?_⟩
  · intro g
    dsimp only
    rw [dite_eq_left g.2]
  · intro g
    dsimp only
    split_ifs with h
    · exact hE _
    · exact ⟨0, (zero_mul E).symm⟩
  · intro g hg m
    dsimp only
    rw [dite_eq_left hg, hM, hk2 ⟨g, hg⟩, Submodule.coe_smul, huz ⟨g, hg⟩, smul_eq_mul, mul_assoc]

theorem colFun : StatColFun := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ V _ _ r χ Dl inc Hf₁ Lf H K Kz hK hKz s
  have h := H ((LinearMap.toSpanSingleton A V s).comp inc) Kz hKz
  have e : (fun g : Dl => K g • s) =
      fun g : Dl => ((LinearMap.toSpanSingleton A V s).comp inc) ((Kz : Dl → P) g) := by
    funext g
    rw [hK g]
    rfl
  rw [e]
  exact h

end Formalism.RepresentationBoundsCohomology.JL
end
end
end

-- Source module: Formalism.AdmissibleDesigns.RealDisplayAllKOf

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain
open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
  (InChi InRowRho inputs_from_selmer_inj theorem_n_five_delta_clause)
open Formalism.RepresentationBoundsCohomology.FIN
  (InRhoFixReal blk_ko colPsi_lc decs inRowReal_of kRowRange pi_ko_torsion resLC rowRhoReal)
open Formalism.RepresentationBoundsCohomology.JL (colFun colK colk)
open Formalism.RepresentationBoundsCohomology.JT (BKIn InRowRhoNoBK rowBK)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (clsRow kRow kRowInj lcH1 qK)
open Formalism.RepresentationBoundsCohomology.SplitClassesAll (InRhoFix)
open Formalism.RepresentationBoundsCohomology.T2 (vhEInChi)
open ReciprocityTheory.ChartRestriction.T2 (IsCycOn)
open ReciprocityTheory.Gal (H1)



theorem realDisplayAllK_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAllK ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard1, -, -, -, -, -, -, hOne0⟩ := hR
  obtain ⟨p1, -, -, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha cB cT cols eO vδ N h0 c1
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ ince eve heve PE _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne

  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix2 : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hpD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hk : ∀ w, Function.Injective (kRow (Dat w) _ (uD w) (huD w)) :=
    fun w => kRowInj O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w)
  have hcycw : ∀ w, IsCycOn ℓ (decs Ek Aw w) (ε.comp (decs Ek Aw w).subtype) :=
    fun w g n ζ h => hcyc g.1 n ζ h
  have hnu : ¬ IsUnit (ℓ : O) := fun h => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hO.p_mem)) h
  have hKO : ∀ c : Fin (t + 1), c ≠ 0 → Nonempty (blockRestrictedRepresentationType bl ρk c ≃ₗ[O] KO O) :=
    fun c hc => blk_ko bl ρk c (hcard1 c hc)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hFix2
  have key : ∀ w, w ∈ what₂ →
      ∃ (pr : LinearMap.range (kRow (Dat w) _ (uD w) (huD w)) →ₗ[O] H1 (Dat w).ρTl' →ₗ[O] KO O)
      (pair : H1 (Dat w).ρT →ₗ[FractionRing O] H1 (Dat w).ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (qK (Dat w) _ (hk w)) (Dat w).j' pr pair (HfW w) (Hf₂ w)
        ((((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w))) (Fs w) ∧
      InRowRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ
        (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (clsRow (Dat w) (vD w)) pr (Fs w) (Im w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact rowRhoReal ℓ O (VT w) (VT' w) Ek Ω (Aw w) a1 R' Tc (blockRestrictedRepresentationType bl ρk 0) r χ E ε T₁ T₂ ρ₁ ρ₂ inc π γ
      (Dat w) (uD w) (huD w) (vD w) (HfW w) (Hf₂ w) (Fs w) (Im w) hO hFr hA (hcycw w) a3 a4 e8 a5 a6 a7 a9
      (e10 w hw) (hk w)
  choose! pr pair hpp using key
  let HcG : ∀ c : Fin (t + 1), Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) :=
    fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)
  let HcR : ∀ (c : Fin (t + 1)) (w : ℕ),
      Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))) := fun c =>
    Fin.cases (motive := fun c => ∀ w : ℕ,
        Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))))
      (fun w => LinearMap.range (kRow (Dat w) _ (uD w) (huD w)))
      (fun c' w => lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c'.succ) r χ) (decs Ek Aw w))) c
  have hBK' : ∀ w ∈ what₂, BKIn (HcR 0 w) (qK (Dat w) _ (hk w)) (Dat w).j' (pr w) (pair w) (HfW w) (Hf₂ w)
      (F 0 w) (Fs w) := by
    intro w hw
    rw [(hRows w hw).2.2.2.2.2.2.2.1]
    exact (hpp w hw).1
  have hFix' : InRhoFix (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (HcG 0)
      (HcR 0) (F 0) Io ε ρ₁ ρ₂ inc π γ lam (fun w => clsRow (Dat w) (vD w)) pr Fs Im :=
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, fun w hw => (hpp w hw).2, e11⟩
  obtain ⟨a1, a2, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, a7, a8, a9, a10, a11, a12, a13⟩ := hFix'

  choose Kc Kz hKc1 hKc2 hKc3 using fun l => colK O R' Tc (Ω ≃ₐ[Ek] Ω) Pe L r χ (decs Ek Aw (colIdx l)) ince v₁ eve heve hse
    (Hfe₁ l) (Ff l) ℓ (e' (colIdx l)) (j (colIdx l)) (κ l) (κz l) (c8 l).1 (c8 l).2.2.1 (hLe l)
  choose k0 kz hk01 hk02 hk03 hk04 using fun l => colk O R' Tc (Ω ≃ₐ[Ek] Ω) PE (blockRestrictedRepresentationType bl ρk c1) r χ E δO (decs Ek Aw (colIdx l)) incE
    evE hincE hact hevE hsE (HfE₁ l) (HfE₂ l) ℓ (e' (colIdx l)) (u l) (uz l) (huz l) (hu l) (hLE l)
  have hcont : ∀ (c : Fin (t + 1)) φ, Submodule.mkQ _ (colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ
      (fun l => decs Ek Aw (colIdx l)) (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG c :=
    fun c φ => colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ
  have hRowsA : ∀ w ∈ what₂, InRowRho (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ (HcR 0 w) (F 0 w)
      (clsRow (Dat w) (vD w)) (pr w) (Fs w) (Im w) := by
    intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7⟩ := a12 w hw
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hBK' w hw
    exact ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7,
      rowBK O _ (HcR 0 w) (H1 (Dat w).ρT) (H1 (Dat w).ρTl') (H1 (Dat w).ρT') (qK (Dat w) _ (hk w)) (Dat w).j'
        (pr w) (pair w) (HfW w) (Hf₂ w) (F 0 w) (Fs w) f2 f3 f4 f5 f6 f7⟩

  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w))
        (cT c) (Sha ((c : ℕ) - 1)) (HcG c) (HcR c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc2
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    obtain ⟨c', rfl⟩ : ∃ c', c = Fin.succ c' := ⟨c.pred hc0, (Fin.succ_pred _ _).symm⟩
    obtain ⟨-, hrw, ⟨i1, i3, i4⟩, i5⟩ := hC _ hc2
    refine ⟨fun w hw => ⟨?_, (hrw w hw).2.1, (hrw w hw).2.2.1, (hrw w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, i5⟩
    rw [(hrw w hw).1]
    exact bot_le
  obtain ⟨o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
  have hc1 : c1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [c1] at this
  have hOneA : InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs
      (fun w => ReciprocityTheory.Gal.locDeg (pl w)) (cT c1) (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞))
      (HcG c1) (HcR c1) (F c1) Io IS I γQ ζ ζO nQ := by
    refine ⟨fun w hw => ⟨?_, (o7 w hw).2.1, (o7 w hw).2.2.1, (o7 w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, ?_⟩
    · rw [(o7 w hw).1]
      exact inf_le_left
    · refine vhEInChi Ek Ω Av hAv ℓ O hreal R' Tc (blockRestrictedRepresentationType bl ρk c1) (hKO _ hc1) r χ p1
        (decs Ek Aw) (what₂ ∪ qs ∪ univ.image colIdx) (HcG c1) (F c1) Vo VS Io IS ?_ o10
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, rfl, hc⟩
  obtain ⟨hv1, hv2⟩ := theorem_n_five_delta_clause O ℓ Fact.out hnu s₀ hs1 hs2 (ε gI) y u₁ hε t
  refine ⟨?_, ?_, ?_⟩
  · exact hF ι colIdx hinj (decs Ek Aw) j e' Kc k0
      (fun x' hx' => by
        obtain ⟨q5, q6⟩ := hrat0 x' hx'
        refine ⟨q5, fun l => ?_⟩
        obtain ⟨Lx, w1, w2, w3, w4⟩ := q6 l
        exact ⟨Lx, w1, fun a s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) Pe (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) ince
            (Hfe₁ l) (Lx : Set _) w2 (Kc l a) (Kz l a) (hKc1 l a) (hKc2 l a) s,
          fun s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) PE (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) incE (HfE₁ l)
            (Lx : Set _) w3 (k0 l) (kz l) (hk01 l) (hk02 l) s, w4⟩)
      ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w)) s (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞)) H0 Sha
      (fun l g => hk03 l g) L tens v₁ κ HcG HcR F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂
      inc π γ lam (fun w => H1 (Dat w).ρTl') (fun w => clsRow (Dat w) (vD w)) pr Fs Im cT I γQ ζ ζO nQ u
      (inputs_from_selmer_inj O R' Tc (Ω ≃ₐ[Ek] Ω) (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ ι colIdx (decs Ek Aw) j e' Kc k0 ℓ what₂ s L tens v₁ κ V
        iL qV Ff κz (HcG 0) (HcR 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam (fun w => H1 (Dat w).ρTl')
        (fun w => clsRow (Dat w) (vD w)) pr Fs Im
        ⟨a1, a2, fun l a g hg => hKc3 l a g hg, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, hcont 0, a7, a8,
          a9, a10, a11, hRowsA, a13⟩)
      (fun c hc2 => ⟨(hC c hc2).1, hC' c hc2⟩)
      ⟨fun l g hg m => hk04 l g hg m, o4, o5, o6, hOneA⟩
  · show IsDiscreteValuationRing.addVal O δO = _
    rw [hδO]
    exact hv1
  · show IsDiscreteValuationRing.addVal O δO ≤ _
    rw [hδO]
    exact hv2

end Formalism.MainNotions.N.K
end
end
end
