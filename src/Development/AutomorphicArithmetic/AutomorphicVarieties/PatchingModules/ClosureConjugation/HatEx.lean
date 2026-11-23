module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GKillsTr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PairMf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PairMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ToTMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DQuotDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnopMemCH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarClosure
public import Mathlib.RingTheory.Congruence.Hom

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TrinvBaseChange

section

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.trinv_baseChange :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) (B' : Type) [CommRing B'] [Algebra B B'], ∃ T' : TrInv B' (B' ⊗[B] E), (∀ y, T'.st (1 ⊗ₜ y) = 1 ⊗ₜ T.st y) ∧ ∀ y, T'.tr (1 ⊗ₜ y) = algebraMap B B' (T.tr y) := by
  intro B E _ _ _ T B' _ _
  let s : B' ⊗[B] E →ₗ[B'] B' ⊗[B] E := T.st.baseChange B'
  let t : B' ⊗[B] E →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ T.tr.baseChange B'
  have hs : ∀ (a : B') (y : E), s (a ⊗ₜ y) = a ⊗ₜ T.st y := fun a y => by simp [s]
  have ht : ∀ (a : B') (y : E), t (a ⊗ₜ y) = T.tr y • a := fun a y => by simp [t]
  refine ⟨⟨s, ?_, ?_, t, ?_, ?_⟩, fun y => hs 1 y, fun y => ?_⟩
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, hs, T.st_mul, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, T.st_st]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, ht, T.tr_comm u v, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, ht, T.tr_st]
  · show t (1 ⊗ₜ y) = _
    rw [ht, Algebra.algebraMap_eq_smul_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GensKill

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gens_kill :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ z ∈ P.gens, u.D.Kills z ∧ G.frame.star O B n z ∈ P.gens := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P z hz
  haveI := IsCoef.complete (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.char (l := l) (O := O)
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have hPhi : PhiCond G.frame.G₀ l := phi_fg G.frame P.fg
  obtain ⟨-, hks, -, hoEl, hIp⟩ := pair_kills r u hPhi hn
  obtain ⟨hfin, -, e, χ, hχ, hmf⟩ := pair_mf u hPhi
  haveI := hfin
  haveI := IsCO.complete (O := O) (R := B)
  haveI : CompactSpace G.frame.G₀ := by
    haveI := G.frame.cpt
    show CompactSpace G.frame.η.ker
    exact isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.frame.η_open).isCompact
  obtain ⟨hss, -, -, -, h1, hsub, -⟩ := star_basic G.frame n O B
  have htr : ∀ y, u.D.Kills y ↔ ∀ g, u.D.tr (MonoidAlgebra.single g 1 * y) = 0 :=
    g_kills_tr u.D χ u.cont hχ hmf hn
  unfold OoPt.gens pairGens qGens at hz ⊢
  simp only [Set.mem_union, Set.mem_setOf_eq] at hz ⊢
  rcases hz with ((⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩) | (⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩))
  · exact ⟨hoEl v g, Or.inl (Or.inl ⟨v, g, Or.inr rfl⟩)⟩
  · refine ⟨hks _ (hoEl v g), Or.inl (Or.inl ⟨v, g, Or.inl ?_⟩)⟩
    rw [hss]
  · exact ⟨hIp w g hg, Or.inl (Or.inr ⟨w, g, hg, Or.inr (by rw [hsub, h1])⟩)⟩
  · have hk := hks _ (hIp w g hg)
    rw [hsub, h1] at hk
    refine ⟨hk, Or.inl (Or.inr ⟨w, g, hg, Or.inl ?_⟩)⟩
    rw [hsub, hss, h1]
  · have hk := (htr _).2 (P.q1 j)
    exact ⟨hk, Or.inr (Or.inl ⟨j, Or.inr rfl⟩)⟩
  · have hk := hks _ ((htr _).2 (P.q1 j))
    refine ⟨hk, Or.inr (Or.inl ⟨j, Or.inl ?_⟩)⟩
    rw [hss]
  · have hk := (htr _).2 (P.q2 j i)
    exact ⟨hk, Or.inr (Or.inr ⟨j, i, Or.inr rfl⟩)⟩
  · have hk := hks _ ((htr _).2 (P.q2 j i))
    refine ⟨hk, Or.inr (Or.inr ⟨j, i, Or.inl ?_⟩)⟩
    rw [hss]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Trinv

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.trinv :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → 1 ≤ n → ∀ Z : Set (MonoidAlgebra B F.G₀), (∀ z ∈ Z, u.D.Kills z ∧ F.star O B n z ∈ Z) → ∃ (DE : Det n B (u.D.CHQuot Z)) (T : TrInv B (u.D.CHQuot Z)), DE.IsCH ∧ DE.pull (u.D.toQuot Z) = u.D.toDet ∧ (∀ y, T.st (u.D.toQuot Z y) = u.D.toQuot Z (F.star O B n y)) ∧ ∀ y, T.tr y = DE.tr y := by
  intro l _ F n O _ _ _ _ _ r B _ _ _ u hΦ hn Z hZ
  letI := F.grp
  letI := F.top
  haveI := F.tgrp
  haveI := F.cpt
  haveI := F.tdisc
  haveI : CompactSpace F.G₀ := by
    have hc : IsClosed (F.η.ker : Set F.Γ) := Subgroup.isClosed_of_isOpen _ F.η_open
    exact isCompact_iff_compactSpace.mp hc.isCompact
  obtain ⟨DE, hCH, hpull⟩ := d_quotDet u.D u.cont Z (fun z hz => (hZ z hz).1)
  have hl : ((l : ℕ) : B) ∈ maximalIdeal B := by
    have h1 : ((l : ℕ) : O) ∈ maximalIdeal O := by
      haveI := (IsCoef.char (l := l) (O := O))
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    rw [← map_natCast (algebraMap O B), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp h1) (isUnit_of_map_unit (algebraMap O B) _ hu)
  have hM : Submodule.span B
      ((MonoidHom.mrange (MonoidAlgebra.of B F.G₀) : Submonoid (MonoidAlgebra B F.G₀)) :
        Set (MonoidAlgebra B F.G₀)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    refine MonoidAlgebra.induction_on x ?_ ?_ ?_
    · intro m
      exact Submodule.subset_span ⟨m, rfl⟩
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro b x hx
      exact Submodule.smul_mem _ b hx
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of B F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      u.D.toDet.lam i (MulOpposite.unop (F.starOp O B n x)) = u.D.toDet.lam i x := by
    rintro _ ⟨g, rfl⟩ i _ _
    rw [(d_toDet u.D _).2.1, (d_toDet u.D _).2.1]
    exact u.P i g
  obtain ⟨hop, hCHs, -⟩ := d_star u.D.toDet (F.starOp O B n) _ hM hlam
  have hstarCH : ∀ z ∈ u.D.CH, F.star O B n z ∈ TwoSidedIdeal.span (u.D.CH ∪ Z) := by
    intro z hz
    have hz' : z ∈ u.D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    have h2 := hCHs z hz'
    rw [d_toDet_CH] at h2
    exact TwoSidedIdeal.span_mono Set.subset_union_left h2
  have hI : ∀ y, y ∈ u.D.chBar Z → F.star O B n y ∈ u.D.chBar Z := by
    unfold GDet.chBar
    refine star_closure F n O B (maximalIdeal B) (u.D.CH ∪ Z) hl ?_
    rintro z (hz | hz)
    · exact hstarCH z hz
    · exact TwoSidedIdeal.subset_span (Or.inr (hZ z hz).2)
  have hq : ∀ a b, u.D.toQuot Z a = u.D.toQuot Z b ↔ a - b ∈ u.D.chBar Z := by
    intro a b
    unfold GDet.toQuot
    exact Iff.trans (RingCon.eq _) (TwoSidedIdeal.rel_iff _ _ _)
  have hsurj : Function.Surjective (u.D.toQuot Z) := RingCon.mkₐ_surjective _
  let ψ : u.D.CHQuot Z →ₐ[B] (u.D.CHQuot Z)ᵐᵒᵖ :=
    RingCon.liftₐ (u.D.chBar Z).ringCon ((AlgHom.op (u.D.toQuot Z)).comp (F.starOp O B n)) (by
      intro a b hab
      rw [TwoSidedIdeal.rel_iff] at hab
      show MulOpposite.op (u.D.toQuot Z (F.star O B n a)) = MulOpposite.op (u.D.toQuot Z (F.star O B n b))
      congr 1
      rw [hq, ← (star_basic F n O B).2.2.2.2.2.1]
      exact hI _ hab)
  have hψ : ∀ y, MulOpposite.unop (ψ (u.D.toQuot Z y)) = u.D.toQuot Z (F.star O B n y) := fun y => rfl
  obtain ⟨t, ht⟩ := (d_tr DE).1 hn
  have htq : ∀ w, DE.tr (u.D.toQuot Z w) = u.D.toDet.tr w := by
    intro w
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (u.D.toQuot Z)).1 w]
  have hinv : ∀ w, u.D.toDet.chi (F.star O B n w) = u.D.toDet.chi w := by
    intro w
    conv_rhs => rw [← hop]
    rw [(d_pull _ (F.starOp O B n)).1 w]
    exact ((d_op _).1 (F.star O B n w)).symm
  refine ⟨DE,
    { st := { toFun := fun x => MulOpposite.unop (ψ x)
              map_add' := fun x y => by simp
              map_smul' := fun b x => by simp }
      st_mul := fun x y => by simp
      st_st := ?_
      tr := t
      tr_comm := ?_
      tr_st := ?_ }, hCH, hpull, fun y => hψ y, fun y => ht y⟩
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change MulOpposite.unop (ψ (MulOpposite.unop (ψ (u.D.toQuot Z y)))) = u.D.toQuot Z y
    rw [hψ, hψ, (star_basic F n O B).1]
  · intro x y
    rw [ht, ht]
    exact (d_tr DE).2.1 1 x y
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change t (MulOpposite.unop (ψ (u.D.toQuot Z y))) = t (u.D.toQuot Z y)
    rw [hψ, ht, ht, htq, htq]
    show (-1) ^ 1 * (u.D.toDet.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi y).coeff (n - 1)
    rw [hinv]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatEx

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem lift_ex {B C E M : Type} [CommRing B] [CommRing C] [Algebra B C] [Ring E] [Algebra B E] [Ring M]
    [Algebra C M] (ρ : E →+* M) (hρ : ∀ b, ρ (algebraMap B E b) = algebraMap C M (algebraMap B C b)) :
    ∃ r : C ⊗[B] E →ₐ[C] M, ∀ y, r (1 ⊗ₜ y) = ρ y := by
  letI : Algebra B M := Algebra.compHom M (algebraMap B C)
  haveI : IsScalarTower B C M := .of_algebraMap_eq' rfl
  let ρ' : E →ₐ[B] M := { ρ with commutes' := hρ }
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId C M) ρ' fun s _ => Algebra.commute_algebraMap_left s _, fun y => ?_⟩
  refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
  rw [map_one, one_mul]
  rfl

private theorem tr_bc {n : ℕ} {B E : Type} [CommRing B] [Ring E] [Algebra B E] (D : Det n B E) (hn : 1 ≤ n)
    (C : Type) [CommRing C] [Algebra B C] (t : C ⊗[B] E →ₗ[C] C) (ht : ∀ y, t (1 ⊗ₜ y) = algebraMap B C (D.tr y))
    (y : C ⊗[B] E) : t y = (D.baseChange C).tr y := by
  obtain ⟨t', ht'⟩ := (d_tr (D.baseChange C)).1 hn
  rw [← ht']
  induction y with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul c z =>
    have : c ⊗ₜ[B] z = c • ((1 : C) ⊗ₜ[B] z) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, ht, ht']
    congr 1
    exact (((d_bc D C).2.2.2 z).2 1).symm

theorem UpperTheory.V.Pa.hat_ex :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → Nonempty (Hat h x u.D P.ker Bh (G.frame.eps O B)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hB
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    clear hB
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_comp,
      Function.comp_apply, RingHom.mapMatrix_apply, Algebra.algebraMap_self]
    rfl
  have hρv : ∀ (b : B) (i j : Fin n), (algebraMap x.A (FractionRing x.A)) ((P.rep (MonoidAlgebra.single 1 b)) i j) =
      algebraMap Bh (Matrix (Fin n) (Fin n) (FractionRing x.A)) (algebraMap B Bh b) i j := by
    intro b i j
    rw [hrep, map_one, map_one, Matrix.smul_apply, Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, if_pos rfl, hB, smul_eq_mul, mul_one]
    · rw [Matrix.one_apply_ne hij, if_neg hij, smul_zero, map_zero]
  have hφ : PhiCond G.frame.G₀ l := phi_fg _ P.fg
  have hn : 1 ≤ n := le_trans x.a_pos x.a_le
  haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)
  haveI : CompactSpace G.frame.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.frame.η_open).isCompact
  obtain ⟨DE, T, hCH, hpull, hst, htr⟩ := trinv u hφ hn P.gens (gens_kill P)
  obtain ⟨hres, -, hh, χ, hred, hmf⟩ := pair_mf u hφ
  obtain ⟨-, hfinB, hcont⟩ := finE u.D χ u.cont hred hmf P.gens
  have hπs : Function.Surjective (u.D.toQuot P.gens) := fun q =>
    Quotient.inductionOn' q fun z => ⟨z, rfl⟩
  obtain ⟨ι, hιs, hιmap, hιker, hιpull⟩ := tens u.D DE (u.D.toQuot P.gens) Bh hπs hpull
  have hker : {z | u.D.toQuot P.gens z = 0} = P.ker := by
    ext z
    change ((z : (u.D.chBar P.gens).ringCon.Quotient) = ((0 : MonoidAlgebra B G.G₀) : _)) ↔ _
    rw [RingCon.eq, TwoSidedIdeal.rel_iff, sub_zero]
    rfl
  rw [hker] at hιker
  have hs : ∀ g : G.G₀, ι (MonoidAlgebra.single g 1) = 1 ⊗ₜ[B] u.D.toQuot P.gens (MonoidAlgebra.single g 1) := by
    intro g
    have := hιmap (MonoidAlgebra.single g 1)
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  haveI : Module.Finite B (u.D.CHQuot P.gens) := hfinB
  obtain ⟨T', hT'st, hT'tr⟩ := trinv_baseChange T Bh
  obtain ⟨ρ0, hρ0⟩ := rep_quot P
  have hρ : ∀ b : B, ((algebraMap x.A (FractionRing x.A)).mapMatrix.comp ρ0)
      (algebraMap B (u.D.CHQuot P.gens) b) =
      algebraMap Bh (Matrix (Fin n) (Fin n) (FractionRing x.A)) (algebraMap B Bh b) := by
    intro b
    have e1 : algebraMap B (u.D.CHQuot P.gens) b = u.D.toQuot P.gens (MonoidAlgebra.single 1 b) :=
      ((u.D.toQuot P.gens).commutes b).symm
    ext i j
    rw [RingHom.comp_apply, e1, hρ0, RingHom.mapMatrix_apply, Matrix.map_apply, hρv]
  obtain ⟨rr, hrr⟩ := lift_ex ((algebraMap x.A (FractionRing x.A)).mapMatrix.comp ρ0) hρ
  have hπg : ∀ (g : G.G₀) (c : B), u.D.toQuot P.gens (MonoidAlgebra.single g c) =
      c • u.D.toQuot P.gens (MonoidAlgebra.single g 1) := by
    intro g c
    rw [← map_smul, MonoidAlgebra.smul_single', mul_one]
  refine ⟨Hat.mk (Bh ⊗[B] u.D.CHQuot P.gens) inferInstance ι hιs hιker (DE.baseChange Bh)
    ((d_chS DE Bh).2.2 hCH).1 hιpull T' (fun y => tr_bc DE hn Bh T'.tr (fun z => by rw [hT'tr, htr]) y)
    (fun g => ?_) rr (fun g => ?_) (Submodule.map (TensorProduct.mk B Bh (u.D.CHQuot P.gens) 1) ⊤)
    (Module.Finite.fg_top.map _) (fun g => ⟨_, trivial, (hs g).symm⟩) (fun j => ?_)⟩
  · rw [hs, hs, hT'st, hst, (star_basic G.frame n O B).2.2.2.2.2.2 g 1, one_mul, hπg,
      TensorProduct.tmul_smul, algebraMap_smul]
  · rw [hs, hrr, RingHom.comp_apply, hρ0, hrep, map_one, one_smul, RingHom.mapMatrix_apply]
  · obtain ⟨U, hU⟩ := hcont j
    refine ⟨U, fun g v hv => ?_⟩
    have hl : u.D.toQuot P.gens (MonoidAlgebra.single g 1) * (u.D.toQuot P.gens (MonoidAlgebra.single v 1) - 1) ∈
        (maximalIdeal B ^ j • ⊤ : Submodule B (u.D.CHQuot P.gens)) := by
      have := Submodule.mem_map_of_mem
        (f := LinearMap.mulLeft B (u.D.toQuot P.gens (MonoidAlgebra.single g 1))) (hU v hv)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have key := Submodule.mem_map_of_mem (f := TensorProduct.mk B Bh (u.D.CHQuot P.gens) 1) hl
    rw [Submodule.map_smul''] at key
    convert key using 1
    have e : MonoidAlgebra.single (g * v) (1 : B) = MonoidAlgebra.single g 1 * MonoidAlgebra.single v 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hs, hs, TensorProduct.mk_apply, e, map_mul, mul_sub, mul_one, TensorProduct.tmul_sub]
end
end
