module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Mathlib.Order.Sigma
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquivStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotientStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForall
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.Group.Units
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotientsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOneStatement
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapProductSegments

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {r r' N : ℕ} (hr : r = r') (v : Fin r → IrrGL (k := k)) (w : Fin r' → IrrGL (k := k))
    (hvw : ∀ i, v i = w (Fin.cast hr i)) (hv : ∑ a, (v a).1 = N) (hw : ∑ a, (w a).1 = N) :
    Nonempty ((prodIrr v hv).Equiv (prodIrr w hw)) := by
  subst hr
  have e : v = w := funext fun i => (hvw i).trans (congrArg w (Fin.ext rfl))
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem flatten {s h N : ℕ} (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k)) (d : Fin s → ℕ)
    (hd : ∀ a, ∑ b, (u a b).1 = d a) (hN : ∑ a, d a = N) (F : Fin h ≃o Σₗ a, Fin (t a))
    (x : Fin h → IrrGL (k := k)) (hx : ∀ c, u (ofLex (F c)).1 (ofLex (F c)).2 = x c) (hxN : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks d hN) fun a => prodIrr (u a) (hd a)).Equiv (prodIrr x hxN)) := by
  have e : (fun c => u (ofLex (F c)).1 (ofLex (F c)).2) = x := funext hx
  subst e
  have hS := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1)
    (fun a => stdBlocks (fun b => (u a b).1) (hd a)) (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep)
    (Fin N) (stdBlocks d hN)
  refine Exists.elim hS fun E0 hχ => ?_
  let E : (Σ c : Fin h, Fin (u (ofLex (F c)).1 (ofLex (F c)).2).1) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F.toEquiv).trans E0
  have hω := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F F.strictMono F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  refine hχ.elim fun χ => hω.elim fun ω => ?_
  refine (GlobalTheory.ProdReorder.multiProd_placing (k := k) E (stdBlocks (fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).1) hxN)
    fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).rep).elim fun p => ?_
  exact ⟨(χ.trans ω).trans p⟩

def grp (h j : ℕ) : Fin 3 → ℕ := ![j, 2, h - (j + 2)]

def off (j : ℕ) : Fin 3 → ℕ := ![0, j, j + 2]

theorem off_add_grp_le {h j : ℕ} (hj : j + 1 < h) (a : Fin 3) : off j a + grp h j a ≤ h := by
  fin_cases a <;> simp [off, grp] <;> omega

theorem off_add_grp_le_off {h j : ℕ} (hj : j + 1 < h) {a a' : Fin 3} (haa : a < a') :
    off j a + grp h j a ≤ off j a' := by
  fin_cases a <;> fin_cases a' <;> simp [off, grp] at haa ⊢

def place {h j : ℕ} (hj : j + 1 < h) (c : Σₗ a, Fin (grp h j a)) : Fin h :=
  ⟨off j (ofLex c).1 + (ofLex c).2, by
    have := off_add_grp_le hj (ofLex c).1
    have := (ofLex c).2.2
    omega⟩

theorem place_strictMono {h j : ℕ} (hj : j + 1 < h) : StrictMono (place hj) := by
  intro c c' hc
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  rcases Sigma.Lex.lt_def.1 hc with hlt | ⟨e, hlt⟩
  · have h1 : off j a + grp h j a ≤ off j a' := off_add_grp_le_off hj hlt
    have h2 : (b : ℕ) < grp h j a := b.2
    show off j a + b < off j a' + b'
    omega
  · obtain rfl : a = a' := e
    have : (b : ℕ) < b' := hlt
    show off j a + b < off j a + b'
    omega

theorem card_lex {h j : ℕ} (hj : j + 1 < h) : Fintype.card (Σₗ a, Fin (grp h j a)) = h := by
  rw [Fintype.card_lex, Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_three]
  show j + 2 + (h - (j + 2)) = h
  omega

theorem place_bijective {h j : ℕ} (hj : j + 1 < h) : Function.Bijective (place hj) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨(place_strictMono hj).injective, by simp [card_lex hj]⟩

def order {h j : ℕ} (hj : j + 1 < h) : Fin h ≃o Σₗ a, Fin (grp h j a) :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).symm

theorem place_order {h j : ℕ} (hj : j + 1 < h) (c : Fin h) : place hj (order hj c) = c :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).apply_symm_apply c

theorem sum_place {h j : ℕ} (hj : j + 1 < h) (g : Fin h → ℕ) :
    ∑ a, ∑ b : Fin (grp h j a), g (place hj (toLex ⟨a, b⟩)) = ∑ c, g c := by
  rw [← Fintype.sum_sigma (fun p : Σ a, Fin (grp h j a) => g (place hj (toLex p)))]
  exact Equiv.sum_comp (toLex.trans (Equiv.ofBijective _ (place_bijective hj))) g

theorem fin_three_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (a : Fin 3) : P a := by
  fin_cases a
  exacts [h0, h1, h2]

section Main

variable {h N j M : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k))

def fac (a : Fin 3) (b : Fin (grp h j a)) : IrrGL (k := k) := x (place hj (toLex ⟨a, b⟩))

def fac' (a : Fin 3) (b : Fin (grp h j a)) : IrrGL (k := k) :=
  x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ (place hj (toLex ⟨a, b⟩)))

theorem fac'_zero : fac' hj x 0 = fac hj x 0 := by
  funext b
  have hb : (b : ℕ) < j := b.2
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 0 + b ≠ j
    simp [off]; omega
  · show off j 0 + b ≠ j + 1
    simp [off]; omega

theorem fac'_two : fac' hj x 2 = fac hj x 2 := by
  funext b
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 2 + b ≠ j
    simp [off]; omega
  · show off j 2 + b ≠ j + 1
    simp [off]; omega

theorem place_one_zero : place hj (toLex ⟨1, (0 : Fin 2)⟩) = ⟨j, by omega⟩ := Fin.ext (by
  show off j 1 + 0 = j
  simp [off])

theorem place_one_one : place hj (toLex ⟨1, (1 : Fin 2)⟩) = ⟨j + 1, hj⟩ := Fin.ext (by
  show off j 1 + 1 = j + 1
  simp [off])

theorem fac_one : (fac hj x 1 : Fin 2 → IrrGL (k := k)) = ![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] := by
  funext b
  fin_cases b
  · exact congrArg x (place_one_zero hj)
  · exact congrArg x (place_one_one hj)

theorem fac'_one : (fac' hj x 1 : Fin 2 → IrrGL (k := k)) = ![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] := by
  funext b
  fin_cases b
  · refine congrArg x ?_
    refine (congrArg _ (place_one_zero hj)).trans (Equiv.swap_apply_left _ _)
  · refine congrArg x ?_
    refine (congrArg _ (place_one_one hj)).trans (Equiv.swap_apply_right _ _)

end Main

end GlobalTheory.CompanionTheory.BZSwap
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotient

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMulti

theorem multiProd_isSubquotient_of_forall (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M)
    (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i))
    (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i))
    (hs : ∀ i, IsSmooth (ρ' i)) (hq : ∀ i, IsSubquotient (ρ i) (ρ' i)) :
    IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') :=
  GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ (GlobalTheory.SmGL.stdBlocks N hM) _ _ _ _
    (GlobalTheory.SmGL.isSmooth_piTensor hs)
    (GlobalTheory.piTensor_isSubquotient_of_forall _ _ X Y ρ ρ' hq)

end GlobalTheory.CompanionTheory.GenMulti
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotientStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.product_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M) (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i)) (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i)), (∀ i, IsSmooth (ρ' i)) → (∀ i, IsSubquotient (ρ i) (ρ' i)) → IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') := by
  first | exact @GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | exact GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | (intros; apply GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GenSwap

open GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem isGenericFor_prodIrr (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) (hC : GlobalTheory.BZSeg.CuspGeneric k)
    {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hc : ∀ a, (x a).IsCusp) (hd : ∑ a, (x a).1 = N) : IsGenericFor ψ (prodIrr x hd) := by
  rw [← isGeneric_iff_isGenericFor hψ h1]
  exact (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity k hW h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)).2 fun a =>
      hC _ _ _ (hc a).1 (x a).2.rep.smooth (x a).2.rep.irr (hc a).2

theorem isSubquotient_of_generic_common {N : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) {U V V' W : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (T : Representation ℂ (GL (Fin N) k) U) (P : Representation ℂ (GL (Fin N) k) V)
    (P' : Representation ℂ (GL (Fin N) k) V') (hT : IsSubquotient T P) (hT' : IsSubquotient T P')
    (hTg : IsGenericFor ψ T) (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTs : IsSmooth T := hT.isSmooth hP
  have hTf : GlobalTheory.SmGL.HasFiniteLength T := GlobalTheory.CompanionTheory.IrrSub.hasFiniteLength_of_isSubquotient hT hfl
  obtain ⟨A, B, -, hi', -, hg'⟩ := GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ N T hTs hTf hTg
  have s₁ := GlobalTheory.ParIndExact.isSubquotient_subQuot A B
  obtain ⟨e⟩ := GlobalTheory.T.whittaker_rank_extension_bound k ψ hψ N P σ (subQuot A B) hP hr hi hi' hsq (s₁.trans hT) hgσ hg'
  exact isSubquotient_of_equiv_left e.symm (s₁.trans hT')

theorem isSubquotient_of_common {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y Z : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Z a)) (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a))
    (hτ : ∀ a, IsSmooth (τ a)) (hq : ∀ a, IsSubquotient (τ a) (π a)) (hq' : ∀ a, IsSubquotient (τ a) (π' a))
    (hg : ∀ a, IsGenericFor ψ (τ a)) {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTg : IsGenericFor ψ (multiProd (stdBlocks d hN) τ) := by
    obtain ⟨H⟩ := hW ψ hψ h1 s N d hN Z τ hτ
    have : Nontrivial (⨂[ℂ] a, TwJacquet (τ a) (unipB k (Fin (d a))) (whitChar ψ (d a))) :=
      (GlobalTheory.CompanionTheory.Leib.nontrivial_piTensorProduct_iff _).2 hg
    exact H.toEquiv.nontrivial
  exact isSubquotient_of_generic_common hψ _ P P'
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z X τ π hπ hq) E)
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z Y τ π' hπ' hq') E') hTg hP hfl hr σ hi hgσ hsq

theorem isSubquotient_of_positions {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a)) (hg : ∀ a, IsGenericFor ψ (π a))
    (hf : ∀ a, GlobalTheory.SmGL.HasFiniteLength (π a))
    (hsw : ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (π a) → IsSubquotient g (π' a))
    {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have ex := fun a => GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ (d a) (π a) (hπ a) (hf a) (hg a)
  choose A B _ hirr hsm hgen using ex
  have hq : ∀ a, IsSubquotient (subQuot (A a) (B a)) (π a) := fun a => GlobalTheory.ParIndExact.isSubquotient_subQuot _ _
  exact isSubquotient_of_common hW hψ h1 d hN π π' (fun a => subQuot (A a) (B a)) hπ hπ' hsm hq
    (fun a => hsw a _ _ (hsm a) (hirr a) (hq a)) hgen P P' E E' hP hfl hr σ hi hgσ hsq

theorem fac_rev {h j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (i : Fin 2) :
    (fac hj x 1 : Fin 2 → IrrGL (k := k)) (Fin.rev i) = (fac' hj x 1 : Fin 2 → IrrGL (k := k)) i := by
  rw [fac_one hj x, fac'_one hj x]
  fin_cases i <;> rfl

theorem nonempty_equiv_of_eq {n M : ℕ} {u v : Fin n → IrrGL (k := k)} (e : u = v) (h₁ : ∑ a, (u a).1 = M)
    (h₂ : ∑ a, (v a).1 = M) : Nonempty ((prodIrr u h₁).Equiv (prodIrr v h₂)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩



theorem position_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) {h j : ℕ} (hj : j + 1 < h)
    (x : Fin h → IrrGL (k := k)) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) :
    ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (prodIrr (fac hj x a) (s₁ a)) →
      IsSubquotient g (prodIrr (fac' hj x a) (s₂ a)) := by
  refine fin_three_forall ?_ ?_ ?_
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_zero hj x).symm (s₁ 0) (s₂ 0)
    exact isSubquotient_of_equiv hq E
  · intro W _ _ g hgs hgi hq
    have hd2 : ∑ a, (fac hj x 1 (Fin.rev a)).1 = d 1 :=
      (Equiv.sum_comp Fin.revPerm fun b => (fac hj x 1 b).1).trans (s₁ 1)
    obtain ⟨E⟩ := prodIrr_congr rfl (fun a => fac hj x 1 (Fin.rev a)) (fac' hj x 1) (fun i => fac_rev hj x i) hd2 (s₂ 1)
    exact isSubquotient_of_equiv (GlobalTheory.T.reversed_product_same_subquotients hA hGK (fac hj x 1) (s₁ 1) hd2 g hgs hgi hq) E
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_two hj x).symm (s₁ 2) (s₂ 2)
    exact isSubquotient_of_equiv hq E



theorem core (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) (hW : GlobalTheory.BZMir.Leib.WhitHeredity k)
    (hR : GlobalTheory.BZSeg.WhitRankIrr k) (hC : GlobalTheory.BZSeg.CuspGeneric k) (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {h N j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (hc : ∀ a, (x a).IsCusp) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) (hN : ∑ a, d a = N)
    (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible)
    (hg : IsGenericFor ψ σ) (hsq : IsSubquotient σ (prodIrr x hd)) :
    IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  have hJ : j < h := by omega
  have hkey : ∀ c, fac' hj x (ofLex (order hj c)).1 (ofLex (order hj c)).2 =
      x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ c) := fun c =>
    congrArg (fun y => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ y)) (place_order hj c)
  obtain ⟨p⟩ := flatten (grp h j) (fac hj x) d s₁ hN (order hj) x (fun c => congrArg x (place_order hj c)) hd
  obtain ⟨q⟩ := flatten (grp h j) (fac' hj x) d s₂ hN (order hj)
    (fun a => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ a)) hkey hd'
  exact isSubquotient_of_positions hW hψ h1 d hN (fun a => prodIrr (fac hj x a) (s₁ a))
    (fun a => prodIrr (fac' hj x a) (s₂ a)) (fun _ => isSmooth_prodIrr _ _) (fun _ => isSmooth_prodIrr _ _)
    (fun a => isGenericFor_prodIrr hW hC hψ h1 _ (fun _ => hc _) _) (fun _ => GlobalTheory.T.product_irreducible_finite_length hA _ _)
    (position_swap hA hGK hj x d s₁ s₂) _ _ p q
    (isSmooth_prodIrr _ _) (GlobalTheory.T.product_irreducible_finite_length hA _ _) (GlobalTheory.T.whittaker_rank_product_le_one k hW hR ψ hψ h1 h N x hd) σ hi hg hsq

theorem isSubquotient_prodIrr_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  intro k _ _ _ _ hA hGK hW hR hC ψ hψ h1 h N x hc hd j hj hd' W _ _ σ _ hi hg hsq
  have t : ∑ b : Fin 2, ((fac' hj x 1 : Fin 2 → IrrGL (k := k)) b).1 = ∑ b : Fin 2, ((fac hj x 1 : Fin 2 → IrrGL (k := k)) b).1 := by
    rw [fac_one hj x, fac'_one hj x]
    simp [Fin.sum_univ_two, add_comm]
  have s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = ∑ b, (fac hj x a b).1 :=
    fin_three_forall (by rw [fac'_zero hj x]) t (by rw [fac'_two hj x])
  exact core hA hGK hW hR hC ψ hψ h1 hj x hc (fun a => ∑ b, (fac hj x a b).1) (fun _ => rfl) s₂
    ((sum_place hj fun c => (x c).1).trans hd) hd hd' σ hi hg hsq

end GlobalTheory.CompanionTheory.GenSwap

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGenericStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cuspidal_swap_product_generic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap | exact GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap | (intros; apply GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap <;> assumption)
end
end
