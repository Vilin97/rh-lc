module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGenericStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOneStatement
import Mathlib.Tactic.TypeStar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocks

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMultiProd

theorem multiProd_equiv_stdBlocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  intro k _ _ _ _ h N d hd e X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin N) (fun a => Fin (d a)) e (stdBlocks d hd) _).1 _

end GlobalTheory.CompanionTheory.GenMultiProd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocksStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.multiProd_equiv_standard_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  first | exact @GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | exact GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | (intros; apply GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProduct

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenSupp

theorem hasSupport_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  intro k _ _ _ _ N V _ _ π s hπ
  obtain ⟨h, x, hs, -, hc, e, hsq⟩ := hπ
  have hd : ∑ a, (x a).1 = N := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sigma] using this
  obtain ⟨φ⟩ := GlobalTheory.T.multiProd_equiv_standard_blocks k (fun a => (x a).1) hd e _ (fun a => (x a).rep)
  exact ⟨h, x, hd, hs, fun a => ⟨(hc a).1, (hc a).2.2⟩, hsq.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)⟩

end GlobalTheory.CompanionTheory.GenSupp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProductStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cuspidal_support_realised_by_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | exact GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | (intros; apply GlobalTheory.CompanionTheory.GenSupp.hasSupport_std <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenGK

theorem gkLocal_gen : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k :=
  fun hA => GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA

end GlobalTheory.CompanionTheory.GenGK
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocalStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.gelfand_kazhdan_local : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | exact GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | (intros; apply GlobalTheory.CompanionTheory.GenGK.gkLocal_gen <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.ExistsEquivOfMapUnivEq

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem exists_equiv_of_map_univ_eq {α : Type*} {h h' : ℕ} (x : Fin h → α) (y : Fin h' → α)
    (H : Finset.univ.val.map x = Finset.univ.val.map y) : ∃ e : Fin h ≃ Fin h', ∀ a, y (e a) = x a := by
  classical
  have hc : ∀ v, Fintype.card {a // x a = v} = Fintype.card {b // y b = v} := fun v => by
    have := congrArg (Multiset.count v) H
    simp only [Multiset.count_map] at this
    simp only [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm (b := v)]
    exact this
  exact ⟨Equiv.ofFiberEquiv fun v => Fintype.equivOfCardEq (hc v), fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem genericUnique_of_perm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k)
    (hP : GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd')) :
    GenericUnique k := by
  intro N s V W _ _ _ _ π σ hπ hσ gπ gσ
  obtain ⟨ψ, hψc, hψ1, gπψ⟩ := gπ
  have gσψ : IsGenericFor ψ σ := (isGeneric_iff_isGenericFor hψc hψ1 σ).1 gσ
  obtain ⟨h, x, hd, hxs, hxc, hπx⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k π s hπ
  obtain ⟨h', y, hd', hys, hyc, hσy⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k σ s hσ
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq x y (hxs.trans hys.symm)
  have hh : h = h' := by simpa using Fintype.card_congr e
  subst hh
  have hfun : (fun a => y (e a)) = x := funext he
  subst hfun
  have hσx : IsSubquotient σ (prodIrr (fun a => y (e a)) hd) :=
    hP hA (GlobalTheory.T.gelfand_kazhdan_local hA) hH hW hC ψ hψc hψ1 y hyc hd' e hd σ hσ.isSmooth hσ.isIrreducible gσψ hσy
  exact GlobalTheory.T.whittaker_rank_extension_bound k ψ hψc N (prodIrr (fun a => y (e a)) hd) π σ (isSmooth_prodIrr _ hd)
    (GlobalTheory.T.whittaker_rank_product_le_one k hH hW ψ hψc hψ1 h N _ hd) hπ.isIrreducible hσ.isIrreducible hπx hσx gπψ gσψ

theorem perm_abs {α : Type 1} {h : ℕ} (P : (Fin h → α) → Prop)
    (hP : ∀ (y : Fin h → α) (j : ℕ) (hj : j + 1 < h), P y → P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a))
    (x : Fin h → α) (hx : P x) (τ : Equiv.Perm (Fin h)) : P fun a => x (τ a) := by
  rcases h with _ | n
  · obtain rfl : τ = 1 := Subsingleton.elim _ _
    exact hx
  have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hτ using Submonoid.closure_induction_right with
  | one => exact hx
  | mul_right t ht s hs' ih =>
    obtain ⟨i, rfl⟩ := hs'
    exact hP (fun a => x (t a)) i.1 (by omega) ih

theorem perm_of_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd') := by
  intro k _ _ _ _ hA hG hH hW hC ψ hc h1 h N x hx hd τ hd' W _ _ σ hs hi hg hσ
  let P : (Fin h → IrrGL (k := k)) → Prop := fun y =>
    (∀ a, (y a).IsCusp) ∧ ∃ e : ∑ a, (y a).1 = N, IsSubquotient σ (prodIrr y e)
  have step : ∀ (y : Fin h → IrrGL (k := k)) (j : ℕ) (hj : j + 1 < h), P y →
      P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a) := by
    rintro y j hj ⟨c, e, H⟩
    have e' : ∑ a, (y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N :=
      (Equiv.sum_comp (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) fun a => (y a).1).trans e
    exact ⟨fun a => c _, e', @GlobalTheory.T.cuspidal_swap_product_generic k _ _ _ _ hA hG hH hW hC ψ hc h1 h N y c e j hj e' W _ _ σ hs hi hg H⟩
  obtain ⟨-, e, H⟩ := perm_abs P step x ⟨hx, hd, hσ⟩ τ
  exact H

theorem genericUnique_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k) : GenericUnique k :=
  genericUnique_of_perm hA hH hW hC (@perm_of_swap k _ _ _ _)

end GlobalTheory.RgGu

end
end
end
