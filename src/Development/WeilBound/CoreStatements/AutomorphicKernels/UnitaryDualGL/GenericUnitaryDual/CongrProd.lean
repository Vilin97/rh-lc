module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.NormEqOneOfIsUnitarisableU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIffStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PCentred
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PS_conj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PUnit
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PSLang

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Symm.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isL_of_noPrec {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hL : ∀ j, IsLSeg (Γ j) (x j).rep)
    (hp : ∀ i j, ¬ (Γ i).Precedes (Γ j)) (hd : ∑ j, (x j).1 = N) :
    (prodIrr x hd).IsIrreducible ∧ ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W),
      Nonempty ((prodIrr x hd).Equiv σ) → IsL (Finset.univ.val.map Γ) σ := by
  have hirr : (prodIrr x hd).IsIrreducible :=
    PositivityTheory.Exh.lUnlinkedIrr_of_seg PositivityTheory.RgGu.segmentRepresentation k h N Γ x hd
      (fun i j hl => (GlobalTheory.SmGL.Segment.linked_iff_precedes.mp hl).elim (hp i j) (hp j i)) hL
  refine ⟨hirr, ?_⟩
  intro W _ _ σ e
  obtain ⟨e⟩ := e
  exact ⟨h, x, hd, ⟨Γ, ⟨rfl, fun i j _ => hp i j⟩, hL⟩,
    GlobalTheory.LocGL.IsCosocle.of_equiv (GlobalTheory.LocGL.isCosocle_self hirr) e (Representation.Equiv.refl _)⟩

theorem multiset_of_equiv [CharZero k] {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (t t' : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Γ j) (y j).rep)
    (hp : ∀ i j, ¬ ((Γ i).nu (t i : ℂ)).Precedes ((Γ j).nu (t j : ℂ)))
    (hp' : ∀ i j, ¬ ((Γ i).nu (t' i : ℂ)).Precedes ((Γ j).nu (t' j : ℂ)))
    (hd : ∑ j, ((y j).nu (t j)).1 = N) (hd' : ∑ j, ((y j).nu (t' j)).1 = N)
    (e : Nonempty ((prodIrr (fun j => (y j).nu (t j)) hd).Equiv (prodIrr (fun j => (y j).nu (t' j)) hd'))) :
    (Finset.univ.val.map fun j => (Γ j).nu (t j : ℂ)) = Finset.univ.val.map fun j => (Γ j).nu (t' j : ℂ) := by
  obtain ⟨e⟩ := e
  obtain ⟨hi, hA⟩ := isL_of_noPrec (fun j => (Γ j).nu (t j : ℂ)) (fun j => (y j).nu (t j))
    (fun j => GlobalTheory.isLSeg_nu (hL j) _) hp hd
  obtain ⟨-, hB⟩ := isL_of_noPrec (fun j => (Γ j).nu (t' j : ℂ)) (fun j => (y j).nu (t' j))
    (fun j => GlobalTheory.isLSeg_nu (hL j) _) hp' hd'
  let z := IrrGL.of _ (isSmooth_prodIrr _ hd) hi
  have a : (prodIrr (fun j => (y j).nu (t j)) hd).Equiv z.rep := IrrGL.equivOf _ (isSmooth_prodIrr _ hd) hi
  exact (PositivityTheory.Exh.langlandsMultisegments_holds k).1 _ _ z (hA _ ⟨a⟩) (hB _ ⟨e.symm.trans a⟩)

end PositivityTheory.Gud.Symm.Pf

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PSSeg

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Symm.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segDual_nu (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (s : ℂ) :
    Zc.segDual (Δ.nu s) = (Zc.segDual Δ).nu (-s) := by
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (Zc.dualCl x).IsCusp := fun x hx => (GlobalTheory.T.dual_class_cuspidal hA x hx).1
  refine Segment.ext_first ?_ ?_
  · show (Zc.segDual (Δ.nu s)).first = (Zc.segDual Δ).first.nu (-s)
    rw [GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc]
    show (Zc.dualCl (Δ.first.nu s)).nu (1 - ((Δ.len : ℕ) : ℂ)) = _
    rw [GlobalTheory.T.dual_class_twist_neg hA, IrrGL.nu_nu, IrrGL.nu_nu]
    congr 1
    ring
  · show (Zc.segDual (Δ.nu s)).len = (Zc.segDual Δ).len
    rw [GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc]
    rfl

theorem segDual_segDual (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Zc.segDual (Zc.segDual Δ) = Δ := by
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (Zc.dualCl x).IsCusp :=
    fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  apply GlobalTheory.SmGL.Segment.ext_first
  · rw [GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc,
      GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA,
      GlobalTheory.LocGL.IrrGL.nu_nu, neg_add_cancel, GlobalTheory.LocGL.IrrGL.nu_zero]
  · rw [GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc]



theorem isLSeg_dualCl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} {δ : IrrGL (k := k)} (hL : IsLSeg Δ δ.rep) :
    IsLSeg (Zc.segDual Δ) (Zc.dualCl δ).rep := by
  have gk : Zc.Cos.GKLocal k := by
    intro N V _ _ π hs hi
    exact GlobalTheory.GelfandKazhdan.equiv_contra k N V π (hA k N V π hs hi) hi
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (Zc.dualCl x).IsCusp :=
    fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  obtain ⟨hd, cos⟩ := hL
  have hlen : Δ.len = (Zc.segDual Δ).len := (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc Δ).symm
  obtain ⟨hd1, ⟨e1⟩⟩ := GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW hA gk Δ.term hd
  obtain ⟨hdQ, ⟨e2⟩⟩ := GlobalTheory.CompanionTheory.SegIncDual.exists_equiv_prodIrr_of_cast hlen
    (fun a => Zc.dualCl (Δ.term a.rev)) (Zc.segDual Δ).term (by
      intro a
      rw [GlobalTheory.CompanionTheory.SegIncDual.dualCl_term hA Δ hlen]
      show (Zc.segDual Δ).term (Fin.cast hlen a.rev).rev = _
      congr 1
      ext
      simp [Fin.val_rev]
      omega) hd1
  have c1 : IsCosocle δ.rep
      (MonoidHom.comp (MonoidHom.comp (prodIrr Δ.term hd) (Zc.Cos.thetaW k _)) (Zc.Cos.thetaW k _)) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact cos
  have c2 := GlobalTheory.CompanionTheory.LSocle.isCosocle_comp_thetaW c1
  obtain ⟨e3⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra gk _ δ.rep δ.snd.rep.smooth δ.snd.rep.irr
  have c3 : IsCosocle (contra δ.rep) (prodIrr (Zc.segDual Δ).term hdQ) :=
    GlobalTheory.LocGL.IsCosocle.of_equiv c2 e3 (e1.trans e2)
  have key : ∀ (hs : IsSmooth (contra δ.rep)) (hi : (contra δ.rep).IsIrreducible),
      IsLSeg (Zc.segDual Δ) (IrrGL.of (contra δ.rep) hs hi).rep := by
    intro hs hi
    obtain ⟨e4⟩ := GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep
      (⟨_, contra δ.rep, hs, hi⟩ : IrrRep (GL (Fin δ.fst) k))
    exact ⟨hdQ, GlobalTheory.LocGL.IsCosocle.of_equiv c3 e4.symm (Representation.Equiv.refl _)⟩
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  exact key _ _

end PositivityTheory.Gud.Symm.Pf

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.CongrProd

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Fin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem congrProd' {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem segs_symm [CharZero k] {h N : ℕ} (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Δ j) (δ j).rep) (hU : ∀ j, PositivityTheory.RgUd.UOrder.UnitCC (δ j).rep) (hs : ∀ j, |s j| < 1 / 2)
    (hd : ∑ j, ((δ j).nu (s j)).1 = N) (hi : (prodIrr (fun j => (δ j).nu (s j)) hd).IsIrreducible)
    (hu : IsUnitarisable (prodIrr (fun j => (δ j).nu (s j)) hd)) :
    (Finset.univ.val.map fun j => (Δ j).nu ((s j : ℝ) : ℂ)) =
      Finset.univ.val.map fun j => (Δ j).nu ((-s j : ℝ) : ℂ) := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.RgGu.NR.ConjDual.irrAdm'
  have hδu : ∀ j, IsUnitarisable (δ j).rep := fun j => PositivityTheory.Gud.Pf.unitarisable_of_unitCC (hL j) (hU j)
  have hc : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j) := fun j => PositivityTheory.Gud.Pf.isCentred_of_unitCC (hL j) (hU j)
  obtain ⟨hd1, ⟨e1⟩⟩ := PositivityTheory.Gud.Symm.Pf.conj_side hA δ s hδu hd hi hu
  obtain ⟨hd2, ⟨e2⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun j => (δ j).nu (s j)) hd
  have hfun : (fun j => Zc.dualCl ((δ j).nu (s j))) = fun j => (Zc.dualCl (δ j)).nu (((fun j => -s j) j : ℝ) : ℂ) :=
    funext fun j => by rw [GlobalTheory.T.dual_class_twist_neg hA]; push_cast; rfl
  have hd3 : ∑ j, ((Zc.dualCl (δ j)).nu (((fun j => -s j) j : ℝ) : ℂ)).1 = N := by
    rw [← hd2]; exact congrArg (fun f : Fin h → IrrGL (k := k) => ∑ j, (f j).1) hfun.symm
  obtain ⟨e3⟩ := congrProd' hfun hd2 hd3
  have E := e1.symm.trans (e2.trans e3)

  have key : ∀ (t : Fin h → ℝ), (∀ j, |t j| < 1 / 2) → ∀ i j,
      ¬ ((Zc.segDual (Δ i)).nu (t i : ℂ)).Precedes ((Zc.segDual (Δ j)).nu (t j : ℂ)) := by
    intro t ht i j hP
    have r : ∀ a, (Zc.segDual (Δ a)).nu (t a : ℂ) = Zc.segDual ((Δ a).nu ((-t a : ℝ) : ℂ)) := fun a => by
      rw [PositivityTheory.Gud.Symm.Pf.segDual_nu hA]; push_cast; rw [neg_neg]
    rw [r, r, GlobalTheory.T.segment_dual_precedes_iff hA] at hP
    have := PositivityTheory.UdReth2.add_one_le_of_precedes _ _ (hc j) (hc i) _ _ hP
    have h1 := ht i; have h2 := ht j
    rw [abs_lt] at h1 h2
    linarith
  have hM := PositivityTheory.Gud.Symm.Pf.multiset_of_equiv (fun j => Zc.segDual (Δ j)) (fun j => Zc.dualCl (δ j)) s (fun j => -s j)
    (fun j => PositivityTheory.Gud.Symm.Pf.isLSeg_dualCl hA (hL j)) (key s hs) (key (fun j => -s j) (fun j => by simpa using hs j))
    hd1 hd3 ⟨E⟩
  have hM2 := congrArg (Multiset.map Zc.segDual) hM
  simp only [Multiset.map_map, Function.comp_def] at hM2
  have r2 : ∀ (a : Fin h) (t : ℝ), Zc.segDual ((Zc.segDual (Δ a)).nu (t : ℂ)) = (Δ a).nu ((-t : ℝ) : ℂ) := fun a t => by
    rw [PositivityTheory.Gud.Symm.Pf.segDual_nu hA, PositivityTheory.Gud.Symm.Pf.segDual_segDual hA]; push_cast; rfl
  simp only [r2, neg_neg] at hM2
  exact hM2.symm

end PositivityTheory.Gud.Fin

end
end
end
