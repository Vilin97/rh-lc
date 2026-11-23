module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CobApplyOfDeg
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.Spread
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkBijective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkStrictMono
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CarImpFrel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CardOther
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfUnitaryConjugate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreAnnApply
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FinsetCAR
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsCocycleOfMapToDegreeOneTerm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExpMemUJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GlRelOfBracket
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExpMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExt
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HwMapOfLowSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IndOfNot
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InnerEqZeroOfWeight
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KExp
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KhwExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KsetSubsetUjset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KummerLiftedCocycleImageEqPicardClass
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemUJsetOfMemKset
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MulMemUJset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumInsertErase
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordMonomial
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZetaDegZero

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AlgCoreSubOfAlgCore

section

section

open Formalism.REAL CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.DSCoreSub

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

theorem ofFn_prod_intertwine (φ : V' →ₗ[ℂ] V) :
    ∀ {t : ℕ} (f' : Fin t → Module.End ℂ V') (f : Fin t → Module.End ℂ V),
      (∀ k x, φ (f' k x) = f k (φ x)) → ∀ x, φ ((List.ofFn f').prod x) = (List.ofFn f).prod (φ x)
  | 0, _, _, _, x => by simp
  | t + 1, f', f, h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, ofFn_prod_intertwine φ _ (fun k => f k.succ) (fun k => h k.succ)]

theorem qdet_intertwine (φ : V' →ₗ[ℂ] V) (E' : Fin n → Fin n → Module.End ℂ V')
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b x, φ (E' a b x) = E a b (φ x)) (u : ℂ) (x : V') :
    φ (qdet E' u x) = qdet E u (φ x) := by
  unfold qdet qminor

  simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, Module.End.intCast_apply, map_zsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine ofFn_prod_intertwine φ _ _ (fun k y => ?_) x
  unfold Tm
  split_ifs <;> simp [h, Module.algebraMap_end_apply]

theorem algCoreSub_of_algCore : AlgCore → AlgCoreSub := by
  intro hA n ε lam V _ _ E V₀ v S hlam hgl hun hst hS hv hfd hK hvS hmin Y
  let E' : Fin n → Fin n → Module.End ℂ V₀ := fun a b => (E a b).restrict (hst a b)
  have hE : ∀ a b (x : V₀), ((E' a b x : V₀) : V) = E a b x := fun a b x => rfl
  have hhi : ∀ (μ : Fin n → ℝ) (x : V₀), KHighest ε E' μ x ↔ KHighest ε E μ (x : V) := by
    intro μ x
    unfold KHighest IsWeight
    simp only [Subtype.ext_iff, hE, Submodule.coe_smul, Submodule.coe_zero]
  have hgl' : GlRel E' := by
    intro a b c d
    ext x
    have := LinearMap.congr_fun (hgl a b c d) (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE] at this ⊢
    rw [this]
    split_ifs <;> simp [hE]
  have hun' : IsUnitary ε E' := fun a b x y => hun a b x y
  haveI : FiniteDimensional ℂ (S.comap V₀.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  have key := hA n ε lam V₀ E' ⟨v, hS hvS⟩ (S.comap V₀.subtype) hlam hgl' hun' ((hhi _ _).2 hv) inferInstance
    (fun a b hab x hx => hK a b hab x hx) hvS
    (fun μ x hx hμ => hmin μ x x.2 (fun h0 => hx (Subtype.ext h0)) ((hhi μ x).1 hμ)) Y
  have h2 := qdet_intertwine V₀.subtype E' E hE (Y + ((n : ℂ) - 1) / 2) ⟨v, hS hvS⟩
  rw [key] at h2
  simpa using h2.symm

end GlobalTheory.CompanionTheory.DSCoreSub
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreApply

section

@[expose] public section

open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainCAR

variable {n : ℕ} {ε : Fin n → Bool}

theorem key_inj {i j : NC ε} (h : key i = key j) : i = j := by
  apply Subtype.ext (finProdFinEquiv.injective (Fin.ext ?_))
  change (i.1.2 : ℕ) + n * (i.1.1 : ℕ) = (j.1.2 : ℕ) + n * (j.1.1 : ℕ)
  unfold key at h
  simpa [Nat.mul_comm, Nat.add_comm] using h

def tw (i j : NC ε) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : NC ε) : tw i i = 1 := by
  simp [tw]

theorem tw_mul_self (i j : NC ε) : tw i j * tw i j = 1 :=
  _root_.CompanionTheory.FinsetCAR.tw_mul_self key i j

theorem tw_swap {i j : NC ε} (h : i ≠ j) : tw j i = -tw i j :=
  _root_.CompanionTheory.FinsetCAR.tw_swap key (fun _ _ h => key_inj h) h

theorem sg_mul_self (i : NC ε) (A : Finset (NC ε)) : sg i A * sg i A = 1 :=
  _root_.CompanionTheory.FinsetCAR.sg_mul_self key i A

theorem sg_insert (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_insert key i h

theorem sg_erase (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_erase key i h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : NC ε) : (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_ann key (fun _ _ h => key_inj h) i j

theorem cre_cre (i j : NC ε) : (cre i * cre j + cre j * cre i : Module.End ℂ (Ch ε V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.cre_cre key (fun _ _ h => key_inj h) i j

theorem ann_cre (i j : NC ε) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Ch ε V)) = if i = j then 1 else 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_cre key (fun _ _ h => key_inj h) i j

theorem car : CompanionTheory.D.DSIC.CAR := fun _ _ _ _ _ i j => ⟨ann_ann i j, cre_cre i j, ann_cre i j⟩

end GlobalTheory.CompanionTheory.ChainCAR
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsAlt

section

section

namespace GlobalTheory.CompanionTheory.DSCapelliAction

theorem actQ : CompanionTheory.D.DSIC.ActQ := by
  intro n ε H _ _ σ S E h u v
  exact GlobalTheory.CapelliFreeAction.actU_qdet n ε H σ S E (fun a b w => h.act a b w) u v

end GlobalTheory.CompanionTheory.DSCapelliAction
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WlemOfGfacts

section

@[expose] public section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICWLem

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

def ht {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) * w c

theorem ht_add_root {n : ℕ} (w : Fin n → ℝ) (c d : Fin n) (h : c < d) :
    ht w < ht (w + Pi.single c 1 - Pi.single d 1) := by
  have hcd : ((c : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast h
  have : ht (w + Pi.single c 1 - Pi.single d 1) =
      ht w + ((n : ℝ) - (c : ℕ)) - ((n : ℝ) - (d : ℕ)) := by
    simp [ht, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  rw [this]
  linarith

theorem wlem_of_gfacts (hG : GFacts) : WLem := by
  intro n ε V _ _ E γ x hx hK
  obtain ⟨g, hg, -, hwt, hdiag, -⟩ := hG n ε
  classical
  have hne : (univ.filter fun A : Finset (NC ε) => x A ≠ 0).Nonempty := by
    by_contra hc
    apply hx
    funext A
    by_contra hA
    exact hc ⟨A, by simpa using hA⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (fun A : Finset (NC ε) => ht (wtA A)) hne
  have hA0 : x A ≠ 0 := by simpa using hA
  refine ⟨A, hA0, ?_⟩
  have hF : ∀ c d, Fop ε E c d x A = E c d (x A) + ∑ B, (g c d A B : ℂ) • x B := by
    intro c d
    rw [← hg V c d x A]
    rfl
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · have h1 := congrFun (hK.1 a) A
    rw [hF] at h1
    have h2 : ∑ B, (g a a A B : ℂ) • x B = (wtA A a : ℂ) • x A := by
      rw [Finset.sum_eq_single A]
      · simp [hdiag]
      · intro B _ hB
        simp [hdiag, Ne.symm hB]
      · simp
    rw [h2, Pi.smul_apply] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]
  · have h1 := congrFun (hK.2 a b hab hε) A
    rw [hF] at h1
    have h2 : ∑ B, (g a b A B : ℂ) • x B = 0 := by
      refine Finset.sum_eq_zero fun B _ => ?_
      by_cases hgB : g a b A B = 0
      · simp [hgB]
      by_cases hxB : x B = 0
      · simp [hxB]
      exfalso
      have h3 := hmin B (by simpa using hxB)
      have h4 := ht_add_root (wtA B) a b hab
      rw [← (hwt a b A B hgB).2] at h4
      exact absurd h3 (not_le.mpr h4)
    rw [h2, add_zero] at h1
    exact h1

end GlobalTheory.CompanionTheory.DSICWLem
end
end
end

-- Source module: CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

section

@[expose] public section

namespace CompanionTheory.D.DSIC

theorem hCAR : CAR := GlobalTheory.CompanionTheory.ChainCAR.car
theorem hFRel : FRel := GlobalTheory.CompanionTheory.DSICFRel.car_imp_frel hCAR
theorem hBdFacts : BdFacts := GlobalTheory.CompanionTheory.KoszulBd.bdFacts hCAR
theorem hGFacts : GFacts := GlobalTheory.CompanionTheory.GopEntries.gFacts
theorem hKoszul : Koszul := GlobalTheory.CompanionTheory.DSICKoszul.koszul hCAR
theorem hVerma : Verma := GlobalTheory.CompanionTheory.DSVerma.verma
theorem hCover : Cover := GlobalTheory.CompanionTheory.DSCover.cover hKoszul hVerma
theorem hCO0 : CapelliDeterminantBlockProduct := GlobalTheory.CompanionTheory.CapelliBlocks.co0
theorem hCO : CO := GlobalTheory.CompanionTheory.CasselmanOsborne.co_of hBdFacts hGFacts hCover hCO0
theorem hZetaHW : ZetaHW := GlobalTheory.CompanionTheory.ZetaHighest.zetaHW
theorem hWLem : WLem := GlobalTheory.CompanionTheory.DSICWLem.wlem_of_gfacts hGFacts
theorem hNormLt : NormLt := GlobalTheory.CompanionTheory.DSNormLt.normLt
theorem hAdj : Adj := GlobalTheory.CompanionTheory.DSChainAdj.adj
theorem hGamDom : GamDom := GlobalTheory.CompanionTheory.GamDomProof.gamDom
theorem hKHWExists : KHWExists := GlobalTheory.CompanionTheory.KHighestExists.khwExists
theorem hLowSpan : LowSpan := GlobalTheory.CompanionTheory.KLowSpan.lowSpan_holds
theorem hHWMap : HWMap := GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan hLowSpan
theorem hPRV : PRV := GlobalTheory.CompanionTheory.ChainHighest.aux₃ hFRel hGFacts hGamDom hKHWExists hHWMap
theorem hAlgCore : AlgCore := algCore_of hFRel hBdFacts hCO hZetaHW hWLem hNormLt hAdj hPRV
theorem hAlgCoreSub : AlgCoreSub := GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore hAlgCore
theorem hSmLin : SmLin := GlobalTheory.CompanionTheory.DSSmLin.smLin
theorem hSmBracket : SmBracket := GlobalTheory.CompanionTheory.SmBracket.smBracket_of hSmLin
theorem hSmMod : SmMod := GlobalTheory.CompanionTheory.SmoothModule.smMod hSmLin hSmBracket
theorem hActQ : ActQ := GlobalTheory.CompanionTheory.DSCapelliAction.actQ
theorem hSpread : Spread := capelli_spread
theorem hKFinStab : KFinStab := GlobalTheory.CompanionTheory.KFinStab.kFinStab
theorem hKExp : KExp := GlobalTheory.CompanionTheory.DSICKExp.kExp
theorem hStabLink : StabLink := GlobalTheory.CompanionTheory.DSStabLink.stabLink hKExp
theorem hWtLink : WtLink := GlobalTheory.CompanionTheory.WtLinkPf.wtLink
theorem hHWofType : HWofType := GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType hStabLink hWtLink
theorem hTypeOfHW : TypeOfHW := GlobalTheory.CompanionTheory.DSKType.typeOfHW hLowSpan hStabLink hWtLink

theorem discrete_series_infinitesimal_character : PI.DSInfCharCap.DSInfCharCap :=
  dsInfCharCap_of hAlgCoreSub hSmMod hActQ hSpread CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs hKFinStab hStabLink
    hHWofType hTypeOfHW

end CompanionTheory.D.DSIC
end
end
