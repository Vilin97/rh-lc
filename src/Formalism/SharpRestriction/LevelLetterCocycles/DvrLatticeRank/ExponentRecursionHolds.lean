module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExistsAutPrim

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut_prim (K : FinExt l) {z z' : Om l} (hz : IsPrimitiveRoot z l)
    (hz' : IsPrimitiveRoot z' l) : ∃ g : Om l ≃ₐ[↥(K0 K)] Om l, g z = z' := by
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  haveI : IsAlgClosure ↥(K0 K) (Om l) := ⟨inferInstance, inferInstance⟩
  have hint : IsIntegral ↥(K0 K) z := Algebra.IsIntegral.isIntegral z
  have hle : K0 K ≤ Ks K 1 := le_sup_left
  have hdeg := CyclotomicLifting.cyclotomic_degree_max_unramified K
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hdeg
  have hsub : IntermediateField.extendScalars hle ≤ IntermediateField.adjoin ↥(K0 K) {z} := by
    have h : Ks K 1 ≤ (IntermediateField.adjoin ↥(K0 K) {z}).restrictScalars ℚ_[l] := by
      refine sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)
      · exact (IntermediateField.adjoin ↥(K0 K) {z}).algebraMap_mem ⟨x, hx⟩
      · have hx1 : x ^ l = 1 := by simpa using hx
        obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hx1
        exact pow_mem (IntermediateField.mem_adjoin_simple_self ↥(K0 K) z) b
    intro x hx
    exact h hx
  haveI := IntermediateField.adjoin.finiteDimensional hint
  have hd : l - 1 ≤ (minpoly ↥(K0 K) z).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, ← hdeg]
    exact IntermediateField.finrank_le_of_le_right hsub
  have hroot : ∀ {w : Om l}, IsPrimitiveRoot w l →
      Polynomial.aeval w (Polynomial.cyclotomic l ↥(K0 K)) = 0 := fun {w} hw => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hw.isRoot_cyclotomic hl.pos
  have hdvd : minpoly ↥(K0 K) z ∣ Polynomial.cyclotomic l ↥(K0 K) := minpoly.dvd _ _ (hroot hz)
  have heq : Polynomial.cyclotomic l ↥(K0 K) = minpoly ↥(K0 K) z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic _ _) hdvd
      (by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl]; exact hd)
  have h0 : Polynomial.aeval z' (minpoly ↥(K0 K) z) = 0 := heq ▸ hroot hz'
  exact minpoly.exists_algEquiv_of_root' hint.isAlgebraic h0

theorem exists_pt (D : D7) (HW : HWOf D.loc) {K LL : FinExt l} (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hG).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hG).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := exists_aut_prim K hζ₁ hβ
  let g' : Om l →ₐ[ℚ_[l]] Om l := (g.toAlgHom).restrictScalars ℚ_[l]
  have hmem : ∀ y, ((σ.comp g').comp (Ks K 1).val) y ∈ LL.1 := hG.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp g').comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hG.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    have hgx : g (x : Om l) = x := g.commutes x
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionOfDimension

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem exponent_recursion_of_dimension (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : Formalism.MainNotions.ElementDenominator.adm1 D HW F Cm) (h8 : Formalism.MainNotions.ElementDenominator.adm8 D)
    (hdim : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ≤
          finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ)) :
    ExpansionFormAll D HW := by
  intro l _ hl K LL hG T h' hh' hT hJ c y _ hyc hk hexp
  obtain ⟨p1, -, p3, p4, p5, -⟩ := h1 l K 1 LL hG
  obtain ⟨⟨hfc, -⟩, hfd⟩ := h8 l K LL T
  have hFr : IsFractionRing ↥(OL LL) ↥LL.1 := by
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : FiniteDimensional ↥LL.1
      ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c)) :=
    Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)
  haveI : FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
    infer_instance
  have hyc' : (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have h := LinearMap.mem_ker.1 hyc
    simpa only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using h
  refine mem_N_of_exp ((HW l).W K 1 LL hG) hFr ((HW l).W_s K 1 LL hG) T
    (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (M := fun _ => h') (h := fun _ => h') (p1 T hT) (p3 T hT)
    (p4 T hT) (p5 T _ _ hT fun τ _ _ => hJ τ) c (fun ζ hζ => ?_) (fun τ => (hfd τ).1)
    (hdim l K LL hG T hT c) y hyc' hk hexp
  rw [(D.loc l).PD_p] at hζ
  exact exists_pt D HW hG c ζ hζ

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionHolds

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem exponent_recursion_holds : ExpansionFormHypothesis := fun D HW F Cm _ _ _ hA hd hr =>
  CrystallineExponents.exponent_recursion_of_dimension D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1 fun l _ K LL hG T hT c τ =>
    ((hr l K LL hG T hT c).trans (hd l K LL ⟨1, hG⟩ T hT τ).symm).le

end Formalism.MainNotions.N.Ln34

end
end
end
