module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HilbEventuallyPolyQualified
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
public import Mathlib.Algebra.MvPolynomial.Monad
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Combinatorics.Nullstellensatz
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbIrrelevantZero
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumUnique
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumZeroSlot
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMixedDiffConst
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMultEqualsCoeff
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPrimeFiltration
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRelevantPrimeDimGe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum

-- Source module: GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyShift

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial Filter

noncomputable section

theorem totalDegree_bind₁_le_of_le_one {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by

  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem EventuallyPolyShift.proof : EventuallyPolyShift.Statement := by
  intro K _ h p c hp
  refine ⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩
  · have ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    refine (ht.eventually hp).mono fun m hm => ?_
    simp only [← sub_eq_add_neg] at hm
    have e := eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p
    rw [hm]
    refine Eq.trans ?_ e.symm
    show eval _ p = eval _ p
    refine congrArg (fun x => eval x p) (funext fun k => ?_)
    simp
  · exact totalDegree_bind₁_le_of_le_one _
      (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p
  · rintro rfl
    exact map_zero _

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyUnique

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventuallyPolyUnique.proof : EventuallyPolyUnique.Statement := by
  intro K _ h p q hp hq
  classical
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hp.and hq)
  have hpq : p - q = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q)
      (fun k => (Finset.range ((p - q).degreeOf k + 1)).image
        (fun i : ℕ => ((M k + (i : ℤ) : ℤ) : ℚ)))
    · intro k
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        simpa using hab
    · intro x hx
      choose i _ hix using fun k => Finset.mem_image.1 (hx k)
      have hm : M ≤ fun k => M k + (i k : ℤ) := fun k => by simp
      have hxm : x = fun k => (((M k + (i k : ℤ) : ℤ)) : ℚ) := funext fun k => (hix k).symm
      obtain ⟨h1, h2⟩ := hM _ hm
      rw [map_sub, hxm, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 hpq

end GroundTheory.Heights₂.Heights.FieldNumbers
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section

variable {K : Type*}

theorem diffStep_add (b b' : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    diffStep (b + b') h m = diffStep b h m + diffStep b' h (m - b) := by
  simp only [diffStep, sub_add_eq_sub_sub]
  ring

theorem foldr_diffStep_set_add (h : (K → ℤ) → ℤ) (b b' : K → ℤ) :
    ∀ (L : List (K → ℤ)) (i : ℕ), i < L.length → ∀ m : K → ℤ,
      (L.set i (b + b')).foldr diffStep h m =
        (L.set i b).foldr diffStep h m + (L.set i b').foldr diffStep h (m - b)
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: L, 0, _, m => by
      simp only [List.set_cons_zero, List.foldr_cons]
      exact diffStep_add b b' _ m
  | a :: L, i + 1, hi, m => by
      simp only [List.set_cons_succ, List.foldr_cons, diffStep]
      have hi' : i < L.length := by simpa using hi
      rw [foldr_diffStep_set_add h b b' L i hi' m, foldr_diffStep_set_add h b b' L i hi' (m - a),
        ← sub_right_comm m a b]
      ring

theorem ofFn_update {α : Type*} {n : ℕ} (bs : Fin n → α) (i : Fin n) (x : α) :
    List.ofFn (Function.update bs i x) = (List.ofFn bs).set i x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    split_ifs with h h' h'
    · rfl
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · rfl

theorem mixedDiff_update_add {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ)
    (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    mixedDiff (Function.update bs i (b + b')) h m =
      mixedDiff (Function.update bs i b) h m + mixedDiff (Function.update bs i b') h (m - b) := by
  simp only [mixedDiff, ofFn_update]
  exact foldr_diffStep_set_add h b b' _ i (by simp) m

theorem tendsto_sub_const_atTop (b : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.2 fun c => ⟨c + b, fun _ hm => le_sub_iff_add_le.mpr hm⟩

theorem IntNumAdd.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumAdd.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs i b b'
  have e := fun x : K → ℤ => (h1 F K ι I hI hrel n hn).1 (Function.update bs i x)
  have e' := (tendsto_sub_const_atTop b).eventually (e b')
  obtain ⟨m, h0, hb, hb'⟩ := ((e (b + b')).and ((e b).and e')).exists
  rw [← h0, ← hb, ← hb']
  exact mixedDiff_update_add bs i b b' _ m

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameHilbFn

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem map_comap_renameEquiv {F : Type u} [Field F] {S K' : Type} {κ : S → Type}
    {ι' : K' → Type} (σ : (Σ s, κ s) ≃ (Σ k', ι' k')) (P : Ideal (MRing ι' F)) :
    (P.comap (rename σ)).map (renameEquiv F σ) = P := by
  have h : P.comap (rename σ) = P.comap (renameEquiv F σ) := rfl
  rw [h]
  exact Ideal.map_comap_of_surjective _ (renameEquiv F σ).surjective P

theorem RenameHilbFn.proof : RenameHilbFn.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P m
  have h := Relabel.hilbFn_map_rename E σ hσ (P.comap (rename σ)) (m ∘ E.symm)
  rw [map_comap_renameEquiv σ P] at h
  rw [h]
  congr 1
  funext s
  simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem GradedFinite.full : GradedFinite.Statement.{u} := GradedFinite.proof

theorem HilbExactDivide.full : HilbExactDivide.Statement.{u} :=
  HilbExactDivide.proof GradedFinite.full

theorem PolyOfDiffs.full : PolyOfDiffs.Statement := PolyOfDiffs.proof

theorem HilbEventuallyPoly.full : HilbEventuallyPoly.Statement.{u} :=
  HilbEventuallyPoly.of_exactDivide_polyOfDiffs HilbExactDivide.full PolyOfDiffs.full

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof HilbExactDivide.full

theorem EventuallyPolyUnique.full : EventuallyPolyUnique.Statement := EventuallyPolyUnique.proof

theorem EventuallyPolyShift.full : EventuallyPolyShift.Statement := EventuallyPolyShift.proof

theorem HilbIrrelevantZero.full : HilbIrrelevantZero.Statement.{u} := HilbIrrelevantZero.proof

theorem RelevantPrimeDimGe.full : RelevantPrimeDimGe.Statement.{u} := RelevantPrimeDimGe.proof

theorem HilbDegreeBound.full : HilbDegreeBound.Statement.{u} :=
  HilbDegreeBound.proof HilbEventuallyPoly.full HilbExactDivide.full PolyOfDiffs.full
    PrimeFiltration.full EventuallyPolyUnique.full EventuallyPolyShift.full
    HilbIrrelevantZero.full RelevantPrimeDimGe.full

theorem MixedDiffConst.full : MixedDiffConst.Statement.{u} :=
  MixedDiffConst.proof HilbDegreeBound.full HilbEventuallyPoly.full

theorem IntNumSymm.full : IntNumSymm.Statement := IntNumSymm.proof

theorem IntNumAdd.full : IntNumAdd.Statement.{u} := IntNumAdd.proof MixedDiffConst.full

theorem IntNumZeroSlot.full : IntNumZeroSlot.Statement.{u} :=
  IntNumZeroSlot.proof MixedDiffConst.full HilbEventuallyPoly.full HilbDegreeBound.full

theorem IntNumBase.full : IntNumBase.Statement.{u} := IntNumBase.proof MixedDiffConst.full

theorem MultEqualsCoeff.full : MultEqualsCoeff.Statement.{u} :=
  MultEqualsCoeff.proof PrimeFiltration.full MixedDiffConst.full RelevantPrimeDimGe.full

theorem CutRegular.full : CutRegular.Statement.{u} :=
  CutRegular.proof HilbExactDivide.full MultEqualsCoeff.full IntNumSymm.full

theorem CutRational.full : CutRational.Statement.{u} :=
  CutRational.proof CutRegular.full IntNumAdd.full

theorem ExistsForm.full : ExistsForm.Statement.{u} := ExistsForm.proof

theorem DivCycleSupport.full : DivCycleSupport.Statement.{u} := DivCycleSupport.proof

theorem IntNumUnique.full : IntNumUnique.Statement.{u} :=
  IntNumUnique.proof CutRational.full IntNumBase.full ExistsForm.full DivCycleSupport.full

theorem ProjectionFormulaContracted.full : ProjectionFormulaContracted.Statement.{u} :=
  PFContracted.proof MixedDiffConst.full CutRational.full

theorem ProjectionFormulaDegree.of_divPushForward (h : DivPushForward.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} :=
  ProjectionFormulaDegree.proof CutRational.full IntNumBase.full ProjectionFormulaContracted.full h

theorem RenameHilbFn.full : RenameHilbFn.Statement.{u} := RenameHilbFn.proof

theorem RenameIntNum.full : RenameIntNum.Statement.{u} := RenameIntNum.proof RenameHilbFn.full

end GroundTheory.Heights₂.Heights.FieldNumbers
end
end
