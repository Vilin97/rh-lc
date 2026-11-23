module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfMatrixMoveDeepCongruenceBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.LevLift

theorem exists_mem_U_finM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  intro B X I _ _ l Z u a Ch A hA i hi β z
  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) ((I.rec7 l Z).sp.X i) _ (rankN (I.rec7 l Z) i hi)
  obtain ⟨g, hg⟩ := e.toMulEquiv.surjective ⟨z.1, (((A.K i hi β).lev.U_eq z.1).1 z.2).1⟩
  have hfin : z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := by
    rw [← he g]
    have h2 : (e g : GL _ _) = z.1 := congrArg Subtype.val hg
    rw [h2]
  exact ⟨⟨g.1, (hA.U i hi β g.1).2 ⟨g.2, z, hfin⟩⟩, hfin⟩

end GlobalTheory.AdForm.LevLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  first | exact @GlobalTheory.AdForm.LevLift.exists_mem_U_finM | exact GlobalTheory.AdForm.LevLift.exists_mem_U_finM | (intros; apply GlobalTheory.AdForm.LevLift.exists_mem_U_finM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimes

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG GlobalTheory.Mem.Col2.AdT GlobalTheory.Mem.Col2.TC

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelAll

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_one_apply (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (r s : Fin n) :
    adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem conj_bound (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (ε : WithZero (Multiplicative ℤ)) (hε : ε < 1)
    (hP : ∀ r s, Valued.v (adAt F P (u.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ ε) (r s : Fin n) :
    Valued.v (adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s) ≤ ε := by
  subst hJ
  have hinv : ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) =
      1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) := by
    have h : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) *
        ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * (u : Matrix (Fin n) (Fin n) (AfE F E)) =
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    have e : 1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) =
        cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) := by
      unfold cT
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one, add_sub_cancel]
    rw [e]
    calc ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
        = (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) * (u : Matrix (Fin n) (Fin n) (AfE F E))) *
            ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) := by rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h1 : (1 + ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, add_sub_cancel, Units.mul_inv]
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add (f := _), map_add (f := _), map_one] at h2
  have key := GlobalTheory.Mem.Col2.AdT.Opn.val_inv_le Valued.v _ _ h2 ε hε (fun a b => ?_) r s
  · have e : ((adAt F (conjPrime₂ P)).mapMatrix ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) r s =
        adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, adAt_one_apply]
    rw [← e]; exact key
  · show Valued.v (adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) b a))) ≤ ε
    rw [GlobalTheory.Mem.Col2.valued_sigR hc, GlobalTheory.CharValCompare.conjP_conjP, Matrix.sub_apply, map_sub, adAt_one_apply]
    exact hP b a

end Gen

theorem map_prod_cases {G M κ : Type} [Monoid G] [Monoid M] (f : κ → G) (c : G →* M)
    (hpair : ∀ P P' : κ, P ≠ P' → c (f P) = 1 ∨ c (f P') = 1) :
    ∀ L : List κ, L.Nodup → c (L.map f).prod = 1 ∨ ∃ P ∈ L, c (L.map f).prod = c (f P) := by
  have hall : ∀ (P : κ) (L : List κ), c (f P) ≠ 1 → (∀ P' ∈ L, P' ≠ P) → c (L.map f).prod = 1 := by
    intro P L h1 hL
    induction L with
    | nil => simp
    | cons P' L ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih fun x hx => hL x (List.mem_cons_of_mem _ hx), mul_one]
      exact (hpair P P' (Ne.symm (hL P' (List.mem_cons.2 (Or.inl rfl))))).resolve_left h1
  intro L
  induction L with
  | nil => intro _; left; simp
  | cons P L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases h1 : c (f P) = 1
    · rw [h1, one_mul]
      rcases ih hL.2 with h | ⟨P', hP', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', List.mem_cons_of_mem _ hP', h⟩
    · rw [hall P L h1 fun P' hP' e => hL.1 (e ▸ hP'), mul_one]
      exact Or.inr ⟨P, List.mem_cons.2 (Or.inl rfl), rfl⟩



theorem exists_level_elt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  intro B X I hOk hPins l Z a T i hi bad S hChi N g
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : S.U →* GA B (B.R.N i) := S.U.subtype
  have hexp : WithZero.exp (-((max N 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by omega)
  have hexp1 : WithZero.exp (-((max N 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hs : ∀ P : SBof I a, GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := fun P => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P 1).1
  have hsep : ∀ P P' : SBof I a, P ≠ P' → P.1 ∈ I.Q a → (P'.1 = P.1 ∨ P'.1 = Formalism.L2.Col.conjPrime₂ P.1) → False := by
    intro P P' hne hP h
    rcases h with h | h
    · exact hne (Subtype.ext h.symm)
    obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
    apply hv' P' (Ne.symm hne)
    rw [hs] at hv ⊢
    have hc := congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).2 (Or.inr h))
    exact Eq.trans hv hc.symm
  have hsel : ∀ P : SBof I a, ∃ z : S.U, S.chi z = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 B.fields.E), cP Q (ι z) = 1 ∨ (P.1 ∈ I.Q a ∧ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1))) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) r s, Valued.v (cP Q (ι z) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g * (show GA B (B.R.N i) from z.1) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, -⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a T i hi bad S hChi P hP v hv (max N 1) g 1
      have hzU := ((S.U_eq _).1 z.2).1
      have hbP := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) (max N 1) P z.1).2.2).1 hz3
      have hvP := hv
      rw [hs] at hvP
      have hoff : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), ¬ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1) → cP Q (ι z) = 1 := fun Q hQ =>
        Matrix.ext fun r s => by
          rw [cP_apply]
          exact LevelElt.support_one z.1 v hz2 Q (fun hO => hQ ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 Q).1
            (HeightOneSpectrum.ext (Eq.trans (Eq.symm hO) hvP)))) r s
      refine ⟨z, hz1, fun Q => ?_, fun Q r s => ?_, fun _ => ?_⟩
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · exact Or.inr ⟨hP, hQ⟩
        · exact Or.inl (hoff Q hQ)
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · rw [cP_apply]
          rcases hQ with rfl | rfl
          · exact (hbP r s).trans hexp
          · exact (conj_bound (I.rec7 l Z).sp.cm hgr hzU P.1 _ hexp1 hbP r s).trans hexp
        · rw [hoff Q hQ, sub_self, Valuation.map_zero]
          exact zero_le'
      · obtain ⟨γ, hγ⟩ := hz4
        exact ⟨γ, fun r s => by rw [← hγ r s, mul_one]⟩
    · refine ⟨1, map_one _, fun Q => Or.inl (by rw [map_one, map_one]), fun Q r s => ?_, fun h => absurd h hP⟩
      rw [map_one, map_one, sub_self, Valuation.map_zero]; exact zero_le'
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  have hpair : ∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) (P P' : SBof I a), P ≠ P' → cP Q (ι (zf P)) = 1 ∨ cP Q (ι (zf P')) = 1 := by
    intro Q P P' hne
    rcases hzf2 P Q with h | ⟨hP, hQ⟩
    · exact Or.inl h
    rcases hzf2 P' Q with h' | ⟨-, hQ'⟩
    · exact Or.inr h'
    exfalso
    apply hsep P P' hne hP
    rcases hQ with rfl | rfl <;> rcases hQ' with h2 | h2
    · exact Or.inl h2.symm
    · refine Or.inr ?_
      rw [h2, GlobalTheory.CharValCompare.conjP_conjP]
    · exact Or.inr h2.symm
    · have h3 := congrArg Formalism.L2.Col.conjPrime₂ h2
      rw [GlobalTheory.CharValCompare.conjP_conjP, GlobalTheory.CharValCompare.conjP_conjP] at h3
      exact Or.inl h3.symm
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := by
    intro P P' hne
    rcases hzf2 P P'.1 with h | ⟨hP, hQ⟩
    · exact h
    · exact (hsep P P' hne.symm hP hQ).elim
  have hlistP : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : S.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlistP _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : S.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨w, hchiw, fun P hP => ?_, fun Q r s => ?_⟩
  · obtain ⟨γ, hγ⟩ := hzf4 ⟨P, hQsub P hP⟩ hP
    refine ⟨(γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E), fun r s => ?_⟩
    have e0 : cP P (ι w) = cP P (ι (zf ⟨P, hQsub P hP⟩)) := hwP ⟨P, hQsub P hP⟩
    have e1 : cP P (g * ι w) = cP P (g * ι (zf ⟨P, hQsub P hP⟩)) := by rw [map_mul, map_mul, e0]
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · rw [map_sub, adAt_one_apply]
    change Valued.v (cP Q (ι w) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ _
    rcases map_prod_cases zf ((cP Q).comp ι) (hpair Q) _ (Finset.nodup_toList _) with h | ⟨P, -, h⟩
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h]; exact hzf3 P Q r s

end GlobalTheory.Mem.Col2.AdT.LevelAll

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all | exact GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all | (intros; apply GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatApprox

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem actO_actO' {D : D7} (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem isHalf_actO' {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

end GlobalTheory.AdForm.RatApprox

namespace GlobalTheory.AdForm.RatApprox



theorem approx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have hi' : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨NB, hNB⟩ := GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent (I.rec7 l Z) (A.chr (i + 1)) (hA.chr ⟨i, hi⟩).1
  have hee : A.e * A.e = A.e := GlobalTheory.PlaceDatum.idemSum_mul_self hA.idem
  have hez : IsHalf A.e (z.map fun r => A.e * incA (I.rec7 l Z) r) := fun r s => by
    simp only [Matrix.map_apply, ← mul_assoc, hee]
  have hM := isHalf_actO' κ.1⁻¹ κ'.1⁻¹ hez
  obtain ⟨NC, hNC⟩ := GlobalTheory.T.halfMatrix_move_deepCongruence_bound (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i hi') (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hM k hk
  have hfin : ∀ j (hj : j ≤ B.R.m) (β : Ch j), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (A.K j hj β).lev := fun j hj β => by
    obtain ⟨n, hn, h⟩ := hA.fin j hj β
    exact ⟨n, hn, fun κ _ => h κ⟩
  have step : ∀ j (hj : j ≤ B.R.m) (β : Ch j) (g : A.U j β), ∃ w : A.U j β, A.chi j β w = 1 ∧
      (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) (g * w).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧
      ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin (B.R.N j)), Valued.v (adAt (I.rec7 l Z).host.F P (finM _ (rankN (I.rec7 l Z) j hj) w.1 r s - (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ)) := by
    intro j hj β g
    obtain ⟨g₀, hg₀⟩ := ((hA.U j hj β g.1).1 g.2).2
    obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes I hI hP l Z a _ j hj _ (A.K j hj β).lev (hfin j hj β) (max NB NC) (show TC.GA B (B.R.N j) from g₀.1)
    obtain ⟨w, hw⟩ := GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift I hI hP l Z u a Ch A hA j hj β zz
    refine ⟨w, ?_, fun P hPQ => ?_, fun P r s => ?_⟩
    · rw [hA.chi j hj β w zz hw, hz1]
    · obtain ⟨M, hM⟩ := hz2 P hPQ
      refine ⟨M, fun r s => ?_⟩
      rw [← hM r s, Subgroup.coe_mul, GlobalTheory.RepLattice.finM_mul', ← hg₀, ← hw]
      rfl
    · rw [← hw]
      exact hz3 P r s
  obtain ⟨w, hw1, hw2, hw3⟩ := step i hi' α κ
  obtain ⟨w', hw1', hw2', hw3'⟩ := step (i + 1) hi γ κ'
  have hwG : w.1 ∈ GfC _ := ((hA.U i hi' α w.1).1 w.2).1
  have hwG' : w'.1 ∈ GfC _ := ((hA.U (i + 1) hi γ w'.1).1 w'.2).1
  have dB : ∀ {n : ℕ} (f : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))), (∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ))) → ∀ N₀ : ℕ, N₀ ≤ max NB NC → ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro n f hf N₀ hN P r s
    exact (hf P r s).trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hN)))
  obtain ⟨x₁, hx₁, hcx⟩ := hNB _ (rankN (I.rec7 l Z) i hi') κ.1 w.1 hwG (dB _ hw3 NB (le_max_left _ _)) x hx
  obtain ⟨y₁, hy₁, hcy⟩ := hNB _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 w'.1 hwG' (dB _ hw3' NB (le_max_left _ _)) y hy
  obtain ⟨t, ht, hth, hte⟩ := hNC w.1 w'.1 hwG hwG' (dB _ hw3 NC (le_max_right _ _)) (dB _ hw3' NC (le_max_right _ _))
  refine ⟨κ * w, κ' * w', x₁, y₁, t, hw2, hw2', hx₁, hy₁, hcx, hcy, ?_, ?_, ht, hth, ?_⟩
  · rw [map_mul, hw1, mul_one]
  · rw [map_mul, hw1', mul_one]
  · rw [← hte, actO_actO']
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

end GlobalTheory.AdForm.RatApprox
end
end
