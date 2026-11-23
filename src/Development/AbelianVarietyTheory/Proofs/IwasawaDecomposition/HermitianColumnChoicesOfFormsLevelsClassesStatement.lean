module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLevelOfStepZeroFormsLevelTrueColumnsStatement
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClassesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianClassCondition_of_chartClasses : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  first | exact @GlobalTheory.HermTransport.classTie_of_chart | exact GlobalTheory.HermTransport.classTie_of_chart | (intros; apply GlobalTheory.HermTransport.classTie_of_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.TC.level_of_chart | exact GlobalTheory.Mem.Col2.TC.level_of_chart | (intros; apply GlobalTheory.Mem.Col2.TC.level_of_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldEquivRealSubfieldQuotientTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ResF

variable {D : D7} {u : D.what₂.Word}

theorem conj_conj_host (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_intF (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem res_algebraMap_surjective (A : AtTTied u) (v : (D.mem u).A.vT) :
    Function.Surjective ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
  intro r
  obtain ⟨y, rfl⟩ := A.res_surj v r
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  obtain ⟨t, ht⟩ := exists_intF (D := D) (A.piU + cO A.piU) (by
    push_cast; simp only [hcO, map_add (f := _), conj_conj_host]; ring)
  obtain ⟨z, hz⟩ := exists_intF (D := D) (y * cO A.piU + cO y * A.piU) (by
    push_cast; simp only [hcO, map_add (f := _), map_mul, conj_conj_host]; ring)
  have htp : t ∉ (A.eV v).1.asIdeal := by
    rw [A.res_v, ht, map_add (f := _), A.res_pi, zero_add]; exact A.res_conj v _ rfl
  obtain ⟨s, i, hi, hsi⟩ := ((A.eV v).1.isMaximal).exists_inv htp
  have hi0 : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) i) = 0 := (A.res_v v i).1 hi
  have hst : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s) * A.res v (cO A.piU) = 1 := by
    have := congrArg (fun x => A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x)) hsi
    simp only [map_add (f := _), map_mul, map_one, hi0, add_zero, ht, A.res_pi, zero_add] at this
    exact this
  refine ⟨s * z, ?_⟩
  simp only [RingHom.comp_apply, map_mul, hz, map_add (f := _), A.res_pi, mul_zero, add_zero]
  rw [mul_comm (A.res v y), ← mul_assoc, hst, one_mul]

theorem exists_fv_equiv (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ e : (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal),
      ∀ a : 𝓞 D.host.F, e (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a := by
  have hker : (A.eV v).1.asIdeal = RingHom.ker ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
    ext x; rw [RingHom.mem_ker]; exact A.res_v v x
  refine ⟨((Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (res_algebraMap_surjective A v))).symm, fun a => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem fv_equiv_quot : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X),
    ColIn.Ok I → TC.Pins B X →
    ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word)
      {Ch : ℕ → Type} {chOf : ∀ i, ((TC.rec7 I l Z).mem u).C.cls i → Ch i}
      (F : Formalism.L2.Forms.FormsTiedSym (TC.rec7 I l Z) u Ch chOf),
      TC.StdF I l Z u F → ∀ v : ((TC.rec7 I l Z).mem u).A.vT,
      ∃ e : ((TC.rec7 I l Z).mem u).A.Fv v ≃+* (𝓞 (TC.rec7 I l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
        ∀ a : 𝓞 (TC.rec7 I l Z).host.F,
          e (F.atT.res v (algebraMap (𝓞 (TC.rec7 I l Z).host.F) (𝓞 (TC.rec7 I l Z).host.E) a)) =
            Ideal.Quotient.mk _ a := by
  intro B X I _ _ l Z u Ch chOf F _ v
  exact exists_fv_equiv F.atT v

end GlobalTheory.Mem.Col2.ResF

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldEquivRealSubfieldQuotientTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a := by
  first | exact @GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | exact GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | (intros; apply GlobalTheory.Mem.Col2.ResF.fv_equiv_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClasses

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


theorem chart_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : Ch i),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
      P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
      (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i h1 h2 β
  obtain ⟨k, hk⟩ := hS.mid i h1 h2
  obtain ⟨L, hLb, hUl, hU⟩ := GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel I hOk hP l Z u F hS i (le_of_succ_m h2) (F.ch i h1 h2 β) (F.glevC i h1 h2 β) (hk.lb β)
  obtain ⟨C, hy, hst⟩ := GlobalTheory.T.hermitianClassCondition_of_chartClasses (I.rec7 l Z) i (le_of_succ_m h2) (Equiv.refl _) (fun c : {c // chOf i c = β} => (I.rec7 l Z).clsLat u i c.1)
    (F.ch i h1 h2 β) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := hy, st_eq := hst }⟩


theorem top_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hm : i ≤ (I.rec7 l Z).R.m) (him : i = (I.rec7 l Z).R.m) (β : Ch i) (hβ : ∀ c, chOf i c = β),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
      P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
      (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i hm him β hβ
  subst him
  obtain ⟨k, hk⟩ := hS.ends _ hm (Or.inr rfl)
  obtain ⟨L, hLb, hUl, hU⟩ := GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel I hOk hP l Z u F hS _ hm ((F.cls _ hm (Or.inr rfl)).toChart) F.glevM (hk.lb ())
  obtain ⟨C, hy, hst⟩ := GlobalTheory.T.hermitianClassCondition_of_chartClasses (I.rec7 l Z) _ hm (Equiv.subtypeUnivEquiv hβ) (fun c => (I.rec7 l Z).clsLat u _ c)
    ((F.cls _ hm (Or.inr rfl)).toChart) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := fun c => hy ⟨c, hβ c⟩, st_eq := fun c => hst ⟨c, hβ c⟩ }⟩


theorem level_classes_of {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
    (hS : I.StdF l Z u F) (hU : Nonempty (Unique (Ch (I.rec7 l Z).R.m))) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : Ch i) :
    ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
      (∀ h2 : i + 1 ≤ (I.rec7 l Z).R.m,
        SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
          P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
          (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1)) ∧
      (∀ (him : i = (I.rec7 l Z).R.m) (hβ : ∀ c, chOf i c = β),
        SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
          P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
          (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1)) := by
  by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
  · obtain ⟨P, hP2⟩ := chart_level_classes I hOk hP l Z u F hS i h1 h2 β
    exact ⟨P, fun _ => hP2, fun him _ => absurd h2 (by omega)⟩
  · have him : i = (I.rec7 l Z).R.m := by omega
    have hβ : ∀ c, chOf i c = β := by
      intro c
      subst him
      obtain ⟨U⟩ := hU
      exact Subsingleton.elim _ _
    obtain ⟨P, hP3⟩ := top_level_classes I hOk hP l Z u F hS i hm him β hβ
    exact ⟨P, fun h => absurd h h2, fun _ _ => hP3⟩


theorem hermColsCh_of_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  intro B X I hOk hP l Z Ch chOf F hf hm hS
  have L0 := fun u => GlobalTheory.T.columnLevel_of_stepZeroFormsLevel_trueColumns I hOk hP l Z u (F u) (hS u)
  have LP := fun u i h1 hm' β => level_classes_of I hOk hP l Z u (F u) (hS u) (hm u) i h1 hm' β
  have LF := fun u v => GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns I hOk hP l Z u (F u) (hS u) v
  refine ⟨fun u => (L0 u).choose, fun u i h1 hm' β => (LP u i h1 hm' β).choose.1,
    fun u i h1 hm' β => (LP u i h1 hm' β).choose.2, fun u => (F u).atT.eV, fun u v => (LF u v).choose, ?_⟩
  exact {
    eV := fun u => rfl
    fv := fun u v a => (LF u v).choose_spec a
    car0 := fun u => (L0 u).choose_spec.1
    carC := fun u i h1 h2 β => (LP u i h1 (le_of_succ_m h2) β).choose_spec.1 h2
    carM := fun u => (LP u _ (one_le_m _) le_rfl _).choose_spec.2 rfl (fun c => @Unique.eq_default _ (hm u).some (chOf u _ c))
    sp := fun u => (L0 u).choose_spec.2.1
    fr0 := fun u => (L0 u).choose_spec.2.2 }

end GlobalTheory.Mem.Col2.TC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClassesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  first | exact @GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms | exact GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms | (intros; apply GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms <;> assumption)
end
end
