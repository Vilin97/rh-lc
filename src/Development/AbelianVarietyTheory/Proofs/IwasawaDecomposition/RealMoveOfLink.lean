module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelsExtendedDataCorrespondFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFockPolynomialsAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalFormsLinkedConstructionStatesIdentifiedStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgree

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.LevExt

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem frat_delAt_heq {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) (l : ℕ) :
    HEq ((Top.Fr.at a'.st f').delAt l) ((Top.Fr.at a.st f).delAt l) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))



theorem chars_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hP : B'.toPre = B.toPre := l.enl.1
  have hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (by rw [w.C_eq])
  have hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f' := x'.m.z.lev.C.trans (by rw [w'.C_eq])
  have hs := x.m.z.lev.is
  have hs' := x'.m.z.lev.is
  have hm : (Dof x').R.m = (Dof x).R.m := by
    exact congrArg (fun p : Pre => p.R.m) hP
  have hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' →
      HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h
  refine ⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩
  · have heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta := by
      rw [hC, hC']
      exact frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm
  · let j' : Fin (Dof x').R.m := ⟨j, lt_of_lt_of_eq j.2 hm.symm⟩
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm
  · exact (hmu0 j j' h).symm
  · show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)
    rw [hC, hC']
    exact (frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm

end GlobalTheory.HeightCounting.SerMove

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgreeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linked_construction_states_characters_agree : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  first | exact @GlobalTheory.HeightCounting.SerMove.chars_of_link | exact GlobalTheory.HeightCounting.SerMove.chars_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.chars_of_link <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.Ids

theorem coeffF_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (hH : H' = H) (hl : HEq l' l) (hc : HEq c' c) : c'.F = c.F := by
  subst hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  rfl

theorem gc_equiv {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (h : Enl B B') (hp : HEq px' px) :
    ∃ γ : GlobalTheory.Mem.R3.Gc B px ≃* GlobalTheory.Mem.R3.Gc B' px', ∀ u, HEq (γ u) u := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨MulEquiv.refl _, fun _ => HEq.rfl⟩

theorem dat_F_eq {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (h : Enl B B') (e : ExtN z z') : z'.core.Q.c.F = z.core.Q.c.F := by
  have hH := e.H
  have hl := e.l
  have hc := e.c
  clear e
  obtain ⟨e0, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e0
  subst e0
  exact coeffF_eq (eq_of_heq hH) hl hc

theorem field_group_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hc := l.extN.c
  have hH := l.extN.H
  have hl := l.extN.l
  show ∃ (eK : x.m.z.core.Q.c.F ≃+* x'.m.z.core.Q.c.F) (γ : GlobalTheory.Mem.R3.Gc B w.px ≃* GlobalTheory.Mem.R3.Gc B' w'.px), _
  obtain ⟨γ, hγ⟩ := gc_equiv l.enl l.px
  have hF : x'.m.z.core.Q.c.F = x.m.z.core.Q.c.F := dat_F_eq (z := datAt x g) (z' := datAt x' g') l.enl l.extN
  exact ⟨(IntermediateField.equivOfEq hF.symm).toRingEquiv, γ, fun y => rfl, hγ⟩

end GlobalTheory.HeightCounting.SerMove.Ids
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linkedStates_coefficientField_finiteGroup_eq : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  first | exact @GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link | exact GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespond

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem eG_heq (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E)) (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* Formalism.L2.DIV.G0 Pg B.R.r) (eG' : Gc B' px' ≃* Formalism.L2.DIV.G0 Pg' B'.R.r) (he : HEq eG' eG)
    (u : Gc B px) (u' : Gc B' px') (hu : HEq u' u) : HEq (eG u) (eG' u') := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp Pg Pg' hPg eG eG' he u u' hu ⊢
  subst h
  cases hp
  cases hPg
  cases he
  cases hu
  rfl

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_heq (B B' : Base) (h : B'.toPre = B.toPre) (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E))
    (hPg : HEq Pg' Pg) (Q Q' : Fin 2 → Type) (hQ : Q = Q') (pw : ∀ k, Q k → Formalism.L2.DIV.Pl B.host.E)
    (pw' : ∀ k, Q' k → Formalism.L2.DIV.Pl B'.host.E) (hpw : HEq pw pw')
    (c : Formalism.L2.DIV.G0 Pg B.R.r ≃* ∀ kv : (Σ k : Fin 2, Q k), GL (Fin B.R.r) (ZMod (B.host.g kv.1)))
    (c' : Formalism.L2.DIV.G0 Pg' B'.R.r ≃* ∀ kv : (Σ k : Fin 2, Q' k), GL (Fin B'.R.r) (ZMod (B'.host.g kv.1)))
    (hc : ∃ (plg : (Σ k : Fin 2, Q k) ≃ Pg) (iso : ∀ kv, ZMod (B.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Formalism.L2.DIV.Pl B.host.E) = pw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c y kv))
    (hc' : ∃ (plg : (Σ k : Fin 2, Q' k) ≃ Pg') (iso : ∀ kv, ZMod (B'.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg') : Formalism.L2.DIV.Pl B'.host.E) = pw' kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B'.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c' y kv)) :
    HEq c c' := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h Pg Pg' hPg pw pw' hpw c c' hc hc' ⊢
  subst h
  cases hPg
  subst hQ
  cases hpw
  apply heq_of_eq
  obtain ⟨p, i, h1, h2⟩ := hc
  obtain ⟨p', i', h1', h2'⟩ := hc'
  obtain rfl : p = p' := Equiv.ext fun kv => Subtype.ext ((h1 kv).trans (h1' kv).symm)
  refine MulEquiv.ext fun y => funext fun kv => ?_
  have h3 := (h2 y kv).symm.trans (h2' y kv)
  refine Units.ext (Matrix.ext fun a b => (i' kv).injective ?_)
  have h4 : (i kv) ((c y kv).1 a b) = (i' kv) ((c' y kv).1 a b) := congrArg (fun m : GL _ _ => m.1 a b) h3
  have h5 : (i kv) ((c y kv).1 a b) = (i' kv) ((c y kv).1 a b) :=
    RingHom.congr_fun (Subsingleton.elim (i kv).toRingHom (i' kv).toRingHom) _
  exact h5.symm.trans h4

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_read {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B} {Wt : Set X.B.places.Pl}
    (z : Dat X I hX T Wt) :
    ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ z.R.Pg) (iso : ∀ kv, ZMod (X.toD7.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : z.R.Pg) : Formalism.L2.DIV.Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (z.cG y kv) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := z.pins.keep.grp
  refine ⟨plg, iso, h1, fun y kv => ?_⟩
  obtain ⟨u, rfl⟩ := z.R.eG.surjective y
  exact h4 u kv

theorem grps_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → Grps (sideAt x g hg a) (sideAt x' g' hg' a') ι γ := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ
  refine ⟨fun u => ?_, ?_, fun u => ?_, fun u u' hu => ?_⟩
  · exact eG_heq B B' l.enl.1 w.px w'.px l.px x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG u (γ u) (hγ u)
  · exact cG_heq B B' l.enl.1 x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg (Dof x).nd.PlG (Dof x').nd.PlG (eq_of_heq l.gal.gal.PlG)
      (Dof x).naut.plGw (Dof x').naut.plGw l.gal.pl x.m.z.cG x'.m.z.cG (cG_read x.m.z) (cG_read x'.m.z)
  · exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u (γ u) (hγ u)).1.symm
  · have h : HEq (u' : (sideAt x' g' hg' a').Γ) (u : (sideAt x g hg a).Γ) := hu ▸ hγ u
    exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u.1 u'.1 h).2 u.2 u'.2

end GlobalTheory.HeightCounting.SerMove.GrpsPf

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespondStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linkedStates_finiteGroups_levels_correspond : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → Grps (sideAt x g hg a) (sideAt x' g' hg' a') ι γ := by
  first | exact @GlobalTheory.HeightCounting.SerMove.GrpsPf.grps_of_link | exact GlobalTheory.HeightCounting.SerMove.GrpsPf.grps_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.GrpsPf.grps_of_link <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealMoveOfLink

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove

theorem realMove_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x' g' hg' a') ι) :=
  fun x x' ι e g g' l hg hg' a a' =>
    let ⟨eK, γ, h1, h2⟩ := GlobalTheory.T.linkedStates_coefficientField_finiteGroup_eq x x' ι e g g' l hg hg' a a'
    realMove_of_parts (GlobalTheory.T.linkedStates_frames_lattices_models_agree x x' ι e g g' l hg hg' a a') (GlobalTheory.T.linked_construction_states_characters_agree x x' ι e g g' l hg hg' a a')
      (GlobalTheory.T.linkedStates_finiteGroups_levels_correspond x x' ι e g g' l hg hg' a a' γ h2) (GlobalTheory.T.linkedStates_tuplePlaces_over_fixedCharacterPrime x x' ι e g g' l hg hg' a a')
      (GlobalTheory.T.linkedStates_fockPolynomials_agree x x' ι e g g' l hg hg' a a') (GlobalTheory.T.rationalForms_linkedConstructionStates_identified x x' ι e g g' l hg hg' a a' eK γ h1 h2)

end GlobalTheory.HeightCounting.SerMove
end
end
