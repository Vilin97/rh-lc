module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedData
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharactersOnLiftFormsExtendedData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesGeometricActionsCorrespondStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesRationalFormsCorrespondCoordinatewisStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCorrespondingFormsSameAdelicFunction

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem.R3.Tr GlobalTheory.TwInputs.Move

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.ReadMove



theorem sameMap_of_heq {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X)
    (u : X.H) (u' : X'.H) (hu : HEq u' u) : SameMap (X.e u) (X'.e u') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  have e'' : u' = u := eq_of_heq hu
  subst e''
  intro v v' hv y y' hy
  cases hy
  have : v' = v := funext fun τ => Subtype.ext (eq_of_heq (hv τ τ HEq.rfl)).symm
  subst this
  rfl



theorem read_same {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (σ : (w.st Z).toD7.what₂.LL →+* ℂ) (σ' : (w'.st Z').toD7.what₂.LL →+* ℂ), σ = (w.st Z).toD7.what₂.embLL →
      σ' = (w'.st Z').toD7.what₂.embLL →
      SameMap ((z.R.HW j σ).e ((z.R.FW j).j σ x)) ((z'.R.HW j' σ').e ((z'.R.FW j').j σ' x')) := by
  rintro σ σ' rfl rfl
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, -⟩ := hE.MW j j' hj
  exact sameMap_of_heq q j j' hj _ _ a b c d l e g _ _ hW _ _
    (GlobalTheory.Mem.R3.LiftRead.read_extN q hE j j' hj φ hφ x x' hx)

end GlobalTheory.HeightCounting.SerMove.ReadMove

namespace GlobalTheory.HeightCounting.SerMove



theorem reading_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → GlobalTheory.TwInputs.Move.SameMap (GlobalTheory.TwInputs.Move.evidence (sideAt x g hg a) j y) (GlobalTheory.TwInputs.Move.evidence (sideAt x' g' hg' a') j' y') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hy
  exact ReadMove.read_same l.enl.1 l.extN j j' hj ι l.cp.embLL y y' hy _ _ (GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a))
    (GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a'))

end GlobalTheory.HeightCounting.SerMove

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCorrespondingFormsSameAdelicFunctionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linkedStates_corresponding_forms_same_adelicFunctions : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → GlobalTheory.TwInputs.Move.SameMap (GlobalTheory.TwInputs.Move.evidence (sideAt x g hg a) j y) (GlobalTheory.TwInputs.Move.evidence (sideAt x' g' hg' a') j' y') := by
  first | exact @GlobalTheory.HeightCounting.SerMove.reading_link | exact GlobalTheory.HeightCounting.SerMove.reading_link | (intros; apply GlobalTheory.HeightCounting.SerMove.reading_link <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupCharactersCorrespond

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr

theorem chi_link_side : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ u : (sideAt x g hg a).Γ, ((((sideAt x' g' hg' a').R.FW j').chi (γ u) : (Dof x').what₂.LLˣ) : (Dof x').what₂.LL) = ι ((((sideAt x g hg a).R.FW j).chi u : (Dof x).what₂.LLˣ) : (Dof x).what₂.LL) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj u
  apply RingHom.injective (Dof x').what₂.embLL
  have hC : x.m.z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [x.m.z.lev.C, w.C_eq]; rfl
  have hC' : x'.m.z.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [x'.m.z.lev.C, w'.C_eq]; rfl
  refine (x'.m.z.pins.char.base.grp.chiW j' (γ u)).trans
    (Eq.trans ?_ ((l.cp.embLL _).trans (x.m.z.pins.char.base.grp.chiW j u)).symm)
  exact GlobalTheory.Mem.R3.ChiExt.prod_eq l.enl.1 l.fr l.px j j' hj l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG
    (x.m.z.R.chi ((j : ℕ) + 1)) (x'.m.z.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ x.m.z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ x'.m.z.lev.is.chi j' PP hP) u (γ u) (hγ u)

end GlobalTheory.HeightCounting.SerMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupCharactersCorrespondStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linkedStates_finiteGroupCharacters_correspond : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ u : (sideAt x g hg a).Γ, ((((sideAt x' g' hg' a').R.FW j').chi (γ u) : (Dof x').what₂.LLˣ) : (Dof x').what₂.LL) = ι ((((sideAt x g hg a).R.FW j).chi u : (Dof x).what₂.LLˣ) : (Dof x).what₂.LL) := by
  exact @GlobalTheory.HeightCounting.SerMove.chi_link_side
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesSupLatticeMemIffCoordinateImage

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.MKLink
open GlobalTheory.Mem.R3.MKExt Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor



theorem mk_iff_of_extN {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hN : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (y : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (y' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hyy : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y' k' = φ (y k))
    (hy : y ∈ (z.R.FW j).WK) : y ∈ (z.R.FW j).MK ↔ y' ∈ (z'.R.FW j').MK := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  obtain ⟨g, he⟩ : ∃ g, z.geo.fw.e j g = ⟨y, hy⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨g', hgg, hP⟩ := cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 g
  have hx : ((z.geo.fw.e j g : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = y :=
    congrArg Subtype.val he
  have hx' : y' = ((z'.geo.fw.e j' g' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
    funext k'
    have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
    have h3 := hN.forms j j' hj g g' hgg (Fin.cast hn k') k' hk
    have h4 := hyy (Fin.cast hn k') k' hk
    apply hinj
    rw [h4]
    exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
  subst hx'
  subst hx
  constructor
  · rintro ⟨_, h2⟩
    exact ⟨(z'.geo.fw.e j' g').2, (nrm_le_one_iff z'.geo.fw j' g').2 (hP.2 ((nrm_le_one_iff z.geo.fw j g).1 h2))⟩
  · rintro ⟨_, h2⟩
    exact ⟨(z.geo.fw.e j g).2, (nrm_le_one_iff z.geo.fw j g).2 (hP.1 ((nrm_le_one_iff z'.geo.fw j' g').1 h2))⟩

end GlobalTheory.HeightCounting.SerMove.MKLink

namespace GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr



theorem mk_iff_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → y ∈ ((sideAt x g hg a).R.FW j).WK → (y ∈ ((sideAt x g hg a).R.FW j).MK ↔ y' ∈ ((sideAt x' g' hg' a').R.FW j').MK) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hyy hy
  exact MKLink.mk_iff_of_extN (datAt x g) (datAt x' g') l.enl.1 l.extN j j' hj ι (fun t => l.cp.embLL t) y y' hyy hy

end GlobalTheory.HeightCounting.SerMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesSupLatticeMemIffCoordinateImageStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linkedStates_supLattice_mem_iff_coordinateImage : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → y ∈ ((sideAt x g hg a).R.FW j).WK → (y ∈ ((sideAt x g hg a).R.FW j).MK ↔ y' ∈ ((sideAt x' g' hg' a').R.FW j').MK) := by
  first | exact @GlobalTheory.HeightCounting.SerMove.mk_iff_of_link | exact GlobalTheory.HeightCounting.SerMove.mk_iff_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.mk_iff_of_link <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalFormsLinkedConstructionStatesIdentified

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.FormsMove

theorem coord_eq_iff {L L' : Type} [Field L] [Field L'] (ι : L →+* L') {n n' : ℕ} (hn : n = n') {a b : Fin n → L}
    {a' b' : Fin n' → L'} (ha : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → a' k' = ι (a k))
    (hb : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → b' k' = ι (b k)) : a = b ↔ a' = b' := by
  subst hn
  refine ⟨fun h => funext fun k => ?_, fun h => funext fun k => ι.injective ?_⟩
  · rw [ha k k rfl, hb k k rfl, h]
  · rw [← ha k k rfl, ← hb k k rfl, h]

theorem coord_smul {L L' F F' : Type} [Field L] [Field L'] [Field F] [Field F'] [Algebra F L] [Algebra F' L'] (ι : L →+* L')
    {n n' : ℕ} (hn : n = n') {W : Submodule F (Fin n → L)} {W' : Submodule F' (Fin n' → L')} (φ : W → W')
    (hφ : ∀ (y : W) (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k)) {c : F} {c' : F'}
    (hc : algebraMap F' L' c' = ι (algebraMap F L c)) (y : W) : φ (c • y) = c' • φ y := by
  subst hn
  refine Subtype.ext (funext fun k => ?_)
  rw [hφ _ k k rfl]
  change ι (c • y.1 k) = c' • (φ y).1 k
  rw [hφ _ k k rfl, Algebra.smul_def, Algebra.smul_def, map_mul, hc]

theorem formsCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) → (∀ u, HEq (γ u) u) → FormsCl (sideAt x g hg a) (sideAt x' g' hg' a') ι eK γ := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' eK γ heK hγ
  have halg : ∀ c, algebraMap _ (Dof x').what₂.LL (eK c) = ι (algebraMap (sideAt x g hg a).core.Q.c.F (Dof x).what₂.LL c) := by
    intro c
    apply (Dof x').what₂.embLL.injective
    rw [l.cp.embLL]
    exact (x'.m.z.alg_eq (eK c)).trans ((heK c).trans (x.m.z.alg_eq c).symm)
  have hphi := fun j j' h => (GlobalTheory.T.linkedStates_rationalForms_correspond_coordinatewise x x' ι e g g' l hg hg' a a' j j' h)
  choose hn φ hφ using hphi
  refine ⟨fun j j' h => { φ := φ j j' h, alg := halg, smul := ?_, mk_iff := ?_, rho := ?_, chi := ?_ }, ?_⟩
  · intro c y
    exact coord_smul ι (hn j j' h) (φ j j' h) (hφ j j' h) (halg c) y
  · intro y
    exact GlobalTheory.T.linkedStates_supLattice_mem_iff_coordinateImage x x' ι e g g' l hg hg' a a' j j' h y.1 (φ j j' h y).1 (hφ j j' h y) y.2
  · intro u y z
    exact coord_eq_iff ι (hn j j' h)
      (GlobalTheory.T.linkedStates_geometricActions_correspond x x' ι e g g' l hg hg' a a' γ hγ j j' h y.1 (φ j j' h y).1 (hφ j j' h y) u) (hφ j j' h z)
  · intro u
    exact GlobalTheory.T.linkedStates_finiteGroupCharacters_correspond x x' ι e g g' l hg hg' a a' γ hγ j j' h u
  · intro j j' h y
    exact GlobalTheory.T.linkedStates_corresponding_forms_same_adelicFunctions x x' ι e g g' l hg hg' a a' j j' h y.1 (φ j j' h y).1 (hφ j j' h y)

end GlobalTheory.HeightCounting.SerMove.FormsMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalFormsLinkedConstructionStatesIdentifiedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.rationalForms_linkedConstructionStates_identified : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) → (∀ u, HEq (γ u) u) → FormsCl (sideAt x g hg a) (sideAt x' g' hg' a') ι eK γ := by
  first | exact @GlobalTheory.HeightCounting.SerMove.FormsMove.formsCl_of_link | exact GlobalTheory.HeightCounting.SerMove.FormsMove.formsCl_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.FormsMove.formsCl_of_link <;> assumption)
end
end
