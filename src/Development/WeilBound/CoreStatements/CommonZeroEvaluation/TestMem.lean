module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecSep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.GenSpecDesc

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SRel {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (scal y.x a i * y.s.f i) = y'.s.f i

def pmOfGS {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) : Gx x' ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom) (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
    (by
      show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ x =
        pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
      rw [← hx]
      exact pullback.condition)

theorem pmOf_snd {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) :
    pmOfGS hx ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left :=
  pullback.lift_snd _ _ _

theorem pmOf_fst {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) :
    pmOfGS hx ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

theorem srel_iff {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) (s : LB.Sec (PPx x))
    (s' : LB.Sec (PPx x')) (pm : Gx x' ⟶ Gx x)
    (h1 : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (h2 : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left) (a : S) :
    (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
        (pm.appLE _ _ h).hom (scal x a i * s.f i) = s'.f i) ↔
      ∀ i, (hx ▸ s').f i = scal x a i * s.f i := by
  subst hx
  have e1 : pm ≫ pullback.fst (Over.mk x').hom Xo.univ.t.G.hom =
      𝟙 _ ≫ pullback.fst (Over.mk x').hom Xo.univ.t.G.hom := by
    rw [Category.id_comp]
    exact h2
  have e2 : pm ≫ pullback.snd (Over.mk x').hom Xo.univ.t.G.hom =
      𝟙 _ ≫ pullback.snd (Over.mk x').hom Xo.univ.t.G.hom := by
    rw [Category.id_comp]
    exact h1
  have hpm : pm = 𝟙 (Gx x') := pullback.hom_ext e1 e2
  subst hpm
  have e : ∀ (U : (Gx x').Opens) (h : U ≤ (𝟙 (Gx x')) ⁻¹ᵁ U), Scheme.Hom.appLE (𝟙 (Gx x')) U U h = 𝟙 _ := by
    intro U h
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx x').presheaf.map_id]
    rfl
  constructor
  · intro H i
    have := H i (fun _ hp => hp)
    erw [e] at this
    exact this.symm
  · intro H i h
    erw [e]
    exact (H i).symm

theorem srel_exists {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃ a : S, SRel a y y' := by
  obtain ⟨a, ha, -⟩ := y.gen (hx ▸ y'.s)
  exact ⟨a, pmOfGS hx, pmOf_snd hx, pmOf_fst hx, (srel_iff hx y.s y'.s _ (pmOf_snd hx) (pmOf_fst hx) a).2 ha⟩

theorem srel_unique {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (hx : y'.x = y.x) {a b : S}
    (ha : SRel a y y') (hb : SRel b y y') : a = b := by
  obtain ⟨pa, pa1, pa2, pa3⟩ := ha
  obtain ⟨pb, pb1, pb2, pb3⟩ := hb
  have ea := (srel_iff hx y.s y'.s pa pa1 pa2 a).1 pa3
  have eb := (srel_iff hx y.s y'.s pb pb1 pb2 b).1 pb3
  obtain ⟨a', -, hu⟩ := y.gen (hx ▸ y'.s)
  exact (hu a ea).trans (hu b eb).symm

theorem srel_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {a : S} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hs : SRel a y y') (hz : FrMap φ y z) (hz' : FrMap φ y' z')
    (hxz : z'.x = z.x) : SRel (φ a) z z' := by
  obtain ⟨pmC, hsC, hfC, haC⟩ := hs
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  obtain ⟨hx2, hu2, pmB, hsB, hfB, haB⟩ := hz'
  let pm : Gx z'.x ⟶ Gx z.x := pmOfGS hxz
  have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom :=
    pullback.lift_fst _ _ _
  have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom :=
    pullback.lift_snd _ _ _
  have hsA' : pmA ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hsA
  have hfA' : pmA ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfA
  have hsB' : pmB ≫ pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom := hsB
  have hfB' : pmB ≫ pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfB
  have hsC' : pmC ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom := hsC
  have hfC' : pmC ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom := hfC
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfA', ← Category.assoc, pfst, Category.assoc, hfC', hfB']
    · rw [Category.assoc, hsA', psnd, Category.assoc, hsC', hsB']
  refine ⟨pm, psnd, pfst, fun i h => ?_⟩
  have hA := ppx_le_cov pmA hsA i
  have hB' := ppx_le_cov pmB hsB i
  have hC' := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z'.x ⟶ Gx y.x), q = pmB ≫ pmC → ∀ hh : (PPx z'.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
      (q.appLE _ _ hh).hom (scal y.x a i * y.s.f i) = z'.s.f i := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC' ≫ pmB.appLE _ _ hB' :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC' hB').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC', haB i hB']
  show (pm.appLE _ _ h).hom (scal z.x (φ.toRingHom a) i * z.s.f i) = z'.s.f i
  rw [← haA i hA, ← scal_pull φ.toRingHom pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y.x a i * y.s.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frBor_descend {S T : Type} [CommRing S] [Algebra c.F S] [IsReduced S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (hφ : Function.Injective φ) {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} {t : Ix Dw → Tˣ}
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') (hb : FrBor t z z')
    (hinv : ∀ k, ∃ b : S, φ b = ((t k)⁻¹ : Tˣ)) :
    ∃ tS : Ix Dw → Sˣ, FrBor tS y y' ∧ ∀ k, φ (tS k : S) = t k := by
  classical
  have hx : y'.x = y.x := x_eq_of_inj Xo φ.toRingHom hφ (by rw [y'.x_over, y.x_over])
    (by rw [← hz'.1, ← hz.1]; exact hb.1)
  have hU : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ a : Fin (Dw.mult τ) → S,
      IsCombAt y.x (y.u τ) a (y'.u τ i) ∧ (∀ j, i < j → a j = 0) ∧ φ (a i) = t (some ⟨τ, i⟩) := by
    intro τ i
    obtain ⟨a, ha, -⟩ := y.basis τ (y'.u τ i) (hx ▸ y'.tan τ i) (y'.eig τ i)
    have hp := isCombAt_pull φ.toRingHom hz.1 (hz.2.1 τ) (hz'.2.1 τ i) ha
    obtain ⟨cf, hci, hlow, hc⟩ := hb.2.1 τ i
    obtain ⟨a', -, hu⟩ := z.basis τ (z'.u τ i) (hb.1 ▸ z'.tan τ i) (z'.eig τ i)
    have e : (fun j => φ.toRingHom (a j)) = cf := (hu _ hp).trans (hu _ hc).symm
    refine ⟨a, ha, fun j hj => hφ ?_, ?_⟩
    · rw [map_zero, ← hlow j hj]
      exact congrFun e j
    · rw [← hci]
      exact congrFun e i
  choose a ha hlow hdiag using hU
  obtain ⟨a0, hs0⟩ := srel_exists y y' hx
  have hs1 := srel_bc φ hs0 hz hz' hb.1
  have hs2 : SRel (t none : T) z z' := hb.2.2
  have hd0 : φ a0 = t none := srel_unique hb.1 hs1 hs2
  let d : Ix Dw → S := fun k => match k with
    | none => a0
    | some ⟨τ, i⟩ => a τ i i
  have hd : ∀ k, φ (d k) = t k := by
    rintro (_ | ⟨τ, i⟩)
    · exact hd0
    · exact hdiag τ i
  choose b hb' using hinv
  have hdb : ∀ k, d k * b k = 1 := fun k => hφ (by rw [map_mul, hd, hb', map_one, Units.mul_inv])
  let tS : Ix Dw → Sˣ := fun k => ⟨d k, b k, hdb k, by rw [mul_comm]; exact hdb k⟩
  exact ⟨tS, ⟨hx, fun τ i => ⟨a τ i, rfl, hlow τ i, ha τ i⟩, hs0⟩, hd⟩

end Formalism.L2.Pj
end
end
end

-- Source module: Development.WeilBound.CoreStatements.CommonZeroEvaluation.TestMem

section

@[expose] public section

open NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace ModelDimension.Spread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem spec_bor {Ω : Type} [Field Ω] [Algebra c.F Ω] {S₁ S₂ : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂]
    [Algebra c.F S₂] (φ₁ : S₁ →ₐ[c.F] Ω) (φ₂ : S₂ →ₐ[c.F] Ω) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z₁ z₂ : FrPt Xo c Ω} {t : Ix Dw → Ωˣ} (h₁ : FrMap φ₁ y₁ z₁) (h₂ : FrMap φ₂ y₂ z₂) (hb : FrBor t z₁ z₂)
    (A : Subring Ω) (hA₁ : ∀ r, φ₁ r ∈ A) (hA₂ : ∀ r, φ₂ r ∈ A) (hAt : ∀ k, (((t k)⁻¹ : Ωˣ) : Ω) ∈ A)
    {L : Type} [CommRing L] [Algebra c.F L] (ev : A →+* L) (ψ₁ : S₁ →ₐ[c.F] L) (ψ₂ : S₂ →ₐ[c.F] L)
    (e₁ : ∀ r, ψ₁ r = ev ⟨_, hA₁ r⟩) (e₂ : ∀ r, ψ₂ r = ev ⟨_, hA₂ r⟩) {w₁ w₂ : FrPt Xo c L}
    (k₁ : FrMap ψ₁ y₁ w₁) (k₂ : FrMap ψ₂ y₂ w₂) : ∃ t' : Ix Dw → Lˣ, FrBor t' w₁ w₂ := by
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  have hc : ∀ a : c.F, algebraMap c.F Ω a ∈ A := fun a => by
    rw [← φ₁.commutes]; exact hA₁ _
  let D : Subalgebra c.F Ω := { A with algebraMap_mem' := hc }
  let evD : D →ₐ[c.F] L :=
    { toFun := fun x => ev ⟨x.1, x.2⟩
      map_one' := map_one ev
      map_mul' := fun x y => map_mul ev ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_zero' := map_zero ev
      map_add' := fun x y => map_add ev ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      commutes' := fun a => by
        rw [← ψ₁.commutes a, e₁]
        exact congrArg ev (Subtype.ext (φ₁.commutes a).symm) }
  let χ₁ : S₁ →ₐ[c.F] D := φ₁.codRestrict D hA₁
  let χ₂ : S₂ →ₐ[c.F] D := φ₂.codRestrict D hA₂
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ χ₁ y₁
  obtain ⟨u₂, hu₂⟩ := hL.bc _ _ χ₂ y₂
  have g₁ : FrMap D.val u₁ z₁ := frMap_cancel _ _ _ χ₁ D.val y₁ u₁ z₁ hu₁ h₁
  have g₂ : FrMap D.val u₂ z₂ := frMap_cancel _ _ _ χ₂ D.val y₂ u₂ z₂ hu₂ h₂
  obtain ⟨tD, hD, -⟩ := frBor_descend D.val Subtype.val_injective g₁ g₂ hb (fun k => ⟨⟨_, hAt k⟩, rfl⟩)
  have m₁ : FrMap evD u₁ w₁ := frMap_cancel _ _ _ χ₁ evD y₁ u₁ w₁ hu₁
    (by rw [show evD.comp χ₁ = ψ₁ from AlgHom.ext fun r => (e₁ r).symm]; exact k₁)
  have m₂ : FrMap evD u₂ w₂ := frMap_cancel _ _ _ χ₂ evD y₂ u₂ w₂ hu₂
    (by rw [show evD.comp χ₂ = ψ₂ from AlgHom.ext fun r => (e₂ r).symm]; exact k₂)
  exact ⟨_, frBorBC _ _ evD _ _ _ _ _ hD m₁ m₂⟩

theorem test_mem {K Ω : Type} [Field K] [CommRing Ω] [Algebra K Ω] (q : TRing K) (φ : q.R →ₐ[K] Ω) (A : Subring Ω)
    (hc : ∀ a : K, algebraMap K Ω a ∈ A) (hx : ∀ i, φ (Ideal.Quotient.mk q.I (MvPolynomial.X i)) ∈ A) (r : q.R) :
    φ r ∈ A := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : Ideal.Quotient.mk q.I (MvPolynomial.C a) = algebraMap K q.R a := rfl
    rw [this, φ.commutes]; exact hc a
  | add p p' hp hp' => rw [map_add (f := _), map_add (f := _)]; exact A.add_mem hp hp'
  | mul_X p i hp => rw [map_mul, map_mul]; exact A.mul_mem hp (hx i)

def evAlg {K S Ω L : Type} [Field K] [CommRing S] [Algebra K S] [CommRing Ω] [Algebra K Ω] [CommRing L] [Algebra K L]
    (φ : S →ₐ[K] Ω) (A : Subring Ω) (hA : ∀ r, φ r ∈ A) (ev : A →+* L)
    (hc : ∀ (a : K) (h : algebraMap K Ω a ∈ A), ev ⟨_, h⟩ = algebraMap K L a) : S →ₐ[K] L :=
  { ev.comp (φ.toRingHom.codRestrict A hA) with
    commutes' := fun a => by
      have h : algebraMap K Ω a ∈ A := by rw [← φ.commutes]; exact hA _
      rw [← hc a h]
      exact congrArg ev (Subtype.ext (φ.commutes a)) }

end ModelDimension.Spread
end
end
end
