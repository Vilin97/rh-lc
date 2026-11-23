module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Order.CompletePartialOrder
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas
import Mathlib.Tactic.TypeStar

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSec

open GlobalTheory.EtC

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  change (F.obj.map (k ≫ g).op).hom y = (F.obj.map k.op).hom ((F.obj.map g.op).hom y)
  rw [op_comp, Functor.map_comp]
  rfl

theorem loc_bind' {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h' V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

theorem tw_loc (hG : E.InGen) (Q : ℕ) [NeZero Q] (i : ℤ) (U : Scheme.{0}) (y : Sec (tw Q i) U) :
    Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
  have hsurj : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF Q i)) y ∈ Scheme.etaleTopology U :=
    Presheaf.imageSieve_mem Scheme.etaleTopology _ (U := op U) y
  refine loc_bind' ⟨_, hsurj, fun V g hg => hg⟩ ?_
  rintro V g ⟨t, ht⟩
  by_cases hP : Nonempty (Prim Q Γ(V, ⊤))
  · obtain ⟨ζ₀⟩ := hP
    obtain ⟨S, hS, hS'⟩ := (hG Q i).1 V ζ₀ (Sec.res g y)
    refine ⟨S, hS, fun W k hk => Or.inr ?_⟩
    obtain ⟨c, hc⟩ := hS' W k hk
    exact ⟨ζ₀.map k.appTop.hom, c, (res_comp k g y).trans hc⟩
  · have : IsEmpty (Prim Q Γ(V, ⊤)) := not_nonempty_iff.mp hP
    have ht0 : t = 0 := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel Q i Γ(V, ⊤))
        (show (Prim Q Γ(V, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(V, ⊤) from t)
      have hf : f = 0 := Finsupp.ext fun a => (IsEmpty.false a).elim
      rw [hf]
      exact Submodule.Quotient.mk_zero _
    have hy : Sec.res g y = 0 := by
      refine ht.symm.trans ?_
      rw [ht0]
      exact map_zero _
    refine ⟨⊤, Scheme.etaleTopology.top_mem V, fun W k _ => Or.inl ?_⟩
    rw [res_comp, hy]
    exact map_zero _

end CrystallineSemistableComparison.TwSec
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.SheafSectionLemmas

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hSP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  refine ⟨Sieve.bind S.arrows (fun V g hg => (h' V g (hSP V g hg)).choose),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => (h' V g (hSP V g hg)).choose_spec.1), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hSP V g hg)).choose_spec.2 W k hk

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

theorem sec_eq_of_loc {F : Shv R} {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ((isSheaf_types F) S hS).isSeparatedFor.ext fun _ g hg => hSP _ g hg

theorem sec_subsingleton_of_isEmpty (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ⟨fun a b => ((isSheaf_types F).isSheafFor (⊥ : Presieve U)
    (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology U)).isSeparatedFor.ext (fun _ _ h => h.elim)⟩

theorem epi_of_loc {F G : Shv R} (φ : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec G U), Loc U fun V g => ∃ x : Sec F V, Sec.map φ x = Sec.res g y) : Epi φ := by
  have : Sheaf.IsLocallySurjective φ := by
    constructor
    intro U y
    obtain ⟨S, hS, hSP⟩ := h U y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hSP V g hg
    exact ⟨x, hx⟩
  infer_instance

theorem sec_map_comp {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_injective_of_mono {X Y : Shv R} (f : X ⟶ Y) [Mono f] (U : Scheme.{0}) :
    Function.Injective (Sec.map f (U := U)) := by
  have h1 : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have h2 : Mono (f.hom.app (op U)) := (NatTrans.mono_iff_mono_app f.hom).1 h1 (op U)
  exact (ModuleCat.mono_iff_injective _).1 h2

theorem epi_lift_of_loc {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ (U : Scheme.{0}) (y : Sec Y U), Sec.map g y = 0 →
      Loc U fun V k => ∃ x : Sec X V, Sec.map f x = Sec.res k y) :
    Epi (kernel.lift g f w) := by
  apply epi_of_loc
  intro U y
  have hy : Sec.map g (Sec.map (kernel.ι g) y) = 0 := by
    rw [← sec_map_comp, kernel.condition]; rfl
  refine loc_mono (h U _ hy) fun V k ⟨x, hx⟩ => ⟨x, ?_⟩
  apply sec_map_injective_of_mono (kernel.ι g)
  rw [← sec_map_comp, kernel.lift_ι, hx, GlobalTheory.EtC.CupSpec.map_res]

theorem ker_comp_zero {X Y Z : Shv R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ (U : Scheme.{0}) (y : Sec X U), Sec.map f y = 0 → Sec.map g y = 0) : kernel.ι f ≫ g = 0 := by
  apply Sheaf.hom_ext
  ext U y
  refine (h U.unop (Sec.map (kernel.ι f) y) ?_).trans rfl
  rw [← sec_map_comp, kernel.condition]; rfl

end CrystallineSemistableComparison.SheafSectionLemmas
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem sec_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (k • f) x = k • Sec.map f x := map_nsmul (CupSpec.mapHom X Y x) k f

theorem sec_map_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map f (k • x) = k • Sec.map f x := map_nsmul (f.hom.app (op U)).hom k x

theorem res_nsmul {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (k : ℕ) (x : Sec X U) :
    Sec.res g (k • x) = k • Sec.res g x := map_nsmul (X.obj.map g.op).hom k x

theorem res_zero {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec X U) = 0 :=
  map_zero (X.obj.map g.op).hom

theorem sec_map_zero' {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U : Scheme.{0}} : Sec.map f (0 : Sec X U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem sec_char {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (x : Sec F U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_self]
    rfl
  rw [this, zero_smul]

theorem morph_zero_of_sec {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y)
    (h : ∀ (U : Scheme.{0}) (x : Sec X U), Sec.map f x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

theorem loc_of_img {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U V : Scheme.{0}} (g : V ⟶ U) (y : Sec Y U)
    (x : Sec X V) (hx : Sec.map f x = Sec.res g y) :
    Loc V fun W k => ∃ x' : Sec X W, Sec.map f x' = Sec.res (k ≫ g) y :=
  SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true V) fun W k _ => ⟨Sec.res k x, by rw [← CupSpec.map_res, hx, TwSec.res_comp]⟩

theorem twSeq (hG : E.InGen) : InTwSeq := by
  intro p a b _ i
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, hπ, hπg⟩ := redSheaf hG (dvdB p a b) i
  obtain ⟨π', hπ', hπ'g⟩ := redSheaf hG (dvdA p a b) i
  obtain ⟨m, hmdef⟩ : ∃ m : tw (p ^ (a + b)) i ⟶ tw (p ^ (a + b)) i, m = p ^ b • 𝟙 _ := ⟨_, rfl⟩
  have hm : ∀ (U : Scheme.{0}) (x : Sec (tw (p ^ (a + b)) i) U), Sec.map m x = p ^ b • x := fun U x => by
    rw [hmdef]; exact sec_nsmul _ _ x
  have hw : m ≫ π = 0 := morph_zero_of_sec _ fun U x => by
    change Sec.map π (Sec.map m x) = 0
    rw [hm, sec_map_nsmul]
    exact sec_char (q := p ^ b) (F := tw (p ^ b) i) (Sec.map π x)
  have hQ : p ^ a • m = 0 := by
    rw [hmdef, smul_smul, ← pow_add]
    exact morph_zero_of_sec _ fun U x => by rw [sec_nsmul]; exact sec_char x

  have hπepi : Epi π := by
    refine SheafSectionLemmas.epi_of_loc π fun U y => ?_
    rcases Nat.eq_zero_or_pos b with hb | hb
    · have hy : y = 0 := by
        have h0 := sec_char (q := p ^ b) (F := tw (p ^ b) i) y
        have h1 : p ^ b = 1 := by rw [hb, pow_zero]
        exact (one_nsmul y).symm.trans ((congrArg (fun n : ℕ => n • y) h1.symm).trans h0)
      exact SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true U) fun V g _ => ⟨0, by rw [sec_map_zero', hy]; exact (res_zero g).symm⟩
    · refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ b) i U y) fun V g hy => ?_
      rcases hy with hy | ⟨ξ, c, hy⟩
      · exact loc_of_img π g y 0 (by rw [sec_map_zero']; exact hy.symm)
      · refine SheafSectionLemmas.loc_mono (KummerTwistLemmas.rootLoc p a b hb V ξ) fun W k ⟨ζ, hζ⟩ => ⟨c • twGen i ζ, ?_⟩
        rw [sec_map_nsmul, hπg]
        change c • twGen i (pw (dvdB p a b) ζ) = Sec.res (k ≫ g) (show Sec (tw (p ^ b) i) U from y)
        rw [TwSec.res_comp, hy, res_nsmul, twGen_res]
        congr 2
        apply Subtype.ext
        change ζ.1 ^ (p ^ (a + b) / p ^ b) = (k.appTop.hom) ξ.1
        rw [← hζ, Nat.pow_div (Nat.le_add_left b a) (Nat.pos_of_ne_zero hp), Nat.add_sub_cancel]

  have hepi : Epi (kernel.lift π m hw) := by
    refine SheafSectionLemmas.epi_lift_of_loc m π hw fun U y hy => ?_
    refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · exact loc_of_img m g y 0 (by rw [sec_map_zero']; exact hy'.symm)
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact loc_of_img m g y 0 ((SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _)
      · have h0 : c • twGen i (pw (dvdB p a b) ζ) = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', sec_map_nsmul, hπg] at this
          exact this
        obtain ⟨d, rfl⟩ := (hG (p ^ b) i).2.1 V (pw (dvdB p a b) ζ) c h0
        exact loc_of_img m g y (d • twGen i ζ) (by rw [hm, smul_smul, hy'])

  have hker : kernel.ι m ≫ π' = 0 := by
    refine SheafSectionLemmas.ker_comp_zero m π' fun U y hy => ?_
    refine SheafSectionLemmas.sec_eq_of_loc _ _ (SheafSectionLemmas.loc_mono (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_)
    rw [res_zero, CupSpec.map_res]
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · rw [hy', sec_map_zero']
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact (SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _
      · have h0 : (p ^ b * c) • twGen i ζ = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', hm, smul_smul] at this
          exact this
        have hd := (hG (p ^ (a + b)) i).2.1 V ζ _ h0
        rw [pow_add, mul_comm (p ^ a)] at hd
        obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos (Nat.pos_of_ne_zero hp) b) hd
        rw [hy', sec_map_nsmul, hπ'g, ← smul_smul]
        exact sec_char (q := p ^ a) (F := tw (p ^ a) i) _

  obtain ⟨e, hedef⟩ : ∃ e, e = kernel.lift π m hw := ⟨_, rfl⟩
  have he : e ≫ kernel.ι π = m := by rw [hedef]; exact kernel.lift_ι _ _ _
  have : Epi e := by rw [hedef]; exact hepi
  have hz : kernel.ι e ≫ π' = 0 := by
    have h1 : kernel.ι e ≫ m = 0 := by rw [← he, kernel.condition_assoc, zero_comp]
    rw [← kernel.lift_ι m (kernel.ι e) h1, Category.assoc, hker, comp_zero]
  obtain ⟨l, hl⟩ : ∃ l, e ≫ l = π' := ⟨Abelian.epiDesc e π' hz, Abelian.comp_epiDesc e π' hz⟩
  have hcomp : kernel.ι π ≫ π' = p ^ b • l := by
    apply (cancel_epi e).1
    have h2 : e ≫ kernel.ι π ≫ π' = m ≫ π' := by rw [← Category.assoc, he]
    rw [h2, Preadditive.comp_nsmul, hl, hmdef, Preadditive.nsmul_comp, Category.id_comp]
  have htor : p ^ a • kernel.ι π = 0 := by
    apply (cancel_epi e).1
    rw [Preadditive.comp_nsmul, he, hQ, comp_zero]
  exact ⟨π, π', l, hπ, hπ', hπepi, htor, hcomp⟩

end CrystallineSemistableComparison.TwSeq
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace CyclicComplexMaps

def semiComp {T S R : Type} [CommRing T] [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx T} {J : GlobalTheory.EtC.Cx S} {L : GlobalTheory.EtC.Cx R}
    (τ : SemiMap I J) (ρ : SemiMap J L) : SemiMap I L where
  app U s := (ρ.app U s).comp (τ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.nat, τ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.comm, τ.comm]

theorem pick_neg' {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  exact dif_neg h

theorem op_zero {S R : Type} [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx S} {J : GlobalTheory.EtC.Cx R} (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (0 : SemiMap I J).op.app E n x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]
  · rfl
  · rw [Cocycle.coe_zero, CupSpec.ev_zero]
    rfl

end CyclicComplexMaps

theorem redSh (hF : FormalIn) : InRedSh := by
  intro Q q _ _ h i π hπ E n z
  by_cases hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))),
      ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
          (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a)
  · have hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U),
        (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
          Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
            (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a) := pick_spec hρ
    have hτ := hF.et.red Q q h i
    let σ := CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))
    have hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 =
        π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) := by
      refine CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)
      obtain ⟨ξ, hξ⟩ := CyclicComplexMaps.prim_pow h ζ
      change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))
      rw [hτ U ζ ξ hξ, hπ U ζ ξ hξ]
      exact hρ' U (twGen i ξ)
    obtain ⟨α, rfl⟩ := z.mk_surjective
    obtain ⟨β, hβ⟩ := SemiMap.image_exists (redMap Q q i) E n α
    obtain ⟨γ, hγ⟩ := SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _
    rw [SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ,
      ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]
    congr 1
    apply Cocycle.ext
    apply CupSpec.ev_ext
    intro p s hs U x
    rw [hγ, hβ]
    exact (CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm
  · have h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0 := CyclicComplexMaps.pick_neg' hρ
    obtain ⟨y, hy⟩ := (hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2
      (HK.post _ ((chains _).obj E) π n z)
    rw [← hy]
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _
    rw [h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]

theorem bock_tw (hS : InTwSeq) : BocksteinInputFromFormal := fun hF => bock_of hS (redSh hF) hF

end CrystallineSemistableComparison
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock

section

@[expose] public section

namespace CrystallineSemistableComparison

theorem bock : BocksteinInputFromFormal := fun hF => bock_tw (TwSeq.twSeq hF.et.gen) hF

end CrystallineSemistableComparison
end
end
