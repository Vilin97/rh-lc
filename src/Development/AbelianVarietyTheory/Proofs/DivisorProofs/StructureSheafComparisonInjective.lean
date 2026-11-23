module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainValueOnThickeningHomEqSubOfGluedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleLocalSectionsRestrictCompatibly

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem resThk_pt (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    spMap ((RingHom.id (Sec (algStr R T.obj.B) p.1.1.1)).comp
      (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) : Sec (algStr R T.obj.B) q.1.1.1 →+* Sec (algStr R T.obj.B) p.1.1.1)) ≫
      (affPt (algStr R T.obj.B) q.1.1 ≫ pt T) = affPt (algStr R T.obj.B) p.1.1 ≫ pt T := by
  rw [RingHom.id_comp, ← Category.assoc, affPt_res]

def resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) : thk T q ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq)) (resThk_pt T hpq)⟩

theorem bM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    bM T q ≫ resThk T hpq = bM T p :=
  ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun b ↦
    res_toSec R T.obj.B (homOfLE (Pair.le_fst hpq)).op b))

theorem aM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    aM T q ≫ resThk T hpq = (affF s).map (homOfLE (Pair.le_snd hpq)).op ≫ aM T p :=
  ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun u ↦
    (congrArg (fun t ↦ t.hom u) ((pt T).appLE_map q.2 (homOfLE (Pair.le_fst hpq)).op)).trans
      (congrArg (fun t ↦ t.hom u) ((pt T).map_appLE p.2 (homOfLE (Pair.le_snd hpq)).op)).symm))

theorem hSec_res (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s))
    (hg : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a))
    (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q) :
    Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  set ρ := Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) with hρ
  let d : op q.1.2 ⟶ op p.1.2 := (homOfLE (Pair.le_snd hpq)).op
  have e1 : fv f (bM T p) = ρ (fv f (bM T q)) + fv f (resThk T hpq) := by
    rw [← bM_resThk T hpq]; exact f.2 _ _
  have e2 : ρ (fv f (aM T q)) + fv f (resThk T hpq) =
      secPullA T p (fv f ((affF s).map d)) + fv f (aM T p) := by
    have k := f.2 (aM T q) (resThk T hpq)
    rw [aM_resThk] at k
    exact k.symm.trans (f.2 ((affF s).map d) (aM T p))
  have e3 : g (op p.1.2) = Sec.res s (Pair.le_snd hpq) (g (op q.1.2)) +
      (show Sec s p.1.2.1 from fv f ((affF s).map d)) :=
    sub_eq_iff_eq_add'.1 (hg d)
  have e4 : ∀ u, secPullA T p (Sec.res s (Pair.le_snd hpq) u) = ρ (secPullA T q u) := fun u ↦
    (congrArg (fun m ↦ m.hom.φ u) (aM_resThk T hpq)).symm
  change ρ (secPullA T q (g (op q.1.2)) + fv f (aM T q) - fv f (bM T q)) =
    secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)
  rw [map_sub, map_add (f := _), e1, e3, map_add (f := _), e4]
  linear_combination e2

end GlobalTheory.CechDR.AffLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleLocalSectionsRestrictCompatiblyStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

theorem _root_.GlobalTheory.T.cocycle_local_sections_restrict_compatibly : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q), Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  first | exact @GlobalTheory.CechDR.AffLoc.hSec_res | exact GlobalTheory.CechDR.AffLoc.hSec_res | (intros; apply GlobalTheory.CechDR.AffLoc.hSec_res <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsSpecFromPairs

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

theorem exists_glue_pair {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X)
    (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1))
    (hh : ∀ p q : Pair x, ∀ hpq : p ≤ q,
      ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) :
    ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  have sub : ∀ (p q : Pair x) (y : Sp B), y ∈ p.1.1.1 → y ∈ q.1.1.1 →
      ∃ r : Pair x, r ≤ p ∧ r ≤ q ∧ y ∈ r.1.1.1 := by
    intro p q y hp hq
    have hyU : x.base y ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hp, q.2 hq⟩
    obtain ⟨W, hW, hyW, hWs⟩ := exists_isAffineOpen_mem_and_subset hyU
    have hyV : y ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ x ⁻¹ᵁ W := ⟨⟨hp, hq⟩, hyW⟩
    obtain ⟨V, hV, hyV', hVs⟩ := exists_isAffineOpen_mem_and_subset hyV
    refine ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), fun z hz ↦ (hVs hz).2⟩, ?_, ?_, hyV'⟩
    · exact ⟨fun z hz ↦ (hVs hz).1.1, fun z hz ↦ (hWs hz).1⟩
    · exact ⟨fun z hz ↦ (hVs hz).1.2, fun z hz ↦ (hWs hz).2⟩
  have cover : ∀ y : Sp B, ∃ p : Pair x, y ∈ p.1.1.1 := by
    intro y
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (show x.base y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hyV, hVs⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ x ⁻¹ᵁ W from hyW)
    exact ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), fun z hz ↦ hVs hz⟩, hyV⟩
  have key : ∀ (p r : Pair x) (hr : r ≤ p) (y : Sp B) (hy : y ∈ r.1.1.1),
      (Sp B).presheaf.germ p.1.1.1 y (Pair.le_fst hr hy) (h p) =
        (Sp B).presheaf.germ r.1.1.1 y hy (h r) := by
    intro p r hr y hy
    rw [← hh r p hr]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  let U : Pair x → (Sp B).Opens := fun p ↦ p.1.1.1
  have hc : TopCat.Presheaf.IsCompatible (Sp B).presheaf U h := by
    intro i j
    refine TopCat.Presheaf.section_ext (Sp B).sheaf _ _ _ fun y hy ↦ ?_
    obtain ⟨r, hri, hrj, hyr⟩ := sub i j y hy.1 hy.2
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ((key i r hri y hyr).trans
      ((key j r hrj y hyr).symm.trans (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm))
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (Sp B).sheaf U ⊤
    (fun _ ↦ homOfLE le_top) (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (cover y)) h hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom s, fun p ↦ ?_⟩
  rw [← hs p]
  have e1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s) = s :=
    Iso.hom_inv_id_apply _ _
  change ((𝟙 (Sp B) : Sp B ⟶ Sp B).appLE ⊤ p.1.1.1 le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s)) = _
  rw [e1]
  simp [Scheme.Hom.appLE]
  rfl

end GlobalTheory.CechDR.AffLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsSpecFromPairsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

theorem _root_.GlobalTheory.T.exists_glue_functions_spec_from_pairs : ∀ {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X) (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1)), (∀ p q : Pair x, ∀ hpq : p ≤ q, ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) → ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  first | exact @GlobalTheory.CechDR.AffLoc.exists_glue_pair | exact GlobalTheory.CechDR.AffLoc.exists_glue_pair | (intros; apply GlobalTheory.CechDR.AffLoc.exists_glue_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR

theorem cmpO_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    Function.Injective (cmpO s) := by
  intro R _ X s
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
  have hg' : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V),
      g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a) :=
    fun U V a ↦ congrFun (congrFun (congrFun hg U) V) a
  have ex : ∀ T : TT s, ∃ G : T.obj.B, ∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p :=
    fun T ↦ GlobalTheory.T.exists_glue_functions_spec_from_pairs T.obj.B (pt T) (hSec f g T) fun p q hpq ↦ GlobalTheory.T.cocycle_local_sections_restrict_compatibly f g hg' T p q hpq
  choose G hG using ex
  exact H1.mk_eq_zero.2 ⟨G, funext fun T ↦ funext fun T' ↦ funext fun φ ↦
    (GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued f g hg' φ (G T) (G T') (hG T) (hG T')).symm⟩

end GlobalTheory.CechDR
end
end
end
